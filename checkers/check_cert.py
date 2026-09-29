"""The Python checker: checks a certificate for G(A;B) <= T in exact rational arithmetic (Section 6.2).

The geometry and the tree walk are in check_cert_core.py. This program reads the certificate strictly
(only the tokens L and 0, ..., 2k-1 for k hallways, separated by white space), checks that
W >= min_a W_a (Lemma 5.1), splits the tree into tasks that are checked in parallel, and exits with
status 0 only after "CERTIFICATE VALID", 1 if the certificate is rejected, and 2 on a usage or log error.

Finished tasks are recorded in a log, so that an interrupted run can be resumed with the same log. The
first line of the log is a fingerprint of the run (hashes of the spec, the certificate, both program
files and the task layout, and the values of T and W); a log written for another run is refused. The
verdict also requires one record per task, leaf counts that add up to the number of leaves, and no
recorded value above T.

Usage, from the data folder, with a log file that does not exist yet:
  CHECK_ARITH=flint python ../checkers/check_cert.py specs/c_3653_1765.json NPROC LOG [MAXLEAVES]
"""

import hashlib
import json
import os
import sys
import time
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check_cert_core as C  # noqa: E402

DEPTH_CUT = 24  # the tree is first split at this depth
SPLIT_DEPTH = 6  # tasks with more than MAXLEAVES leaves are split again, this much deeper
SEPARATORS = b" \t\r\n\f\v"
ALLOWED = b"L0123456789" + SEPARATORS


def fail(message, status):
    print(message, flush=True)
    sys.exit(status)


def positive_int(text, name):
    try:
        v = int(text)
    except ValueError:
        v = 0
    if v < 1:
        fail(f"usage error: {name} must be a positive integer, got {text!r}", 2)
    return v


def sha256_file(path, chunk=1 << 24):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for block in iter(lambda: fh.read(chunk), b""):
            h.update(block)
    return h.hexdigest()


def read_spec(path):
    try:
        with open(path) as fh:
            spec = json.load(fh)
        hallways, W, T = C.parse_spec(spec)
        if not os.path.isfile(spec["cert"]):
            raise OSError("certificate file {} not found".format(spec["cert"]))
    except (OSError, ValueError, KeyError, TypeError, ZeroDivisionError, AssertionError) as e:
        fail(f"usage error: cannot read spec {path} ({e})", 2)
    # Lemma 5.1 needs W >= min_a W_a, with W_a = (1 + s)/c + (1 + c)/s (Lemma 3.5)
    width = min((1 + C.F(p, r)) / C.F(q, r) + (1 + C.F(q, r)) / C.F(p, r) for q, p, r, *_ in spec["hallways"])
    if width > W:
        fail("CERTIFICATE INVALID (W too small for the normalisation lemma)", 1)
    return spec, hallways, W, T


def read_tokens(path, ncoord, chunk=1 << 24):
    """The tokens of a certificate as a byte array (see check_cert_core), read strictly."""

    def convert(text, out):
        words = text.split()
        out.extend(C.LEAF if w == b"L" else int(w) for w in words)
        return words.count(b"L")

    out, rest, nleaf = bytearray(), b"", 0
    with open(path, "rb") as fh:
        while True:
            block = fh.read(chunk)
            if block.translate(None, ALLOWED):
                raise ValueError("a character other than L, a digit or white space")
            if not block:
                break
            block = rest + block
            cut = max(block.rfind(bytes([c])) for c in SEPARATORS)  # the last separator in the block
            if cut < 0:
                rest = block
                continue
            rest = block[cut + 1 :]
            nleaf += convert(block[:cut], out)
    nleaf += convert(rest, out)
    if out.count(C.LEAF) != nleaf:
        raise ValueError("255 is not a valid token")
    if out.translate(None, bytes(range(ncoord)) + bytes([C.LEAF])):
        raise ValueError("a split coordinate is not below %d" % ncoord)
    return out


def make_tasks(tokens, root_box, maxleaves):
    """Tasks of at most maxleaves leaves, largest first, in an order that depends only on the tree."""
    stack, small = C.split_tasks(tokens, root_box, DEPTH_CUT), []
    while stack:
        task = stack.pop()
        if task[0].count(C.LEAF) <= maxleaves:
            small.append(task)
        else:
            stack.extend(C.split_tasks(task[0], task[1], SPLIT_DEPTH))
    leaves = {id(t): t[0].count(C.LEAF) for t in small}
    small.sort(key=lambda t: (-leaves[id(t)], repr(t[1])))  # distinct subtrees have distinct boxes
    return [(t, leaves[id(t)], box_hash(t[1])) for t in small]


def box_hash(box):
    return hashlib.sha256(repr([(str(lo), str(hi)) for lo, hi in box]).encode()).hexdigest()[:16]


def layout_hash(tasks):
    h = hashlib.sha256()
    for i, (task, leaves, bhash) in enumerate(tasks):
        h.update(("%d %d %d %s\n" % (i, leaves, len(task[0]), bhash)).encode())
    return h.hexdigest()


def parse_record(line, ntasks):
    """A log record: task index, worst bound, leaves above T, leaves, complete, box hash."""
    fields = line.split()
    if len(fields) != 6:
        raise ValueError("wrong number of fields")
    i, bad, leaves = int(fields[0]), int(fields[2]), int(fields[3])
    if not 0 <= i < ntasks or bad < 0 or fields[4] not in ("True", "False"):
        raise ValueError("field out of range")
    return i, C.F(fields[1]), bad, leaves, fields[4] == "True", fields[5]


def read_log(path, header, tasks):
    """The records of an existing log, as {task index: (worst, bad, leaves, complete)}."""
    try:
        with open(path, encoding="ascii") as fh:
            lines = fh.read().splitlines()
    except (OSError, UnicodeError) as e:
        fail(f"LOG REFUSED: cannot read {path} ({e})", 2)
    if not lines or lines[0] != header:
        fail(
            f"LOG REFUSED: {path} was written for a different run (certificate, spec, threshold, "
            "checker or task layout differ). Use a new log file.",
            2,
        )
    done = {}
    for line in lines[1:]:
        try:
            i, worst, bad, leaves, complete, bhash = parse_record(line, len(tasks))
        except (ValueError, TypeError, ZeroDivisionError):
            fail(f"LOG REFUSED: malformed record {line!r}", 2)
        if i in done:
            fail(f"LOG REFUSED: duplicate task index in {line!r}", 2)
        if leaves != tasks[i][1] or bhash != tasks[i][2]:
            fail("LOG REFUSED: record %r does not match task %d" % (line, i), 2)
        done[i] = (worst, bad, leaves, complete)
    return done


def run(item):
    i, task = item
    return (i, *C.check_subtree(task))


def main(argv):
    if len(argv) not in (4, 5):
        fail("usage: python check_cert.py spec.json NPROC LOG [MAXLEAVES]", 2)
    spec_path, log_path = argv[1], argv[3]
    nproc = positive_int(argv[2], "NPROC")
    maxleaves = positive_int(argv[4], "MAXLEAVES") if len(argv) > 4 else 200000
    spec, hallways, W, T = read_spec(spec_path)

    t0 = time.time()
    try:
        tokens = read_tokens(spec["cert"], 2 * len(hallways))
    except OSError as e:
        fail("usage error: cannot read certificate {} ({})".format(spec["cert"], e), 2)
    except ValueError as e:
        fail(f"CERTIFICATE INVALID (malformed certificate: {e})", 1)
    total_leaves = tokens.count(C.LEAF)
    try:
        tasks = make_tasks(tokens, C.initial_box(hallways, W), maxleaves)
    except (ValueError, KeyError, IndexError) as e:
        fail(f"CERTIFICATE INVALID (structure: {e})", 1)
    del tokens

    fingerprint = {
        "spec_sha256": sha256_file(spec_path),
        "cert_sha256": sha256_file(spec["cert"]),
        "check_cert_core_sha256": sha256_file(C.__file__),
        "check_cert_sha256": sha256_file(os.path.abspath(__file__)),
        "arith": C.ARITH,
        "T": str(T),
        "W": str(W),
        "hallways": spec["hallways"],
        "depth_cut": DEPTH_CUT,
        "maxleaves": maxleaves,
        "tasks": len(tasks),
        "leaves": total_leaves,
        "layout_sha256": layout_hash(tasks),
    }
    header = "# " + json.dumps(fingerprint, sort_keys=True)
    if os.path.exists(log_path):
        done = read_log(log_path, header, tasks)
    else:
        done = {}
        try:
            with open(log_path, "w", encoding="ascii") as fh:
                fh.write(header + "\n")
        except OSError as e:
            fail(f"usage error: cannot create log {log_path} ({e})", 2)

    todo = [(i, task) for i, (task, _, _) in enumerate(tasks) if i not in done]
    print(
        f"spec {spec_path} arith {C.ARITH} leaves {total_leaves} tasks {len(tasks)} "
        f"already done {len(done)} T {T} {float(T)} parse {time.time() - t0:.1f}s",
        flush=True,
    )
    try:
        with (
            open(log_path, "a", encoding="ascii") as fh,
            Pool(nproc, initializer=C.init_worker, initargs=(hallways, W, T)) as pool,
        ):
            for n, (i, worst, bad, leaves, complete) in enumerate(
                pool.imap_unordered(run, todo, chunksize=1), start=1
            ):
                done[i] = (worst, bad, leaves, complete)
                fh.write("%d %s %d %d %s %s\n" % (i, worst, bad, leaves, complete, tasks[i][2]))
                fh.flush()
                if n % 2000 == 0:
                    elapsed = time.time() - t0
                    print("progress: %d/%d tasks, %.0fs" % (len(done), len(tasks), elapsed), flush=True)
    except OSError as e:
        fail(
            f"LOG ERROR: cannot write to {log_path} ({e}); no verdict. The log may end with an incomplete "
            "record: resume with it only if its last line is complete, otherwise use a new log.",
            2,
        )

    worst = max(r[0] for r in done.values())
    bad = sum(r[1] for r in done.values())
    leaves = sum(r[2] for r in done.values())
    complete = all(r[3] for r in done.values())
    covered = (
        len(done) == len(tasks) and all(done[i][2] == tasks[i][1] for i in done) and leaves == total_leaves
    )
    valid = bad == 0 and complete and covered and worst <= T
    print(
        "leaves %d of %d ; worst leaf lambda* = %.9f (exact %s) ; leaves exceeding T: %d ; "
        "structure ok: %s ; time %.1fs"
        % (leaves, total_leaves, float(worst), worst, bad, complete and covered, time.time() - t0)
    )
    print("CERTIFICATE %s" % ("VALID" if valid else "INVALID"), flush=True)
    sys.exit(0 if valid else 1)


if __name__ == "__main__":
    main(sys.argv)
