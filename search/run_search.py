"""Searches for a certificate of G(A;B) <= T (Section 5.5): writes the spec file read by the checkers and
the input file of the search program, then runs the search program csearch, built next to this file.

Usage, from the data folder:
  python ../search/run_search.py A B T NAME [csearch options]
A and B are comma-separated sines, T is a fraction. Writes specs/NAME.json, certs/in_NAME.txt and
certs/cert_NAME.txt. The certificates of Table 6.2 were made with
  python ../search/run_search.py 3/5,4/5 3/5,4/5 18/10 c_3653_18_10
  python ../search/run_search.py 3/5,4/5 3/5,4/5 353/200 c_3653_1765 -c 16
The number of threads is set by OMP_NUM_THREADS (default 4); it does not change the certificate.
Neither does the option -c, which only saves time.
"""

import json
import os
import subprocess
import sys
from fractions import Fraction

from relaxation import Relaxation

MARGIN = 1e-7  # a box is a leaf if its floating-point value is at most T - MARGIN
PRESPLIT = 4096  # number of subtrees searched in parallel


def main(argv):
    A, B = (s.split(",") if s != "-" else [] for s in argv[1:3])
    T, name, options = argv[3], argv[4], argv[5:]
    rel = Relaxation(A, B)

    hallways = [[q, p, r, 1, 0, m] for (q, p, r), m in zip(rel.triples, rel.mirrored, strict=True)]
    spec = {
        "problem": rel.name,
        "hallways": hallways,
        "W": str(rel.W),
        "T": T,
        "cert": f"certs/cert_{name}.txt",
    }
    with open(f"specs/{name}.json", "w") as fh:
        json.dump(spec, fh)

    lines = ["%d %.17g %.17g %.3g %d" % (len(hallways), rel.W, Fraction(T), MARGIN, PRESPLIT)]
    lines += [" ".join(f"{t:.17g}" for t in f + g) for f, g in zip(rel.f, rel.g, strict=True)]
    lines += ["{:.17g} {:.17g}".format(*interval) for interval in rel.box()]
    with open(f"certs/in_{name}.txt", "w") as fh:
        fh.write("\n".join(lines) + "\n")

    program = os.path.join(os.path.dirname(os.path.abspath(__file__)), "csearch")
    env = dict(os.environ, OMP_NUM_THREADS=os.environ.get("OMP_NUM_THREADS", "4"))
    command = [program, f"certs/in_{name}.txt", f"certs/cert_{name}.txt", *options]
    result = subprocess.run(command, capture_output=True, text=True, env=env, check=False)
    print(rel.name, f"T={T}", result.stdout.strip(), result.stderr.strip()[:300], flush=True)
    return result.returncode


if __name__ == "__main__":
    sys.exit(main(sys.argv))
