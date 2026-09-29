# Upper bounds for the ambidextrous moving sofa problem: programs and data

This repository accompanies the paper *Upper bounds for the ambidextrous moving sofa problem*
(`paper/main.pdf`). It contains the certificates for Theorem 6.1, G({α1,α2};{α1,α2}) ≤ 353/200, the three
programs that check them, the program that found them, the Lean formalisation, and the records of the runs
reported in the paper. The certificate for 353/200 (1.74 GB) is too large for the repository; it is attached
to the GitHub release as `cert_c_3653_1765.txt.xz` (124 MB).

| Folder | Contents |
|---|---|
| `data/` | `specs/`: the hallways and thresholds; `certs/`: the certificate for 9/5 and a small one for T = 2 |
| `checkers/` | `cchk.c` (C checker), `check_cert.py` with `check_cert_core.py` (Python checker), tests |
| `search/` | `csearch.c` (search program), `run_search.py` (runs it), `local_search.py` (Section 8.1) |
| `checks/` | `relaxation_values.py`: the two areas quoted in Section 8.1 |
| `lean/` | the Lean project: formal proofs and the verified checker (see `lean/README.md`) |
| `paper/` | LaTeX source, figures and the scripts that draw them |
| `runs/` | records of the runs reported in the paper |

`SHA256SUMS.txt` lists the SHA-256 of every file, including the separate certificate; `sha256sum -c
SHA256SUMS.txt` in the top folder checks them. Unpack the certificate with `xz -d cert_c_3653_1765.txt.xz`
and move it to `data/certs/`.

## Checking the certificates

Run these commands from `data/`.

**C checker.** Build with MSVC (`cl -O2 -openmp ../checkers/cchk.c`) or with gcc or clang:
```
gcc -O2 -fopenmp -I ../checkers/portable ../checkers/cchk.c -o cchk
./cchk specs/c_3653_18_10.json 4 18
./cchk specs/c_3653_1765.json 4 20
```
The arguments after the spec file are the number of threads (default 4) and the depth at which the tree is
split into tasks (default 18). Without OpenMP, drop `-fopenmp` and add `-I ../checkers/portable/noomp`. The exit
status is 0 if the certificate is valid, 1 if a leaf exceeds T, and 2 if the certificate could not be checked
(for example, a malformed file or an arithmetic overflow).

**Python checker.** Needs Python 3 and, for speed, `python-flint` (without it, Python's `fractions` are used):
```
CHECK_ARITH=flint python ../checkers/check_cert.py specs/c_3653_18_10.json 16 check_9_5.log
CHECK_ARITH=flint python ../checkers/check_cert.py specs/c_3653_1765.json 16 check_353_200.log
```
The second argument is the number of processes. The log file must not exist yet; an interrupted run is resumed
by repeating the command. `bash ../checkers/test_check_cert.sh` tests the checker on small inputs.

**Lean checker.** See `lean/README.md`.

**Corrupted certificates.** `python ../checkers/make_controls.py` writes four corrupted versions of the 9/5
certificate to `controls/`; all three checkers reject all four.

## Making the certificates

From `data/`, after building `csearch.c` in `search/` (`cl -O2 -openmp csearch.c`, or
`gcc -O2 -fopenmp csearch.c -o csearch -lm`):
```
python ../search/run_search.py 3/5,4/5 3/5,4/5 18/10 c_3653_18_10
python ../search/run_search.py 3/5,4/5 3/5,4/5 353/200 c_3653_1765 -c 16
```
Angles are given by their sines. With MSVC these commands reproduce both certificates byte for byte. Another
compiler may round differently and produce a different tree, which is still a valid certificate if the
checkers accept it. `python ../search/local_search.py 3/5,4/5 3/5,4/5` runs the local search of Section 8.1
(it needs numpy and scipy).

## Code style

The Python files follow `ruff.toml` (`ruff check .` and `ruff format .` in the top folder) and the C files
follow `.clang-format` and `.clang-tidy`. Both C programs compile without warnings with
`gcc -std=c11 -Wall -Wextra -Wshadow -Wpedantic` and with MSVC `-W4 -D_CRT_SECURE_NO_WARNINGS`, and
`test_check_cert.sh` passes shellcheck.

## File formats

**Spec file.** A JSON file such as `specs/c_3653_1765.json`:
```
{"hallways": [[4,3,5,1,0,0], [3,4,5,1,0,0], [4,3,5,1,0,1], [3,4,5,1,0,1]],
 "W": "5", "T": "353/200", "cert": "certs/cert_c_3653_1765.txt", ...}
```
Hallway `[q,p,r,eps,phi,m]` has the angle a with cos a = q/r and sin a = eps·p/r, where p² + q² = r²; it is
L_a if m = 0 and ρ(L_a) if m = 1, and phi = 1 would replace a by a + 180° (it is 0 here). `W` and `T` are the
width of Lemma 5.1 and the threshold.

**Certificate.** The nodes of the tree in preorder, separated by white space. The letter `L` is a leaf; an
integer i in {0, ..., 2k−1}, for k hallways, is a node whose box is bisected at the midpoint of coordinate i,
with the coordinates ordered u⁽¹⁾₁, u⁽¹⁾₂, u⁽²⁾₁, ... as the hallways in the spec file. The lower half comes
first. The root box is E₀ of Lemma 5.1, given for the main certificate in Table 6.1.

## Records

| Claim in the paper | Record in `runs/` |
|---|---|
| Table 6.2, search | `search.txt` |
| Table 6.2, Lean checker | `lean_9_5.txt`, `lean_353_200.txt` |
| Table 6.2, C checker | `c_9_5.txt`, `c_353_200.txt` |
| Table 6.2, Python checker | `python_9_5.txt`, `python_353_200.txt`, with their logs `*.log` |
| Table 8.1; three angles at T = 1.85 (Section 8.1) | `search.txt` |
| Section 8.1, local search | `local_search.txt` |
| Section 8.1, the areas 1.7229… and 1.73172… | `relaxation_values.txt` |
| Section 7, the axioms of the final theorems | `lean_axioms.txt` |
| Corrupted certificates (not in the paper) | `c_controls.txt`, `lean_controls.txt`, `python_controls.txt` |
| Tests of the Python checker (not in the paper) | `test_check_cert.txt`, `test_check_cert_linux.txt` |
| Builds with gcc on Linux (not in the paper) | `linux_build.txt` |

All records were made on 28–29 September 2026 with the files in this repository. Times are wall-clock times
on an Intel Core i9-14900K that was also running other jobs. Software: Microsoft C/C++ 19.12, Python 3.13.5
with python-flint 0.9.0, Lean v4.34.0-rc2.

The worst value printed by a checker is the bound it used for the leaf: the total area of the pieces when that
is at most T, and otherwise the largest component. For some leaves of the 353/200 certificate the total area
is exactly 353/200, so the printed worst value is exactly T.

`cchk.c` reads `W` and `T` with unchecked 64-bit arithmetic, so both must be positive with at most 18 digits
in numerator and denominator, as in all spec files here. All its other arithmetic is checked for overflow.
