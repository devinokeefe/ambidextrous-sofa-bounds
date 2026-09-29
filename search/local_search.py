"""Local search for a large value of lambda*(B_W cap X(w)), a lower estimate of G(A;B) (Section 8.1).

Floating point and heuristic. The starting points are u^(j) = r (cos a_j, sin a_j) + R_{-a_j}(W/2, 0) for
all hallways j, for 13 values of r between 0.15 and 0.75; the best of them is improved by four rounds of
Nelder-Mead.

Usage:  python local_search.py A B        for example  python local_search.py 3/5,4/5 3/5,4/5
A and B are comma-separated sines, as in run_search.py.
"""

import math
import sys

import numpy as np
from scipy.optimize import minimize

from relaxation import Relaxation

NELDER_MEAD = {"maxiter": 4000, "xatol": 1e-8, "fatol": 1e-11, "adaptive": True}


def local_search(rel):
    x0 = float(rel.W) / 2
    best_value, best_w = -1, None
    for r in np.linspace(0.15, 0.75, 13):
        w = []
        for q, p, d in rel.triples:
            c, s = q / d, p / d
            t = math.atan2(s, c)
            w += [r * math.cos(t) + c * x0, r * math.sin(t) - s * x0]
        w = np.array(w)
        value = rel.lam_star(w)
        if value > best_value:
            best_value, best_w = value, w
    for _ in range(4):
        result = minimize(lambda z: -rel.lam_star(z), best_w, method="Nelder-Mead", options=NELDER_MEAD)
        if -result.fun > best_value:
            best_value, best_w = -result.fun, result.x
    return best_value, best_w


if __name__ == "__main__":
    A, B = (s.split(",") if s != "-" else [] for s in sys.argv[1:3])
    rel = Relaxation(A, B)
    value, w = local_search(rel)
    print(
        "{}  local maximum {:.5f}  at w = {}".format(rel.name, value, " ".join(f"{x:.6f}" for x in w)),
        flush=True,
    )
