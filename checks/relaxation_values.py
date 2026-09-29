"""Checks the two configurations of Section 8.1 (Figure 8.1) in exact rational arithmetic, with the
routines of the Python checker. For hallway parameters u_1 = v_1 (angle a1 = arcsin 3/5) and u_2 = v_2
(a2 = arcsin 4/5) it computes the intersection
  H cap L_{a1}(u_1) cap L_{a2}(u_2) cap rho L_{a1}(v_1) cap rho L_{a2}(v_2)
and the areas of its connected components. Expected: both intersections are connected, with areas
  (a) 1.72296... at the positions taken by Romik's motions,
  (b) 29092957301/16800000000 = 1.73172... at u_1 = (0.1260, 0.4425), u_2 = (0.1322, 0.5397).

(a) Romik's shape moves along the rotation path x(t) of [Romik 2018, Theorem 5]. At orientation t it lies in
the hallway x(t) + R_t(L_0) = L_t(u) with u = R_{-t} x(t), and, being symmetric under rho, also in rho L_t(u).
The path is evaluated in floating point and u is rounded to a fraction with denominator at most 10^12.

The checker works in the window B_W = [0, 5] x [0, 1], so each configuration is first moved 3 to the right
(u -> u + R_{-a}(3, 0)); by Lemma 3.5 the intersection then lies in the window. A box with a = b and c = d,
that is a single parameter point, gives exactly the intersection X(w) (Lemma 5.2).

Usage, from the data folder:  python ../checks/relaxation_values.py
"""

import json
import math
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "checkers"))
import check_cert_core as C  # noqa: E402

# Romik's rotation path (constants from [Romik 2018, Theorem 5])
BETA = 0.289653820817320941
E1 = 0.875287362412732241
F1 = 1.202938908156911389
F2 = -(math.sqrt(2) - 1) * F1
K1, K6, K5 = (1 - E1, 0.5), (1 - 4.0 / 3 * E1, 0.5), (1 - 5.0 / 3 * E1, 0.5)
SHIFT = 3  # moves the configuration into B_W


def rotate(t, v):
    c, s = math.cos(t), math.sin(t)
    return (c * v[0] - s * v[1], s * v[0] + c * v[1])


def x_romik(t):
    """The point x(t) of Romik's rotation path."""
    if t < BETA:
        v, k = rotate(t, (E1 * math.cos(t) - 1, E1 * math.sin(t) - 0.5)), K1
    elif t <= math.pi / 2 - BETA:
        c, s = math.cos(t / 2), math.sin(t / 2)
        v, k = rotate(t, (F1 * c + F2 * s - 1, -F2 * c + F1 * s - 1)), K6
    else:
        v, k = rotate(t, (E1 * math.cos(t) - 0.5, E1 * math.sin(t) - 1)), K5
    return (v[0] + k[0], v[1] + k[1])


def romik_positions(angles):
    """u = R_{-t} x(t) at the orientations t of the angles, rounded to fractions."""
    u = []
    for c, s in angles:
        x, y = x_romik(math.atan2(float(s), float(c)))
        for v in (float(c) * x + float(s) * y, -float(s) * x + float(c) * y):
            r = Fraction(v).limit_denominator(10**12)
            u.append(C.F(r.numerator, r.denominator))
    return u


def show(a):
    """A component area: the exact fraction if it is short, and its decimal value."""
    return (f"{a} = " if len(str(a)) < 40 else "") + f"{float(a):.9f}"


with open("specs/c_3653_1765.json") as fh:
    hallways, W, T = C.parse_spec(json.load(fh))
angles = [(C.F(4, 5), C.F(3, 5)), (C.F(3, 5), C.F(4, 5))]  # (cos, sin) of a1 and a2
search = [C.F(1260, 10000), C.F(4425, 10000), C.F(1322, 10000), C.F(5397, 10000)]

for label, p in (("(a) Romik's positions", romik_positions(angles)), ("(b) local search", search)):
    # the x-extent of H cap L_{a1}(u_1), from the proof of Lemma 3.5
    c1, s1 = angles[0]
    xlo = min((p[0] - s1) / c1, (-p[1] - 1) / s1) + SHIFT
    xhi = max((p[0] + 1) / c1, (c1 - p[1]) / s1) + SHIFT
    assert xlo >= 0 and xhi <= W, "the shifted intersection is not in B_W"
    box = []
    for j in (0, 1, 0, 1):  # hallways a1, a2, rho a1, rho a2
        (c, s), u1, u2 = angles[j], p[2 * j], p[2 * j + 1]
        box += [(u1 + SHIFT * c, u1 + SHIFT * c), (u2 - SHIFT * s, u2 - SHIFT * s)]
    areas, polys = C.pieces(hallways, W, box)
    comps = sorted(C.components(areas, polys), reverse=True)
    print(label + ": u_1 = ({:.4f}, {:.4f}), u_2 = ({:.4f}, {:.4f})".format(*tuple(float(t) for t in p)))
    print(
        "  %d pieces, %d connected component(s), areas %s"
        % (len(polys), len(comps), ", ".join(show(a) for a in comps))
    )
