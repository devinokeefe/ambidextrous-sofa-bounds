"""The relaxation G(A;B) of Definition 3.2: its hallways, the width W and the box E_0 of Lemma 5.1, in
exact rational arithmetic, and a floating-point evaluation of lambda*(B_W cap X(w)) for the local search.

An angle is given by its sine, a fraction p/r whose cosine q/r is rational too; for example 3/5 stands
for arcsin(3/5) = 36.87 degrees. The hallways are L_a for a in A, then rho L_b for b in B. Hallway j is
described by the affine functions f_j, g_j of (5.1), each stored as its coefficients (constant, x, y).
"""

from fractions import Fraction
from math import asin, degrees, isqrt


def pythagorean(sine):
    """(q, p, r) with sin = p/r and cos = q/r, for a sine given as a string such as '3/5'."""
    s = Fraction(sine)
    p, r = s.numerator, s.denominator
    q = isqrt(r * r - p * p) if 0 < p < r else 0
    if q == 0 or q * q + p * p != r * r:
        raise ValueError(f"{sine} is not the sine of an angle in (0, 90) degrees with rational cosine")
    return q, p, r


class Relaxation:
    def __init__(self, A, B):
        self.triples = [pythagorean(s) for s in A + B]
        self.mirrored = [0] * len(A) + [1] * len(B)
        self.f, self.g = [], []
        for (q, p, r), mirrored in zip(self.triples, self.mirrored, strict=True):
            c, s = Fraction(q, r), Fraction(p, r)
            if mirrored:  # f and g evaluated at rho(x, y) = (x, 1 - y)
                self.f.append((s, c, -s))
                self.g.append((c, -s, -c))
            else:
                self.f.append((0, c, s))
                self.g.append((0, -s, c))
        self.W = min(width(Fraction(q, r), Fraction(p, r)) for q, p, r in self.triples)

        def degree_list(sines):
            return ",".join(f"{degrees(asin(Fraction(s))):.2f}" for s in sines)

        self.name = f"R({degree_list(A)} ; {degree_list(B)}) W={self.W:.4f}"

    def box(self):
        """E_0 of Lemma 5.1: for each hallway, u_1 in [min f - 1, max f] and u_2 in [min g - 1, max g]."""
        corners = [(0, 0), (self.W, 0), (self.W, 1), (0, 1)]
        box = []
        for f, g in zip(self.f, self.g, strict=True):
            for h in (f, g):
                values = [h[0] + h[1] * x + h[2] * y for x, y in corners]
                box.append((min(values) - 1, max(values)))
        return box

    def lam_star(self, w):
        """lambda*(B_W cap X(w)) in floating point, for w = (u^(1)_1, u^(1)_2, u^(2)_1, ...)."""
        W = float(self.W)
        rectangle = [(0.0, 0.0), (W, 0.0), (W, 1.0), (0.0, 1.0)]
        pieces = [(rectangle, [(1.0, 0.0, 0.0), (-1.0, 0.0, W), (0.0, 1.0, 0.0), (0.0, -1.0, 1.0)])]
        for j, (f_exact, g_exact) in enumerate(zip(self.f, self.g, strict=True)):
            f = [float(t) for t in f_exact]
            g = [float(t) for t in g_exact]
            u1, u2 = w[2 * j], w[2 * j + 1]
            both = [at_most(g, u2 + 1), at_most(f, u1 + 1)]
            arms = ([at_least(f, u1)], [at_most(f, u1), at_least(g, u2)])
            new = []
            for poly, constraints in pieces:
                p0 = clip_all(poly, both)
                if not p0:
                    continue
                for arm in arms:
                    p = clip_all(p0, arm)
                    if p:
                        new.append((p, constraints + both + arm))
            pieces = new
            if not pieces:
                return 0
        return largest_component(pieces)


def width(c, s):
    """W_a of Lemma 3.5."""
    return (1 + s) / c + (1 + c) / s


# Floating-point geometry. A half-plane (A, B, C) is the set A x + B y + C >= 0; a piece is a convex
# polygon together with the half-planes that define it.


def at_least(h, v):
    return (h[1], h[2], h[0] - v)


def at_most(h, v):
    return (-h[1], -h[2], v - h[0])


def clip(poly, A, B, C):
    """The part of the convex polygon poly in the half-plane (A, B, C)."""
    values = [A * x + B * y + C for x, y in poly]
    if min(values) >= 0:
        return poly
    if max(values) < 0:
        return []
    n = len(poly)
    out = []
    for i in range(n):
        P, vP = poly[i], values[i]
        Q, vQ = poly[(i + 1) % n], values[(i + 1) % n]
        if vP >= 0:
            out.append(P)
        if (vP > 0 and vQ < 0) or (vP < 0 and vQ > 0):
            t = vP / (vP - vQ)
            out.append((P[0] + (Q[0] - P[0]) * t, P[1] + (Q[1] - P[1]) * t))
    result = []
    for p in out:
        if not result or result[-1] != p:
            result.append(p)
    if len(result) > 1 and result[0] == result[-1]:
        result.pop()
    return result


def clip_all(poly, constraints):
    for h in constraints:
        poly = clip(poly, *h)
        if not poly:
            break
    return poly


def area(poly):
    if len(poly) < 3:
        return 0
    twice = sum(x1 * y2 - x2 * y1 for (x1, y1), (x2, y2) in zip(poly, poly[1:] + poly[:1], strict=True))
    return abs(twice) / 2


def largest_component(pieces):
    """The largest total area of a connected component; two closed pieces are connected if they meet."""
    n = len(pieces)
    parent = list(range(n))

    def find(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    boxes = []
    for poly, _ in pieces:
        xs, ys = [p[0] for p in poly], [p[1] for p in poly]
        boxes.append((min(xs), max(xs), min(ys), max(ys)))
    for i in range(n):
        for j in range(i + 1, n):
            bi, bj = boxes[i], boxes[j]
            if bi[1] < bj[0] or bj[1] < bi[0] or bi[3] < bj[2] or bj[3] < bi[2]:
                continue
            ri, rj = find(i), find(j)
            if ri != rj and clip_all(pieces[i][0], pieces[j][1]):
                parent[ri] = rj
    total = {}
    for i in range(n):
        total[find(i)] = total.get(find(i), 0) + area(pieces[i][0])
    return max(total.values())
