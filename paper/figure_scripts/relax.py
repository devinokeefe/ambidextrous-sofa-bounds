"""Float geometry of hallway relaxations, used only to draw figures.

Conventions follow the paper:
  f_a(x,y) =  x cos a + y sin a,   g_a(x,y) = -x sin a + y cos a,
  L_a(u)   = {u1 <= f <= u1+1, g <= u2+1}  U  {f <= u1+1, u2 <= g <= u2+1},
  rho(x,y) = (x, 1-y), and the mirrored hallway is rho(L_a(u)).
A half-plane is a triple (A, B, C) meaning A x + B y <= C.
"""

import math

import numpy as np


def clip(poly, hp, eps=1e-12):
    A, B, C = hp
    out = []
    n = len(poly)
    for i in range(n):
        P, Q = poly[i], poly[(i + 1) % n]
        fp = A * P[0] + B * P[1] - C
        fq = A * Q[0] + B * Q[1] - C
        if fp <= eps:
            out.append(P)
        if (fp < -eps and fq > eps) or (fp > eps and fq < -eps):
            t = fp / (fp - fq)
            out.append((P[0] + t * (Q[0] - P[0]), P[1] + t * (Q[1] - P[1])))
    return out


def area(poly):
    if len(poly) < 3:
        return 0.0
    s = 0.0
    for i in range(len(poly)):
        x1, y1 = poly[i]
        x2, y2 = poly[(i + 1) % len(poly)]
        s += x1 * y2 - x2 * y1
    return abs(s) / 2


def affine(a, mirror):
    """Return (F, G) with F = (cx, cy, k) meaning f = cx x + cy y + k."""
    c, s = math.cos(a), math.sin(a)
    if mirror:  # f(x, 1-y), g(x, 1-y)
        return (c, -s, s), (-s, -c, c)
    return (c, s, 0.0), (-s, c, 0.0)


def _le(L, val):  # L <= val
    return (L[0], L[1], val - L[2])


def _ge(L, val):  # L >= val
    return (-L[0], -L[1], -(val - L[2]))


def pieces(a, u, mirror=False):
    """The two closed convex pieces of L_a(u) (or its mirror) with disjoint interiors."""
    F, G = affine(a, mirror)
    u1, u2 = u
    P1 = [_ge(F, u1), _le(F, u1 + 1), _le(G, u2 + 1)]
    P2 = [_le(F, u1), _ge(G, u2), _le(G, u2 + 1)]
    return [P1, P2]


def box(x0, x1, y0=0.0, y1=1.0):
    return [(x0, y0), (x1, y0), (x1, y1), (x0, y1)]


def intersection(halls, base):
    """halls: list of (a, u, mirror). Returns list of (polygon, constraints) pieces of base ∩ ⋂ halls."""
    combos = [[]]
    for a, u, m in halls:
        combos = [c + p for c in combos for p in pieces(a, u, m)]
    out = []
    for cons in combos:
        poly = base
        for hp in cons:
            poly = clip(poly, hp)
            if not poly:
                break
        if poly:
            out.append((poly, cons))
    return out


def components(pcs):
    n = len(pcs)
    par = list(range(n))

    def find(i):
        while par[i] != i:
            par[i] = par[par[i]]
            i = par[i]
        return i

    for i in range(n):
        for j in range(i + 1, n):
            poly = pcs[i][0]
            for hp in pcs[j][1]:
                poly = clip(poly, (hp[0], hp[1], hp[2] + 1e-10))
                if not poly:
                    break
            if poly:
                par[find(i)] = find(j)
    comp = {}
    for i in range(n):
        comp.setdefault(find(i), []).append(i)
    res = [(sum(area(pcs[i][0]) for i in idx), [pcs[i][0] for i in idx]) for idx in comp.values()]
    res.sort(key=lambda t: -t[0])
    return res


def lam_star(halls, base):
    comps = components(intersection(halls, base))
    return comps[0][0] if comps else 0.0


def hallway_outline(a, u, mirror=False, R=30.0):
    """Polygon of L_a(u) (or mirror) clipped to a large box, for drawing."""
    L0 = [(-R, 0.0), (0.0, 0.0), (0.0, -R), (1.0, -R), (1.0, 1.0), (-R, 1.0)]
    c, s = math.cos(a), math.sin(a)
    pts = []
    for X0, Y0 in L0:
        X, Y = X0 + u[0], Y0 + u[1]
        x, y = c * X - s * Y, s * X + c * Y
        if mirror:
            y = 1 - y
        pts.append((x, y))
    return np.array(pts)
