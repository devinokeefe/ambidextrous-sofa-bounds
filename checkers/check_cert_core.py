"""Exact rational geometry and tree walk of the Python checker; the command line is check_cert.py.

For a leaf box E, the checker bounds Gamma(E) = lambda*(B_W cap cap_j Xhat_j), the largest area of a
connected component. Inside {f_j <= b + 1, g_j <= d + 1}, the set Xhat_j of Lemma 5.2 is split into the
pieces {g_j >= c} and {g_j <= c, f_j >= a}, and two pieces touch if a vertex of one lies in the other or
two of their edges meet. Both choices differ from those made in cchk.c.

A hallway is the pair (f, g) of its affine functions, each stored as its coefficients (constant, x, y).
A box is a list of intervals (lo, hi), in the order u^(1)_1, u^(1)_2, u^(2)_1, ...

Arithmetic: fractions.Fraction, or python-flint's fmpq if CHECK_ARITH=flint (about five times faster).
"""

import os

if os.environ.get("CHECK_ARITH", "fraction") == "flint":
    import flint

    def F(p, q=1):
        """The rational number p/q, or the value of a string such as '353/200'."""
        if isinstance(p, str):
            num, _, den = p.partition("/")
            return flint.fmpq(int(num), int(den) if den else 1)
        return flint.fmpq(p, q)

    ARITH = "flint.fmpq"
else:
    from fractions import Fraction as F

    ARITH = "fractions.Fraction"

LEAF = 255  # the token L in a byte array of tokens; the bisection of coordinate k is stored as k


def parse_spec(spec):
    """The hallways, W and T given by a spec file (as a dict).

    Hallway [q, p, r, eps, phi, m] has cos a = q/r and sin a = eps p/r; phi = 1 replaces a by a + 180
    degrees, and m = 1 gives the mirrored hallway rho(L_a), with rho(x, y) = (x, 1 - y).
    """
    hallways = []
    for q, p, r, eps, phi, mirrored in spec["hallways"]:
        assert q * q + p * p == r * r and r > 0
        cos, sin = F(q, r), F(eps * p, r)
        if phi:
            cos, sin = -cos, -sin
        if mirrored:  # f and g evaluated at (x, 1 - y)
            f, g = (sin, cos, -sin), (cos, -sin, -cos)
        else:
            f, g = (F(0), cos, sin), (F(0), -sin, cos)
        hallways.append((f, g))
    return hallways, F(spec["W"]), F(spec["T"])


def value(fn, x, y):
    return fn[0] + fn[1] * x + fn[2] * y


def initial_box(hallways, W):
    """The box E_0 of Lemma 5.1: u_1 in [min f - 1, max f] and u_2 in [min g - 1, max g] over B_W."""
    corners = [(F(0), F(0)), (W, F(0)), (W, F(1)), (F(0), F(1))]
    box = []
    for f, g in hallways:
        for fn in (f, g):
            values = [value(fn, x, y) for x, y in corners]
            box.append((min(values) - 1, max(values)))
    return box


def bisect(box, k):
    """The lower and upper halves of the box, bisected at the midpoint of coordinate k."""
    lo, hi = box[k]
    mid = (lo + hi) / 2
    lower, upper = list(box), list(box)
    lower[k] = (lo, mid)
    upper[k] = (mid, hi)
    return lower, upper


# ---------------------------------------------------------------------------------------------------
# Polygons: lists of vertices (x, y) of a closed convex polygon, possibly degenerate (a segment or a
# point).


def cut(poly, fn, sense, bound):
    """The part of poly where sense * (fn - bound) >= 0 (one step of Sutherland-Hodgman)."""
    if not poly:
        return poly
    s = [sense * (value(fn, x, y) - bound) for x, y in poly]
    out = []
    n = len(poly)
    for i in range(n):
        j = (i + 1) % n
        if s[i] >= 0:
            out.append(poly[i])
        if s[i] * s[j] < 0:
            t = s[i] / (s[i] - s[j])
            (x1, y1), (x2, y2) = poly[i], poly[j]
            out.append((x1 + t * (x2 - x1), y1 + t * (y2 - y1)))
    result = []
    for p in out:
        if p not in result:  # repeated vertices; the order of a convex polygon is kept
            result.append(p)
    return result


def area(poly):
    if len(poly) < 3:
        return F(0)
    twice = F(0)
    for i in range(len(poly)):
        (x1, y1), (x2, y2) = poly[i], poly[(i + 1) % len(poly)]
        twice += x1 * y2 - x2 * y1
    return abs(twice) / 2


def orient(p, q, r):
    return (q[0] - p[0]) * (r[1] - p[1]) - (q[1] - p[1]) * (r[0] - p[0])


def in_box(p, q, r):
    """Whether r lies in the bounding box of the segment pq (for r on the line pq: on the segment)."""
    return min(p[0], q[0]) <= r[0] <= max(p[0], q[0]) and min(p[1], q[1]) <= r[1] <= max(p[1], q[1])


def segments_meet(p1, p2, p3, p4):
    """Whether the closed segments p1p2 and p3p4 meet."""
    d1, d2 = orient(p3, p4, p1), orient(p3, p4, p2)
    d3, d4 = orient(p1, p2, p3), orient(p1, p2, p4)
    if ((d1 > 0 and d2 < 0) or (d1 < 0 and d2 > 0)) and ((d3 > 0 and d4 < 0) or (d3 < 0 and d4 > 0)):
        return True
    return (
        (d1 == 0 and in_box(p3, p4, p1))
        or (d2 == 0 and in_box(p3, p4, p2))
        or (d3 == 0 and in_box(p1, p2, p3))
        or (d4 == 0 and in_box(p1, p2, p4))
    )


def contains(poly, p):
    """Whether the closed convex polygon poly, in either orientation, contains the point p."""
    n = len(poly)
    if n == 1:
        return poly[0] == p
    if n == 2:
        return orient(poly[0], poly[1], p) == 0 and in_box(poly[0], poly[1], p)
    sign = 0
    for i in range(n):
        o = orient(poly[i], poly[(i + 1) % n], p)
        if o != 0:
            if sign == 0:
                sign = 1 if o > 0 else -1
            elif (o > 0) != (sign > 0):
                return False
    return True


def edges(poly):
    n = len(poly)
    if n == 1:
        return [(poly[0], poly[0])]
    return [(poly[i], poly[(i + 1) % n]) for i in range(n)]


def touch(P, Q):
    """Whether the closed convex polygons P and Q meet."""
    if any(contains(Q, p) for p in P) or any(contains(P, q) for q in Q):
        return True
    return any(segments_meet(a, b, c, d) for a, b in edges(P) for c, d in edges(Q))


# ---------------------------------------------------------------------------------------------------
# The bound for one leaf


def pieces(hallways, W, box):
    """The pieces of B_W cap cap_j Xhat_j for the box, and their areas, as (areas, polygons)."""
    poly = [(F(0), F(0)), (W, F(0)), (W, F(1)), (F(0), F(1))]
    for j, (f, g) in enumerate(hallways):
        (_, b), (_, d) = box[2 * j], box[2 * j + 1]
        poly = cut(poly, f, -1, b + 1)
        poly = cut(poly, g, -1, d + 1)
        if not poly:
            return [], []
    polys = [poly]
    for j, (f, g) in enumerate(hallways):
        (a, _), (c, _) = box[2 * j], box[2 * j + 1]
        new = []
        for P in polys:
            upper = cut(P, g, +1, c)  # g_j >= c
            if upper:
                new.append(upper)
            lower = cut(cut(P, g, -1, c), f, +1, a)  # g_j <= c, f_j >= a
            if lower:
                new.append(lower)
        polys = new
        if not polys:
            return [], []
    return [area(P) for P in polys], polys


def components(areas, polys):
    """The areas of the connected components of the union of the polygons."""
    parent = list(range(len(polys)))

    def root(i):
        while parent[i] != i:
            i = parent[i]
        return i

    for i in range(len(polys)):
        for j in range(i + 1, len(polys)):
            if root(i) != root(j) and touch(polys[i], polys[j]):
                parent[root(i)] = root(j)
    total = {}
    for i, a in enumerate(areas):
        total[root(i)] = total.get(root(i), F(0)) + a
    return list(total.values())


def leaf_bound(hallways, W, box, T):
    """The bound used for a leaf: the total area of the pieces if that is at most T, otherwise Gamma(E)."""
    areas, polys = pieces(hallways, W, box)
    if not polys:
        return F(0)
    total = sum(areas)
    if total <= T:
        return total
    return max(components(areas, polys))


# ---------------------------------------------------------------------------------------------------
# The tree. Tokens are a byte array: LEAF for L, k for a bisection of coordinate k, in preorder.


def split_tasks(tokens, root_box, depth_cut):
    """Splits the tree into its subtrees at depth depth_cut and its leaves of smaller depth.

    Returns the tasks (tokens of the subtree, box of its root) in preorder. Raises ValueError if the
    tokens do not form exactly one complete binary tree.
    """
    # First pass: for every node of depth <= depth_cut, the position just after its subtree.
    end = {}
    open_nodes = []  # [position, depth, children still to come] of the nodes above the current one
    n = len(tokens)
    for i in range(n):
        depth = len(open_nodes)
        if tokens[i] != LEAF:
            open_nodes.append([i, depth, 2])
            continue
        if depth <= depth_cut:
            end[i] = i + 1
        while open_nodes:
            open_nodes[-1][2] -= 1
            if open_nodes[-1][2] > 0:
                break
            start, start_depth, _ = open_nodes.pop()
            if start_depth <= depth_cut:
                end[start] = i + 1
        if not open_nodes and i + 1 != n:
            raise ValueError("certificate has trailing tokens")
    if open_nodes:
        raise ValueError("certificate truncated")

    # Second pass: descend to depth depth_cut.
    tasks = []

    def descend(i, box, depth):
        if tokens[i] == LEAF or depth == depth_cut:
            tasks.append((tokens[i : end[i]], box))
            return
        lower, upper = bisect(box, tokens[i])
        descend(i + 1, lower, depth + 1)
        descend(end[i + 1], upper, depth + 1)

    descend(0, root_box, 0)
    return tasks


_problem = {}  # hallways, W and T, set in each worker process by init_worker


def init_worker(hallways, W, T):
    _problem.update(hallways=hallways, W=W, T=T)


def check_subtree(task):
    """Checks the leaves of one task (tokens, box).

    Returns (worst, bad, leaves, complete): the largest bound of a leaf, the number of leaves whose bound
    exceeds T, the number of leaves, and whether the tokens form exactly one tree.
    """
    tokens, box = task
    tokens = bytes(tokens)
    hallways, W, T = _problem["hallways"], _problem["W"], _problem["T"]
    worst, bad, leaves = F(0), 0, 0
    stack = [box]
    pos = 0
    while stack:
        box = stack.pop()
        if pos >= len(tokens):
            return worst, bad + 1, leaves, False
        token = tokens[pos]
        pos += 1
        if token == LEAF:
            bound = leaf_bound(hallways, W, box, T)
            leaves += 1
            worst = max(worst, bound)
            if bound > T:
                bad += 1
        else:
            if token >= len(box):
                return worst, bad + 1, leaves, False
            lower, upper = bisect(box, token)
            stack.append(upper)
            stack.append(lower)
    return worst, bad, leaves, pos == len(tokens)
