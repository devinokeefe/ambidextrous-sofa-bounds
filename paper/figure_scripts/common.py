"""Style and shared geometry for the paper's figures (floating point, for drawing only).

Run the scripts from this folder; they write PDF files to ../tex/figures/.
"""

import math
import os

import matplotlib
import numpy as np

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

plt.rcParams.update(
    {
        "font.family": "serif",
        "mathtext.fontset": "cm",
        "font.size": 9,
        "axes.linewidth": 0.6,
        "lines.linewidth": 0.8,
        "savefig.bbox": "tight",
        "savefig.pad_inches": 0.02,
        "pdf.fonttype": 42,
    }
)
WALL = "0.15"
FLOOR = "0.93"
SOFA = "#2b5c8a"
SOFA_L = "#9fbad4"
ACC = "#b3462f"
ACC_L = "#e9b8ab"
OUTDIR = "../tex/figures/"

# Romik's rotation path (constants from [Romik 2018, Theorem 5], as in checks/relaxation_values.py)
BETA = 0.289653820817320941
E1 = 0.875287362412732241
F1 = 1.202938908156911389
F2 = -(math.sqrt(2) - 1) * F1
K1, K6, K5 = (1 - E1, 0.5), (1 - 4.0 / 3 * E1, 0.5), (1 - 5.0 / 3 * E1, 0.5)


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


def in_hall(X, Y, t, px, py):
    """Whether (X, Y) lies in x(t) + R_t(L_0), with L_0 = {x <= 1, y <= 1} minus {x < 0, y < 0}."""
    c, s = math.cos(t), math.sin(t)
    qx = c * (X - px) + s * (Y - py)
    qy = -s * (X - px) + c * (Y - py)
    return (qx <= 1) & (qy <= 1) & ~((qx < 0) & (qy < 0))


def sigma_mask(X, Y, nt=700):
    """Whether (X, Y) lies in Romik's shape, tested at nt orientations of each motion."""
    ok = (X <= 1) & (Y >= 0) & (Y <= 1)
    for Xs, Ys in ((X, Y), (X, 1 - Y)):
        for t in np.linspace(0, math.pi / 2, nt):
            px, py = x_romik(t)
            ok &= in_hall(Xs, Ys, t, px, py)
        pe = x_romik(math.pi / 2)
        qx = Ys - pe[1]
        qy = -(Xs - pe[0])
        ok &= (qx >= 0) & (qx <= 1) & (qy <= 1)
    return ok


def sigma_outline(n=900):
    """The boundary of Romik's shape Sigma as a closed polyline (by marching squares), and its area."""
    xs = np.linspace(-1.36, 1.02, 2 * n)
    ys = np.linspace(-0.02, 1.02, n)
    X, Y = np.meshgrid(xs, ys)
    M = sigma_mask(X, Y).astype(float)
    cs = plt.figure().gca().contour(X, Y, M, levels=[0.5])
    segs = cs.allsegs[0]
    plt.close()
    seg = max(segs, key=len)
    return seg, M.sum() * (xs[1] - xs[0]) * (ys[1] - ys[0])


def sigma_outline_cached(path="sigma_outline.npy"):
    """sigma_outline(), computed on the first call and then read from a file."""
    if os.path.exists(path):
        return np.load(path)
    seg, raster_area = sigma_outline()
    print("raster area of Sigma", raster_area)
    np.save(path, seg)
    return seg


def motion_right(P, t):
    """Right-turn motion of Romik's shape: g_t(p) = R_{-t}(p - x(t)) (clockwise)."""
    px, py = x_romik(t)
    c, s = math.cos(t), math.sin(t)
    X = P[:, 0] - px
    Y = P[:, 1] - py
    return np.column_stack([c * X + s * Y, -s * X + c * Y])


def motion_left(P, t):
    """Left-turn motion: rho g_t rho."""
    Q = P.copy()
    Q[:, 1] = 1 - Q[:, 1]
    R = motion_right(Q, t)
    R[:, 1] = 1 - R[:, 1]
    return R
