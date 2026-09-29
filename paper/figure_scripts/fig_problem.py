"""Figure 1.1: (a) the two-way corridor with Romik's shape; (b) the Z-shaped corridor Z_D."""

import math

import numpy as np
from matplotlib.patches import Polygon as Poly

from common import (
    ACC,
    ACC_L,
    FLOOR,
    OUTDIR,
    SOFA,
    SOFA_L,
    WALL,
    motion_left,
    motion_right,
    plt,
    sigma_outline_cached,
)

seg = sigma_outline_cached()

fig, axs = plt.subplots(1, 2, figsize=(6.2, 3.35), gridspec_kw={"width_ratios": [1.0, 1.12]})

# (a) two-way corridor
ax = axs[0]
X0, Y0, Y1 = -2.7, -3.7, 4.7
ax.add_patch(
    Poly(
        [(X0, 0), (0, 0), (0, Y0), (1, Y0), (1, Y1), (0, Y1), (0, 1), (X0, 1)],
        closed=True,
        fc=FLOOR,
        ec="none",
    )
)
ax.plot([X0, 0, 0], [0, 0, Y0], color=WALL, lw=1.0)
ax.plot([X0, 0, 0], [1, 1, Y1], color=WALL, lw=1.0)
ax.plot([1, 1], [Y0, Y1], color=WALL, lw=1.0)
# start position (filled)
ax.add_patch(Poly(seg, closed=True, fc=SOFA, ec="none", alpha=0.9, zorder=3))
# intermediate positions of the right turn (clockwise) and the left turn (counterclockwise)
P = motion_right(seg, math.pi / 4)
ax.add_patch(Poly(P, closed=True, fc="none", ec=SOFA, lw=0.7, ls=(0, (3, 2)), zorder=4))
P = motion_left(seg, math.pi / 4)
ax.add_patch(Poly(P, closed=True, fc="none", ec=ACC, lw=0.7, ls=(0, (3, 2)), zorder=4))
# final positions, moved along the arms
P = motion_right(seg, math.pi / 2)
P[:, 1] -= 1.25
ax.add_patch(Poly(P, closed=True, fc=SOFA_L, ec=SOFA, lw=0.7, zorder=3))
Q = motion_left(seg, math.pi / 2)
Q[:, 1] += 1.25
ax.add_patch(Poly(Q, closed=True, fc=ACC_L, ec=ACC, lw=0.7, zorder=3))
print("final right y-range", P[:, 1].min(), P[:, 1].max(), " left", Q[:, 1].min(), Q[:, 1].max())
ax.annotate(
    "", xy=(1.55, -2.6), xytext=(1.55, -0.3), arrowprops={"arrowstyle": "->", "color": SOFA, "lw": 0.7}
)
ax.annotate("", xy=(1.55, 3.6), xytext=(1.55, 1.3), arrowprops={"arrowstyle": "->", "color": ACC, "lw": 0.7})
ax.text(1.72, -1.5, "right\nturn", color=SOFA, fontsize=8, va="center")
ax.text(1.72, 2.5, "left\nturn", color=ACC, fontsize=8, va="center")
ax.set_xlim(X0 - 0.05, 2.6)
ax.set_ylim(Y0 - 0.05, Y1 + 0.05)
ax.set_aspect("equal")
ax.axis("off")
ax.set_title("(a)", fontsize=9, y=-0.08)

# (b) Z-shaped corridor
ax = axs[1]
D = 5.0
XL, XR = -2.6, 3.6
Z = [(XL, 0), (1, 0), (1, D), (XR, D), (XR, D + 1), (0, D + 1), (0, 1), (XL, 1)]
ax.add_patch(Poly(Z, closed=True, fc=FLOOR, ec="none"))
ax.plot([XL, 1, 1, XR], [0, 0, D, D], color=WALL, lw=1.0)
ax.plot([XL, 0, 0, XR], [1, 1, D + 1, D + 1], color=WALL, lw=1.0)
S0 = seg + np.array([0.0, 0.0])
ax.add_patch(Poly(S0, closed=True, fc=SOFA, ec="none", alpha=0.9, zorder=3))
# middle position: Sigma after its left turn, moved up the middle arm
M = motion_left(seg, math.pi / 2)
M[:, 1] += (D + 1) / 2 - 0.5 * (M[:, 1].min() + M[:, 1].max())
ax.add_patch(Poly(M, closed=True, fc="none", ec=SOFA, lw=0.7, ls=(0, (3, 2)), zorder=3))
# end position in the upper arm
E = seg.copy()
E[:, 0] += 2.55
E[:, 1] += D
ax.add_patch(Poly(E, closed=True, fc=SOFA_L, ec=SOFA, lw=0.7, zorder=3))
ax.annotate(
    "",
    xy=(0.5, D - 1.9),
    xytext=(-0.3, 1.25),
    arrowprops={"arrowstyle": "->", "color": ACC, "lw": 0.8, "connectionstyle": "arc3,rad=0.3"},
)
ax.annotate(
    "",
    xy=(2.0, D + 0.5),
    xytext=(0.5, D - 0.95),
    arrowprops={"arrowstyle": "->", "color": ACC, "lw": 0.8, "connectionstyle": "arc3,rad=-0.3"},
)
ax.annotate(
    "",
    xy=(-0.35, 1),
    xytext=(-0.35, D + 1),
    arrowprops={"arrowstyle": "<->", "color": "0.4", "lw": 0.5, "shrinkA": 0, "shrinkB": 0},
)
ax.text(-0.5, D / 2 + 0.5, "$D$", fontsize=8.5, color="0.25", ha="right", va="center")
ax.text(XL + 0.1, -0.35, "$A_1$", fontsize=8.5, color="0.25")
ax.text(XR - 0.45, D - 0.37, "$A_2$", fontsize=8.5, color="0.25")
ax.set_xlim(XL - 0.05, XR + 0.05)
ax.set_ylim(-0.6, D + 1.15)
ax.set_aspect("equal")
ax.axis("off")
ax.set_title("(b)", fontsize=9, y=-0.08)
fig.savefig(OUTDIR + "fig_problem.pdf")
