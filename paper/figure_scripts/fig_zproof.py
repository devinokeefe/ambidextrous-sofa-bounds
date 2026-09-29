"""Figure 4.1: (a) the Z-shaped corridor Z_D (D = 7) with its lower part Lo (contained in a left-turn
hallway) and its upper part Up (contained in a right-turn hallway); (b) a schematic of the
orientation theta(t) of a sofa of area T > sqrt 2 during its motion (not data)."""

import math

import numpy as np
from matplotlib.patches import Polygon as Poly
from matplotlib.patches import Rectangle
from scipy.interpolate import PchipInterpolator

from common import ACC, OUTDIR, SOFA, WALL, plt

fig, axs = plt.subplots(1, 2, figsize=(6.2, 3.05), gridspec_kw={"width_ratios": [0.78, 1.22], "wspace": 0.18})

# (a) Lo and Up
ax = axs[0]
D = 7.0
XL, XR = -2.4, 3.4
Z = [(XL, 0), (1, 0), (1, D), (XR, D), (XR, D + 1), (0, D + 1), (0, 1), (XL, 1)]
Lo = [(XL, 0), (1, 0), (1, D - 0.5), (0, D - 0.5), (0, 1), (XL, 1)]
Up = [(0, 1.5), (1, 1.5), (1, D), (XR, D), (XR, D + 1), (0, D + 1)]
ax.add_patch(Poly(Lo, closed=True, fc=SOFA, alpha=0.28, ec="none"))
ax.add_patch(Poly(Up, closed=True, fc=ACC, alpha=0.28, ec="none"))
ax.plot([XL, 1, 1, XR], [0, 0, D, D], color=WALL, lw=0.9)
ax.plot([XL, 0, 0, XR], [1, 1, D + 1, D + 1], color=WALL, lw=0.9)
# the containing hallways (dashed): rho(L_0) and Rot_90(L_0) + (1, D)
ax.plot([XL, 1, 1], [0, 0, D + 1.35], color=SOFA, lw=0.7, ls=(0, (3, 2)))
ax.plot([XL, 0, 0], [1, 1, D + 1.35], color=SOFA, lw=0.7, ls=(0, (3, 2)))
ax.plot([0, 0, XR], [-0.35, D + 1, D + 1], color=ACC, lw=0.7, ls=(0, (3, 2)))
ax.plot([1, 1, XR], [-0.35, D, D], color=ACC, lw=0.7, ls=(0, (3, 2)))
ax.text(-1.25, 0.5, r"$\mathit{Lo}$", color=SOFA, fontsize=9, ha="center", va="center")
ax.text(2.3, D + 0.5, r"$\mathit{Up}$", color=ACC, fontsize=9, ha="center", va="center")
ax.annotate(
    "",
    xy=(1.35, 1.5),
    xytext=(1.35, D - 0.5),
    arrowprops={"arrowstyle": "<->", "color": "0.35", "lw": 0.5, "shrinkA": 0, "shrinkB": 0},
)
ax.text(1.5, D / 2 + 0.5, "overlap", fontsize=7.5, color="0.3", rotation=90, va="center")
ax.text(-0.15, D - 0.5, r"$D-\frac{1}{2}$", fontsize=7.5, color="0.3", ha="right", va="center")
ax.text(-0.15, 1.5, r"$\frac{3}{2}$", fontsize=7.5, color="0.3", ha="right", va="center")
ax.plot([-0.1, 0], [D - 0.5, D - 0.5], color="0.3", lw=0.5)
ax.plot([-0.1, 0], [1.5, 1.5], color="0.3", lw=0.5)
ax.set_xlim(XL - 0.05, XR + 0.05)
ax.set_ylim(-0.4, D + 1.4)
ax.set_aspect("equal")
ax.axis("off")
ax.set_title("(a)", fontsize=9, y=-0.07)

# (b) orientation timeline (schematic)
ax = axs[1]
T = 353 / 200
dl = math.degrees(math.asin(1 / T))
gm = 90 - dl
ax.add_patch(Rectangle((0, 90 - dl), 1, 2 * dl, fc="0.9", ec="none"))
ax.add_patch(Rectangle((0, -dl), 1, 2 * dl, fc="0.9", ec="none"))
for yv in (-45, 135):
    ax.plot([0, 1], [yv, yv], color=ACC, lw=0.8, ls=(0, (4, 2)))
ts = [0, 0.1, 0.22, 0.33, 0.43, 0.52, 0.6, 0.68, 0.8, 0.9, 1.0]
th = [0, 12, 45, 80, 97, 104, 94, 86, 52, 18, 8]
f = PchipInterpolator(ts, th)
tt = np.linspace(0, 1, 400)
ax.plot(tt, f(tt), color=SOFA, lw=1.1)
tstar, tss = 0.36, 0.68
for tv, lab in ((tstar, r"$t^*$"), (tss, r"$t^{**}$")):
    ax.plot([tv, tv], [-60, f(tv)], color="0.35", lw=0.5, ls=(0, (1, 1.5)))
    ax.plot([tv], [f(tv)], "o", ms=2.5, color=SOFA)
    ax.text(tv, -66, lab, fontsize=8.5, ha="center", va="top")
ax.text(tstar / 2, 118, r"$S_t\subset\mathit{Lo}$", fontsize=8, ha="center", color=SOFA)
ax.text((tss + 1) / 2, 118, r"$S_t\subset\mathit{Up}$", fontsize=8, ha="center", color=ACC)
ax.text(1.02, 135, r"$135^\circ$", fontsize=7.5, va="center", color=ACC)
ax.text(1.02, -45, r"$-45^\circ$", fontsize=7.5, va="center", color=ACC)
ax.text(1.02, 90, r"$90^\circ\!\pm\!\delta_T$", fontsize=7.5, va="center")
ax.text(1.02, 0, r"$0^\circ\!\pm\!\delta_T$", fontsize=7.5, va="center")
ax.set_xlim(0, 1)
ax.set_ylim(-60, 150)
ax.set_xticks([0, 1])
ax.set_xticklabels(["$0$", "$1$"])
ax.set_yticks([])
ax.set_xlabel("$t$")
ax.xaxis.set_label_coords(0.9, -0.035)
ax.set_ylabel(r"$\theta(t)$", labelpad=2)
for s in ("top", "right"):
    ax.spines[s].set_visible(False)
ax.set_title("(b)", fontsize=9, y=-0.2)
fig.savefig(OUTDIR + "fig_zproof.pdf")
