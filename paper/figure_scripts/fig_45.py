"""Figure 3.2: hallways at 45 degrees.
(a) A sideways hallway L_{-pi/4}(u): every horizontal line meets it in a segment of length sqrt 2,
    so it meets H in area exactly sqrt 2.
(b) The one-angle extremal configuration H ∩ L_{pi/4}(u) ∩ rho(L_{pi/4}(v)), u = v = (0, 1/sqrt2):
    two clipped squares touching at (-1/2, 1/2), of total area 2 sqrt2 - 1."""

import math

from matplotlib.patches import Polygon as Poly

from common import ACC, FLOOR, OUTDIR, SOFA, SOFA_L, WALL, plt
from relax import area, box, components, hallway_outline, intersection

c = 1 / math.sqrt(2)
fig, axs = plt.subplots(1, 2, figsize=(6.2, 2.35), gridspec_kw={"wspace": 0.06})
XL, XR, YB, YT = -2.45, 2.45, -1.55, 2.55

for ax in axs:
    ax.add_patch(Poly(box(XL, XR), closed=True, fc=FLOOR, ec="none", zorder=0))
    ax.plot([XL, XR], [0, 0], color=WALL, lw=0.7)
    ax.plot([XL, XR], [1, 1], color=WALL, lw=0.7)
    ax.text(XR - 0.05, 0.5, "$H$", fontsize=8.5, ha="right", va="center", color="0.25")
    ax.set_xlim(XL, XR)
    ax.set_ylim(YB, YT)
    ax.set_aspect("equal")
    ax.axis("off")

# (a) sideways hallway
ax = axs[0]
a = -math.pi / 4
u = (-0.35 - 0.5 * c, 0.35 - 0.5 * c)
P = hallway_outline(a, u, False)
ax.add_patch(Poly(P, closed=True, fc="none", ec=SOFA, lw=0.8, zorder=3))
pcs = intersection([(a, u, False)], box(XL, XR))
tot = sum(area(p) for p, _ in pcs)
print("sideways area", tot, "sqrt2", math.sqrt(2))
for p, _ in pcs:
    ax.add_patch(Poly(p, closed=True, fc=SOFA_L, ec=SOFA_L, lw=0.4, zorder=2))
for y in (0.15, 0.5, 0.85):
    # slice [mu, mu + sqrt2] with mu = min(xi1, xi2)
    xi1 = math.sqrt(2) * u[0] + y
    xi2 = math.sqrt(2) * u[1] - y
    mu = min(xi1, xi2)
    ax.annotate(
        "",
        xy=(mu + math.sqrt(2), y),
        xytext=(mu, y),
        arrowprops={"arrowstyle": "<->", "color": ACC, "lw": 0.6, "shrinkA": 0, "shrinkB": 0},
        zorder=4,
    )
ax.text(-0.4, 1.08, r"$\sqrt{2}$", color=ACC, fontsize=8.5, ha="center", va="bottom")
ax.text(
    0.15,
    2.1,
    r"$L_{-45^\circ}(\mathbf{u})$",
    color=SOFA,
    fontsize=8.5,
    ha="left",
    va="center",
    bbox={"fc": "white", "ec": "none", "pad": 0.6, "alpha": 0.9},
)
ax.set_title("(a)", fontsize=9, y=-0.12)

# (b) the bow-tie
ax = axs[1]
halls = [(math.pi / 4, (0.0, c), False), (math.pi / 4, (0.0, c), True)]
for (aa, uu, m), col in zip(halls, (SOFA, ACC), strict=True):
    ax.add_patch(Poly(hallway_outline(aa, uu, m), closed=True, fc="none", ec=col, lw=0.8, zorder=3))
comps = components(intersection(halls, box(XL, XR)))
print("bow-tie components", [round(x[0], 10) for x in comps], "target", 2 * math.sqrt(2) - 1)
for i, (_, polys) in enumerate(comps):
    for p in polys:
        ax.add_patch(
            Poly(
                p,
                closed=True,
                fc=(SOFA if i == 0 else SOFA_L),
                ec=(SOFA if i == 0 else SOFA_L),
                lw=0.4,
                zorder=2,
            )
        )
ax.plot([-0.5], [0.5], "o", ms=2.2, color="white", zorder=4)
ax.text(
    -0.5,
    2.2,
    r"$L_{45^\circ}(\mathbf{u})$",
    color=SOFA,
    fontsize=8.5,
    ha="center",
    va="center",
    bbox={"fc": "white", "ec": "none", "pad": 0.6, "alpha": 0.9},
)
ax.text(
    -0.5,
    -1.3,
    r"$\rho(L_{45^\circ}(\mathbf{v}))$",
    color=ACC,
    fontsize=8.5,
    ha="center",
    va="center",
    bbox={"fc": "white", "ec": "none", "pad": 0.6, "alpha": 0.9},
)
ax.set_title("(b)", fontsize=9, y=-0.12)
fig.savefig(OUTDIR + "fig_45.pdf")
