"""Figure 3.1: (a) the hallway L_0 and a rotated copy L_a(u); (b) a plain hallway L_a(u), a
mirrored hallway rho(L_b(v)) and the connected components of H ∩ L_a(u) ∩ rho(L_b(v))."""

import math

from matplotlib.patches import Arc
from matplotlib.patches import Polygon as Poly

from common import ACC, FLOOR, OUTDIR, SOFA, SOFA_L, WALL, plt
from relax import box, components, hallway_outline, intersection

fig, axs = plt.subplots(1, 2, figsize=(6.2, 2.75), gridspec_kw={"width_ratios": [1.0, 1.45], "wspace": 0.08})

# (a) L_0 and L_a(u)
ax = axs[0]
a0, u0 = math.radians(30), (0.3, 0.45)
ax.plot([-2.3, 2.1], [0, 0], color="0.55", lw=0.4)
ax.plot([0, 0], [-2.2, 2.3], color="0.55", lw=0.4)
L0 = hallway_outline(0.0, (0.0, 0.0), False)
ax.add_patch(Poly(L0, closed=True, fc=FLOOR, ec="0.35", lw=0.7, ls=(0, (3, 2)), zorder=1))
La = hallway_outline(a0, u0, False)
ax.add_patch(Poly(La, closed=True, fc=SOFA, alpha=0.20, ec="none", zorder=2))
ax.add_patch(Poly(La, closed=True, fc="none", ec=SOFA, lw=0.9, zorder=3))
# rotated axis direction and the angle a
ax.plot([0, 1.9 * math.cos(a0)], [0, 1.9 * math.sin(a0)], color=SOFA, lw=0.5, ls=(0, (1, 1.5)))
ax.add_patch(Arc((0, 0), 1.3, 1.3, theta1=0, theta2=30, color=SOFA, lw=0.6))
ax.text(0.78, 0.17, "$a$", color=SOFA, fontsize=8.5)
ax.text(-2.2, 0.8, "$L_0$", fontsize=8.5, color="0.3", va="center")
ax.text(0.9, 1.78, r"$L_a(\mathbf{u})$", fontsize=8.5, color=SOFA, ha="left", va="center")
ax.set_xlim(-2.3, 2.1)
ax.set_ylim(-2.2, 2.3)
ax.set_aspect("equal")
ax.axis("off")
ax.set_title("(a)", fontsize=9, y=-0.1)

# (b) a plain and a mirrored hallway, and the components
ax = axs[1]
a, b = math.radians(30), math.radians(40)
u, v = (0.35, 0.55), (0.25, 0.85)
XL, XR, YB, YT = -3.0, 3.2, -1.6, 2.6
ax.add_patch(Poly(box(XL, XR), closed=True, fc=FLOOR, ec="none", zorder=0))
ax.plot([XL, XR], [0, 0], color=WALL, lw=0.7)
ax.plot([XL, XR], [1, 1], color=WALL, lw=0.7)
Pa = hallway_outline(a, u, False)
Pb = hallway_outline(b, v, True)
ax.add_patch(Poly(Pa, closed=True, fc="none", ec=SOFA, lw=0.8, zorder=3))
ax.add_patch(Poly(Pb, closed=True, fc="none", ec=ACC, lw=0.8, zorder=3))
comps = components(intersection([(a, u, False), (b, v, True)], box(XL, XR)))
print("components:", [round(c[0], 4) for c in comps])
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
ax.text(XR - 0.05, 0.5, "$H$", fontsize=8.5, ha="right", va="center", color="0.25")
ax.text(
    0.4,
    2.2,
    r"$L_a(\mathbf{u})$",
    color=SOFA,
    fontsize=8.5,
    ha="center",
    va="center",
    bbox={"fc": "white", "ec": "none", "pad": 0.6, "alpha": 0.9},
)
ax.text(
    -1.55,
    -1.38,
    r"$\rho(L_b(\mathbf{v}))$",
    color=ACC,
    fontsize=8.5,
    ha="center",
    va="center",
    bbox={"fc": "white", "ec": "none", "pad": 0.6, "alpha": 0.9},
)
ax.set_xlim(XL, XR)
ax.set_ylim(YB, YT)
ax.set_aspect("equal")
ax.axis("off")
ax.set_title("(b)", fontsize=9, y=-0.1)
fig.savefig(OUTDIR + "fig_hallways.pdf")
