"""Figure 5.1: the union of the hallways L(u) over a box of translations u in [a,b] x [c,d],
drawn in the hallway's own coordinates (f, g). It is the union of two closed convex pieces."""

from matplotlib.patches import Polygon as Poly
from matplotlib.patches import Rectangle

from common import ACC, ACC_L, OUTDIR, SOFA, SOFA_L, plt

a, b, c, d = 0.0, 0.7, 0.0, 0.55
FL, GB = -2.6, -2.4  # drawing window: f >= FL, g >= GB
fig, ax = plt.subplots(figsize=(3.3, 2.75))
P1 = [(a, GB), (b + 1, GB), (b + 1, d + 1), (a, d + 1)]  # a <= f <= b+1, g <= d+1
P2 = [(FL, c), (a, c), (a, d + 1), (FL, d + 1)]  # f <= a, c <= g <= d+1
ax.add_patch(Poly(P1, closed=True, fc=SOFA_L, ec="none"))
ax.add_patch(Poly(P2, closed=True, fc=ACC_L, ec="none"))
for u1, u2 in ((a, c), (b, c), (a, d), (b, d)):
    L = [(FL, u2), (u1, u2), (u1, GB), (u1 + 1, GB), (u1 + 1, u2 + 1), (FL, u2 + 1)]
    ax.add_patch(Poly(L, closed=True, fc="none", ec="0.25", lw=0.5))
ax.add_patch(Rectangle((a, c), b - a, d - c, fc="0.2", ec="none", alpha=0.85))
ax.annotate(
    r"inner corners $\mathbf{u}\in[a,b]\times[c,d]$",
    xy=(b - 0.05, c + 0.1),
    xytext=(1.95, -1.0),
    fontsize=7.5,
    arrowprops={"arrowstyle": "-", "lw": 0.4, "color": "0.3"},
    ha="left",
    va="center",
)
ax.text(
    (a + b + 1) / 2,
    -1.7,
    "piece 1\n" + r"$a\leq f\leq b+1,\ g\leq d+1$",
    fontsize=7.5,
    ha="center",
    va="center",
    color=SOFA,
    bbox={"fc": "white", "ec": "none", "alpha": 0.75, "pad": 1.0},
)
ax.text(
    -1.4,
    1.05,
    "piece 2\n" + r"$f\leq a,\ c\leq g\leq d+1$",
    fontsize=7.5,
    ha="center",
    va="center",
    color=ACC,
    bbox={"fc": "white", "ec": "none", "alpha": 0.75, "pad": 1.0},
)
ax.annotate(
    "", xy=(FL + 0.9, GB + 0.02), xytext=(FL + 0.02, GB + 0.02), arrowprops={"arrowstyle": "->", "lw": 0.6}
)
ax.annotate(
    "", xy=(FL + 0.02, GB + 0.9), xytext=(FL + 0.02, GB + 0.02), arrowprops={"arrowstyle": "->", "lw": 0.6}
)
ax.text(FL + 0.95, GB + 0.02, "$f$", fontsize=8.5, va="center")
ax.text(FL + 0.05, GB + 0.98, "$g$", fontsize=8.5, ha="center", va="bottom")
ax.set_xlim(FL, 4.2)
ax.set_ylim(GB, 2.0)
ax.set_aspect("equal")
ax.axis("off")
fig.savefig(OUTDIR + "fig_boxunion.pdf")
