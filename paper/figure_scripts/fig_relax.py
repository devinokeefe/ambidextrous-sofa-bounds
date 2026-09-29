"""Figure 8.1: the relaxation of Theorem 6.1, with the angles b1 = arcsin 3/5 and b2 = arcsin 4/5 on
both sides.
(a) Romik's shape Sigma inside H ∩ L_b1 ∩ L_b2 ∩ rho L_b1 ∩ rho L_b2 at its own hallway positions;
(b) a configuration found by local search in floating point, cached in relax_best.json
(its exact area is checked by checks/relaxation_values.py)."""

import json
import math
import os

import numpy as np
from matplotlib.patches import Polygon as Poly
from scipy.optimize import minimize

from common import FLOOR, OUTDIR, SOFA, SOFA_L, WALL, plt, sigma_outline_cached, x_romik
from relax import box, components, intersection, lam_star

b1, b2 = math.atan2(3, 4), math.atan2(4, 3)
seg = sigma_outline_cached()
XL, XR = -1.9, 1.6
BASE = box(XL - 2, XR + 2)


def romik_params():
    ps = []
    for t in (b1, b2):
        x = x_romik(t)
        c, s = math.cos(t), math.sin(t)
        ps.append((c * x[0] + s * x[1], -s * x[0] + c * x[1]))  # u = Rot_{-t} x(t)
    return ps


def halls_from(p):
    return [
        (b1, (p[0], p[1]), False),
        (b2, (p[2], p[3]), False),
        (b1, (p[4], p[5]), True),
        (b2, (p[6], p[7]), True),
    ]


pr = romik_params()
p0 = [pr[0][0], pr[0][1], pr[1][0], pr[1][1], pr[0][0], pr[0][1], pr[1][0], pr[1][1]]
lam0 = lam_star(halls_from(p0), BASE)
print("Romik positions: lambda* =", lam0)

cache = "relax_best.json"
if os.path.exists(cache):
    with open(cache) as fh:
        best = json.load(fh)
else:
    rng = np.random.default_rng(7)
    best = {"val": lam0, "p": p0}
    starts = [np.array(p0)] + [np.array(p0) + rng.normal(0, 0.08, 8) for _ in range(24)]
    for x0 in starts:
        r = minimize(
            lambda z: -lam_star(halls_from(z), BASE),
            x0,
            method="Nelder-Mead",
            options={"maxiter": 6000, "xatol": 1e-9, "fatol": 1e-12, "adaptive": True},
        )
        if -r.fun > best["val"]:
            best = {"val": -r.fun, "p": list(map(float, r.x))}
            print("improved", best["val"], flush=True)
    with open(cache, "w") as fh:
        json.dump(best, fh)
print("best found lambda* =", best["val"])

fig, axs = plt.subplots(2, 1, figsize=(4.6, 3.0), gridspec_kw={"hspace": 0.12})
for k, (ax, p) in enumerate(zip(axs, (p0, best["p"]), strict=True)):
    ax.add_patch(Poly(box(XL, XR), closed=True, fc=FLOOR, ec="none", zorder=0))
    ax.plot([XL, XR], [0, 0], color=WALL, lw=0.7)
    ax.plot([XL, XR], [1, 1], color=WALL, lw=0.7)
    comps = components(intersection(halls_from(p), BASE))
    for i, (_, polys) in enumerate(comps):
        for q in polys:
            col = SOFA_L if i == 0 else "0.8"
            ax.add_patch(Poly(q, closed=True, fc=col, ec=col, lw=0.3, zorder=1))
    if k == 0:
        ax.add_patch(Poly(seg, closed=True, fc=SOFA, ec="none", zorder=2))
    print("panel", k, "components", [round(c[0], 5) for c in comps])
    ax.set_xlim(XL, XR)
    ax.set_ylim(-0.12, 1.12)
    ax.set_aspect("equal")
    ax.axis("off")
    ax.set_title("(a)" if k == 0 else "(b)", fontsize=9, y=-0.2)
fig.savefig(OUTDIR + "fig_relax.pdf")
