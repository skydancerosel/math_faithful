"""Figure for Chapter 13: geodesics between antipodal points, and the stable range.

Left: the sphere S^2 = S^{n+1} with n = 1, its north pole p and south pole q = -p.  The minimal
geodesics from p to q are the half great circles; each crosses the equator once, at its midpoint,
so the space Omega^d of minimal geodesics is a copy of the equator S^n.  One non-minimal geodesic of
length 3*pi is drawn (offset slightly outward so that its two passes are visible), with its two
interior conjugate points (passages through q and p), each of multiplicity n; its index is 2n.

Right: the groups pi_{n+k}(S^n) for 1 <= n <= 8, 0 <= k <= 7 (Toda's table).  Shaded cells are those
covered by Corollary 22.3 (Freudenthal): pi_{n+k}(S^n) = pi_{n+k+1}(S^{n+1}) when n >= k + 2.

Writes fig13-antipodes.png (150 dpi, 7 inches wide).
"""
import math
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

fig = plt.figure(figsize=(7.0, 3.5))
ax = fig.add_axes([0.0, 0.02, 0.43, 0.93])
tx = fig.add_axes([0.45, 0.06, 0.54, 0.86])

# ---------- the sphere, orthographic projection ----------
elev = math.radians(18.0)   # viewing elevation
azim = math.radians(-35.0)  # viewing azimuth


def project(P):
    """Rotate the point P (3-vector) to view coordinates; return (x, y, depth)."""
    x, y, z = P
    # rotate about the z-axis by -azim, then tilt about the x-axis by elev
    x1 = math.cos(azim) * x - math.sin(azim) * y
    y1 = math.sin(azim) * x + math.cos(azim) * y
    z1 = z
    yv = math.cos(elev) * z1 - math.sin(elev) * y1
    dv = math.sin(elev) * z1 + math.cos(elev) * y1   # depth: > 0 means on the near hemisphere
    return x1, yv, dv


def draw_curve(points, **kw):
    """Draw a curve, dashing the parts on the hidden hemisphere."""
    xs, ys, front = [], [], []
    for P in points:
        x, y, d = project(P)
        xs.append(x)
        ys.append(y)
        front.append(d >= -1e-9)
    seg_x, seg_y, cur = [xs[0]], [ys[0]], front[0]
    for i in range(1, len(xs)):
        if front[i] != cur:
            ax.plot(seg_x, seg_y, ls="-" if cur else ":", **kw)
            seg_x, seg_y, cur = [xs[i - 1]], [ys[i - 1]], front[i]
        seg_x.append(xs[i])
        seg_y.append(ys[i])
    ax.plot(seg_x, seg_y, ls="-" if cur else ":", **kw)


circ = np.linspace(0, 2 * math.pi, 400)
ax.plot(np.cos(circ), np.sin(circ), color="black", lw=1.0)  # outline

p = np.array([0.0, 0.0, 1.0])
# meridians: minimal geodesics from p to q
for phi in np.linspace(0, 2 * math.pi, 12, endpoint=False):
    u = np.array([math.cos(phi), math.sin(phi), 0.0])
    pts = [math.cos(s) * p + math.sin(s) * u for s in np.linspace(0, math.pi, 120)]
    draw_curve(pts, color="0.6", lw=0.7)
# the equator = Omega^d
eq = [np.array([math.cos(a), math.sin(a), 0.0]) for a in np.linspace(0, 2 * math.pi, 400)]
draw_curve(eq, color="#2e6fba", lw=2.2)

# one non-minimal geodesic of length 3 pi, offset outwards to show the two passes
u0 = np.array([math.cos(math.radians(70)), math.sin(math.radians(70)), 0.0])
pts = []
for s in np.linspace(0, 3 * math.pi, 700):
    r = 1.0 + 0.035 * s / math.pi
    pts.append(r * (math.cos(s) * p + math.sin(s) * u0))
draw_curve(pts, color="#c0392b", lw=1.6)
# conjugate points at s = pi (q) and s = 2 pi (p), slightly offset like the curve
for s, lab in [(math.pi, "conj."), (2 * math.pi, "conj.")]:
    r = 1.0 + 0.035 * s / math.pi
    x, y, d = project(r * (math.cos(s) * p + math.sin(s) * u0))
    ax.scatter([x], [y], s=34, facecolor="white", edgecolor="#c0392b", lw=1.5, zorder=6)

xp, yp, _ = project(p)
xq, yq, _ = project(-p)
ax.scatter([xp, xq], [yp, yq], s=26, color="black", zorder=7)
ax.text(xp + 0.06, yp + 0.05, "p", fontsize=10)
ax.text(xq + 0.2, yq - 0.16, "q = −p", fontsize=10)
xe, ye, _ = project(np.array([math.cos(math.radians(110)), math.sin(math.radians(110)), 0.0]))
ax.text(-1.12, -0.42, "$\\Omega^d \\cong S^n$\n(equator)", fontsize=8, color="#2e6fba", ha="right")
ax.text(-0.2, -1.42, "red: a geodesic of length $3\\pi$,\nindex $2n$ (two conjugate points)",
        fontsize=7.5, color="#c0392b", ha="center")
ax.set_xlim(-1.75, 1.3)
ax.set_ylim(-1.6, 1.25)
ax.set_aspect("equal")
ax.axis("off")

# ---------- the table of pi_{n+k}(S^n) ----------
TABLE = {
    1: ["Z", "0", "0", "0", "0", "0", "0", "0"],
    2: ["Z", "Z", "2", "2", "12", "2", "2", "3"],
    3: ["Z", "2", "2", "12", "2", "2", "3", "15"],
    4: ["Z", "2", "2", "Z+12", "2²", "2²", "24+3", "15"],
    5: ["Z", "2", "2", "24", "2", "2", "2", "30"],
    6: ["Z", "2", "2", "24", "0", "Z", "2", "60"],
    7: ["Z", "2", "2", "24", "0", "0", "2", "120"],
    8: ["Z", "2", "2", "24", "0", "0", "2", "Z+120"],
}
nrows, ncols = 8, 8
for n in range(1, nrows + 1):
    for k in range(ncols):
        x0, y0 = k, nrows - n
        if n >= k + 2:
            tx.add_patch(plt.Rectangle((x0, y0), 1, 1, color="#dbe7f5", lw=0))
        tx.add_patch(plt.Rectangle((x0, y0), 1, 1, fill=False, ec="0.75", lw=0.5))
        tx.text(x0 + 0.5, y0 + 0.5, TABLE[n][k], ha="center", va="center", fontsize=7)
    tx.text(-0.15, nrows - n + 0.5, "$S^{%d}$" % n, ha="right", va="center", fontsize=8)
for k in range(ncols):
    tx.text(k + 0.5, nrows + 0.2, "k=%d" % k, ha="center", va="bottom", fontsize=7.5)
tx.text(4.0, nrows + 0.9, "$\\pi_{n+k}(S^n)$   (Toda)", ha="center", fontsize=9)
tx.text(4.0, -0.55, "shaded: $n \\geq k+2$, where Corollary 22.3 gives "
        "$\\pi_{n+k}(S^n)\\cong\\pi_{n+k+1}(S^{n+1})$", ha="center", fontsize=6.6)
tx.text(4.0, -1.05, "notation: Z = integers, m = Z/m, 2² = Z/2+Z/2, + = direct sum",
        ha="center", fontsize=6.4, color="0.3")
tx.set_xlim(-0.9, ncols + 0.1)
tx.set_ylim(-1.3, nrows + 1.4)
tx.axis("off")

fig.savefig("fig13-antipodes.png", dpi=150)
print("wrote fig13-antipodes.png")
