"""Figure for Chapter 1 (Milnor, Morse Theory, section 1): the torus standing on a plane.

Milnor's Diagram 1.  Left: the torus of revolution (core radius R, tube radius rho) standing
upright on the horizontal plane V, its height function f, the critical points p, q, r, s at the
heights 0, 2 rho, 2R, 2R + 2 rho, and level curves f = a at several heights; at the two middle
critical values the level curve is a figure eight through q, resp. r.  Right: the sublevel set
M^a, shaded as water, for one a in each of the ranges (2)-(5) of the text: a disk, a cylinder, a
torus with a disk removed, the whole torus.

The surface is drawn by the painter's algorithm (quadrilaterals sorted by depth, orthographic
view); a point of a level curve is drawn only if the ray from it towards the viewer does not
enter the solid torus.

Writes fig1-torus.png (150 dpi, 7 inches wide).
"""

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.collections import PolyCollection

FG = "#1f1f1d"
MUTED = "#8a8984"
ACCENT = "#2a78d6"
CRIT = "#eb6834"
SURF = np.array([0.86, 0.85, 0.82])
WATER = np.array([0.55, 0.72, 0.92])

R, RHO = 2.0, 0.8
C0 = R + RHO                                  # height of the axis
HEIGHTS = {"p": 0.0, "q": 2 * RHO, "r": 2 * R, "s": 2 * R + 2 * RHO}
UV = {"p": (-np.pi / 2, 0.0), "q": (-np.pi / 2, np.pi), "r": (np.pi / 2, np.pi), "s": (np.pi / 2, 0.0)}


def surface(u, v):
    return np.stack([(R + RHO * np.cos(v)) * np.cos(u), RHO * np.sin(v),
                     C0 + (R + RHO * np.cos(v)) * np.sin(u)], axis=-1)


def normal(u, v):
    return np.stack([np.cos(v) * np.cos(u), np.sin(v), np.cos(v) * np.sin(u)], axis=-1)


def height(u, v):
    return C0 + (R + RHO * np.cos(v)) * np.sin(u)


class View:
    """Orthographic view: azimuth az from the axis of the torus, elevation el (degrees)."""

    def __init__(self, az, el):
        a, e = np.radians(az), np.radians(el)
        self.d = np.array([np.sin(a) * np.cos(e), np.cos(a) * np.cos(e), np.sin(e)])   # towards viewer
        f = -self.d
        right = np.cross(f, [0, 0, 1.0])
        self.right = right / np.linalg.norm(right)
        self.up = np.cross(self.right, f)
        light = self.d + np.array([-0.5, 0.2, 0.9])
        self.light = light / np.linalg.norm(light)

    def project(self, P):
        return np.stack([P @ self.right, P @ self.up], axis=-1)

    def visible(self, P, steps=500, T=10.0):
        """For points P on the surface: does the ray towards the viewer stay outside the torus?"""
        t = np.linspace(0.015, T, steps)
        Q = P[:, None, :] + t[None, :, None] * self.d[None, None, :]
        F = (np.sqrt(Q[..., 0] ** 2 + (Q[..., 2] - C0) ** 2) - R) ** 2 + Q[..., 1] ** 2 - RHO ** 2
        return ~(F < -1e-4).any(axis=1)


def draw_torus(ax, view, water=None, nu=150, nv=70):
    u = np.linspace(-np.pi, np.pi, nu + 1)
    v = np.linspace(-np.pi, np.pi, nv + 1)
    U, Vv = np.meshgrid(u, v, indexing="ij")
    P = surface(U, Vv)
    quads = np.stack([P[:-1, :-1], P[1:, :-1], P[1:, 1:], P[:-1, 1:]], axis=2)     # nu x nv x 4 x 3
    uc, vc = (U[:-1, :-1] + U[1:, 1:]) / 2, (Vv[:-1, :-1] + Vv[1:, 1:]) / 2
    shade = np.clip(normal(uc, vc) @ view.light, 0, 1)
    base = np.where(((height(uc, vc) <= water) if water is not None else np.zeros_like(uc, bool))[..., None],
                    WATER, SURF)
    col = base * (0.42 + 0.58 * shade[..., None])
    depth = quads.mean(axis=2) @ view.d
    order = np.argsort(depth.ravel())
    polys = view.project(quads.reshape(-1, 4, 3)[order])
    ax.add_collection(PolyCollection(polys, facecolors=col.reshape(-1, 3)[order],
                                     edgecolors=col.reshape(-1, 3)[order], linewidths=0.35, zorder=2))


def level_curve(a, n=2400):
    """Points of f = a, as two branches over v (u = asin w and u = pi - asin w), w the sine of u.

    Where |w| reaches 1 the two branches meet (u = +-pi/2); the meeting points are found by
    bisection and added, so that the curve has no gap there."""
    def wv(v):
        return (a - C0) / (R + RHO * np.cos(v))

    v = np.linspace(-np.pi, np.pi, n)
    ok = np.abs(wv(v)) <= 1
    vs = list(v)
    for i in np.nonzero(ok[:-1] != ok[1:])[0]:
        lo, hi = v[i], v[i + 1]
        for _ in range(60):
            mid = (lo + hi) / 2
            if (abs(wv(mid)) <= 1) == ok[i]:
                lo = mid
            else:
                hi = mid
        vs.append(lo if ok[i] else hi)
    v = np.sort(np.array(vs))
    w = wv(v)
    ok = np.abs(w) <= 1 + 1e-12
    w = np.clip(w, -1, 1)
    out = []
    for u in (np.arcsin(w), np.pi - np.arcsin(w)):
        P = surface(u, v)
        P[~ok] = np.nan
        out.append(P)
    return out


def draw_curve(ax, view, a, **kw):
    for P in level_curve(a):
        good = ~np.isnan(P[:, 0])
        vis = np.zeros(len(P), bool)
        vis[good] = view.visible(P[good])
        S = view.project(P)
        S[~vis] = np.nan
        ax.plot(S[:, 0], S[:, 1], zorder=3, solid_capstyle="round", **kw)


def draw_plane(ax, view, w=4.2, h=2.6):
    corners = np.array([[-w, -h, 0], [w, -h, 0], [w, h, 0], [-w, h, 0]])
    ax.add_collection(PolyCollection([view.project(corners)], facecolors="#efede7",
                                     edgecolors="#c9c5bb", linewidths=0.8, zorder=1))
    return view.project(np.array([[w - 0.35, -h + 0.3, 0]]))[0]


def main():
    fig = plt.figure(figsize=(7, 3.9), dpi=150)
    big = fig.add_axes([0.0, 0.0, 0.56, 1.0])
    small = [fig.add_axes([0.56 + 0.22 * (k % 2), 0.5 - 0.5 * (k // 2), 0.22, 0.5]) for k in range(4)]

    # the large view: levels and critical points
    view = View(32, 11)
    lab = draw_plane(big, view)
    big.text(*lab, "$V$", color=MUTED, fontsize=10, ha="right", va="bottom", zorder=5)
    draw_torus(big, view)
    for a in (0.55, 1.05, 2.4, 3.2, 4.6, 5.15):
        draw_curve(big, view, a, color=MUTED, lw=0.7)
    for k in ("q", "r"):
        draw_curve(big, view, HEIGHTS[k], color=CRIT, lw=1.3)
    # height scale on the left
    uu, vv = np.meshgrid(np.linspace(-np.pi, np.pi, 200), np.linspace(-np.pi, np.pi, 100))
    xs = view.project(surface(uu, vv))[..., 0]
    x0 = xs.min() - 0.45
    ys = {k: view.project(surface(*UV[k])[None])[0] for k in HEIGHTS}
    y_lo = view.project(np.array([[0, 0, 0.0]]))[0, 1]
    y_hi = view.project(np.array([[0, 0, 2 * C0 + 0.4]]))[0, 1]
    big.annotate("", xy=(x0, y_hi), xytext=(x0, y_lo - 0.1),
                 arrowprops=dict(arrowstyle="-|>", color=FG, lw=0.8), zorder=4)
    big.text(x0 - 0.12, y_hi, "$f$", color=FG, fontsize=10, ha="right", va="top")
    names = {"p": "f(p)=0", "q": r"f(q)=2\rho", "r": "f(r)=2R", "s": r"f(s)=2R+2\rho"}
    for k, (sx, sy) in ys.items():
        big.plot([x0, sx], [sy, sy], color=CRIT, lw=0.6, ls=(0, (3, 3)), zorder=4)
        big.plot([x0 - 0.06, x0 + 0.06], [sy, sy], color=FG, lw=0.8, zorder=4)
        big.text(x0 - 0.12, sy, f"${names[k]}$", color=FG, fontsize=7.5, ha="right", va="center")
        P = surface(*UV[k])[None]
        seen = view.visible(P)[0]
        big.plot([sx], [sy], "o", ms=4.2, zorder=6, mec=CRIT, mfc=CRIT if seen else "white", mew=1.1)
        dx = {"p": 0.16, "q": 0.14, "r": 0.14, "s": 0.16}[k]
        dy = {"p": -0.2, "q": 0.2, "r": -0.22, "s": 0.2}[k]
        big.text(sx + dx, sy + dy, f"${k}$", color=CRIT, fontsize=10, ha="left", va="center", zorder=6)
    big.set_aspect("equal")
    big.set_xlim(x0 - 2.05, xs.max() + 0.5)
    big.set_ylim(y_lo - 1.2, y_hi + 0.3)
    big.axis("off")

    # the four sublevel sets
    titles = [(0.9, "$f(p) < a < f(q)$", "a disk"),
              (2.8, "$f(q) < a < f(r)$", "a cylinder"),
              (4.8, "$f(r) < a < f(s)$", "a torus with a disk removed"),
              (6.2, "$a > f(s)$", "the whole torus")]
    sview = View(32, 11)
    for ax, (a, cond, what) in zip(small, titles):
        draw_torus(ax, sview, water=a, nu=130, nv=60)
        if a < HEIGHTS["s"]:
            draw_curve(ax, sview, a, color=ACCENT, lw=1.0)
        ax.set_aspect("equal")
        lo = sview.project(np.array([[0, 0, -0.1]]))[0, 1]
        hi = sview.project(np.array([[0, 0, 2 * C0 + 0.1]]))[0, 1]
        ax.set_xlim(-3.4, 3.4)
        ax.set_ylim(lo - 1.15, hi + 0.15)
        ax.axis("off")
        ax.text(0, lo - 0.55, cond, ha="center", va="center", fontsize=7.5, color=FG)
        ax.text(0, lo - 1.0, "$M^a$ is " + what, ha="center", va="center", fontsize=7.5, color=MUTED)

    fig.savefig("fig1-torus.png", dpi=150, facecolor="white")


if __name__ == "__main__":
    main()
