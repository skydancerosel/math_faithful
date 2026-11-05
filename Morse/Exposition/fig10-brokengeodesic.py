"""Figure for Chapter 10 (Milnor, Morse Theory, Sections 16-17).

The round unit sphere S^2 with two points p, q at angle theta = 120 degrees.  A broken geodesic
with one break at t = 1/2 is determined by its break point x, and its energy is

    E'(x) = 2 rho(p, x)^2 + 2 rho(x, q)^2 ,

defined on B = {E' < 2 pi^2}.  E' has a minimum m0 (midpoint of the short arc, E = theta^2) and a
saddle m1 (midpoint of the long arc, E = (2 pi - theta)^2).  The three panels show

  (a) the front of the sphere (centred at m0), with a broken geodesic p -> x -> q;
  (b) the back (centred at m1) at a level just below the saddle: B^a is a disc;
  (c) the back at a level just above the saddle: B^a is an annulus around p' and q'.

Writes fig10-brokengeodesic.png (150 dpi, 7 inches wide).
"""

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap

FG = "#0b0b0b"
MUTED = "#8a8984"
ACCENT = "#2a78d6"
BG = "#ffffff"

THETA = np.radians(120.0)
P = np.array([np.cos(-THETA / 2), np.sin(-THETA / 2), 0.0])
Q = np.array([np.cos(THETA / 2), np.sin(THETA / 2), 0.0])
E_MIN = THETA ** 2 / np.pi ** 2                 # energies in units of pi^2
E_SADDLE = (2 * np.pi - THETA) ** 2 / np.pi ** 2
E_EDGE = 2.0                                     # boundary of B


def energy(x):
    """E'(x) / pi^2 for unit vectors x (array of shape (..., 3))."""
    rp = np.arccos(np.clip(x @ P, -1.0, 1.0))
    rq = np.arccos(np.clip(x @ Q, -1.0, 1.0))
    return 2.0 * (rp ** 2 + rq ** 2) / np.pi ** 2


def view(centre, right, up):
    centre, right, up = (np.asarray(v, float) for v in (centre, right, up))
    return centre, right, up


def project(points, v):
    c, r, u = v
    pts = np.atleast_2d(points)
    return pts @ r, pts @ u, pts @ c


def slerp(a, b, n=200, longway=False, through=None):
    """Points on the great circle arc from a to b (short arc unless told otherwise)."""
    a = a / np.linalg.norm(a)
    b = b / np.linalg.norm(b)
    ang = np.arccos(np.clip(a @ b, -1, 1))
    axis = np.cross(a, b)
    if np.linalg.norm(axis) < 1e-12:
        axis = np.cross(a, through) if through is not None else np.array([0, 0, 1.0])
    axis /= np.linalg.norm(axis)
    if longway:
        ang = ang - 2 * np.pi
    t = np.linspace(0, ang, n)
    perp = np.cross(axis, a)
    return np.outer(np.cos(t), a) + np.outer(np.sin(t), perp)


def draw_curve(ax, pts, v, **kw):
    x, y, z = project(pts, v)
    front = z >= 0
    xs = np.where(front, x, np.nan)
    ys = np.where(front, y, np.nan)
    ax.plot(xs, ys, **kw)


def draw_point(ax, pt, v, label, offset, marker="o", size=5, color=FG):
    x, y, z = project(pt, v)
    if z[0] < 0:
        return
    ax.plot(x, y, marker=marker, ms=size, color=color, mec=BG, mew=0.8, zorder=6)
    ax.annotate(label, (x[0], y[0]), xytext=offset, textcoords="offset points",
                fontsize=9, color=FG, zorder=7)


def panel(ax, v, level, title, show_x=False):
    n = 500
    u = np.linspace(-1, 1, n)
    U, V = np.meshgrid(u, u)
    R2 = U ** 2 + V ** 2
    inside = R2 <= 1.0
    W = np.sqrt(np.clip(1 - R2, 0, None))
    c, r, up = v
    X = (W[..., None] * c + U[..., None] * r + V[..., None] * up)
    Ev = energy(X)
    Ev[~inside] = np.nan

    # sublevel set B^a (accent), outside B (light grey), rest white
    img = np.full(Ev.shape, np.nan)
    img[inside] = 0.0
    img[inside & (Ev <= level)] = 1.0
    img[inside & (Ev >= E_EDGE)] = 2.0
    cmap = ListedColormap(["#ffffff", "#bcd6f3", "#e4e3df"])
    ax.imshow(img, extent=(-1, 1, -1, 1), origin="lower", cmap=cmap, vmin=0, vmax=2,
              interpolation="nearest", zorder=1)
    levels = [0.5, 0.75, 1.0, 1.25, 1.5, 1.75, 2.0]
    cs = ax.contour(U, V, Ev, levels=levels, colors=MUTED, linewidths=0.5, zorder=2)
    ax.contour(U, V, Ev, levels=[level], colors=ACCENT, linewidths=1.6, zorder=3)
    ax.contour(U, V, Ev, levels=[E_EDGE], colors=MUTED, linewidths=1.0, linestyles="--", zorder=3)
    ax.clabel(cs, levels=[1.5], fmt=lambda s: f"{s:g}" + r"$\pi^2$", fontsize=6,
              colors=MUTED)

    t = np.linspace(0, 2 * np.pi, 400)
    ax.plot(np.cos(t), np.sin(t), color=FG, lw=0.8, zorder=4)
    # the great circle through p and q (equator)
    eq = np.stack([np.cos(t), np.sin(t), 0 * t], axis=1)
    draw_curve(ax, eq, v, color=MUTED, lw=0.6, zorder=4)

    m0 = np.array([1.0, 0, 0])
    m1 = -m0
    # gamma_0 (short arc) and gamma_1 (long arc)
    draw_curve(ax, slerp(P, Q), v, color=FG, lw=1.6, zorder=5)
    draw_curve(ax, slerp(P, Q, longway=True), v, color=FG, lw=1.0, ls=(0, (4, 2)), zorder=5)

    if show_x:
        lat, lon = np.radians(38.0), np.radians(25.0)
        x = np.array([np.cos(lat) * np.cos(lon), np.cos(lat) * np.sin(lon), np.sin(lat)])
        draw_curve(ax, slerp(P, x), v, color=ACCENT, lw=1.8, zorder=5)
        draw_curve(ax, slerp(x, Q), v, color=ACCENT, lw=1.8, zorder=5)
        draw_point(ax, x, v, r"$x$", (4, 3), color=ACCENT)
        ex = energy(x)
        ax.text(0.0, -1.18, rf"$E'(x) = {float(ex):.2f}\,\pi^2$", ha="center", fontsize=8,
                color=FG)

    draw_point(ax, P, v, r"$p$", (3, -13))
    draw_point(ax, Q, v, r"$q$", (-9, -13))
    draw_point(ax, -P, v, r"$p'$", (3, 6))
    draw_point(ax, -Q, v, r"$q'$", (-13, 6))
    draw_point(ax, m0, v, r"$m_0$", (4, 4), marker="s", size=5)
    draw_point(ax, m1, v, r"$m_1$", (4, 5), marker="X", size=7)

    ax.set_title(title, fontsize=9, color=FG)
    ax.set_xlim(-1.08, 1.08)
    ax.set_ylim(-1.3, 1.08)
    ax.set_aspect("equal")
    ax.axis("off")


def main():
    front = view([1, 0, 0], [0, 1, 0], [0, 0, 1])
    back = view([-1, 0, 0], [0, -1, 0], [0, 0, 1])
    below = 0.5 * (E_SADDLE + 1.62)
    above = 0.5 * (E_SADDLE + E_EDGE)
    fig, axes = plt.subplots(1, 3, figsize=(7.0, 2.85), dpi=150)
    panel(axes[0], front, above,
          "(a) front, centred at $m_0$:\nbroken geodesic $p\\to x\\to q$", show_x=True)
    panel(axes[1], back, below,
          f"(b) back, $a = {below:.2f}\\,\\pi^2$:\n$B^a$ is a disc")
    panel(axes[2], back, above,
          f"(c) back, $a = {above:.2f}\\,\\pi^2$:\n$B^a$ is an annulus")
    fig.text(0.5, 0.015,
             rf"$\theta = 120^\circ$: $E(\gamma_0) = {E_MIN:.2f}\pi^2$ (minimum $m_0$), "
             rf"$E(\gamma_1) = {E_SADDLE:.2f}\pi^2$ (saddle $m_1$, index 1); "
             r"shaded: $B^a$; grey: outside $B$ ($E' \geq 2\pi^2$)",
             ha="center", fontsize=7.2, color=FG)
    fig.subplots_adjust(left=0.01, right=0.99, top=0.86, bottom=0.08, wspace=0.04)
    fig.savefig("fig10-brokengeodesic.png", dpi=150, facecolor=BG)


if __name__ == "__main__":
    main()
