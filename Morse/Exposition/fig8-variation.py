"""Figure for Chapter 8: the second variation of the energy along a great-circle route.

A route of angle theta along the equator of the unit sphere, starting at p = (1, 0, 0), and the
variation alpha(u, t) = exp_{gamma(t)}(u sin(k pi t) N), N = (0, 0, 1): the point at latitude
u sin(k pi t) and longitude theta t.  Panels (a), (b): the globe for theta = 0.7 pi and 1.5 pi with
the varied routes u = +-0.35 (k = 1).  Panel (c): E(alpha(u)) - E(gamma) against u, with the
parabola (k^2 pi^2 - theta^2) u^2 / 2 predicted by the second variation formula.

Writes fig8-variation.png (150 dpi, 7 inches wide).
"""
import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

FG, ACCENT, MUTED, BLUE = "#1d1d1f", "#b4441f", "#8a8780", "#2c5d8a"


def view_frame(lon_v, lat_v):
    """Orthonormal screen frame (ex, ey, ez) for a viewer in direction (lon_v, lat_v)."""
    v = np.array([np.cos(lat_v) * np.cos(lon_v), np.cos(lat_v) * np.sin(lon_v), np.sin(lat_v)])
    ex = np.array([-np.sin(lon_v), np.cos(lon_v), 0.0])
    ey = np.cross(v, ex)
    return ex, ey, v


def project(P, frame):
    ex, ey, ez = frame
    return P @ ex, P @ ey, P @ ez


def draw_curve(ax, P, frame, color, lw, front_ls="-", zorder=3, alpha_back=0.5):
    x, y, z = project(P, frame)
    vis = z >= 0
    # split into runs of constant visibility
    start = 0
    for i in range(1, len(x) + 1):
        if i == len(x) or vis[i] != vis[start]:
            sl = slice(start, min(i + 1, len(x)))
            if vis[start]:
                ax.plot(x[sl], y[sl], color=color, lw=lw, ls=front_ls, zorder=zorder,
                        solid_capstyle="round")
            else:
                ax.plot(x[sl], y[sl], color=color, lw=lw * 0.7, ls=(0, (2, 2)), alpha=alpha_back,
                        zorder=zorder - 1)
            start = i


def route(theta, n=400):
    lam = np.linspace(0, theta, n)
    return np.stack([np.cos(lam), np.sin(lam), 0 * lam], 1)


def varied(theta, u, k, n=400):
    t = np.linspace(0, 1, n)
    psi = u * np.sin(k * np.pi * t)
    lam = theta * t
    return np.stack([np.cos(psi) * np.cos(lam), np.cos(psi) * np.sin(lam), np.sin(psi)], 1)


def globe(ax, theta, u, k, title):
    frame = view_frame(theta / 2, np.radians(38))
    circ = np.linspace(0, 2 * np.pi, 300)
    ax.plot(np.cos(circ), np.sin(circ), color=FG, lw=0.9)
    # graticule
    for lat in np.radians([-60, -30, 30, 60]):
        lon = np.linspace(0, 2 * np.pi, 300)
        P = np.stack([np.cos(lat) * np.cos(lon), np.cos(lat) * np.sin(lon), np.sin(lat) + 0 * lon], 1)
        draw_curve(ax, P, frame, MUTED, 0.4, zorder=1, alpha_back=0.0)
    for lon in np.radians(np.arange(0, 360, 30)):
        lat = np.linspace(-np.pi / 2, np.pi / 2, 200)
        P = np.stack([np.cos(lat) * np.cos(lon), np.cos(lat) * np.sin(lon), np.sin(lat)], 1)
        draw_curve(ax, P, frame, MUTED, 0.4, zorder=1, alpha_back=0.0)
    # full equator (faint), the route, and the varied routes
    draw_curve(ax, route(2 * np.pi), frame, MUTED, 0.6, zorder=2, alpha_back=0.0)
    draw_curve(ax, route(theta), frame, FG, 2.0, zorder=4)
    for s in (+1, -1):
        draw_curve(ax, varied(theta, s * u, k), frame, ACCENT, 1.4, zorder=5)
    # marked points
    pts = {"$p$": np.array([1.0, 0, 0]), "$q$": np.array([np.cos(theta), np.sin(theta), 0]),
           "$p'$": np.array([-1.0, 0, 0])}
    for lab, P in pts.items():
        x, y, z = project(P[None, :], frame)
        if lab == "$p'$" and theta < np.pi:
            col = MUTED
        else:
            col = BLUE if lab == "$p'$" else FG
        a = 1.0 if z[0] >= 0 else 0.55
        ax.plot(x, y, "o", ms=4.5, color=col, alpha=a, zorder=6)
        r = np.hypot(x[0], y[0]) + 1e-9
        off = (11 * x[0] / r - 4, 11 * y[0] / r - 4)
        ax.annotate(lab, (x[0], y[0]), xytext=off, textcoords="offset points", fontsize=9,
                    color=col, alpha=a)
    ax.set_xlim(-1.2, 1.2)
    ax.set_ylim(-1.12, 1.12)
    ax.set_aspect("equal")
    ax.axis("off")
    ax.set_title(title, fontsize=9, color=FG)


def energy(theta, u, k, n=4001):
    t = np.linspace(0, 1, n)
    f = (k * np.pi * u) ** 2 * np.cos(k * np.pi * t) ** 2 + theta ** 2 * np.cos(u * np.sin(k * np.pi * t)) ** 2
    w = np.ones(n)
    w[1:-1:2], w[2:-1:2] = 4, 2
    return (t[1] - t[0]) / 3 * np.sum(w * f)


fig = plt.figure(figsize=(7.0, 2.75), dpi=150)
ax1 = fig.add_axes([0.0, 0.04, 0.29, 0.84])
ax2 = fig.add_axes([0.29, 0.04, 0.29, 0.84])
ax3 = fig.add_axes([0.665, 0.17, 0.325, 0.71])

globe(ax1, 0.7 * np.pi, 0.35, 1, r"(a) $\theta = 0.7\pi$: a minimum")
globe(ax2, 1.5 * np.pi, 0.35, 1, r"(b) $\theta = 1.5\pi$: a saddle")

us = np.linspace(-1.0, 1.0, 161)
for theta, col, lab in ((0.7 * np.pi, FG, r"$0.7\pi$"), (np.pi, MUTED, r"$\pi$"),
                        (1.5 * np.pi, ACCENT, r"$1.5\pi$")):
    E0 = theta ** 2
    ax3.plot(us, [energy(theta, u, 1) - E0 for u in us], color=col, lw=1.6, label=r"$\theta=$" + lab)
    ax3.plot(us, 0.5 * (np.pi ** 2 - theta ** 2) * us ** 2, color=col, lw=0.9, ls="--")
ax3.axhline(0, color=MUTED, lw=0.5)
ax3.set_xlim(-1, 1)
ax3.set_ylim(-4.2, 4.2)
ax3.set_xlabel(r"$u$", fontsize=9)
ax3.set_title(r"(c) $E(\bar\alpha(u)) - E(\gamma)$, $k = 1$", fontsize=9)
ax3.tick_params(labelsize=8)
ax3.legend(fontsize=7.5, frameon=False, loc="lower center", ncol=1)
for s in ("top", "right"):
    ax3.spines[s].set_visible(False)

fig.savefig("fig8-variation.png", dpi=150)
print("wrote fig8-variation.png")
