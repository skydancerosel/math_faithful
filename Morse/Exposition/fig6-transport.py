"""Figure for Chapter 6 (Milnor §8–§9): parallel transport around a circle of latitude.

(a) Orthographic view of the unit sphere. A vector pointing north at longitude 0 on the circle of
    latitude 48.85 deg (Paris) is parallel transported eastward; it is drawn every 30 degrees of
    longitude. Relative to north it turns clockwise at the rate sin(latitude) per radian, and
    after one circuit it has turned by 360 sin(48.85 deg) = 271.1 deg.
(b) Foucault's sine law: clockwise turn per sidereal day, 360 sin(latitude), against latitude.

Writes fig6-transport.png (150 dpi, 7 inches wide).
"""
import os

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

INK = "#0b0b0b"
INK2 = "#52514e"
MUTED = "#898781"
GRID = "#e1e0d9"
AXIS = "#c3c2b7"
SURFACE = "#fcfcfb"
BLUE = "#2a78d6"
ORANGE = "#eb6834"

plt.rcParams.update({
    "font.family": "sans-serif",
    "font.size": 8.5,
    "axes.edgecolor": AXIS,
    "axes.labelcolor": INK2,
    "xtick.color": MUTED,
    "ytick.color": MUTED,
    "axes.titlesize": 9,
    "axes.titlecolor": INK,
    "figure.facecolor": SURFACE,
    "axes.facecolor": SURFACE,
})

# ---------- orthographic projection ----------
A = np.radians(25.0)   # azimuth of the viewer
E = np.radians(32.0)   # elevation of the viewer
v_dir = np.array([np.cos(E) * np.cos(A), np.cos(E) * np.sin(A), np.sin(E)])   # towards viewer
r_dir = np.array([-np.sin(A), np.cos(A), 0.0])                                 # screen right
u_dir = np.array([-np.sin(E) * np.cos(A), -np.sin(E) * np.sin(A), np.cos(E)])  # screen up


def proj(p):
    p = np.asarray(p)
    return p @ r_dir, p @ u_dir, p @ v_dir


def sph(phi, lam):
    phi, lam = np.broadcast_arrays(np.asarray(phi, dtype=float), np.asarray(lam, dtype=float))
    return np.stack([np.cos(phi) * np.cos(lam), np.cos(phi) * np.sin(lam), np.sin(phi)], axis=-1)


def north(phi, lam):
    return np.array([-np.sin(phi) * np.cos(lam), -np.sin(phi) * np.sin(lam), np.cos(phi)])


def east(lam):
    return np.array([-np.sin(lam), np.cos(lam), 0.0])


def draw_curve(ax, pts, color, lw, front_style="-", back_alpha=0.25, zorder=2):
    x, y, d = proj(pts)
    front = d >= 0
    # split into runs of constant visibility
    start = 0
    for i in range(1, len(d) + 1):
        if i == len(d) or front[i] != front[start]:
            seg = slice(start, min(i + 1, len(d)))
            if front[start]:
                ax.plot(x[seg], y[seg], color=color, lw=lw, ls=front_style, zorder=zorder)
            else:
                ax.plot(x[seg], y[seg], color=color, lw=lw * 0.8, ls=(0, (2, 2)), alpha=back_alpha,
                        zorder=zorder - 1)
            start = i


fig = plt.figure(figsize=(7.0, 3.7))
axA = fig.add_axes([0.01, 0.04, 0.47, 0.86])
axB = fig.add_axes([0.58, 0.16, 0.40, 0.70])

# (a) the globe
ax = axA
t = np.linspace(0, 2 * np.pi, 400)
ax.add_patch(plt.Circle((0, 0), 1.0, facecolor="#f4f3ef", edgecolor=AXIS, lw=1.0, zorder=0))
for phi_g in np.radians([-60, -30, 0, 30, 60]):
    draw_curve(ax, sph(phi_g, t), GRID if phi_g else AXIS, 0.7, zorder=1)
for lam_g in np.radians(np.arange(0, 360, 30)):
    ph = np.linspace(-np.pi / 2, np.pi / 2, 200)
    draw_curve(ax, sph(ph, lam_g), GRID, 0.7, zorder=1)

phi0 = np.radians(48.85)
s0 = np.sin(phi0)
draw_curve(ax, sph(phi0, t), BLUE, 2.0, zorder=3)

L = 0.30
for k in range(13):
    lam = np.radians(30.0 * k)
    tt = lam  # longitude travelled
    p = sph(phi0, lam)
    w = np.cos(tt * s0) * north(phi0, lam) + np.sin(tt * s0) * east(lam)
    x0, y0, d0 = proj(p)
    x1, y1, _ = proj(p + L * w)
    if k == 0:
        color, lw, alpha, z = INK, 1.8, 1.0, 6
    elif k == 12:
        color, lw, alpha, z = ORANGE, 2.2, 1.0, 7
    else:
        color, lw, alpha, z = INK2, 1.2, (1.0 if d0 >= 0 else 0.25), 5
    ax.annotate("", xy=(x1, y1), xytext=(x0, y0),
                arrowprops=dict(arrowstyle="-|>", color=color, lw=lw, alpha=alpha,
                                shrinkA=0, shrinkB=0, mutation_scale=9), zorder=z)
    if d0 >= 0 and k < 12:
        ax.scatter([x0], [y0], s=10, color=BLUE, zorder=4)

xs, ys, _ = proj(sph(phi0, 0.0))
box = dict(boxstyle="round,pad=0.2", fc=SURFACE, ec="none", alpha=0.9)
ax.annotate("start: pointing north", (xs, ys - 0.02), xytext=(-0.05, -0.12), color=INK, fontsize=8,
            bbox=box, arrowprops=dict(arrowstyle="-", color=INK2, lw=0.6))
ax.annotate("back after one circuit:\nturned 271° clockwise", (xs - 0.2, ys + 0.03),
            xytext=(-0.92, -0.5), color=ORANGE, fontsize=8, bbox=box,
            arrowprops=dict(arrowstyle="-", color=ORANGE, lw=0.6))
xn, yn, _ = proj(np.array([0, 0, 1.0]))
ax.text(xn + 0.04, yn + 0.05, "N", color=INK2, fontsize=8)
xl, yl, _ = proj(sph(phi0, np.radians(110)))
ax.text(0.30, 0.13, "latitude 48.85°", color=BLUE, fontsize=8)
ax.set_xlim(-1.25, 1.25)
ax.set_ylim(-1.12, 1.18)
ax.set_aspect("equal")
ax.axis("off")
ax.set_title("(a) a vector carried east along the circle of latitude", loc="left", x=0.02)

# (b) the sine law
ax = axB
lat = np.linspace(-90, 90, 361)
ax.axhline(0, color=AXIS, lw=0.8)
ax.plot(lat, 360 * np.sin(np.radians(lat)), color=BLUE, lw=2)
pts = [(48.85, "Paris, 48.85° N: 271°\n(11.3° per hour)", (-62, 262)),
       (90.0, "pole: 360°", (22, 372)),
       (0.0, "equator: 0°", (6, -60))]
for la, text, (tx, ty) in pts:
    val = 360 * np.sin(np.radians(la))
    ax.scatter([la], [val], s=36, color=BLUE, edgecolors=SURFACE, linewidths=1.6, zorder=5)
    ax.annotate(text, (la, val), xytext=(tx, ty), color=INK, fontsize=8,
                arrowprops=dict(arrowstyle="-", color=INK2, lw=0.6))
ax.set_xlim(-90, 90)
ax.set_ylim(-380, 420)
ax.set_xticks([-90, -45, 0, 45, 90])
ax.set_yticks([-360, -180, 0, 180, 360])
ax.grid(axis="y", color=GRID, lw=0.6)
ax.set_axisbelow(True)
for side in ("top", "right"):
    ax.spines[side].set_visible(False)
ax.set_xlabel("latitude (degrees; south negative)")
ax.set_ylabel("clockwise turn per sidereal day (°)")
ax.set_title("(b) Foucault's sine law: $360°\\,\\sin\\varphi$", loc="left")

fig.savefig(os.path.join(os.path.dirname(os.path.abspath(__file__)), "fig6-transport.png"), dpi=150,
            facecolor=SURFACE)
print("wrote fig6-transport.png")
