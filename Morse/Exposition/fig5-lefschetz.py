"""Figure for Chapter 5 (Milnor §7): the squared distance L_p near a point q of a complex curve.

(a) The normal plane at q = 0 of the complex curve w = z^2/2 in C^2: the focal points form the
    circle |P| = 1; an observer p = (0, P) inside sees q as a minimum, outside as a saddle.
(b), (c) Contour maps of the distance ||x - p|| over the z-plane for P = 0.6 and P = 1.6 e^{0.6 i}.
(d) For comparison, the real paraboloid h = (x^2 + y^2)/2 in R^3, observer at height P = 1.6,
    beyond its double focal point: the origin is a local maximum (index 2).

Writes fig5-lefschetz.png (150 dpi, 7 inches wide).
"""
import os

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import LinearSegmentedColormap

INK = "#0b0b0b"
INK2 = "#52514e"
MUTED = "#898781"
SURFACE = "#fcfcfb"
ORANGE = "#eb6834"
BLUE_RAMP = ["#cde2fb", "#b7d3f6", "#9ec5f4", "#86b6ef", "#6da7ec", "#5598e7",
             "#3987e5", "#2a78d6", "#256abf", "#1c5cab"]
CMAP = LinearSegmentedColormap.from_list("seqblue", BLUE_RAMP)

plt.rcParams.update({
    "font.family": "sans-serif",
    "font.size": 8.5,
    "axes.edgecolor": "#c3c2b7",
    "axes.labelcolor": INK2,
    "xtick.color": MUTED,
    "ytick.color": MUTED,
    "axes.titlesize": 9,
    "axes.titlecolor": INK,
    "figure.facecolor": SURFACE,
    "axes.facecolor": SURFACE,
})

LIM = 2.4
n = 401
xs = np.linspace(-LIM, LIM, n)
X, Y = np.meshgrid(xs, xs)
Z = X + 1j * Y


def L_complex(P):
    """Squared distance from p = (0, P) to the point (z, z^2/2) of the complex curve."""
    return np.abs(Z) ** 2 + np.abs(Z ** 2 / 2 - P) ** 2


def L_real(P):
    """Squared distance from p = (0, 0, P) to the point (x, y, (x^2+y^2)/2) of the paraboloid."""
    r2 = X ** 2 + Y ** 2
    return r2 + (r2 / 2 - P) ** 2


def contour_panel(ax, L, title, xlabel, ylabel):
    D = np.sqrt(L)
    levels = D.min() + 3.4 * np.linspace(0.0, 1.0, 20) ** 2  # finer near the minimum
    ax.contourf(X, Y, D, levels=levels, cmap=CMAP, extend="max")
    ax.contour(X, Y, D, levels=levels, colors="white", linewidths=0.4, alpha=0.7)
    ax.set_xlim(-LIM, LIM)
    ax.set_ylim(-LIM, LIM)
    ax.set_aspect("equal")
    ax.set_title(title, loc="left")
    ax.set_xlabel(xlabel)
    ax.set_ylabel(ylabel)
    ax.set_xticks([-2, 0, 2])
    ax.set_yticks([-2, 0, 2])


def mark(ax, x, y, kind, label, dx=0.12, dy=0.12, ha="left"):
    style = {"min": dict(marker="o", s=46), "saddle": dict(marker="X", s=60),
             "max": dict(marker="^", s=60)}[kind]
    ax.scatter([x], [y], color=INK, edgecolors=SURFACE, linewidths=1.6, zorder=5, **style)
    ax.annotate(label, (x, y), xytext=(x + dx, y + dy), color=INK, fontsize=8, ha=ha,
                zorder=6, bbox=dict(boxstyle="round,pad=0.15", fc=SURFACE, ec="none", alpha=0.85))


fig, axs = plt.subplots(2, 2, figsize=(7.0, 6.9))
fig.subplots_adjust(left=0.08, right=0.98, top=0.93, bottom=0.07, wspace=0.28, hspace=0.36)

# (a) the normal plane
ax = axs[0, 0]
t = np.linspace(0, 2 * np.pi, 400)
ax.fill_between([-LIM, LIM], -LIM, LIM, color="#f0efec", zorder=0)
ax.fill(np.cos(t), np.sin(t), color=SURFACE, zorder=1)
ax.plot(np.cos(t), np.sin(t), color=ORANGE, lw=2, zorder=3)
ax.axhline(0, color="#c3c2b7", lw=0.8, zorder=2)
ax.axvline(0, color="#c3c2b7", lw=0.8, zorder=2)
ax.scatter([0], [0], color=INK, s=22, zorder=4)
ax.annotate("$q$", (0, 0), xytext=(-0.25, -0.32), color=INK)
P_b = 0.6
P_c = 1.6 * np.exp(0.6j)
for P, lab in [(P_b, "(b)"), (P_c, "(c)")]:
    ax.scatter([P.real if isinstance(P, complex) else P], [P.imag if isinstance(P, complex) else 0],
               color=ORANGE, edgecolors=SURFACE, linewidths=1.6, s=50, zorder=5)
for P, lab, off in [(complex(P_b), "$p$ in (b)", (-0.15, 0.22)), (P_c, "$p$ in (c)", (0.12, 0.12))]:
    ax.annotate(lab, (P.real, P.imag), xytext=(P.real + off[0], P.imag + off[1]), color=INK, fontsize=8)
ax.text(-0.55, -0.55, "index 0", color=INK2, fontsize=8)
ax.text(-2.2, 1.95, "index 1 (saddle)", color=INK2, fontsize=8)
ax.text(1.02, -0.95, "focal circle\n$|P| = 1$", color=ORANGE, fontsize=8)
ax.set_xlim(-LIM, LIM)
ax.set_ylim(-LIM, LIM)
ax.set_aspect("equal")
ax.set_title("(a) normal plane of $w = z^2/2$ at $q$", loc="left")
ax.set_xlabel("Re $P$")
ax.set_ylabel("Im $P$")
ax.set_xticks([-2, 0, 2])
ax.set_yticks([-2, 0, 2])

# (b) complex curve, observer inside the focal circle
ax = axs[0, 1]
contour_panel(ax, L_complex(P_b), "(b) complex curve, $P = 0.6$", "Re $z$", "Im $z$")
mark(ax, 0, 0, "min", "minimum (index 0)")

# (c) complex curve, observer outside the focal circle
ax = axs[1, 0]
contour_panel(ax, L_complex(P_c), r"(c) complex curve, $P = 1.6\,e^{0.6i}$", "Re $z$", "Im $z$")
mark(ax, 0, 0, "saddle", "saddle (index 1)", dx=0.15, dy=-0.6, ha="left")
zc = np.sqrt(2 * (abs(P_c) - 1)) * np.exp(1j * np.angle(P_c) / 2)
mark(ax, zc.real, zc.imag, "min", "min", dx=0.15, dy=0.12)
mark(ax, -zc.real, -zc.imag, "min", "min", dx=0.0, dy=-0.5, ha="center")

# (d) real paraboloid, observer beyond the double focal point
ax = axs[1, 1]
P_d = 1.6
contour_panel(ax, L_real(P_d), "(d) real paraboloid, $P = 1.6$", "$x$", "$y$")
rr = np.sqrt(2 * (P_d - 1))
ax.plot(rr * np.cos(t), rr * np.sin(t), color=INK, lw=1.4, ls=(0, (3, 2)), zorder=4)
ax.annotate("ring of minima", (rr * np.cos(-0.6), rr * np.sin(-0.6)), xytext=(0.35, -1.95),
            color=INK, fontsize=8, arrowprops=dict(arrowstyle="-", color=INK, lw=0.7))
mark(ax, 0, 0, "max", "maximum (index 2)", dx=-0.3, dy=0.25, ha="center")

fig.suptitle("Distance from an observer $p$ to a curved surface near a point $q$", x=0.08, ha="left",
             fontsize=10, color=INK)
fig.savefig(os.path.join(os.path.dirname(os.path.abspath(__file__)), "fig5-lefschetz.png"), dpi=150,
            facecolor=SURFACE)
print("wrote fig5-lefschetz.png")
