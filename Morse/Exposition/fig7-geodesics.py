"""Figure for Chapter 7 (Milnor, Morse Theory, section 10): the exponential map of the sphere.

Left: the unit sphere seen from outside, base point p near the top.  Thin curves: radial
geodesics t -> exp_p(t v) for twelve unit vectors v, t in [0, pi].  Dashed: the shells
S_t(p) = exp_p(sphere of radius t) for t = pi/6, ..., 5 pi/6, which meet the radial geodesics at
right angles (Gauss lemma, Lemma 10.5).  Thick: one geodesic of length 3 pi / 2, minimal up to
the antipode -p (blue) and not minimal after it (orange).  Hidden parts are dotted or dashed.

Right: for a unit-speed geodesic from p, the length t of gamma|[0, t] against the distance
rho(p, gamma(t)) = min(t, 2 pi - t): they agree exactly up to t = pi.

Writes fig7-geodesics.png (150 dpi, 7 inches wide).
"""
import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

FG = "#1f1f1d"
MUTED = "#8a8984"
ACCENT = "#2a78d6"
ORANGE = "#eb6834"
BG = "#ffffff"

TILT = np.radians(25)           # how far the north pole p is tipped towards the viewer
HIGHLIGHT_DIR = np.radians(70)  # direction of the highlighted geodesic at p
HIGHLIGHT_LEN = 3 * np.pi / 2


def project(P):
    """Orthographic view. P has shape (3, N). Returns screen x, screen y, depth (>0 = visible)."""
    x, y, z = P
    depth = y * np.cos(TILT) + z * np.sin(TILT)
    return x, -y * np.sin(TILT) + z * np.cos(TILT), depth


def geodesic(phi, t):
    """exp_p(t v) on the unit sphere, p = (0,0,1), v = (cos phi, sin phi, 0)."""
    return np.array([np.sin(t) * np.cos(phi), np.sin(t) * np.sin(phi), np.cos(t)])


def shell(t, n=400):
    """S_t(p): the circle at distance t from p."""
    phi = np.linspace(0, 2 * np.pi, n)
    return np.array([np.sin(t) * np.cos(phi), np.sin(t) * np.sin(phi), np.cos(t) * np.ones(n)])


def draw(ax, P, color, lw, dashed=False, zorder=2, strong_hidden=False):
    """Draw a space curve, solid (or dashed) where visible and dotted where hidden.

    With strong_hidden the hidden part is drawn dashed and fairly opaque (for the highlight)."""
    X, Y, D = project(P)
    vis = D >= 0
    n = len(X)
    start = 0
    for i in range(1, n + 1):
        if i == n or vis[i] != vis[start]:
            sl = slice(start, min(i + 1, n))
            if vis[start]:
                ax.plot(X[sl], Y[sl], color=color, lw=lw, ls="--" if dashed else "-",
                        zorder=zorder, solid_capstyle="round")
            elif strong_hidden:
                ax.plot(X[sl], Y[sl], color=color, lw=0.6 * lw, ls=(0, (3, 2)), alpha=0.8,
                        zorder=zorder - 1)
            else:
                ax.plot(X[sl], Y[sl], color=color, lw=0.8 * lw, ls=":", alpha=0.45,
                        zorder=zorder - 1)
            start = i


def sphere_panel(ax):
    th = np.linspace(0, 2 * np.pi, 400)
    ax.fill(np.cos(th), np.sin(th), color="#f4f3ef", zorder=0)
    ax.plot(np.cos(th), np.sin(th), color=FG, lw=1.0, zorder=1)

    t = np.linspace(0, np.pi, 300)
    for k in range(12):
        draw(ax, geodesic(np.radians(30 * k + 15), t), MUTED, 0.7)
    for k in range(1, 6):
        draw(ax, shell(k * np.pi / 6), MUTED, 0.7, dashed=True)

    t1 = np.linspace(0, np.pi, 300)
    t2 = np.linspace(np.pi, HIGHLIGHT_LEN, 150)
    draw(ax, geodesic(HIGHLIGHT_DIR, t1), ACCENT, 2.2, zorder=4, strong_hidden=True)
    draw(ax, geodesic(HIGHLIGHT_DIR, t2), ORANGE, 2.2, zorder=4, strong_hidden=True)

    def mark(P, label, xy_text, arrow=False):
        X, Y, D = project(P.reshape(3, 1))
        face = FG if D[0] >= 0 else BG
        ax.plot(X, Y, "o", ms=5, mfc=face, mec=FG, zorder=6)
        props = dict(arrowstyle="-", color=MUTED, lw=0.7) if arrow else None
        ax.annotate(label, (X[0], Y[0]), xytext=xy_text, fontsize=8.5, color=FG, zorder=7,
                    arrowprops=props)

    pX, pY, _ = project(np.array([[0.0], [0.0], [1.0]]))
    mark(np.array([0.0, 0.0, 1.0]), r"$p$", (pX[0] + 0.05, pY[0] + 0.06))
    mark(np.array([0.0, 0.0, -1.0]), r"$-p$ (behind): all geodesics from $p$ meet here",
         (-1.12, -1.17), arrow=True)
    mark(geodesic(HIGHLIGHT_DIR, HIGHLIGHT_LEN), r"$\gamma(3\pi/2)$ (behind)", (0.45, 0.93),
         arrow=True)

    ax.set_xlim(-1.12, 1.12)
    ax.set_ylim(-1.22, 1.12)
    ax.set_aspect("equal")
    ax.axis("off")
    ax.set_title(r"radial geodesics $\exp_p(tv)$ and shells $S_t(p)$", fontsize=9.5, color=FG)


def distance_panel(ax):
    t = np.linspace(0, 2 * np.pi, 500)
    rho = np.minimum(t, 2 * np.pi - t)
    ax.axvspan(np.pi, 2 * np.pi, color=ORANGE, alpha=0.08, lw=0)
    ax.plot(t, t, color=MUTED, lw=1.2, ls="--", label=r"length of $\gamma|[0,t]$")
    ax.plot(t[t <= np.pi], rho[t <= np.pi], color=ACCENT, lw=2.2,
            label=r"distance $\rho(p,\gamma(t))$")
    ax.plot(t[t >= np.pi], rho[t >= np.pi], color=ORANGE, lw=2.2)
    ax.axvline(np.pi, color=FG, lw=0.6)
    ax.annotate("antipode:\nno longer minimal", (np.pi, 0.3), xytext=(np.pi + 0.15, 0.25),
                fontsize=8, color=FG)
    ax.set_xticks([0, np.pi / 2, np.pi, 3 * np.pi / 2, 2 * np.pi])
    ax.set_xticklabels(["0", r"$\pi/2$", r"$\pi$", r"$3\pi/2$", r"$2\pi$"])
    ax.set_yticks([0, np.pi / 2, np.pi, 3 * np.pi / 2, 2 * np.pi])
    ax.set_yticklabels(["0", r"$\pi/2$", r"$\pi$", r"$3\pi/2$", r"$2\pi$"])
    ax.set_xlim(0, 2 * np.pi)
    ax.set_ylim(0, 2 * np.pi)
    ax.set_xlabel(r"$t$ (unit-speed geodesic from $p$)", fontsize=9, color=FG)
    ax.legend(loc="upper left", fontsize=8, frameon=False)
    for s in ax.spines.values():
        s.set_color(MUTED)
    ax.tick_params(colors=MUTED, labelsize=8)
    ax.set_title("minimal exactly up to the antipode", fontsize=9.5, color=FG)


def main():
    fig, (a1, a2) = plt.subplots(1, 2, figsize=(7.0, 3.4),
                                 gridspec_kw={"width_ratios": [1.05, 1.0]})
    fig.patch.set_facecolor(BG)
    sphere_panel(a1)
    distance_panel(a2)
    fig.tight_layout()
    fig.savefig("fig7-geodesics.png", dpi=150, facecolor=BG)


if __name__ == "__main__":
    main()
