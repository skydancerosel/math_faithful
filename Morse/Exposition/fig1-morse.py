"""Figure for Chapter 1 (Milnor, Morse Theory, section 2): the lemma of Morse.

Contour lines of f(x, y) = a x^2 + b y^2 + g (x^3 - 3 x y^2) near the critical point 0, the
sublevel set {f < 0} shaded, and (for non-degenerate cases) the Morse coordinates (y1, y2)
produced by the proof of Lemma 2.2, drawn as a curved grid.  In that grid the contours of f are
the level curves of +-y1^2 +- y2^2.

Writes fig1-morse.png (150 dpi, 7 inches wide).
"""

import os

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

plt.rcParams["contour.negative_linestyle"] = "solid"

FG = "#1f1f1d"
MUTED = "#8a8984"
ACCENT = "#2a78d6"
GRID = "#eb6834"


def f(x, y, a, b, g):
    return a * x**2 + b * y**2 + g * (x**3 - 3 * x * y**2)


def morse_coordinates(x, y, a, b, g):
    """Morse coordinates from Milnor's completing-the-square step.

    For this cubic f, the symmetric coefficients H_ij(x) = int_0^1 (1-t) d_i d_j f(tx) dt are
    H11 = a + g x, H12 = -g y, H22 = b - g x  (so f = sum x_i x_j H_ij).
    Pivot on the larger of |a|, |b| (Milnor's 'linear change of coordinates').
    Returns (y1, y2, valid_mask).
    """
    H11 = a + g * x
    H12 = -g * y
    H22 = b - g * x
    D = H11 * H22 - H12**2
    if abs(a) >= abs(b):
        piv, piv0, u, v = H11, a, x, y
    else:
        piv, piv0, u, v = H22, b, y, x
    with np.errstate(divide="ignore", invalid="ignore"):
        y1 = np.sqrt(np.abs(piv)) * (u + v * H12 / piv)
        y2 = np.sqrt(np.abs(D / piv)) * v
    rc = 0.45 * min(abs(a), abs(b)) / max(g, 1e-9)
    valid = (
        (np.sign(piv) == np.sign(piv0))
        & (np.abs(piv) > 0.3 * abs(piv0))
        & (np.sign(D) == np.sign(a * b))
        & (np.abs(D) > 0.3 * abs(a * b))
        & (x**2 + y**2 < rc**2)
    )
    return y1, y2, valid


def panel(ax, a, b, g, title, R=0.6):
    n = 401
    xs = np.linspace(-R, R, n)
    X, Y = np.meshgrid(xs, xs)
    Z = f(X, Y, a, b, g)

    # sublevel set {f < f(0) = 0}
    ax.contourf(X, Y, Z, levels=[Z.min() - 1, 0.0], colors=[ACCENT], alpha=0.18)

    # quadratically spaced levels, so that small contours near the critical point are visible
    L = np.max(np.abs(Z)) * 0.9
    ks = np.arange(1, 10)
    pos = L * (ks / 9.0) ** 2
    levels = sorted(list(-pos) + list(pos))
    ax.contour(X, Y, Z, levels=levels, colors=MUTED, linewidths=0.7)
    ax.contour(X, Y, Z, levels=[0.0], colors=FG, linewidths=1.4)

    if a != 0 and b != 0:
        y1, y2, valid = morse_coordinates(X, Y, a, b, g)
        y1m = np.where(valid, y1, np.nan)
        y2m = np.where(valid, y2, np.nan)
        m = np.nanmax(np.abs(np.concatenate([y1m[valid], y2m[valid]])))
        glev = np.linspace(-m, m, 13)
        ax.contour(X, Y, y1m, levels=glev, colors=GRID, linewidths=0.6, alpha=0.9)
        ax.contour(X, Y, y2m, levels=glev, colors=GRID, linewidths=0.6, alpha=0.9)

    ax.axhline(0, color=MUTED, lw=0.5, alpha=0.6)
    ax.axvline(0, color=MUTED, lw=0.5, alpha=0.6)
    ax.plot([0], [0], "o", color=FG, ms=4)
    ax.set_xlim(-R, R)
    ax.set_ylim(-R, R)
    ax.set_aspect("equal")
    ax.set_xticks([])
    ax.set_yticks([])
    for s in ax.spines.values():
        s.set_color(MUTED)
        s.set_linewidth(0.6)
    ax.set_title(title, fontsize=10, color=FG)


def main():
    fig, axes = plt.subplots(2, 2, figsize=(7.0, 7.0))
    g = 0.6
    panel(axes[0, 0], 1.0, 0.6, g, "pit: Hessian diag(2, 1.2), index 0")
    panel(axes[0, 1], -1.0, 0.6, g, "pass: Hessian diag(-2, 1.2), index 1")
    panel(axes[1, 0], -1.0, -0.6, g, "peak: Hessian diag(-2, -1.2), index 2")
    panel(axes[1, 1], 0.0, 0.0, 1.0, "monkey saddle: Hessian 0, degenerate")
    fig.suptitle(
        r"$f = a x^2 + b y^2 + \gamma\,(x^3 - 3xy^2)$:  contours of $f$ (grey), $\{f<0\}$ (blue),"
        "\nMorse coordinates $(y^1, y^2)$ from the proof of Lemma 2.2 (orange grid)",
        fontsize=9.5,
        color=FG,
    )
    fig.tight_layout(rect=(0, 0, 1, 0.95), h_pad=1.2, w_pad=1.0)
    fig.savefig(os.path.join(os.path.dirname(os.path.abspath(__file__)), "fig1-morse.png"), dpi=150)


if __name__ == "__main__":
    main()
