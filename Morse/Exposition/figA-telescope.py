"""Figure for the Appendix (Milnor, Morse Theory, Appendix): telescopes of subsets of an interval.

Left: X = [0,1), X_i = [0, 1 - 1/(i+2)].  The telescope X_Sigma = {(x, tau): x in X_floor(tau)} is
the shaded staircase.  The curve is the graph of f(x) = x/(1-x), which satisfies f >= i+1 off X_i;
the arrows show the deformation H_s(x, tau) = (x, (1-s) tau + s f(x)) of Lemma 2.1, which carries
X_Sigma onto the graph, a copy of X.

Right: Milnor's Example 3, X = [0,1], X_i = {0} u [1/(i+1), 1].  The ray over x = 0 is a path
component of X_Sigma by itself.  A graph inside X_Sigma would need f(x) >= 1/x - 1 (dashed), which
is impossible for a function continuous at 0.

Writes figA-telescope.png (150 dpi, 7 inches wide).
"""
import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle

FG = "#1f1f1d"
MUTED = "#8a8984"
ACCENT = "#2a78d6"
ORANGE = "#eb6834"
BG = "#ffffff"

LEVELS = 6


def style(ax, title):
    ax.set_xlim(-0.06, 1.06)
    ax.set_ylim(0, LEVELS)
    ax.set_xticks([0, 0.5, 1])
    ax.set_yticks(range(LEVELS + 1))
    ax.set_xlabel(r"$x$", fontsize=9, color=FG)
    ax.set_ylabel(r"$\tau$", fontsize=9, color=FG, rotation=0, labelpad=8)
    for s in ax.spines.values():
        s.set_color(MUTED)
    ax.tick_params(colors=MUTED, labelsize=8)
    for k in range(1, LEVELS):
        ax.axhline(k, color=MUTED, lw=0.4, alpha=0.5, zorder=0)
    ax.set_title(title, fontsize=9.5, color=FG)


def good_panel(ax):
    """X = [0,1), X_i = [0, 1 - 1/(i+2)]."""
    for i in range(LEVELS):
        right = 1 - 1 / (i + 2)
        ax.add_patch(Rectangle((0, i), right, 1, facecolor=ACCENT, alpha=0.16, lw=0, zorder=1))
        ax.plot([right, right], [i, i + 1], color=ACCENT, lw=1.0, zorder=2)
        if i + 1 < LEVELS:
            ax.plot([right, 1 - 1 / (i + 3)], [i + 1, i + 1], color=ACCENT, lw=1.0, zorder=2)
    ax.plot([0, 0], [0, LEVELS], color=ACCENT, lw=1.0, zorder=2)

    x = np.linspace(0, 1 - 1 / (LEVELS + 1), 400)
    ax.plot(x, x / (1 - x), color=FG, lw=1.8, zorder=4, label=r"graph of $f(x)=x/(1-x)$")

    samples = [(0.1, 2.6), (0.25, 4.5), (0.45, 3.2), (0.4, 0.2), (0.7, 4.8), (0.3, 0.05),
               (0.8, 5.3), (0.62, 1.1), (0.74, 2.2), (0.15, 5.6), (0.55, 5.7)]
    for x0, t0 in samples:
        assert x0 <= 1 - 1 / (int(t0) + 2)          # (x0, t0) lies in X_Sigma
        f0 = x0 / (1 - x0)
        ax.annotate("", xy=(x0, f0), xytext=(x0, t0),
                    arrowprops=dict(arrowstyle="-|>", color=ORANGE, lw=1.1,
                                    shrinkA=0, shrinkB=1.5), zorder=5)
        ax.plot([x0], [t0], "o", ms=3.2, color=ORANGE, zorder=6)
    ax.legend(loc="lower right", fontsize=7.5, frameon=False)
    style(ax, r"$X_i=[0,1-\frac{1}{i+2}]$: $X_\Sigma$ retracts onto a copy of $X$")


def bad_panel(ax):
    """Example 3: X = [0,1], X_i = {0} u [1/(i+1), 1]."""
    for i in range(LEVELS):
        left = 1 / (i + 1)
        if i == 0:
            ax.plot([1, 1], [0, 1], color=ACCENT, lw=2.0, zorder=2)
        else:
            ax.add_patch(Rectangle((left, i), 1 - left, 1, facecolor=ACCENT, alpha=0.16, lw=0,
                                   zorder=1))
            ax.plot([left, left], [i, i + 1], color=ACCENT, lw=1.0, zorder=2)
            ax.plot([left, 1 / i], [i, i], color=ACCENT, lw=1.0, zorder=2)
    ax.plot([1, 1], [0, LEVELS], color=ACCENT, lw=1.0, zorder=2)
    ax.plot([0, 0], [0, LEVELS], color=ORANGE, lw=3.0, zorder=3, solid_capstyle="butt")

    x = np.linspace(1 / (LEVELS + 1), 1, 300)
    ax.plot(x, 1 / x - 1, color=FG, lw=1.4, ls="--", zorder=4, label=r"$\tau=\frac{1}{x}-1$")
    ax.annotate("the ray over $x=0$:\na path component\nby itself", (0.0, 0.75),
                xytext=(0.07, 0.12), fontsize=8, color=FG,
                arrowprops=dict(arrowstyle="-", color=MUTED, lw=0.7))
    ax.legend(loc="upper right", fontsize=8, frameon=False)
    style(ax, r"Example 3, $X_i=\{0\}\cup[\frac{1}{i+1},1]$: two pieces")


def main():
    fig, (a1, a2) = plt.subplots(1, 2, figsize=(7.0, 3.5))
    fig.patch.set_facecolor(BG)
    good_panel(a1)
    bad_panel(a2)
    fig.tight_layout()
    fig.savefig("figA-telescope.png", dpi=150, facecolor=BG)


if __name__ == "__main__":
    main()
