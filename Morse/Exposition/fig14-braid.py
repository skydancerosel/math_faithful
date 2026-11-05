"""Figure for Chapter 14: the eigenvalue braid of a geodesic exp(tA) from I to -I in SU(2m).

The eigenvalues of exp(tA) are exp(i*pi*k_j*t).  Drawing the eigenvalue at time t at radius 1 + t turns
each eigenvalue into a spiral from the inner circle (t = 0, all at 1) to the outer circle (t = 1, all
at -1).  Two spirals with k_j != k_l cross exactly at the conjugate points found in Lemma 4.1, and each
crossing contributes 2 to the index.  Left: a minimal geodesic, no crossings.  Right: the non-minimal
geodesic k = (3, 1, -1, -3), four crossings, index 8 = 4m.

Writes fig14-braid.png (150 dpi, 7 inches wide).
"""
from fractions import Fraction

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


def collisions(ks):
    """All (t, angle, j, l) with 0 < t < 1 at which eigenvalues j and l coincide."""
    out = []
    n = len(ks)
    for j in range(n):
        for l in range(j + 1, n):
            d = abs(ks[j] - ks[l])
            if d == 0:
                continue
            for s in range(1, d // 2):
                t = Fraction(2 * s, d)
                out.append((t, np.pi * ks[j] * float(t), j, l))
    return out


def index_formula(ks):
    return sum(a - b - 2 for a in ks for b in ks if a > b)


def draw(ax, ks, title):
    ax.set_aspect("equal")
    ax.axis("off")
    th = np.linspace(0, 2 * np.pi, 400)
    for t in np.linspace(0, 1, 5):
        lw = 1.2 if t in (0.0, 1.0) else 0.5
        ax.plot((1 + t) * np.cos(th), (1 + t) * np.sin(th), color="0.75", lw=lw, zorder=1)
    ts = np.linspace(0, 1, 600)
    distinct = sorted(set(ks), reverse=True)
    colours = plt.cm.viridis(np.linspace(0.05, 0.85, len(distinct)))
    for c, k in zip(colours, distinct):
        mult = ks.count(k)
        r = 1 + ts
        ax.plot(r * np.cos(np.pi * k * ts), r * np.sin(np.pi * k * ts), color=c, lw=2.0, zorder=2)
        # label near the outer end, slightly before t = 1
        tl = 0.88
        lab = f"$k={k}$" + (rf"$\,\times{mult}$" if mult > 1 else "")
        ax.text(
            (1 + tl) * np.cos(np.pi * k * tl) * 1.13,
            (1 + tl) * np.sin(np.pi * k * tl) * 1.13,
            lab,
            color=c,
            fontsize=8,
            ha="center",
            va="center",
        )
    for t, ang, j, l in collisions(ks):
        r = 1 + float(t)
        ax.plot(r * np.cos(ang), r * np.sin(ang), "o", ms=7, mfc="crimson", mec="k", zorder=4)
        # label just inside the crossing, on a light box so that it stays readable
        rr = r - 0.42
        ax.text(
            rr * np.cos(ang),
            rr * np.sin(ang) + (0.0 if abs(np.sin(ang)) > 0.5 else 0.22),
            f"$t={t.numerator}/{t.denominator}$",
            fontsize=7,
            ha="center",
            va="center",
            color="crimson",
            zorder=5,
            bbox=dict(boxstyle="round,pad=0.12", fc="white", ec="none", alpha=0.85),
        )
    ax.plot([1], [0], "ko", ms=4, zorder=6)
    ax.plot([-2], [0], "ko", ms=4, zorder=6)
    ax.text(1.0, -0.32, "$I$", fontsize=9, ha="center", zorder=6)
    ax.text(-2.12, -0.30, "$-I$", fontsize=9, ha="right", zorder=6)
    ax.set_xlim(-2.9, 2.6)
    ax.set_ylim(-2.6, 2.6)
    ax.set_title(title, fontsize=9)


def main():
    fig, axes = plt.subplots(1, 2, figsize=(7.0, 3.7))
    k_min = [1, 1, -1, -1]
    k_non = [3, 1, -1, -3]
    n_col = len(collisions(k_non))
    assert 2 * n_col == index_formula(k_non) == 8
    assert index_formula(k_min) == 0 and not collisions(k_min)
    draw(axes[0], k_min, "minimal: $k=(1,1,-1,-1)$\nno crossings, $\\lambda=0$")
    draw(
        axes[1],
        k_non,
        f"non-minimal: $k=(3,1,-1,-3)$\n{n_col} crossings, $\\lambda=2\\cdot{n_col}={2 * n_col}=4m$",
    )
    fig.suptitle(
        "Eigenvalues $e^{i\\pi k_j t}$ of $\\exp(tA)$ in $SU(4)$, drawn at radius $1+t$",
        fontsize=10,
    )
    fig.tight_layout(rect=(0, 0, 1, 0.94))
    fig.savefig("fig14-braid.png", dpi=150)


if __name__ == "__main__":
    main()
