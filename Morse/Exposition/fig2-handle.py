"""Figure for Chapter 2 (Milnor, Morse Theory, section 3): the proof of Theorem 3.2.

Milnor's Diagrams 5-7 for n = 2, lambda = 1, c = 0, in the Morse coordinates (x, y) = (u^1, u^2):
f = -x^2 + y^2,  F = f - mu(x^2 + 2 y^2).

Three stages of the deformation of M^{c+eps} onto M^{c-eps} u e^1:
  s = 0: sample points of M^{c+eps};
  s = 1: after the gradient flow of F used in Theorem 3.1 (Assertion 3): all points in F <= c - eps;
  s = 2: after Milnor's three-case deformation r_t (Assertion 4): all points in M^{c-eps} u e^1.

Writes fig2-handle.png (150 dpi, 7 inches wide).
"""

import os

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

plt.rcParams["contour.negative_linestyle"] = "solid"

FG = "#1f1f1d"
ACCENT = "#2a78d6"
MUTED = "#8a8984"
BG = "#ffffff"

EPS = 0.3
WIN = 1.5


# ----------------------------------------------------------------- the function mu


def lam(t):
    t = np.asarray(t, dtype=float)
    out = np.zeros_like(t)
    pos = t > 0
    out[pos] = np.exp(-1.0 / t[pos])
    return out


def step(r, p, q):
    """Smooth step: 0 for r <= p, 1 for r >= q (companion volume, Chapter 4, section 1)."""
    num = lam(r - p)
    return num / (num + lam(q - r))


def make_mu(eps):
    """mu(r) = (6 eps / 5 I) * int_r^inf beta, beta = 1 on [eps/5, 9 eps/5], 0 off (0, 2 eps)."""
    rr = np.linspace(0.0, 2 * eps, 6001)
    beta = step(rr, 0.0, eps / 5) * (1.0 - step(rr, 9 * eps / 5, 2 * eps))
    dr = rr[1] - rr[0]
    I = float(np.sum((beta[1:] + beta[:-1]) / 2) * dr)
    tail = np.concatenate([np.cumsum(((beta[1:] + beta[:-1]) / 2 * dr)[::-1])[::-1], [0.0]])
    mu_tab = 6 * eps / (5 * I) * tail
    dmu_tab = -6 * eps / (5 * I) * beta

    def mu(r):
        r = np.asarray(r, dtype=float)
        return np.interp(r, rr, mu_tab, left=mu_tab[0], right=0.0)

    def dmu(r):
        r = np.asarray(r, dtype=float)
        return np.interp(r, rr, dmu_tab, left=0.0, right=0.0)

    return mu, dmu


MU, DMU = make_mu(EPS)


def f(x, y):
    return -x**2 + y**2


def F(x, y):
    return -x**2 + y**2 - MU(x**2 + 2 * y**2)


def gradF(x, y):
    d = DMU(x**2 + 2 * y**2)
    return -2 * x * (1 + d), 2 * y * (1 - 2 * d)


# ----------------------------------------------------------------- the two deformations


def flow_down(x, y, nsteps=120):
    """Follow -grad F / |grad F|^2 until F = -eps (time F(q) + eps): Theorem 3.1 for F."""
    T = F(x, y) + EPS
    if T <= 0:
        return np.array([[x, y]])
    h = T / nsteps
    path = [(x, y)]

    def vel(px, py):
        gx, gy = gradF(px, py)
        n2 = gx * gx + gy * gy
        return -gx / n2, -gy / n2

    for _ in range(nsteps):
        k1 = vel(x, y)
        k2 = vel(x + h / 2 * k1[0], y + h / 2 * k1[1])
        k3 = vel(x + h / 2 * k2[0], y + h / 2 * k2[1])
        k4 = vel(x + h * k3[0], y + h * k3[1])
        x = x + h / 6 * (k1[0] + 2 * k2[0] + 2 * k3[0] + k4[0])
        y = y + h / 6 * (k1[1] + 2 * k2[1] + 2 * k3[1] + k4[1])
        path.append((x, y))
    return np.array(path)


def milnor_r(x, y, t):
    """Milnor's r_t (Assertion 4), with r_0 = identity and r_1 the retraction."""
    xi, eta = x * x, y * y
    if xi <= EPS:  # Case 1
        return x, (1 - t) * y
    if xi <= eta + EPS:  # Case 2
        if eta == 0:
            return x, y
        s = (1 - t) + t * np.sqrt((xi - EPS) / eta)
        return x, s * y
    return x, y  # Case 3


# ----------------------------------------------------------------- drawing


def background(ax):
    n = 500
    xs = np.linspace(-WIN, WIN, n)
    X, Y = np.meshgrid(xs, xs)
    fv, Fv = f(X, Y), F(X, Y)
    region = np.full(X.shape, np.nan)
    region[fv <= EPS] = 1.0  # band
    region[(Fv <= -EPS) & (fv > -EPS)] = 2.0  # handle
    region[fv <= -EPS] = 3.0  # M^{c-eps}
    ax.contourf(X, Y, region, levels=[0.5, 1.5], colors=[MUTED], alpha=0.16)
    ax.contourf(X, Y, region, levels=[1.5, 2.5], colors=[ACCENT], alpha=0.22)
    ax.contourf(X, Y, region, levels=[2.5, 3.5], colors=[FG], alpha=0.30)
    ax.contour(X, Y, Fv, levels=[-EPS], colors=[ACCENT], linewidths=1.0)
    yy = np.linspace(-WIN, WIN, 400)
    for sgn in (1, -1):
        ax.plot(sgn * np.sqrt(yy**2 + EPS), yy, color=FG, lw=0.9)  # f = c - eps
        ax.plot(yy, sgn * np.sqrt(yy**2 + EPS), color=MUTED, lw=0.9)  # f = c + eps
    th = np.linspace(0, 2 * np.pi, 300)
    ax.plot(np.sqrt(2 * EPS) * np.cos(th), np.sqrt(2 * EPS) * np.sin(th), color=MUTED, lw=0.6)
    ax.plot(np.sqrt(2 * EPS) * np.cos(th), np.sqrt(EPS) * np.sin(th), color=MUTED, lw=0.8, ls=(0, (3, 2)))
    ax.plot([-np.sqrt(EPS), np.sqrt(EPS)], [0, 0], color=FG, lw=2.6, solid_capstyle="butt")
    ax.plot([0], [0], "o", color=FG, ms=3)


def main():
    h = 0.15
    g = np.arange(-WIN + h / 2, WIN, h)
    pts = [(x, y) for x in g for y in g if f(x, y) <= EPS]

    kinds, start, mid, end, paths = [], [], [], [], []
    for (x, y) in pts:
        if f(x, y) <= -EPS:
            kinds.append(0)
        elif F(x, y) <= -EPS:
            kinds.append(1)
        else:
            kinds.append(2)
        p = flow_down(x, y)
        paths.append(p)
        start.append((x, y))
        mid.append(tuple(p[-1]))
        end.append(milnor_r(p[-1][0], p[-1][1], 1.0))
    start, mid, end = map(np.array, (start, mid, end))
    kinds = np.array(kinds)

    fig, axes = plt.subplots(1, 3, figsize=(7.0, 3.15))
    titles = [
        r"$s=0$: points of $M^{c+\epsilon}$",
        r"$s=1$: flow of $F$ (Assertion 3)",
        r"$s=2$: Milnor's $r_1$ (Assertion 4)",
    ]
    stages = [start, mid, end]
    for k, ax in enumerate(axes):
        background(ax)
        if k == 1:
            for p in paths:
                if len(p) > 1:
                    ax.plot(p[:, 0], p[:, 1], color=ACCENT, lw=0.4, alpha=0.5)
        if k == 2:
            for a, b in zip(mid, end):
                if np.hypot(*(a - b)) > 1e-6:
                    ax.plot([a[0], b[0]], [a[1], b[1]], color=FG, lw=0.4, alpha=0.5)
        P = stages[k]
        ax.scatter(P[kinds == 0, 0], P[kinds == 0, 1], s=4, facecolor=BG, edgecolor=MUTED, lw=0.5, alpha=0.8, zorder=3)
        ax.scatter(P[kinds == 1, 0], P[kinds == 1, 1], s=7, color=FG, edgecolor=BG, lw=0.3, zorder=4)
        ax.scatter(P[kinds == 2, 0], P[kinds == 2, 1], s=8, color=ACCENT, edgecolor=BG, lw=0.3, zorder=5)
        ax.set_xlim(-WIN, WIN)
        ax.set_ylim(-WIN, WIN)
        ax.set_aspect("equal")
        ax.set_xticks([])
        ax.set_yticks([])
        for sp in ax.spines.values():
            sp.set_color(MUTED)
            sp.set_linewidth(0.6)
        ax.set_title(titles[k], fontsize=8, color=FG)
    fig.text(
        0.5, 0.02,
        r"$n=2$, $\lambda=1$, $\epsilon=0.3$.  Dark: $M^{c-\epsilon}$.  Tinted: the handle $H$.  Pale: $f^{-1}[c-\epsilon, c+\epsilon]$."
        "\n" r"Thick: the cell $e^1$.  Dashed: $\xi + 2\eta = 2\epsilon$.  Dots start in the band (blue), in $H$ (black), in $M^{c-\epsilon}$ (hollow).",
        ha="center", va="bottom", fontsize=7.5, color=FG,
    )
    fig.tight_layout(rect=(0, 0.12, 1, 0.98), w_pad=0.5)
    fig.savefig(os.path.join(os.path.dirname(os.path.abspath(__file__)), "fig2-handle.png"), dpi=150)

    # sanity checks: all points end in F <= c - eps after stage A, in M^{c-eps} u e^1 after stage B
    Fm = F(mid[:, 0], mid[:, 1])
    assert np.all(Fm <= -EPS + 2e-3), Fm.max()
    on_cell = (np.abs(end[:, 1]) < 1e-9) & (end[:, 0] ** 2 <= EPS + 1e-9)
    in_M = f(end[:, 0], end[:, 1]) <= -EPS + 2e-3
    assert np.all(on_cell | in_M)


if __name__ == "__main__":
    main()
