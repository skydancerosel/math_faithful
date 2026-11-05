"""Figure for Chapter 9: conjugate points and the index theorem on the unit sphere (K = 1).

(a) The Jacobi fields s*sin(t) along a unit-speed geodesic gamma: the linearized fan of geodesics
    leaving gamma(0), refocusing at the conjugate points t = pi, 2 pi, 3 pi.
(b) The eigenvalues of the matrix of E_** on normal broken Jacobi fields along gamma|[0, tau], for
    the subdivision of [0, tau] into k = 5 equal pieces, rescaled by the positive factor sin(tau/k):
    mu_m(tau) = 2 (cos(tau/k) - cos(m pi/k)), m = 1, ..., k - 1.  Each crosses zero at tau = m pi.
(c) The index lambda(tau) = number of negative eigenvalues = number of conjugate points in (0, tau).

Writes fig9-conjugate.png (150 dpi, 7 inches wide).
"""
import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

FG, ACCENT, MUTED = "#1d1d1f", "#b4441f", "#8a8780"
TMAX, TAU, K_PIECES = 10.0, 7.5, 5

fig, (ax1, ax2, ax3) = plt.subplots(3, 1, figsize=(7.0, 6.4), dpi=150, sharex=True,
                                    gridspec_kw={"height_ratios": [1.15, 1.3, 0.75]})

# (a) the fan of Jacobi fields
t = np.linspace(0, TMAX, 800)
for s in (0.25, 0.5, 0.75, 1.0):
    for sign in (1, -1):
        y = sign * s * np.sin(t)
        ax1.plot(t[t <= TAU], y[t <= TAU], color=ACCENT, lw=0.9, alpha=0.85)
        ax1.plot(t[t >= TAU], y[t >= TAU], color=ACCENT, lw=0.8, alpha=0.3)
ax1.plot([0, TAU], [0, 0], color=FG, lw=2.2)
ax1.plot([TAU, TMAX], [0, 0], color=MUTED, lw=1.2, ls="--")
for m in (1, 2, 3):
    ax1.plot(m * np.pi, 0, "o", color=FG, ms=5, zorder=5)
    lab = r"$\pi$" if m == 1 else rf"${m}\pi$"
    ax1.annotate(lab, (m * np.pi, 0), xytext=(4, 6), textcoords="offset points", fontsize=8.5)
ax1.plot(0, 0, "o", color=FG, ms=5)
ax1.annotate(r"$\gamma(0)$", (0, 0), xytext=(4, -13), textcoords="offset points", fontsize=8.5)
ax1.axvline(TAU, color=MUTED, lw=0.8, ls=":")
ax1.set_ylim(-1.25, 1.25)
ax1.set_yticks([])
ax1.set_title(r"(a) Jacobi fields $s\,\sin t$ along a great circle: the fan from $\gamma(0)$ "
              r"refocuses at the conjugate points", fontsize=9)

# (b) eigenvalues of the broken-Jacobi Hessian, rescaled
taus = np.linspace(0.02, TMAX, 600)
k = K_PIECES
for m in range(1, k):
    mu = 2 * (np.cos(taus / k) - np.cos(m * np.pi / k))
    col = ACCENT if m * np.pi < TMAX else MUTED
    ax2.plot(taus, mu, color=col, lw=1.3 if col == ACCENT else 0.9)
    if m * np.pi < TMAX:
        ax2.plot(m * np.pi, 0, "o", color=ACCENT, ms=4.5, zorder=5)
ax2.axhline(0, color=FG, lw=0.7)
ax2.axvline(TAU, color=MUTED, lw=0.8, ls=":")
ax2.set_ylim(-2.7, 3.9)
ax2.set_ylabel(r"$\mu_m(\tau)$", fontsize=9)
ax2.tick_params(labelsize=8)
ax2.set_title(rf"(b) eigenvalues of $E_{{**}}$ on normal broken Jacobi fields, $k = {k}$ pieces "
              r"(rescaled): $2(\cos\frac{\tau}{k} - \cos\frac{m\pi}{k})$", fontsize=9)

# (c) the index as a step function (left-continuous)
edges = [0.0] + [m * np.pi for m in (1, 2, 3)] + [TMAX]
for j in range(len(edges) - 1):
    a, b = edges[j], edges[j + 1]
    ax3.plot([a, b], [j, j], color=FG, lw=2)
    if j > 0:
        ax3.plot(a, j, "o", mfc="white", mec=FG, ms=5, zorder=5)        # open: value not taken
        ax3.plot(a, j - 1, "o", color=FG, ms=5, zorder=5)               # closed: lambda(m pi) = m - 1
ax3.axvline(TAU, color=MUTED, lw=0.8, ls=":")
ax3.annotate(r"$\lambda(7.5) = 2$", (TAU, 2), xytext=(6, -14), textcoords="offset points", fontsize=8.5)
ax3.set_ylim(-0.5, 3.6)
ax3.set_yticks([0, 1, 2, 3])
ax3.set_ylabel(r"$\lambda(\tau)$", fontsize=9)
ax3.set_xlabel(r"$\tau$ (arc length along $\gamma$)", fontsize=9)
ax3.set_xticks([0, np.pi, 2 * np.pi, 3 * np.pi])
ax3.set_xticklabels(["0", r"$\pi$", r"$2\pi$", r"$3\pi$"])
ax3.tick_params(labelsize=8)
ax3.set_title(r"(c) the index $\lambda(\tau)$ = number of negative eigenvalues = conjugate points in "
              r"$(0,\tau)$", fontsize=9)
for ax in (ax1, ax2, ax3):
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)
ax1.spines["left"].set_visible(False)
ax3.set_xlim(0, TMAX)
fig.tight_layout(h_pad=0.6)
fig.savefig("fig9-conjugate.png", dpi=150)
print("wrote fig9-conjugate.png")
