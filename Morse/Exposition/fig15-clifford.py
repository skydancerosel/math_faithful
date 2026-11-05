"""Figure for Chapter 15: the sixteen pieces of R^16 and the eight-step chain.

Left: R^16 with the anti-commuting complex structures J'_1..J'_8 of Chapter 15, section 3, splits into
the sixteen joint eigenlines of the commuting involutions
    theta3 = J1 J2 J3, theta5 = J1 J4 J5, theta6 = J2 J4 J6, theta7 = J1 J6 J7,
drawn as a 4 x 4 grid labelled by their signs.  The nested outlines are the subspaces of Lemma 24.6:
V1 (theta3 = +), W (also theta5 = +), X (also theta6 = +), X1 (also theta7 = +).  Arrows show where
J1, J2, J4, J8 send the line X1: each reverses exactly the signs of the thetas it anti-commutes with.
Right: the eight spaces Omega_0, ..., Omega_7 of the chain, with pi_0(Omega_k) = pi_k(O).

The script also verifies numerically that the sixteen joint eigenspaces are lines and that the flips
are as drawn.  Writes fig15-clifford.png (150 dpi, 7 inches wide).
"""
import itertools

import matplotlib

matplotlib.use("Agg")
import matplotlib.patches as mpatches
import matplotlib.pyplot as plt
import numpy as np

S = np.array([[0.0, -1.0], [1.0, 0.0]])
T = np.diag([1.0, -1.0])
K = np.array([[0.0, 1.0], [1.0, 0.0]])
ONE = np.eye(2)
LETTERS = {"1": ONE, "s": S, "t": T, "k": K}
WORDS = ["11st", "1stt", "s1kt", "sttt", "sktt", "tskt", "kskt", "111s"]  # J'_1 .. J'_8


def kron_word(w):
    m = np.array([[1.0]])
    for c in w:
        m = np.kron(m, LETTERS[c])
    return m


def structures():
    J = [kron_word(w) for w in WORDS]
    n = 16
    for a in range(8):
        assert np.allclose(J[a] @ J[a], -np.eye(n)) and np.allclose(J[a].T, -J[a])
        for b in range(a + 1, 8):
            assert np.allclose(J[a] @ J[b], -J[b] @ J[a])
    th = {
        3: J[0] @ J[1] @ J[2],
        5: J[0] @ J[3] @ J[4],
        6: J[1] @ J[3] @ J[5],
        7: J[0] @ J[5] @ J[6],
    }
    return J, th


def flip_pattern(J, th, a):
    """Which thetas (in the order 3, 5, 6, 7) anti-commute with J_a (a = 1..8)."""
    return tuple(int(not np.allclose(J[a - 1] @ th[key], th[key] @ J[a - 1])) for key in (3, 5, 6, 7))


def check(J, th):
    I = np.eye(16)
    for eps in itertools.product([1, -1], repeat=4):
        P = I.copy()
        for e, key in zip(eps, (3, 5, 6, 7)):
            P = P @ (I + e * th[key]) / 2
        assert round(np.trace(P)) == 1, "joint eigenspace is not a line"


# grid position of a sign pattern (e3, e5, e6, e7): row from (e3, e5), column from (e6, e7)
ORDER = [(1, 1), (1, -1), (-1, 1), (-1, -1)]


def cell(eps):
    e3, e5, e6, e7 = eps
    return ORDER.index((e3, e5)), ORDER.index((e6, e7))


def sgn(e):
    return "+" if e > 0 else "−"


def draw_grid(ax, J, th):
    ax.set_xlim(-0.6, 4.3)
    ax.set_ylim(-0.9, 4.6)
    ax.set_aspect("equal")
    ax.axis("off")
    for eps in itertools.product([1, -1], repeat=4):
        r, c = cell(eps)
        x, y = c, 3 - r
        ax.add_patch(mpatches.Rectangle((x + 0.04, y + 0.04), 0.92, 0.92, fc="#eef2f7", ec="0.6", lw=0.8))
        ax.text(x + 0.5, y + 0.5, "".join(sgn(e) for e in eps), ha="center", va="center", fontsize=8,
                family="monospace")
    # nested subspaces of Lemma 24.6
    nests = [
        ("$V_1$", (0, 2), (4, 2), "#1f5f99"),  # rows 0-1  (theta3 = +)
        ("$W$", (0, 3), (4, 1), "#2a8a6e"),  # row 0     (theta5 = +)
        ("$X$", (0, 3), (2, 1), "#c27c0e"),  # row 0, cols 0-1 (theta6 = +)
        ("$X_1$", (0, 3), (1, 1), "#b22222"),  # the cell ++++
    ]
    pad = [0.0, 0.06, 0.12, 0.18]
    for (lab, (x, y), (w, h), col), p in zip(nests, pad):
        ax.add_patch(mpatches.Rectangle((x - 0.02 + p, y - 0.02 + p), w + 0.04 - 2 * p, h + 0.04 - 2 * p,
                                        fill=False, ec=col, lw=2.0))
    ax.text(4.08, 3.0, "$V_1$", color="#1f5f99", fontsize=9, va="center")
    ax.text(4.08, 3.55, "$W$", color="#2a8a6e", fontsize=9, va="center")
    ax.text(1.6, 4.18, "$X$", color="#c27c0e", fontsize=9, ha="center")
    ax.text(0.5, 4.18, "$X_1$", color="#b22222", fontsize=9, ha="center")
    # arrows from X_1 under J1, J2, J4, J8
    start = (0.5, 3.5)
    styles = {1: ("#444444", -0.35, (2.55, 3.98)), 2: ("#7b3294", 0.45, (1.0, 3.0)),
              4: ("#008837", 0.3, (0.0, 2.0)), 8: ("#d95f02", 0.2, (3.0, 2.0))}
    for a in (1, 2, 4, 8):
        col, rad, lab = styles[a]
        f = flip_pattern(J, th, a)
        eps = tuple(-1 if bit else 1 for bit in f)
        r, c = cell(eps)
        end = (c + 0.5, 3 - r + 0.5)
        ax.annotate("", xy=end, xytext=start,
                    arrowprops=dict(arrowstyle="-|>", color=col, lw=1.5,
                                    connectionstyle=f"arc3,rad={rad}", shrinkA=8, shrinkB=11))
        ax.text(lab[0], lab[1], f"$J_{a}$", color=col, fontsize=10, ha="center", va="center",
                bbox=dict(boxstyle="round,pad=0.12", fc="white", ec="none", alpha=0.85))
    ax.text(2.0, -0.35, "signs of $(\\theta_3,\\theta_5,\\theta_6,\\theta_7)$ on the 16 lines of $\\mathbb{R}^{16}$",
            ha="center", fontsize=8)
    ax.text(2.0, -0.7, "$J_1, J_2, J_4, J_8$ reach every line from $X_1$: $\\mathbb{R}^{16}$ is minimal, $m_8=16$",
            ha="center", fontsize=8)


def draw_clock(ax):
    ax.set_xlim(-1.95, 1.95)
    ax.set_ylim(-1.95, 1.95)
    ax.set_aspect("equal")
    ax.axis("off")
    names = ["$O$", "$O/U$", "$U/Sp$", "$\\mathbb{Z}\\times BSp$", "$Sp$", "$Sp/U$", "$U/O$",
             "$\\mathbb{Z}\\times BO$"]
    pi0 = ["$\\mathbb{Z}/2$", "$\\mathbb{Z}/2$", "$0$", "$\\mathbb{Z}$", "$0$", "$0$", "$0$", "$\\mathbb{Z}$"]
    R = 1.22
    pos = []
    for k in range(8):
        ang = np.pi / 2 - 2 * np.pi * k / 8
        pos.append((R * np.cos(ang), R * np.sin(ang)))
    for k in range(8):
        a = pos[k]
        b = pos[(k + 1) % 8]
        ax.annotate("", xy=a, xytext=b,
                    arrowprops=dict(arrowstyle="-|>", color="0.45", lw=1.0,
                                    connectionstyle="arc3,rad=-0.2", shrinkA=15, shrinkB=15))
    for k, (x, y) in enumerate(pos):
        ax.add_patch(mpatches.Circle((x, y), 0.33, fc="#eef2f7", ec="#1f5f99", lw=1.2))
        ax.text(x, y + 0.1, f"$\\Omega_{k}$", ha="center", va="center", fontsize=9)
        ax.text(x, y - 0.12, names[k], ha="center", va="center", fontsize=7)
        lx, ly = 1.66 * x / R, 1.66 * y / R
        ax.text(lx, ly, pi0[k], ha="center", va="center", fontsize=8, color="#b22222")
    ax.text(0, 0.12, "$\\Omega_{k+1}\\simeq\\Omega\\,\\Omega_k$", ha="center", va="center", fontsize=9)
    ax.text(0, -0.12, "$\\Omega_8\\cong\\Omega_0 = O$", ha="center", va="center", fontsize=9)
    ax.text(0, -1.93, "red: $\\pi_0\\Omega_k\\cong\\pi_kO$; arrows: one loop each step", ha="center",
            fontsize=8)


def main():
    J, th = structures()
    check(J, th)
    expected = {1: (0, 0, 1, 0), 2: (0, 1, 0, 1), 4: (1, 0, 0, 1), 8: (1, 1, 1, 1)}
    for a, f in expected.items():
        assert flip_pattern(J, th, a) == f
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 3.7), gridspec_kw={"width_ratios": [1.15, 1.0]})
    draw_grid(ax1, J, th)
    draw_clock(ax2)
    fig.tight_layout()
    fig.savefig("fig15-clifford.png", dpi=150)


if __name__ == "__main__":
    main()
