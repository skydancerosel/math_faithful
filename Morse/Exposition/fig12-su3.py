"""Figure for Chapter 12: the geodesics of SU(3) from the identity to a regular element.

The maximal torus of SU(3) has Lie algebra t = {diag(i th1, i th2, i th3) : th1+th2+th3 = 0},
drawn here in orthonormal coordinates for the bi-invariant metric <X,Y> = -trace(XY).
For a regular element q = exp(H), the geodesics from e to q are t -> exp(tX) with
X in H + 2*pi*Gamma (Gamma = integer vectors with sum 0).  By Theorem 20.5 / 21.7 the
index of such a geodesic is 2 * sum_{j<k} floor(|th_j - th_k| / 2 pi): twice the number
of walls {th_j - th_k = 2 pi m, m != 0} crossed by the segment from 0 to X.

Writes fig12-su3.png (150 dpi, 7 inches wide).
"""
import math
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

TWO_PI = 2 * math.pi
E1 = np.array([1.0, -1.0, 0.0]) / math.sqrt(2)
E2 = np.array([1.0, 1.0, -2.0]) / math.sqrt(6)
PAIRS = [(0, 1), (0, 2), (1, 2)]


def to_xy(theta):
    theta = np.asarray(theta, dtype=float)
    return float(theta @ E1), float(theta @ E2)


def index_of(theta):
    lam = 0
    for j, k in PAIRS:
        lam += 2 * math.floor(abs(theta[j] - theta[k]) / TWO_PI)
    return lam


def crossings(theta):
    """Parameters t in (0,1) at which exp(tX) meets a conjugate point."""
    ts = []
    for j, k in PAIRS:
        a = abs(theta[j] - theta[k])
        m = 1
        while TWO_PI * m < a:
            ts.append(TWO_PI * m / a)
            m += 1
    return sorted(ts)


H = np.array([0.4, -0.05, -0.35]) * TWO_PI  # a regular element in the fundamental alcove
R = 17.0  # half-width of the plotted window
MAXLAM = 10

fig, (ax, bx) = plt.subplots(1, 2, figsize=(7.0, 3.6), gridspec_kw={"width_ratios": [1.15, 1.0]})

# Walls: th_j - th_k = 2 pi m.  In (x, y) coordinates the three roots are these linear forms.
roots = [np.array([math.sqrt(2), 0.0]),
         np.array([1 / math.sqrt(2), math.sqrt(6) / 2]),
         np.array([-1 / math.sqrt(2), math.sqrt(6) / 2])]
s = np.linspace(-2 * R, 2 * R, 2)
for a in roots:
    n = a / np.linalg.norm(a)          # unit normal
    tdir = np.array([-n[1], n[0]])    # direction of the line
    for m in range(-6, 7):
        c = TWO_PI * m / np.linalg.norm(a)   # signed distance of the line from 0
        p0 = c * n
        pts = np.array([p0 + u * tdir for u in s])
        if m == 0:
            ax.plot(pts[:, 0], pts[:, 1], color="0.75", lw=0.6, ls="--", zorder=1)
        else:
            ax.plot(pts[:, 0], pts[:, 1], color="0.6", lw=0.6, zorder=1)

cmap = plt.get_cmap("viridis")
colors = {lam: cmap(lam / MAXLAM * 0.9) for lam in range(0, MAXLAM + 1, 2)}
count = {lam: 0 for lam in range(0, 40, 2)}
lattice = []
for n1 in range(-8, 9):
    for n2 in range(-8, 9):
        n3 = -n1 - n2
        th = H + TWO_PI * np.array([n1, n2, n3])
        lam = index_of(th)
        count[lam] = count.get(lam, 0) + 1
        x, y = to_xy(th)
        lattice.append((x, y, lam, th))
for x, y, lam, th in lattice:
    if lam <= MAXLAM and abs(x) < R and abs(y) < R:
        ax.scatter([x], [y], s=46, color=colors[lam], edgecolor="black", lw=0.5, zorder=3)
        ax.text(x + 0.55, y + 0.45, str(lam), fontsize=6.5, zorder=4)

# Highlight one geodesic of index 6 and its conjugate points.
th_sel = H + TWO_PI * np.array([1, -1, 0])
xs, ys = to_xy(th_sel)
ax.plot([0, xs], [0, ys], color="#c0392b", lw=1.6, zorder=2)
for t in crossings(th_sel):
    ax.scatter([t * xs], [t * ys], s=30, facecolor="white", edgecolor="#c0392b", lw=1.3, zorder=5)
ax.scatter([0], [0], marker="s", s=36, color="black", zorder=5)
ax.text(0.6, -1.6, "0 (= e)", fontsize=7)
ax.set_xlim(-R, R)
ax.set_ylim(-R, R)
ax.set_aspect("equal")
ax.set_xticks([])
ax.set_yticks([])
ax.set_title("geodesics e → q in SU(3), labelled by index", fontsize=8)

# Right panel: number of geodesics of each index versus 1/((1-t^2)(1-t^4)).
ms = list(range(0, 8))
observed = [count.get(2 * m, 0) for m in ms]
predicted = [m // 2 + 1 for m in ms]
bx.bar([2 * m for m in ms], observed, width=1.2, color="#8fa8c8",
       edgecolor="black", lw=0.5, label="geodesics counted")
bx.plot([2 * m for m in ms], predicted, "o", mfc="white", mec="#c0392b", ms=6,
        label="coefficient of $t^{\\lambda}$ in $1/((1-t^2)(1-t^4))$")
bx.set_xticks([2 * m for m in ms])
bx.set_xlabel("index $\\lambda$ (= cell dimension)", fontsize=8)
bx.set_ylabel("number of $\\lambda$-cells", fontsize=8)
bx.set_ylim(0, 5.5)
bx.tick_params(labelsize=7)
bx.legend(fontsize=6.5, loc="upper left", frameon=False)
bx.set_title("odd cells: none; $H_{\\lambda}(\\Omega SU(3))=\\mathbb{Z}^{N_\\lambda}$", fontsize=8)

fig.tight_layout()
fig.savefig("fig12-su3.png", dpi=150)
print("observed counts by index 0,2,4,...:", observed)
