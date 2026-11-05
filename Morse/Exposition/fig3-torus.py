"""Figure for Chapter 3 (Milnor, Morse Theory, sections 4-5): Morse functions on the torus.

Left: the double pendulum potential V = (1 - cos phi)/2 + (1 - cos psi)/4 (equal masses and
lengths, rescaled), with C = (1, 2, 1).  Right: two coupled threefold rotors,
V = (1 - cos 3 phi)/2 + (1 - cos 3 psi)/2 - kappa cos(phi - psi), kappa = 1.75, with
C = (3, 12, 9).  In both, C1 = C0 + C2 as the Morse inequalities of the torus demand.

Writes fig3-torus.png (150 dpi, 7 inches wide).
"""
import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

TWO_PI = 2 * np.pi


def make_model(k, B, kap, delta=0.0):
    """V = (1 - cos k x)/2 + B (1 - cos k y)/2 - kap cos(x - y - delta), with derivatives."""

    def V(x, y):
        return 0.5 * (1 - np.cos(k * x)) + 0.5 * B * (1 - np.cos(k * y)) - kap * np.cos(x - y - delta)

    def grad(x, y):
        s = kap * np.sin(x - y - delta)
        return np.array([0.5 * k * np.sin(k * x) + s, 0.5 * B * k * np.sin(k * y) - s])

    def hess(x, y):
        c = kap * np.cos(x - y - delta)
        return np.array([[0.5 * k * k * np.cos(k * x) + c, -c],
                         [-c, 0.5 * B * k * k * np.cos(k * y) + c]])

    return V, grad, hess


def critical_points(grad, hess, n=240):
    """Cells where both gradient components change sign, refined by damped Newton steps."""
    xs = np.linspace(0, TWO_PI, n, endpoint=False) + 1e-3
    X, Y = np.meshgrid(xs, xs, indexing="ij")
    G = grad(X, Y)
    pts = []
    for i in range(n):
        for j in range(n):
            i2, j2 = (i + 1) % n, (j + 1) % n
            a = (G[0, i, j], G[0, i2, j], G[0, i, j2], G[0, i2, j2])
            b = (G[1, i, j], G[1, i2, j], G[1, i, j2], G[1, i2, j2])
            if not (min(a) <= 0 <= max(a) and min(b) <= 0 <= max(b)):
                continue
            z = np.array([xs[i], xs[j]])
            converged = False
            for _ in range(60):
                g = grad(*z)
                try:
                    d = np.linalg.solve(hess(*z), g)
                except np.linalg.LinAlgError:
                    break
                step = np.linalg.norm(d)
                if step > 0.05:
                    d *= 0.05 / step
                z = z - d
                if np.linalg.norm(grad(*z)) < 1e-12:
                    converged = True
                    break
            if not converged:
                continue
            z = np.mod(z, TWO_PI)
            dup = False
            for p in pts:
                dd = np.abs(p[:2] - z)
                dd = np.minimum(dd, TWO_PI - dd)
                if dd.max() < 1e-5:
                    dup = True
                    break
            if dup:
                continue
            ev = np.linalg.eigvalsh(hess(*z))
            pts.append(np.array([z[0], z[1], int(np.sum(ev < 0))]))
    return pts


def panel(ax, model, title, offset):
    """Plot V on the fundamental domain [offset, offset + 2 pi]^2 (opposite edges are glued).

    The offset is chosen so that no critical point lies on the edge of the square."""
    V, grad, hess = model
    t = np.linspace(offset, offset + TWO_PI, 361)
    X, Y = np.meshgrid(t, t, indexing="xy")
    Z = V(X, Y)
    lo, hi = offset, offset + TWO_PI
    ax.imshow(Z, origin="lower", extent=(lo, hi, lo, hi), cmap="Greys",
              interpolation="bilinear", alpha=0.85)
    ax.contour(X, Y, Z, levels=12, colors="0.35", linewidths=0.5, linestyles="solid")
    pts = critical_points(grad, hess)
    counts = [0, 0, 0]
    for x, y, idx in pts:
        idx = int(idx)
        counts[idx] += 1
        x = offset + np.mod(x - offset, TWO_PI)
        y = offset + np.mod(y - offset, TWO_PI)
        if idx == 0:
            ax.plot(x, y, "o", ms=7, mfc="#c0392b", mec="white", mew=0.8)
        elif idx == 1:
            ax.plot(x, y, "x", ms=7, mew=2.0, color="#1f4e79")
        else:
            ax.plot(x, y, "^", ms=7, mfc="white", mec="black", mew=1.2)
    ax.set_xlim(lo, hi)
    ax.set_ylim(lo, hi)
    names = {-1: r"$-\pi/2$", 0: "0", 1: r"$\pi/2$", 2: r"$\pi$", 3: r"$3\pi/2$", 4: r"$2\pi$"}
    ticks = [m for m in range(-1, 5) if lo - 1e-9 <= m * np.pi / 2 <= hi + 1e-9]
    ax.set_xticks([m * np.pi / 2 for m in ticks])
    ax.set_xticklabels([names[m] for m in ticks])
    ax.set_yticks([m * np.pi / 2 for m in ticks])
    ax.set_yticklabels([names[m] for m in ticks])
    ax.set_xlabel(r"$\varphi$")
    ax.set_ylabel(r"$\psi$")
    ax.set_aspect("equal")
    c0, c1, c2 = counts
    ax.set_title(f"{title}\n$C_0={c0}$, $C_1={c1}$, $C_2={c2}$;  "
                 f"$C_0-C_1+C_2={c0 - c1 + c2}$", fontsize=9)
    return counts


def main():
    fig, axes = plt.subplots(1, 2, figsize=(7.0, 3.9))
    c_left = panel(axes[0], make_model(1, 0.5, 0.0), "Double pendulum", -np.pi / 2)
    c_right = panel(axes[1], make_model(3, 1.0, 1.75), r"Two rotors, $\kappa = 1.75$", -0.27)
    assert c_left == [1, 2, 1], c_left
    assert c_right == [3, 12, 9], c_right
    handles = [
        plt.Line2D([], [], ls="", marker="o", ms=7, mfc="#c0392b", mec="white", label="minimum (index 0)"),
        plt.Line2D([], [], ls="", marker="x", ms=7, mew=2.0, color="#1f4e79", label="saddle (index 1)"),
        plt.Line2D([], [], ls="", marker="^", ms=7, mfc="white", mec="black", label="maximum (index 2)"),
    ]
    fig.legend(handles=handles, loc="lower center", ncol=3, fontsize=8, frameon=False)
    fig.tight_layout(rect=(0, 0.07, 1, 1))
    fig.savefig("fig3-torus.png", dpi=150)


if __name__ == "__main__":
    main()
