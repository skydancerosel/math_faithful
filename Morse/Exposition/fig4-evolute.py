"""Figure for Chapter 4 (Milnor, Morse Theory, section 6): focal points and the normals from a point.

The wall of an oval room is the ellipse x^2/a^2 + y^2/b^2 = 1 with a = 10 m, b = 6 m.  Its focal
set is the evolute (dashed).  For a listener inside the evolute there are four normals to the
wall (four single-reflection echoes), for one outside it two.  A normal is drawn dashed when its
foot is a local maximum of the distance (index 1); by Milnor's Lemma 6.9 this happens exactly
when the centre of curvature at the foot (small circle) lies between the foot and the listener.

Left: the room.  Right: the distance from each listener to the wall point x(theta).
Writes fig4-evolute.png (150 dpi, 7 inches wide).
"""
import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

A, B = 10.0, 6.0
LISTENERS = [((3.0, 2.0), "#c0392b", "listener at (3, 2): inside the evolute"),
             ((8.0, 1.0), "#1f4e79", "listener at (8, 1): outside the evolute")]


def wall(theta):
    return np.array([A * np.cos(theta), B * np.sin(theta)])


def centre_of_curvature(theta):
    c = A * A - B * B
    return np.array([c / A * np.cos(theta) ** 3, -c / B * np.sin(theta) ** 3])


def half_dL(theta, p):
    """(1/2) d/dtheta |x(theta) - p|^2."""
    return ((B * B - A * A) * np.sin(theta) * np.cos(theta)
            + A * p[0] * np.sin(theta) - B * p[1] * np.cos(theta))


def half_d2L(theta, p):
    return ((B * B - A * A) * np.cos(2 * theta)
            + A * p[0] * np.cos(theta) + B * p[1] * np.sin(theta))


def normals(p, n=4000):
    """Feet of the normals from p: zeros of dL/dtheta, with the Morse index of L_p there."""
    # the grid is shifted so that roots on symmetry axes do not fall on grid points
    th = 0.000731 + np.linspace(0, 2 * np.pi, n, endpoint=False)
    v = half_dL(th, p)
    feet = []
    for i in range(n):
        t0, t1 = th[i], th[i] + 2 * np.pi / n
        f0, f1 = v[i], half_dL(t1, p)
        if f0 == 0 or f0 * f1 < 0:
            for _ in range(60):
                tm = 0.5 * (t0 + t1)
                fm = half_dL(tm, p)
                if f0 * fm <= 0:
                    t1 = tm
                else:
                    t0, f0 = tm, fm
            t = (0.5 * (t0 + t1)) % (2 * np.pi)
            if any(min(abs(t - s), 2 * np.pi - abs(t - s)) < 1e-7 for s, _ in feet):
                continue
            index = 1 if half_d2L(t, p) < 0 else 0
            feet.append((t, index))
    return feet


def inside_evolute(p):
    return (A * abs(p[0])) ** (2 / 3) + (B * abs(p[1])) ** (2 / 3) < (A * A - B * B) ** (2 / 3)


def main():
    fig, (ax, bx) = plt.subplots(1, 2, figsize=(7.0, 3.6), gridspec_kw={"width_ratios": [1.25, 1]})
    th = np.linspace(0, 2 * np.pi, 721)
    wx, wy = wall(th)
    ex, ey = centre_of_curvature(th)
    ax.plot(wx, wy, color="black", lw=2.0)
    ax.plot(ex, ey, color="0.35", lw=1.0, ls="--", label="evolute (focal points)")
    for p, colour, label in LISTENERS:
        feet = normals(p)
        for t, index in feet:
            q = wall(t)
            c = centre_of_curvature(t)
            # Lemma 6.9: index 1 iff the centre of curvature lies on the segment from q to p
            on_segment = np.dot(c - q, np.array(p) - q) > 0 and \
                np.linalg.norm(c - q) < np.linalg.norm(np.array(p) - q)
            assert on_segment == (index == 1)
            ax.plot([p[0], q[0]], [p[1], q[1]], color=colour, lw=1.3,
                    ls="--" if index == 1 else "-")
            ax.plot(q[0], q[1], "o", ms=3.5, color=colour)
            ax.plot(c[0], c[1], "o", ms=5, mfc="white", mec=colour, mew=1.2)
        ax.plot(p[0], p[1], "o", ms=7, color=colour, mec="white", mew=1.0)
        d = np.hypot(wx - p[0], wy - p[1])
        bx.plot(th, d, color=colour, lw=1.4, label=label)
        for t, index in feet:
            dist = np.hypot(*(wall(t) - np.array(p)))
            bx.plot(t, dist, "^" if index == 1 else "o", ms=6, color=colour,
                    mfc="white" if index == 1 else colour)
        assert len(feet) == (4 if inside_evolute(p) else 2), (p, len(feet))
    ax.set_xlim(-11.5, 11.5)
    ax.set_ylim(-11.5, 11.5)
    ax.set_aspect("equal")
    ax.set_xlabel("m")
    ax.set_title("Normals from two listeners\n(dashed: index 1; circles: centres of curvature)",
                 fontsize=9)
    ax.legend(loc="upper left", fontsize=7, frameon=False, handlelength=1.6)
    bx.set_xlim(0, 2 * np.pi)
    bx.set_xticks([0, np.pi / 2, np.pi, 3 * np.pi / 2, 2 * np.pi])
    bx.set_xticklabels(["0", r"$\pi/2$", r"$\pi$", r"$3\pi/2$", r"$2\pi$"])
    bx.set_xlabel(r"position on the wall $\theta$")
    bx.set_ylabel(r"distance $|p - x(\theta)|$ (m)")
    bx.set_title("Distance along the wall\n(dots: minima, triangles: maxima)", fontsize=9)
    bx.legend(loc="upper center", fontsize=7, frameon=False)
    bx.set_ylim(0, 24)
    fig.tight_layout()
    fig.savefig("fig4-evolute.png", dpi=150)


if __name__ == "__main__":
    main()
