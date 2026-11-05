"""Figure for Chapter 11 (Milnor, Morse Theory, Sections 18-19).

Geodesics fired from one point p of the quadric surface  x^2 + y^2 + sigma z^2 = 1,  together with
the first conjugate point along each of them.  The geodesic equation is integrated in R^3,

    x'' = -(x'^T A x' / |A x|^2) A x,      A = diag(1, 1, sigma),

with the Jacobi equation  j'' + K j = 0,  j(0) = 0, j'(0) = 1  for the normal Jacobi field, where
K = sigma / (x^2 + y^2 + sigma^2 z^2)^2 is the Gaussian curvature.  A conjugate point is a zero of j.

  (a) sigma = -0.6, a hyperboloid of one sheet, K < 0: no conjugate points (Lemma 19.1), although
      geodesics winding round the neck cross one another;
  (b) sigma = 1, the round sphere: every geodesic from p reaches its first conjugate point at the
      antipode, at distance pi;
  (c) sigma = 2.5, an oblate spheroid: the first conjugate points fill a curve with four cusps,
      the caustic, a set of measure zero (Corollary 18.2).

Writes fig11-caustic.png (150 dpi, 7 inches wide).
"""

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

FG = "#0b0b0b"
MUTED = "#8a8984"
ACCENT = "#2a78d6"
BG = "#ffffff"


def surface_point(sigma, lat_deg, lon_deg=0.0):
    """The point of the quadric on the ray from 0 in direction (lat, lon)."""
    lat, lon = np.radians(lat_deg), np.radians(lon_deg)
    d = np.array([np.cos(lat) * np.cos(lon), np.cos(lat) * np.sin(lon), np.sin(lat)])
    A = np.array([1.0, 1.0, sigma])
    return d / np.sqrt(d @ (A * d))


def fire(sigma, p, length, nrays=90, h=0.01, zmax=1.7):
    """Integrate nrays unit-speed geodesics from p, with the Jacobi equation along each."""
    A = np.array([1.0, 1.0, sigma])
    nrm = A * p
    nrm /= np.linalg.norm(nrm)
    e1 = np.cross([0.0, 0.0, 1.0], nrm)
    if np.linalg.norm(e1) < 1e-9:
        e1 = np.array([1.0, 0.0, 0.0])
    e1 /= np.linalg.norm(e1)
    e2 = np.cross(nrm, e1)
    ang = np.linspace(0, 2 * np.pi, nrays, endpoint=False)
    x = np.tile(p, (nrays, 1))
    v = np.outer(np.cos(ang), e1) + np.outer(np.sin(ang), e2)
    j = np.zeros(nrays)
    jd = np.ones(nrays)

    def deriv(x, v, j, jd):
        Ax = x * A
        acc = -((v * v * A).sum(1) / (Ax * Ax).sum(1))[:, None] * Ax
        K = sigma / ((x[:, 0] ** 2 + x[:, 1] ** 2 + sigma ** 2 * x[:, 2] ** 2) ** 2)
        return v, acc, jd, -K * j

    conj = np.full((nrays, 3), np.nan)
    conj_t = np.full(nrays, np.nan)
    alive = np.ones(nrays, bool)
    paths = [x.copy()]
    for k in range(int(length / h)):
        k1 = deriv(x, v, j, jd)
        k2 = deriv(*(s + h / 2 * d for s, d in zip((x, v, j, jd), k1)))
        k3 = deriv(*(s + h / 2 * d for s, d in zip((x, v, j, jd), k2)))
        k4 = deriv(*(s + h * d for s, d in zip((x, v, j, jd), k3)))
        new = [s + h / 6 * (a + 2 * b + 2 * c + d)
               for s, a, b, c, d in zip((x, v, j, jd), k1, k2, k3, k4)]
        xn, vn, jn, jdn = new
        xn = xn / np.sqrt((xn * xn * A).sum(1))[:, None]          # back onto the surface
        nn = xn * A
        nn /= np.linalg.norm(nn, axis=1)[:, None]
        vn = vn - (vn * nn).sum(1)[:, None] * nn                  # tangent, unit speed
        vn /= np.linalg.norm(vn, axis=1)[:, None]
        hit = (j > 0) & (jn <= 0) & np.isnan(conj_t) & alive & (k > 2)
        if hit.any():
            fr = j[hit] / (j[hit] - jn[hit])
            conj[hit] = x[hit] + fr[:, None] * (xn[hit] - x[hit])
            conj_t[hit] = (k + fr) * h
        x, v, j, jd = xn, vn, jn, jdn
        alive &= np.abs(x[:, 2]) < zmax
        paths.append(np.where(alive[:, None], x, np.nan))
    return np.array(paths), conj, conj_t


def camera(az_deg, el_deg):
    az, el = np.radians(az_deg), np.radians(el_deg)
    c = np.array([np.cos(el) * np.cos(az), np.cos(el) * np.sin(az), np.sin(el)])
    r = np.array([-np.sin(az), np.cos(az), 0.0])
    u = np.cross(c, r)
    return c, r, u


def visible(points, sigma, cam):
    """Front-facing test: outward normal has positive component towards the viewer."""
    A = np.array([1.0, 1.0, sigma])
    return (points * A) @ cam[0] > 0


def draw_polyline(ax, pts, sigma, cam, color, lw, alpha_front, alpha_back, z=3):
    c, r, u = cam
    X, Y = pts @ r, pts @ u
    vis = visible(pts, sigma, cam)
    for front, alpha in ((True, alpha_front), (False, alpha_back)):
        mask = vis if front else ~vis
        xs = np.where(mask, X, np.nan)
        ys = np.where(mask, Y, np.nan)
        ax.plot(xs, ys, color=color, lw=lw, alpha=alpha, zorder=z, solid_capstyle="round")


def wireframe(ax, sigma, cam, zmax):
    if sigma > 0:
        zt = 1 / np.sqrt(sigma)
        zs = np.linspace(-0.85 * zt, 0.85 * zt, 7)
    else:
        zs = np.linspace(-zmax, zmax, 7)
    t = np.linspace(0, 2 * np.pi, 361)
    for z0 in zs:
        rad = np.sqrt(1 - sigma * z0 ** 2)
        pts = np.stack([rad * np.cos(t), rad * np.sin(t), z0 + 0 * t], axis=1)
        draw_polyline(ax, pts, sigma, cam, MUTED, 0.5, 0.7, 0.18, z=1)
    for phi in np.radians(np.arange(0, 360, 30)):
        if sigma > 0:
            zt = 1 / np.sqrt(sigma)
            zz = np.linspace(-zt, zt, 300)
        else:
            zz = np.linspace(-zmax, zmax, 300)
        rad = np.sqrt(np.clip(1 - sigma * zz ** 2, 0, None))
        pts = np.stack([rad * np.cos(phi), rad * np.sin(phi), zz], axis=1)
        draw_polyline(ax, pts, sigma, cam, MUTED, 0.5, 0.7, 0.18, z=1)
    # silhouette (outline) of convex surfaces
    if sigma > 0:
        c, r, u = cam
        A = np.array([1.0, 1.0, sigma])
        # sample many surface points, keep those with normal nearly orthogonal to the view
        th = np.linspace(0, 2 * np.pi, 720)
        out = []
        for a in th:
            # direction in the screen plane; find the surface point whose normal is it
            w = np.cos(a) * r + np.sin(a) * u
            x = w / A
            x = x / np.sqrt(x @ (A * x))
            out.append([x @ r, x @ u])
        out = np.array(out)
        ax.plot(out[:, 0], out[:, 1], color=FG, lw=0.9, zorder=2)


def panel(ax, sigma, lat, length, cam, title, zmax=1.7):
    p = surface_point(sigma, lat)
    paths, conj, conj_t = fire(sigma, p, length, zmax=zmax)
    wireframe(ax, sigma, cam, zmax)
    for i in range(paths.shape[1]):
        draw_polyline(ax, paths[:, i, :], sigma, cam, ACCENT, 0.7, 0.75, 0.16, z=3)
    c, r, u = cam
    ok = np.isfinite(conj_t)
    if ok.any():
        cp = conj[ok]
        vis = visible(cp, sigma, cam)
        ax.scatter(cp[vis] @ r, cp[vis] @ u, s=9, color=FG, zorder=5, linewidths=0)
        ax.scatter(cp[~vis] @ r, cp[~vis] @ u, s=9, facecolors="none", edgecolors=MUTED,
                   linewidths=0.6, zorder=4)
    pv = visible(p[None, :], sigma, cam)[0]
    if pv:
        ax.scatter([p @ r], [p @ u], s=30, color=FG, edgecolors=BG, linewidths=0.8, zorder=6)
        ax.annotate(r"$p$", (p @ r, p @ u), xytext=(5, 4), textcoords="offset points",
                    fontsize=8, color=FG)
    nconj = int(ok.sum())
    if nconj:
        msg = (f"{nconj} of {paths.shape[1]} rays reach a conjugate point,\n"
               f"the first at distance {np.nanmin(conj_t):.2f} to {np.nanmax(conj_t):.2f}")
    else:
        msg = f"none of {paths.shape[1]} rays reaches a conjugate point"
    ax.text(0.5, -0.02, msg, transform=ax.transAxes, ha="center", va="top", fontsize=6.6,
            color=FG)
    ax.set_title(title, fontsize=8.3, color=FG)
    ax.set_aspect("equal")
    ax.axis("off")


def main():
    fig, axes = plt.subplots(1, 3, figsize=(7.0, 3.1), dpi=150)
    panel(axes[0], -0.6, 12, 4.4, camera(20, 18),
          "(a) hyperboloid, $\\sigma = -0.6$, $K<0$:\nrays cross, but never refocus", zmax=1.6)
    panel(axes[1], 1.0, 30, 3.9, camera(180, -18),
          "(b) sphere, $\\sigma = 1$, viewed from\nopposite $p$: all rays meet at $p'$")
    panel(axes[2], 2.5, 30, 3.9, camera(180, -24),
          "(c) spheroid, $\\sigma = 2.5$, viewed from\nopposite $p$: a caustic curve")
    for ax in axes[1:]:
        ax.set_xlim(-1.08, 1.08)
        ax.set_ylim(-1.12, 1.12)
    fig.text(0.5, 0.012,
             r"Surface $x^2+y^2+\sigma z^2=1$; 90 geodesics from $p$ (blue; faint = far side); "
             r"dots: first conjugate points (zeros of $j''+Kj=0$, $j(0)=0$, $j'(0)=1$)",
             ha="center", fontsize=6.8, color=FG)
    fig.subplots_adjust(left=0.01, right=0.99, top=0.86, bottom=0.12, wspace=0.06)
    fig.savefig("fig11-caustic.png", dpi=150, facecolor=BG)


if __name__ == "__main__":
    main()
