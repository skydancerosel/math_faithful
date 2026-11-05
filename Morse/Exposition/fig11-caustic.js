/*
 * Interactive figure for Chapter 11 (Milnor, Morse Theory, Sections 18-19).
 *
 * Geodesics fired from a point p of the quadric  x^2 + y^2 + sigma z^2 = 1, with the first
 * conjugate point on each.  The geodesic equation  x'' = -(x'.Ax'/|Ax|^2) Ax,  A = diag(1,1,sigma),
 * is integrated in R^3 together with the Jacobi equation  j'' + K j = 0, j(0) = 0, j'(0) = 1,
 * where K = sigma / (x^2 + y^2 + sigma^2 z^2)^2 is the Gaussian curvature.  A conjugate point is a
 * zero of j.  Sliders: the shape sigma, the position of p, the length of the rays.  Drag to turn.
 * Plain JavaScript, no libraries.  Colours from the CSS variables --fg, --bg, --accent, --muted.
 */
(function () {
  "use strict";

  var ID = "caustic-figure";
  var PI = Math.PI;
  var NRAYS = 72;
  var H = 0.01;          // integration step (arc length)
  var ZMAX = 1.6;        // truncation height for the hyperboloid and the cylinder

  function clamp(v, lo, hi) { return v < lo ? lo : (v > hi ? hi : v); }

  function init() {
    var root = document.getElementById(ID);
    if (!root || root.getAttribute("data-ready")) { return; }
    root.setAttribute("data-ready", "1");

    var dark = window.matchMedia && window.matchMedia("(prefers-color-scheme: dark)").matches;
    var FALLBACK = dark
      ? { fg: "#f2f2f0", bg: "#1a1a19", accent: "#3987e5", muted: "#9a9992" }
      : { fg: "#111111", bg: "#ffffff", accent: "#2a78d6", muted: "#8a8984" };
    var probe = document.createElement("canvas");
    probe.width = 1; probe.height = 1;
    var pctx = probe.getContext("2d");
    function rgbOf(name, fallback) {
      var v = "";
      try { v = getComputedStyle(root).getPropertyValue(name).trim(); } catch (e) { v = ""; }
      pctx.clearRect(0, 0, 1, 1);
      pctx.fillStyle = fallback;
      if (v) { pctx.fillStyle = v; }
      pctx.fillRect(0, 0, 1, 1);
      var d = pctx.getImageData(0, 0, 1, 1).data;
      return [d[0], d[1], d[2]];
    }
    function css(c, a) {
      return "rgba(" + c[0] + "," + c[1] + "," + c[2] + "," + (a === undefined ? 1 : a) + ")";
    }
    var COL = {};
    function readColours() {
      COL.fg = rgbOf("--fg", FALLBACK.fg);
      COL.bg = rgbOf("--bg", FALLBACK.bg);
      COL.accent = rgbOf("--accent", FALLBACK.accent);
      COL.muted = rgbOf("--muted", FALLBACK.muted);
    }

    /* ---------- DOM ---------- */
    root.style.maxWidth = "460px";
    root.style.margin = "1em auto";
    root.style.fontFamily = "system-ui, -apple-system, Segoe UI, Roboto, sans-serif";
    root.style.fontSize = "14px";
    root.style.lineHeight = "1.35";

    var canvas = document.createElement("canvas");
    canvas.setAttribute("role", "img");
    canvas.setAttribute("aria-label",
      "Geodesics fired from a point of a quadric surface, with their first conjugate points.");
    canvas.style.display = "block";
    canvas.style.margin = "0 auto";
    canvas.style.touchAction = "none";
    canvas.style.cursor = "grab";
    root.appendChild(canvas);

    var buttons = document.createElement("div");
    buttons.style.textAlign = "center";
    buttons.style.margin = "0.4em 0 0";
    root.appendChild(buttons);
    function makeButton(label, onClick) {
      var b = document.createElement("button");
      b.type = "button";
      b.textContent = label;
      b.style.margin = "0 0.3em";
      b.style.font = "inherit";
      b.addEventListener("click", onClick);
      buttons.appendChild(b);
      return b;
    }

    function makeSlider(labelHtml, min, max, step, value) {
      var wrap = document.createElement("label");
      wrap.style.display = "block";
      wrap.style.margin = "0.5em 0 0";
      var text = document.createElement("span");
      text.innerHTML = labelHtml;
      var out = document.createElement("span");
      out.style.float = "right";
      out.style.fontVariantNumeric = "tabular-nums";
      var input = document.createElement("input");
      input.type = "range";
      input.min = String(min); input.max = String(max); input.step = String(step);
      input.value = String(value);
      input.style.width = "100%";
      input.style.display = "block";
      wrap.appendChild(text);
      wrap.appendChild(out);
      wrap.appendChild(input);
      root.appendChild(wrap);
      return { input: input, out: out };
    }
    var sShape = makeSlider("shape &sigma; in x<sup>2</sup> + y<sup>2</sup> + &sigma;z<sup>2</sup> = 1",
      -1, 2.5, 0.05, 2.5);
    var sPos = makeSlider("position of p (height along a meridian)", -0.8, 0.8, 0.02, 0.45);
    var sLen = makeSlider("length of the rays", 0.5, 4.5, 0.05, 3.9);

    var info = document.createElement("div");
    info.style.marginTop = "0.6em";
    root.appendChild(info);

    /* ---------- geometry ---------- */
    var yaw = PI, pitch = -0.35;
    var size = 360, dpr = 1, internal = 360;
    var rays = null;     // computed geodesics

    function sigma() { return parseFloat(sShape.input.value); }
    function zExtent(s) { return s > 1e-6 ? 1 / Math.sqrt(s) : ZMAX; }
    function startPoint(s) {
      var f = parseFloat(sPos.input.value);
      var z0 = f * (s > 1e-6 ? 1 / Math.sqrt(s) : 1.0);
      var rad = Math.sqrt(Math.max(1 - s * z0 * z0, 1e-6));
      return [rad, 0, z0];
    }
    function curvature(s, x) {
      var d = x[0] * x[0] + x[1] * x[1] + s * s * x[2] * x[2];
      return s / (d * d);
    }

    function fire() {
      var s = sigma(), L = parseFloat(sLen.input.value);
      var A = [1, 1, s];
      var p = startPoint(s);
      var nrm = [p[0], p[1], s * p[2]];
      var nn = Math.sqrt(nrm[0] * nrm[0] + nrm[1] * nrm[1] + nrm[2] * nrm[2]);
      nrm = [nrm[0] / nn, nrm[1] / nn, nrm[2] / nn];
      var e1 = [-nrm[1], nrm[0], 0];          // z-axis cross normal: horizontal tangent
      var l1 = Math.sqrt(e1[0] * e1[0] + e1[1] * e1[1]);
      if (l1 < 1e-9) { e1 = [1, 0, 0]; l1 = 1; }
      e1 = [e1[0] / l1, e1[1] / l1, 0];
      var e2 = [nrm[1] * e1[2] - nrm[2] * e1[1], nrm[2] * e1[0] - nrm[0] * e1[2],
                nrm[0] * e1[1] - nrm[1] * e1[0]];
      var steps = Math.round(L / H);
      var out = { p: p, s: s, paths: [], conj: [], conjT: [] };

      function deriv(st) {
        // st = [x0,x1,x2,v0,v1,v2,j,jd]
        var ax0 = st[0], ax1 = st[1], ax2 = s * st[2];
        var vAv = st[3] * st[3] + st[4] * st[4] + s * st[5] * st[5];
        var den = ax0 * ax0 + ax1 * ax1 + ax2 * ax2;
        var c = -vAv / den;
        var K = curvature(s, st);
        return [st[3], st[4], st[5], c * ax0, c * ax1, c * ax2, st[7], -K * st[6]];
      }
      function addScaled(a, b, h) {
        var r = new Array(8);
        for (var i = 0; i < 8; i++) { r[i] = a[i] + h * b[i]; }
        return r;
      }
      for (var k = 0; k < NRAYS; k++) {
        var ang = 2 * PI * k / NRAYS;
        var ca = Math.cos(ang), sa = Math.sin(ang);
        var st = [p[0], p[1], p[2],
                  ca * e1[0] + sa * e2[0], ca * e1[1] + sa * e2[1], ca * e1[2] + sa * e2[2], 0, 1];
        var path = [[st[0], st[1], st[2]]];
        var conj = null, conjT = null;
        for (var n = 0; n < steps; n++) {
          var k1 = deriv(st);
          var k2 = deriv(addScaled(st, k1, H / 2));
          var k3 = deriv(addScaled(st, k2, H / 2));
          var k4 = deriv(addScaled(st, k3, H));
          var nx = new Array(8);
          for (var i = 0; i < 8; i++) {
            nx[i] = st[i] + H / 6 * (k1[i] + 2 * k2[i] + 2 * k3[i] + k4[i]);
          }
          // back onto the surface, tangent unit velocity
          var q = nx[0] * nx[0] + nx[1] * nx[1] + s * nx[2] * nx[2];
          if (!(q > 0)) { break; }
          var sq = Math.sqrt(q);
          nx[0] /= sq; nx[1] /= sq; nx[2] /= sq;
          var g0 = nx[0], g1 = nx[1], g2 = s * nx[2];
          var gl = Math.sqrt(g0 * g0 + g1 * g1 + g2 * g2);
          g0 /= gl; g1 /= gl; g2 /= gl;
          var vn = nx[3] * g0 + nx[4] * g1 + nx[5] * g2;
          nx[3] -= vn * g0; nx[4] -= vn * g1; nx[5] -= vn * g2;
          var vl = Math.sqrt(nx[3] * nx[3] + nx[4] * nx[4] + nx[5] * nx[5]);
          nx[3] /= vl; nx[4] /= vl; nx[5] /= vl;
          if (conj === null && n > 2 && st[6] > 0 && nx[6] <= 0) {
            var fr = st[6] / (st[6] - nx[6]);
            conj = [st[0] + fr * (nx[0] - st[0]), st[1] + fr * (nx[1] - st[1]),
                    st[2] + fr * (nx[2] - st[2])];
            conjT = (n + fr) * H;
          }
          st = nx;
          if (s <= 1e-6 && Math.abs(st[2]) > ZMAX) { break; }
          if (n % 2 === 1) { path.push([st[0], st[1], st[2]]); }
        }
        out.paths.push(path);
        out.conj.push(conj);
        out.conjT.push(conjT);
      }
      return out;
    }

    function frame() {
      var cp = Math.cos(pitch), sp = Math.sin(pitch), cy = Math.cos(yaw), sy = Math.sin(yaw);
      return { c: [cp * cy, cp * sy, sp], r: [-sy, cy, 0], u: [-sp * cy, -sp * sy, cp] };
    }

    function resize() {
      var w = root.clientWidth || 360;
      size = Math.max(240, Math.min(w, 440));
      dpr = Math.min(window.devicePixelRatio || 1, 2);
      internal = Math.round(size * dpr);
      canvas.width = internal;
      canvas.height = internal;
      canvas.style.width = size + "px";
      canvas.style.height = size + "px";
    }

    var ctx = canvas.getContext("2d");

    function render() {
      readColours();
      var s = rays.s;
      var F = frame();
      var N = internal;
      ctx.fillStyle = css(COL.bg);
      ctx.fillRect(0, 0, N, N);
      var zext = zExtent(s);
      // radius of the smallest ball about 0 containing the drawn part of the surface
      var ext = s > 1e-6 ? Math.max(1, zext)
        : Math.sqrt(1 - s * ZMAX * ZMAX + ZMAX * ZMAX);
      ext *= 1.04;
      var R = (N / 2 - 6 * dpr) / ext;
      var cx = N / 2, cy = N / 2;
      function proj(x) {
        return [cx + R * (x[0] * F.r[0] + x[1] * F.r[1] + x[2] * F.r[2]),
                cy - R * (x[0] * F.u[0] + x[1] * F.u[1] + x[2] * F.u[2])];
      }
      function front(x) {
        // outward normal (x, y, sigma z) facing the viewer
        return x[0] * F.c[0] + x[1] * F.c[1] + s * x[2] * F.c[2] > 0;
      }
      function polyline(pts, colour, width, aFront, aBack) {
        ctx.lineWidth = width * dpr;
        for (var pass = 0; pass < 2; pass++) {
          var want = pass === 1;
          ctx.beginPath();
          var started = false;
          for (var i = 0; i < pts.length; i++) {
            if (front(pts[i]) !== want) { started = false; continue; }
            var P = proj(pts[i]);
            if (!started) { ctx.moveTo(P[0], P[1]); started = true; } else { ctx.lineTo(P[0], P[1]); }
          }
          ctx.strokeStyle = css(colour, want ? aFront : aBack);
          ctx.stroke();
        }
      }
      // wireframe
      var zs = [], m, t, i;
      var zt = s > 1e-6 ? 0.85 * zext : ZMAX;
      for (m = 0; m < 7; m++) { zs.push(-zt + 2 * zt * m / 6); }
      for (m = 0; m < zs.length; m++) {
        var rad = Math.sqrt(Math.max(1 - s * zs[m] * zs[m], 0));
        var ring = [];
        for (i = 0; i <= 144; i++) {
          t = 2 * PI * i / 144;
          ring.push([rad * Math.cos(t), rad * Math.sin(t), zs[m]]);
        }
        polyline(ring, COL.muted, 0.8, 0.7, 0.15);
      }
      var zTop = s > 1e-6 ? zext : ZMAX;
      for (m = 0; m < 12; m++) {
        var phi = 2 * PI * m / 12, mer = [];
        for (i = 0; i <= 120; i++) {
          var zz = -zTop + 2 * zTop * i / 120;
          var rr = Math.sqrt(Math.max(1 - s * zz * zz, 0));
          mer.push([rr * Math.cos(phi), rr * Math.sin(phi), zz]);
        }
        polyline(mer, COL.muted, 0.8, 0.7, 0.15);
      }
      // silhouette of a convex surface: the points whose normal lies in the screen plane
      if (s > 1e-6) {
        ctx.beginPath();
        for (i = 0; i <= 360; i++) {
          t = 2 * PI * i / 360;
          var w = [Math.cos(t) * F.r[0] + Math.sin(t) * F.u[0], Math.cos(t) * F.r[1] + Math.sin(t) * F.u[1],
                   Math.cos(t) * F.r[2] + Math.sin(t) * F.u[2]];
          var x = [w[0], w[1], w[2] / s];
          var qq = Math.sqrt(x[0] * x[0] + x[1] * x[1] + s * x[2] * x[2]);
          x = [x[0] / qq, x[1] / qq, x[2] / qq];
          var P = proj(x);
          if (i === 0) { ctx.moveTo(P[0], P[1]); } else { ctx.lineTo(P[0], P[1]); }
        }
        ctx.strokeStyle = css(COL.fg, 0.9);
        ctx.lineWidth = 1.2 * dpr;
        ctx.stroke();
      }
      // rays
      for (i = 0; i < rays.paths.length; i++) {
        polyline(rays.paths[i], COL.accent, 1.0, 0.8, 0.15);
      }
      // conjugate points
      var count = 0, tmin = Infinity, tmax = -Infinity;
      for (i = 0; i < rays.conj.length; i++) {
        var c = rays.conj[i];
        if (!c) { continue; }
        count++;
        tmin = Math.min(tmin, rays.conjT[i]); tmax = Math.max(tmax, rays.conjT[i]);
        var Q = proj(c), fr = front(c);
        ctx.beginPath();
        ctx.arc(Q[0], Q[1], 2.6 * dpr, 0, 2 * PI);
        if (fr) { ctx.fillStyle = css(COL.fg); ctx.fill(); }
        else { ctx.strokeStyle = css(COL.muted, 0.8); ctx.lineWidth = 1 * dpr; ctx.stroke(); }
      }
      // the point p
      var pp = rays.p;
      if (front(pp)) {
        var Pp = proj(pp);
        ctx.beginPath();
        ctx.arc(Pp[0], Pp[1], 4.5 * dpr, 0, 2 * PI);
        ctx.fillStyle = css(COL.fg);
        ctx.fill();
        ctx.strokeStyle = css(COL.bg);
        ctx.lineWidth = 1.5 * dpr;
        ctx.stroke();
        ctx.font = (13 * dpr) + "px system-ui, sans-serif";
        ctx.lineWidth = 3 * dpr;
        ctx.strokeStyle = css(COL.bg, 0.85);
        ctx.strokeText("p", Pp[0] + 7 * dpr, Pp[1] - 7 * dpr);
        ctx.fillStyle = css(COL.fg);
        ctx.fillText("p", Pp[0] + 7 * dpr, Pp[1] - 7 * dpr);
      }

      // readout
      sShape.out.textContent = s.toFixed(2);
      sPos.out.textContent = "z = " + pp[2].toFixed(2);
      sLen.out.textContent = parseFloat(sLen.input.value).toFixed(2);
      var kind;
      if (s < -1e-6) { kind = "hyperboloid of one sheet, K &lt; 0"; }
      else if (s <= 1e-6) { kind = "cylinder, K = 0"; }
      else if (s < 1 - 1e-6) { kind = "prolate spheroid, K &gt; 0"; }
      else if (s <= 1 + 1e-6) { kind = "round sphere, K = 1"; }
      else { kind = "oblate spheroid, K &gt; 0"; }
      var Kp = curvature(s, pp);
      var lines = [kind + "; curvature at p: K = " + Kp.toFixed(3) + "."];
      if (count === 0) {
        lines.push(s <= 1e-6
          ? "No ray reaches a conjugate point, however long: Lemma 19.1. Rays that wind round " +
            "the surface cross each other without refocusing."
          : "No conjugate point yet: lengthen the rays.");
      } else {
        lines.push(count + " of " + NRAYS + " rays reach a conjugate point (dots), the first at " +
          "distance " + tmin.toFixed(2) + (tmax - tmin > 0.005 ? " to " + tmax.toFixed(2) : "") + ".");
        if (s > 1e-6) {
          var kmin = Math.min(s, 1 / s);
          lines.push("Myers (19.4): every geodesic longer than &pi;/&radic;(min K) = " +
            (PI / Math.sqrt(kmin)).toFixed(2) + " contains a conjugate point.");
        }
        if (Math.abs(s - 1) < 1e-6) {
          lines.push("On the sphere the whole fan refocuses at the antipode: the caustic is one point.");
        } else if (s > 1e-6) {
          lines.push("The dots trace the caustic, the critical values of exp<sub>p</sub>: a curve, " +
            "of measure zero (Corollary 18.2).");
        }
      }
      lines.push("Drag to turn the surface.");
      info.innerHTML = lines.join("<br>");
      info.style.color = css(COL.fg);
    }

    var pending = false, needFire = false;
    function schedule(refire) {
      if (refire) { needFire = true; }
      if (pending) { return; }
      pending = true;
      window.requestAnimationFrame(function () {
        pending = false;
        if (needFire || !rays) { rays = fire(); needFire = false; }
        render();
      });
    }

    /* ---------- interaction ---------- */
    var drag = null;
    canvas.addEventListener("pointerdown", function (ev) {
      drag = { x: ev.clientX, y: ev.clientY, yaw0: yaw, pitch0: pitch };
      try { canvas.setPointerCapture(ev.pointerId); } catch (e) { /* ignore */ }
      canvas.style.cursor = "grabbing";
    });
    canvas.addEventListener("pointermove", function (ev) {
      if (!drag) { return; }
      yaw = drag.yaw0 - (ev.clientX - drag.x) * 0.012;
      pitch = clamp(drag.pitch0 + (ev.clientY - drag.y) * 0.012, -1.45, 1.45);
      schedule(false);
    });
    function endDrag() { drag = null; canvas.style.cursor = "grab"; }
    canvas.addEventListener("pointerup", endDrag);
    canvas.addEventListener("pointercancel", endDrag);
    makeButton("look at p", function () {
      var p = startPoint(sigma());
      yaw = Math.atan2(p[1], p[0]);
      pitch = clamp(Math.atan2(sigma() * p[2], Math.sqrt(p[0] * p[0] + p[1] * p[1])), -1.2, 1.2);
      schedule(false);
    });
    makeButton("look at the far side", function () {
      var p = startPoint(sigma());
      yaw = Math.atan2(p[1], p[0]) + PI;
      pitch = clamp(-Math.atan2(sigma() * p[2], Math.sqrt(p[0] * p[0] + p[1] * p[1])), -1.2, 1.2);
      schedule(false);
    });
    sShape.input.addEventListener("input", function () { schedule(true); });
    sPos.input.addEventListener("input", function () { schedule(true); });
    sLen.input.addEventListener("input", function () { schedule(true); });
    window.addEventListener("resize", function () { resize(); schedule(false); });
    if (window.matchMedia) {
      var mq = window.matchMedia("(prefers-color-scheme: dark)");
      var onScheme = function () { schedule(false); };
      if (mq.addEventListener) { mq.addEventListener("change", onScheme); }
      else if (mq.addListener) { mq.addListener(onScheme); }
    }

    if (window.MutationObserver) {
      // the web edition switches themes through attributes on <html>
      new MutationObserver(function () { schedule(false); }).observe(document.documentElement,
        { attributes: true, attributeFilter: ["data-theme", "class", "style"] });
    }

    resize();
    rays = fire();
    render();
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }
})();
