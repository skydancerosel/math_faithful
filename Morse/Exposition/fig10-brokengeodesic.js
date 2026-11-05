/*
 * Interactive figure for Chapter 10 (Milnor, Morse Theory, Sections 16-17).
 *
 * Broken geodesics on the unit sphere with one break point x = omega(1/2).  Their energy is
 *     E'(x) = 2 rho(p,x)^2 + 2 rho(x,q)^2,
 * defined on B = {E' < 2 pi^2}.  The shaded set is the sublevel set B^a.  Drag to rotate the
 * globe, click (or tap) to move the break point x, and use the sliders to change the angle theta
 * between p and q and the energy level a.  Plain JavaScript, no libraries.
 * Colours come from the CSS variables --fg, --bg, --accent, --muted (with fallbacks).
 */
(function () {
  "use strict";

  var ID = "brokengeodesic-figure";
  var PI = Math.PI;
  var PI2 = PI * PI;

  function clamp(v, lo, hi) { return v < lo ? lo : (v > hi ? hi : v); }
  function dot(a, b) { return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]; }
  function cross(a, b) {
    return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
  }
  function norm(a) { return Math.sqrt(dot(a, a)); }
  function scale(a, s) { return [a[0] * s, a[1] * s, a[2] * s]; }
  function add(a, b) { return [a[0] + b[0], a[1] + b[1], a[2] + b[2]]; }
  function unit(a) { return scale(a, 1 / norm(a)); }

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
    function mix(c1, c2, t) {
      return [c1[0] + (c2[0] - c1[0]) * t, c1[1] + (c2[1] - c1[1]) * t, c1[2] + (c2[2] - c1[2]) * t];
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
      "Unit sphere with points p and q, the sublevel set B^a of the energy of broken geodesics " +
      "with one break point, and a broken geodesic p to x to q.");
    canvas.style.display = "block";
    canvas.style.margin = "0 auto";
    canvas.style.touchAction = "none";
    canvas.style.cursor = "grab";
    root.appendChild(canvas);

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
    var sTheta = makeSlider("angle &theta; between p and q", 20, 175, 1, 120);
    var sLevel = makeSlider("energy level a (in units of &pi;<sup>2</sup>)", 0, 1.995, 0.005, 1.89);

    var info = document.createElement("div");
    info.style.marginTop = "0.6em";
    root.appendChild(info);

    /* ---------- state ---------- */
    var yaw = PI;            // camera longitude: start looking at the back, centred at m1
    var pitch = 0.3;         // camera latitude
    var xPt = unit([-0.45, 0.35, 0.82]);
    var size = 360, dpr = 1, internal = 360;

    function theta() { return parseFloat(sTheta.input.value) * PI / 180; }
    function level() { return parseFloat(sLevel.input.value); }
    function pPt() { var t = theta(); return [Math.cos(-t / 2), Math.sin(-t / 2), 0]; }
    function qPt() { var t = theta(); return [Math.cos(t / 2), Math.sin(t / 2), 0]; }

    function energy(x, p, q) {
      var rp = Math.acos(clamp(dot(x, p), -1, 1));
      var rq = Math.acos(clamp(dot(x, q), -1, 1));
      return 2 * (rp * rp + rq * rq) / PI2;
    }

    function frame() {
      var cp = Math.cos(pitch), sp = Math.sin(pitch), cy = Math.cos(yaw), sy = Math.sin(yaw);
      return {
        c: [cp * cy, cp * sy, sp],
        r: [-sy, cy, 0],
        u: [-sp * cy, -sp * sy, cp]
      };
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

    /* ---------- drawing ---------- */
    var ctx = canvas.getContext("2d");

    function render(coarse) {
      readColours();
      var p = pPt(), q = qPt(), a = level();
      var F = frame();
      var N = internal;
      var R = N / 2 - 2 * dpr;
      var cx = N / 2, cy = N / 2;
      var step = coarse ? 3 : 1;
      var n = Math.ceil(N / step);
      var E = new Float32Array(n * n);
      var i, j, k;
      for (j = 0; j < n; j++) {
        for (i = 0; i < n; i++) {
          k = j * n + i;
          var X = (i * step + step / 2 - cx) / R;
          var Y = (cy - (j * step + step / 2)) / R;
          var r2 = X * X + Y * Y;
          if (r2 > 1) { E[k] = NaN; continue; }
          var Z = Math.sqrt(1 - r2);
          var x = [X * F.r[0] + Y * F.u[0] + Z * F.c[0],
                   X * F.r[1] + Y * F.u[1] + Z * F.c[1],
                   X * F.r[2] + Y * F.u[2] + Z * F.c[2]];
          E[k] = energy(x, p, q);
        }
      }
      var img = ctx.createImageData(N, N);
      var d = img.data;
      var cIn = mix(COL.bg, COL.accent, 0.33);
      var cOut = mix(COL.bg, COL.muted, 0.38);
      for (j = 0; j < n; j++) {
        for (i = 0; i < n; i++) {
          k = j * n + i;
          var e = E[k];
          var col, alpha = 255;
          if (e !== e) {
            col = COL.bg; alpha = 0;
          } else {
            col = e >= 2 ? cOut : (e <= a ? cIn : COL.bg);
            var band = e < 2 ? Math.floor(e / 0.25) : 99;
            var nb = [];
            if (i + 1 < n) { nb.push(E[k + 1]); }
            if (j + 1 < n) { nb.push(E[k + n]); }
            for (var m = 0; m < nb.length; m++) {
              var f = nb[m];
              if (f !== f) { continue; }
              if ((f < 2 ? Math.floor(f / 0.25) : 99) !== band) { col = mix(col, COL.muted, 0.6); }
              if ((f - a) * (e - a) < 0) { col = COL.accent; }
            }
          }
          for (var yy = j * step; yy < Math.min(N, (j + 1) * step); yy++) {
            for (var xx = i * step; xx < Math.min(N, (i + 1) * step); xx++) {
              var o = 4 * (yy * N + xx);
              d[o] = col[0]; d[o + 1] = col[1]; d[o + 2] = col[2]; d[o + 3] = alpha;
            }
          }
        }
      }
      ctx.clearRect(0, 0, N, N);
      ctx.putImageData(img, 0, 0);

      function proj(x) { return [cx + R * dot(x, F.r), cy - R * dot(x, F.u), dot(x, F.c)]; }

      function arc(a0, b0, longway) {
        var A = unit(a0), Bv = unit(b0);
        var ang = Math.acos(clamp(dot(A, Bv), -1, 1));
        var ax = cross(A, Bv);
        if (norm(ax) < 1e-9) { ax = [0, 0, 1]; }
        ax = unit(ax);
        if (longway) { ang = ang - 2 * PI; }
        var perp = cross(ax, A), pts = [], m = 180;
        for (var s = 0; s <= m; s++) {
          var t = ang * s / m;
          pts.push(add(scale(A, Math.cos(t)), scale(perp, Math.sin(t))));
        }
        return pts;
      }

      function polyline(pts, colour, width, dash) {
        ctx.lineWidth = width * dpr;
        ctx.setLineDash(dash ? dash.map(function (v) { return v * dpr; }) : []);
        for (var pass = 0; pass < 2; pass++) {
          ctx.beginPath();
          var started = false;
          for (var s = 0; s < pts.length; s++) {
            var P = proj(pts[s]);
            var front = P[2] >= 0;
            if ((pass === 0) === front) { started = false; continue; }
            if (!started) { ctx.moveTo(P[0], P[1]); started = true; } else { ctx.lineTo(P[0], P[1]); }
          }
          ctx.strokeStyle = css(colour, pass === 0 ? 0.22 : 1);
          ctx.stroke();
        }
        ctx.setLineDash([]);
      }

      function point(x, label, marker, colour) {
        var P = proj(x);
        var front = P[2] >= 0;
        ctx.globalAlpha = front ? 1 : 0.25;
        ctx.fillStyle = css(colour || COL.fg);
        ctx.strokeStyle = css(COL.bg);
        ctx.lineWidth = 1.5 * dpr;
        var s = 4.2 * dpr;
        ctx.beginPath();
        if (marker === "square") { ctx.rect(P[0] - s, P[1] - s, 2 * s, 2 * s); }
        else if (marker === "cross") {
          ctx.moveTo(P[0] - s, P[1] - s); ctx.lineTo(P[0] + s, P[1] + s);
          ctx.moveTo(P[0] + s, P[1] - s); ctx.lineTo(P[0] - s, P[1] + s);
          ctx.strokeStyle = css(colour || COL.fg); ctx.lineWidth = 2.4 * dpr; ctx.stroke();
          ctx.globalAlpha = 1;
          if (front && label) { text(label, P); }
          return;
        } else { ctx.arc(P[0], P[1], s, 0, 2 * PI); }
        ctx.fill(); ctx.stroke();
        ctx.globalAlpha = 1;
        if (front && label) { text(label, P); }
      }
      function text(label, P) {
        ctx.font = (13 * dpr) + "px system-ui, sans-serif";
        ctx.fillStyle = css(COL.fg);
        ctx.strokeStyle = css(COL.bg, 0.85);
        ctx.lineWidth = 3 * dpr;
        var tx = P[0] + 7 * dpr, ty = P[1] - 7 * dpr;
        if (tx > N - 34 * dpr) { tx = P[0] - 30 * dpr; }
        ctx.strokeText(label, tx, ty);
        ctx.fillText(label, tx, ty);
      }

      // the great circle C through p and q, the two geodesics gamma_0 and gamma_1
      var eq = [];
      for (var s2 = 0; s2 <= 240; s2++) {
        var t2 = 2 * PI * s2 / 240;
        eq.push([Math.cos(t2), Math.sin(t2), 0]);
      }
      polyline(eq, COL.muted, 0.8, null);
      polyline(arc(p, q, false), COL.fg, 2.2, null);
      polyline(arc(p, q, true), COL.fg, 1.4, [6, 4]);
      // the broken geodesic p -> x -> q
      polyline(arc(p, xPt, false), COL.accent, 2.4, null);
      polyline(arc(xPt, q, false), COL.accent, 2.4, null);

      ctx.beginPath();
      ctx.arc(cx, cy, R, 0, 2 * PI);
      ctx.strokeStyle = css(COL.fg, 0.9);
      ctx.lineWidth = 1.2 * dpr;
      ctx.stroke();

      point(p, "p"); point(q, "q");
      point(scale(p, -1), "p′"); point(scale(q, -1), "q′");
      point([1, 0, 0], "m₀", "square");
      point([-1, 0, 0], "m₁", "cross");
      point(xPt, "x", "dot", COL.accent);

      // readout
      var th = theta();
      var e0 = th * th / PI2, e1 = (2 * PI - th) * (2 * PI - th) / PI2;
      var ex = energy(xPt, p, q);
      sTheta.out.textContent = Math.round(th * 180 / PI) + "°";
      sLevel.out.textContent = a.toFixed(3) + " π²";
      var state;
      if (a < e0) { state = "B<sup>a</sup> is empty."; }
      else if (e1 >= 2 || a < e1) {
        state = "B<sup>a</sup> is a disc: one 0-cell, from γ<sub>0</sub>.";
      } else {
        state = "B<sup>a</sup> is an annulus, a circle up to homotopy: a 0-cell from " +
          "γ<sub>0</sub> and a 1-cell from γ<sub>1</sub>.";
      }
      var saddle = e1 < 2
        ? "saddle m<sub>1</sub>, E(γ<sub>1</sub>) = " + e1.toFixed(2) + " π², index 1"
        : "E(γ<sub>1</sub>) = " + e1.toFixed(2) + " π² ≥ 2π²: the saddle " +
          "is outside B, so one break point cannot see γ<sub>1</sub>";
      info.innerHTML =
        "minimum m<sub>0</sub>, E(γ<sub>0</sub>) = " + e0.toFixed(2) + " π²; " + saddle +
        ".<br>" + state +
        "<br>Break point x: E′(x) = " + (ex < 2 ? ex.toFixed(2) + " π²" :
          ex.toFixed(2) + " π² (outside B)") + ". Drag to turn the globe; click to move x.";
      info.style.color = css(COL.fg);
    }

    var pending = false, pendingCoarse = false;
    function schedule(coarse) {
      pendingCoarse = coarse;
      if (pending) { return; }
      pending = true;
      window.requestAnimationFrame(function () {
        pending = false;
        render(pendingCoarse);
      });
    }

    /* ---------- interaction ---------- */
    var drag = null;
    canvas.addEventListener("pointerdown", function (ev) {
      drag = { x: ev.clientX, y: ev.clientY, yaw0: yaw, pitch0: pitch, moved: false };
      try { canvas.setPointerCapture(ev.pointerId); } catch (e) { /* ignore */ }
      canvas.style.cursor = "grabbing";
    });
    canvas.addEventListener("pointermove", function (ev) {
      if (!drag) { return; }
      var dx = ev.clientX - drag.x, dy = ev.clientY - drag.y;
      if (Math.abs(dx) + Math.abs(dy) > 4) { drag.moved = true; }
      if (drag.moved) {
        yaw = drag.yaw0 - dx * 0.012;
        pitch = clamp(drag.pitch0 + dy * 0.012, -1.45, 1.45);
        schedule(true);
      }
    });
    function finish(ev) {
      if (drag && !drag.moved) {
        var rect = canvas.getBoundingClientRect();
        var X = ((ev.clientX - rect.left) / rect.width) * 2 - 1;
        var Y = 1 - ((ev.clientY - rect.top) / rect.height) * 2;
        var Rn = (internal / 2 - 2 * dpr) / (internal / 2);
        X /= Rn; Y /= Rn;
        var r2 = X * X + Y * Y;
        if (r2 < 1) {
          var F = frame(), Z = Math.sqrt(1 - r2);
          xPt = unit(add(add(scale(F.r, X), scale(F.u, Y)), scale(F.c, Z)));
        }
      }
      drag = null;
      canvas.style.cursor = "grab";
      schedule(false);
    }
    canvas.addEventListener("pointerup", finish);
    canvas.addEventListener("pointercancel", function () { drag = null; schedule(false); });
    sTheta.input.addEventListener("input", function () { schedule(false); });
    sLevel.input.addEventListener("input", function () { schedule(false); });
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
    render(false);
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }
})();
