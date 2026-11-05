/* Figure for Chapter 8: the second variation of the energy along a great-circle route.
   Plain JavaScript, no libraries.  Finds <div id="variation-figure"> and draws two canvases:
   a globe with the route gamma (angle theta along the equator, from p = (1,0,0)) and the varied
   route alpha(u, t) = exp_{gamma(t)}(u sin(k pi t) N), i.e. the point at latitude u sin(k pi t)
   and longitude theta t; and the graph of E(alpha(u)) - E(gamma) against u, with the parabola
   (k^2 pi^2 - theta^2) u^2 / 2 of the second variation formula.  Sliders set theta, u and k;
   dragging the globe turns it.  Colours come from the CSS variables --fg, --bg, --accent, --muted
   (with fallbacks). */
(function () {
  "use strict";
  var root = document.getElementById("variation-figure");
  if (!root) { return; }

  var PI = Math.PI;
  var EARTH_KM = 6371;

  function cssVar(name, fallback) {
    var v = "";
    try { v = getComputedStyle(root).getPropertyValue(name).trim(); } catch (e) { v = ""; }
    return v || fallback;
  }
  function el(tag, attrs, text) {
    var e = document.createElement(tag);
    if (attrs) {
      for (var k in attrs) {
        if (Object.prototype.hasOwnProperty.call(attrs, k)) { e.setAttribute(k, attrs[k]); }
      }
    }
    if (text) { e.textContent = text; }
    return e;
  }
  function colors() {
    return {
      fg: cssVar("--fg", "#1d1d1f"),
      bg: cssVar("--bg", "#fbfaf7"),
      accent: cssVar("--accent", "#b4441f"),
      muted: cssVar("--muted", "#8a8780")
    };
  }

  var state = { theta: 1.5 * PI, u: 0.35, k: 1, lonV: 0.75 * PI, latV: 0.62, userRotated: false };

  /* ---------- energy of the varied route (Simpson's rule) ---------- */
  function energy(theta, u, k) {
    var n = 240, h = 1 / n, s = 0;
    for (var i = 0; i <= n; i++) {
      var t = i * h;
      var c = Math.cos(k * PI * t), sn = Math.sin(k * PI * t);
      var cu = Math.cos(u * sn);
      var f = (k * PI * u) * (k * PI * u) * c * c + theta * theta * cu * cu;
      var w = (i === 0 || i === n) ? 1 : (i % 2 ? 4 : 2);
      s += w * f;
    }
    return s * h / 3;
  }

  /* ---------- DOM ---------- */
  var wrap = el("div");
  wrap.style.display = "flex";
  wrap.style.flexWrap = "wrap";
  wrap.style.gap = "10px";
  wrap.style.alignItems = "flex-start";
  var globeBox = el("div");
  globeBox.style.flex = "1 1 280px";
  globeBox.style.maxWidth = "400px";
  globeBox.style.minWidth = "0";
  var graphBox = el("div");
  graphBox.style.flex = "1 1 280px";
  graphBox.style.minWidth = "0";
  var cg = el("canvas", { "aria-label": "Globe with a great-circle route and a varied route", role: "img" });
  cg.style.width = "100%";
  cg.style.display = "block";
  cg.style.touchAction = "none";
  cg.style.cursor = "grab";
  var ce = el("canvas", { "aria-label": "Energy of the varied route against u", role: "img" });
  ce.style.width = "100%";
  ce.style.display = "block";
  globeBox.appendChild(cg);
  graphBox.appendChild(ce);
  wrap.appendChild(globeBox);
  wrap.appendChild(graphBox);
  root.appendChild(wrap);

  var controls = el("div");
  controls.style.marginTop = "6px";
  root.appendChild(controls);
  var readout = el("div");
  readout.style.fontSize = "0.9rem";
  readout.style.lineHeight = "1.45";
  readout.style.marginTop = "4px";
  root.appendChild(readout);

  function slider(label, min, max, step, value, fmt, onInput) {
    var row = el("label");
    row.style.display = "flex";
    row.style.alignItems = "center";
    row.style.gap = "8px";
    row.style.margin = "3px 0";
    row.style.fontSize = "0.9rem";
    var name = el("span", null, label);
    name.style.minWidth = "2.2em";
    var input = el("input", { type: "range", min: String(min), max: String(max), step: String(step), value: String(value) });
    input.style.flex = "1";
    input.style.minWidth = "0";
    input.style.accentColor = "var(--accent, #b4441f)";
    var out = el("span");
    out.style.minWidth = "4.2em";
    out.style.textAlign = "right";
    out.style.fontVariantNumeric = "tabular-nums";
    row.appendChild(name);
    row.appendChild(input);
    row.appendChild(out);
    function upd() { out.textContent = fmt(parseFloat(input.value)); }
    input.addEventListener("input", function () { onInput(parseFloat(input.value)); upd(); draw(); });
    upd();
    controls.appendChild(row);
    return input;
  }
  slider("\u03b8", 0.1, 1.95, 0.01, state.theta / PI, function (v) { return v.toFixed(2) + "\u03c0"; },
    function (v) { state.theta = v * PI; if (!state.userRotated) { state.lonV = state.theta / 2; } });
  slider("u", -1, 1, 0.01, state.u, function (v) { return v.toFixed(2); }, function (v) { state.u = v; });
  slider("k", 1, 3, 1, state.k, function (v) { return String(v); }, function (v) { state.k = Math.round(v); });

  /* ---------- canvas helpers ---------- */
  function setup(canvas, cssW, cssH) {
    var dpr = window.devicePixelRatio || 1;
    canvas.style.height = cssH + "px";
    canvas.width = Math.max(1, Math.round(cssW * dpr));
    canvas.height = Math.max(1, Math.round(cssH * dpr));
    var ctx = canvas.getContext("2d");
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    return ctx;
  }

  function frame() {
    var lo = state.lonV, la = state.latV;
    var v = [Math.cos(la) * Math.cos(lo), Math.cos(la) * Math.sin(lo), Math.sin(la)];
    var ex = [-Math.sin(lo), Math.cos(lo), 0];
    var ey = [-Math.sin(la) * Math.cos(lo), -Math.sin(la) * Math.sin(lo), Math.cos(la)];
    return { ex: ex, ey: ey, ez: v };
  }
  function dot(a, b) { return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]; }

  // draw a polyline of 3D points, solid where it faces the viewer and dashed behind
  function curve(ctx, pts, F, cx, cy, r, color, lw, backAlpha) {
    var prev = null;
    for (var i = 0; i < pts.length; i++) {
      var P = pts[i];
      var X = cx + r * dot(P, F.ex), Y = cy - r * dot(P, F.ey), Z = dot(P, F.ez);
      if (prev) {
        var front = (Z + prev.Z) >= 0;
        if (front || backAlpha > 0) {
          ctx.beginPath();
          ctx.moveTo(prev.X, prev.Y);
          ctx.lineTo(X, Y);
          ctx.strokeStyle = color;
          ctx.globalAlpha = front ? 1 : backAlpha;
          ctx.lineWidth = front ? lw : Math.max(0.8, lw * 0.6);
          ctx.setLineDash(front ? [] : [3, 3]);
          ctx.stroke();
        }
      }
      prev = { X: X, Y: Y, Z: Z };
    }
    ctx.globalAlpha = 1;
    ctx.setLineDash([]);
  }

  function drawGlobe(C) {
    var W = globeBox.clientWidth || 300;
    var S = Math.min(W, 400);
    var ctx = setup(cg, S, S);
    ctx.clearRect(0, 0, S, S);
    var cx = S / 2, cy = S / 2, r = 0.41 * S;
    var F = frame();
    // disc
    ctx.beginPath();
    ctx.arc(cx, cy, r, 0, 2 * PI);
    ctx.fillStyle = C.bg;
    ctx.fill();
    ctx.lineWidth = 1;
    ctx.strokeStyle = C.fg;
    ctx.stroke();
    var i, j, pts, lat, lon;
    // graticule, front side only
    for (j = -2; j <= 2; j++) {
      if (j === 0) { continue; }
      lat = j * PI / 6;
      pts = [];
      for (i = 0; i <= 120; i++) {
        lon = 2 * PI * i / 120;
        pts.push([Math.cos(lat) * Math.cos(lon), Math.cos(lat) * Math.sin(lon), Math.sin(lat)]);
      }
      curve(ctx, pts, F, cx, cy, r, C.muted, 0.5, 0);
    }
    for (j = 0; j < 12; j++) {
      lon = j * PI / 6;
      pts = [];
      for (i = 0; i <= 60; i++) {
        lat = -PI / 2 + PI * i / 60;
        pts.push([Math.cos(lat) * Math.cos(lon), Math.cos(lat) * Math.sin(lon), Math.sin(lat)]);
      }
      curve(ctx, pts, F, cx, cy, r, C.muted, 0.5, 0);
    }
    // the whole equator, faint
    pts = [];
    for (i = 0; i <= 160; i++) { lon = 2 * PI * i / 160; pts.push([Math.cos(lon), Math.sin(lon), 0]); }
    curve(ctx, pts, F, cx, cy, r, C.muted, 0.8, 0.35);
    // the route gamma
    var th = state.theta, u = state.u, k = state.k;
    pts = [];
    for (i = 0; i <= 200; i++) { lon = th * i / 200; pts.push([Math.cos(lon), Math.sin(lon), 0]); }
    curve(ctx, pts, F, cx, cy, r, C.fg, 2.4, 0.45);
    // the varied route
    pts = [];
    for (i = 0; i <= 240; i++) {
      var t = i / 240, psi = u * Math.sin(k * PI * t);
      lon = th * t;
      pts.push([Math.cos(psi) * Math.cos(lon), Math.cos(psi) * Math.sin(lon), Math.sin(psi)]);
    }
    curve(ctx, pts, F, cx, cy, r, C.accent, 2, 0.5);
    // points p, q, p'
    var marks = [
      { lab: "p", P: [1, 0, 0], col: C.fg },
      { lab: "q", P: [Math.cos(th), Math.sin(th), 0], col: C.fg },
      { lab: "p\u2032", P: [-1, 0, 0], col: th > PI ? C.accent : C.muted }
    ];
    ctx.font = "italic 14px Georgia, 'Times New Roman', serif";
    for (i = 0; i < marks.length; i++) {
      var m = marks[i];
      var X = dot(m.P, F.ex), Y = dot(m.P, F.ey), Z = dot(m.P, F.ez);
      var sx = cx + r * X, sy = cy - r * Y;
      ctx.globalAlpha = Z >= 0 ? 1 : 0.45;
      ctx.beginPath();
      ctx.arc(sx, sy, 4, 0, 2 * PI);
      ctx.fillStyle = m.col;
      ctx.fill();
      var rr = Math.sqrt(X * X + Y * Y) + 1e-9;
      ctx.fillText(m.lab, sx + 12 * X / rr - 4, sy - 12 * Y / rr + 5);
      ctx.globalAlpha = 1;
    }
    ctx.font = "12px system-ui, sans-serif";
    ctx.fillStyle = C.muted;
    ctx.fillText("drag to turn", 6, S - 8);
  }

  function niceStep(x) {
    var p = Math.pow(10, Math.floor(Math.log(x) / Math.LN10));
    var m = x / p;
    return (m < 1.5 ? 1 : m < 3.5 ? 2 : m < 7.5 ? 5 : 10) * p;
  }

  function drawGraph(C) {
    var W = graphBox.clientWidth || 300;
    var H = Math.round(Math.min(300, Math.max(200, W * 0.72)));
    var ctx = setup(ce, W, H);
    ctx.clearRect(0, 0, W, H);
    var th = state.theta, k = state.k;
    var E0 = th * th, hess = k * k * PI * PI - th * th;
    var N = 100, us = [], es = [], i;
    var ymax = 0.5;
    for (i = 0; i <= N; i++) {
      var u = -1 + 2 * i / N;
      us.push(u);
      var d = energy(th, u, k) - E0;
      es.push(d);
      ymax = Math.max(ymax, Math.abs(d));
    }
    ymax *= 1.12;
    var L = 44, R = 10, T = 22, B = 30;
    var pw = W - L - R, ph = H - T - B;
    function X(u) { return L + (u + 1) / 2 * pw; }
    function Y(y) { return T + (1 - (y + ymax) / (2 * ymax)) * ph; }
    // axes and ticks
    ctx.strokeStyle = C.muted;
    ctx.fillStyle = C.muted;
    ctx.lineWidth = 0.6;
    ctx.font = "11px system-ui, sans-serif";
    var step = niceStep(ymax / 2);
    for (var yv = -Math.floor(ymax / step) * step; yv <= ymax + 1e-9; yv += step) {
      ctx.beginPath();
      ctx.moveTo(L - 4, Y(yv));
      ctx.lineTo(L, Y(yv));
      ctx.stroke();
      var lab = Math.abs(yv) < 1e-9 ? "0" : (Math.abs(step) < 1 ? yv.toFixed(1) : String(Math.round(yv)));
      ctx.fillText(lab, 4, Y(yv) + 4);
    }
    for (var xv = -1; xv <= 1.0001; xv += 0.5) {
      ctx.beginPath();
      ctx.moveTo(X(xv), T + ph);
      ctx.lineTo(X(xv), T + ph + 4);
      ctx.stroke();
      ctx.fillText(xv.toFixed(1), X(xv) - 9, T + ph + 16);
    }
    ctx.beginPath();
    ctx.moveTo(L, T);
    ctx.lineTo(L, T + ph);
    ctx.lineTo(L + pw, T + ph);
    ctx.stroke();
    ctx.setLineDash([2, 3]);
    ctx.beginPath();
    ctx.moveTo(L, Y(0));
    ctx.lineTo(L + pw, Y(0));
    ctx.stroke();
    ctx.setLineDash([]);
    ctx.fillText("u", L + pw - 8, T + ph + 26 > H ? H - 2 : T + ph + 26);
    // clip to plot area
    ctx.save();
    ctx.beginPath();
    ctx.rect(L, T, pw, ph);
    ctx.clip();
    // parabola from the second variation formula
    ctx.strokeStyle = C.muted;
    ctx.lineWidth = 1.2;
    ctx.setLineDash([5, 4]);
    ctx.beginPath();
    for (i = 0; i <= N; i++) {
      var yp = 0.5 * hess * us[i] * us[i];
      if (i === 0) { ctx.moveTo(X(us[i]), Y(yp)); } else { ctx.lineTo(X(us[i]), Y(yp)); }
    }
    ctx.stroke();
    ctx.setLineDash([]);
    // the energy
    ctx.strokeStyle = hess < 0 ? C.accent : C.fg;
    ctx.lineWidth = 2;
    ctx.beginPath();
    for (i = 0; i <= N; i++) {
      if (i === 0) { ctx.moveTo(X(us[i]), Y(es[i])); } else { ctx.lineTo(X(us[i]), Y(es[i])); }
    }
    ctx.stroke();
    // current u
    var dcur = energy(th, state.u, k) - E0;
    ctx.fillStyle = C.accent;
    ctx.beginPath();
    ctx.arc(X(state.u), Y(dcur), 4.5, 0, 2 * PI);
    ctx.fill();
    ctx.restore();
    ctx.fillStyle = C.fg;
    ctx.font = "12px system-ui, sans-serif";
    ctx.fillText("E(\u1fb1(u)) \u2212 E(\u03b3)   (dashed: \u00bd(k\u00b2\u03c0\u00b2 \u2212 \u03b8\u00b2)u\u00b2)", L, 14);
    return dcur;
  }

  function fmt(x, d) { return (x < 0 ? "\u2212" : "") + Math.abs(x).toFixed(d); }

  function draw() {
    var C = colors();
    root.style.color = C.fg;
    drawGlobe(C);
    var dcur = drawGraph(C);
    var th = state.theta, k = state.k;
    var hess = k * k * PI * PI - th * th;
    var km = Math.round(th * EARTH_KM).toLocaleString("en-US");
    var verdict;
    if (Math.abs(hess) < 0.05) {
      verdict = "zero: a degenerate direction (for k = 1 the end points are antipodal and every half great circle is equally short).";
    } else if (hess < 0) {
      verdict = "negative: pushing the route sideways in " + k + (k === 1 ? " lobe" : " lobes") + " makes it shorter, so it is not a minimum.";
    } else {
      verdict = "positive: in this direction the route is a local minimum of the energy.";
    }
    readout.textContent = "Route angle \u03b8 = " + (th / PI).toFixed(2) + "\u03c0 (" + km +
      " km on the Earth), E(\u03b3) = \u03b8\u00b2 = " + fmt(th * th, 2) +
      ". At u = " + fmt(state.u, 2) + ": E(\u1fb1(u)) \u2212 E(\u03b3) = " + fmt(dcur, 3) +
      ". Second variation E\u2217\u2217(W\u2096, W\u2096) = k\u00b2\u03c0\u00b2 \u2212 \u03b8\u00b2 = " + fmt(hess, 2) + ", " + verdict;
  }

  /* ---------- dragging the globe ---------- */
  var drag = null;
  cg.addEventListener("pointerdown", function (e) {
    drag = { x: e.clientX, y: e.clientY, lon: state.lonV, lat: state.latV };
    cg.style.cursor = "grabbing";
    try { cg.setPointerCapture(e.pointerId); } catch (err) { /* ignore */ }
  });
  cg.addEventListener("pointermove", function (e) {
    if (!drag) { return; }
    var s = 2.6 / Math.max(120, cg.clientWidth);
    state.lonV = drag.lon - (e.clientX - drag.x) * s;
    state.latV = Math.max(-1.45, Math.min(1.45, drag.lat + (e.clientY - drag.y) * s));
    state.userRotated = true;
    draw();
  });
  function endDrag() { drag = null; cg.style.cursor = "grab"; }
  cg.addEventListener("pointerup", endDrag);
  cg.addEventListener("pointercancel", endDrag);

  /* ---------- layout ---------- */
  var lastWidth = -1;
  function onResize() {
    var w = root.clientWidth;
    if (w !== lastWidth) { lastWidth = w; draw(); }
  }
  if (typeof ResizeObserver !== "undefined") {
    new ResizeObserver(onResize).observe(root);
  } else {
    window.addEventListener("resize", onResize);
  }
  if (window.matchMedia) {
    var mq = window.matchMedia("(prefers-color-scheme: dark)");
    if (mq.addEventListener) { mq.addEventListener("change", draw); }
  }
  draw();
})();
