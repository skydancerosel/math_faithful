/* Figure for Chapter 9: conjugate points and the index theorem on a surface of constant curvature K.
   Plain JavaScript, no libraries.  Finds <div id="conjugate-figure"> and draws three canvases:
   (a) the Jacobi fields s*sn_K(t) along a unit-speed geodesic (the linearized fan of geodesics from
       gamma(0)), whose common zeros t = m*pi/sqrt(K) are the conjugate points;
   (b) the eigenvalues of the matrix of E_** on normal broken Jacobi fields along gamma|[0, tau], for
       the subdivision of [0, tau] into k equal pieces, multiplied by the positive factor
       sin(sqrt(K) h)/sqrt(K) (h = tau/k), i.e. mu_m = 2 (cs_K(h) - cos(m pi/k)), m = 1..k-1, with
       cs_K(h) = cos(sqrt(K) h), 1 or cosh(sqrt(-K) h);
   (c) the index lambda(tau), the number of negative eigenvalues.
   Sliders set tau, K and k.  Colours come from the CSS variables --fg, --bg, --accent, --muted
   (with fallbacks). */
(function () {
  "use strict";
  var root = document.getElementById("conjugate-figure");
  if (!root) { return; }

  var PI = Math.PI;
  var TMAX = 10;

  function cssVar(name, fallback) {
    var v = "";
    try { v = getComputedStyle(root).getPropertyValue(name).trim(); } catch (e) { v = ""; }
    return v || fallback;
  }
  function el(tag, attrs, text) {
    var e = document.createElement(tag);
    if (attrs) {
      for (var a in attrs) {
        if (Object.prototype.hasOwnProperty.call(attrs, a)) { e.setAttribute(a, attrs[a]); }
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

  var state = { tau: 7.5, K: 1, k: 5 };

  /* ---------- the mathematics ---------- */
  function sn(K, t) {
    if (K > 1e-9) { var r = Math.sqrt(K); return Math.sin(r * t) / r; }
    if (K < -1e-9) { var q = Math.sqrt(-K); return (Math.exp(q * t) - Math.exp(-q * t)) / (2 * q); }
    return t;
  }
  function cs(K, h) {
    if (K > 1e-9) { return Math.cos(Math.sqrt(K) * h); }
    if (K < -1e-9) { var q = Math.sqrt(-K); return (Math.exp(q * h) + Math.exp(-q * h)) / 2; }
    return 1;
  }
  // largest tau for which the k equal pieces are shorter than the conjugate distance pi/sqrt(K)
  function tauAdmissible(K, k) { return K > 1e-9 ? k * PI / Math.sqrt(K) : Infinity; }
  function eigen(K, k, tau) {
    var h = tau / k, c = cs(K, h), out = [];
    for (var m = 1; m < k; m++) { out.push(2 * (c - Math.cos(m * PI / k))); }
    return out;
  }
  function conjugates(K) {
    var res = [];
    if (K > 1e-9) {
      var d = PI / Math.sqrt(K);
      for (var m = 1; m * d <= TMAX + 1e-9; m++) { res.push(m * d); }
    }
    return res;
  }
  function indexByCount(K, tau) {
    var c = conjugates(K), n = 0;
    for (var i = 0; i < c.length; i++) { if (c[i] < tau - 1e-12) { n++; } }
    return n;
  }

  /* ---------- DOM ---------- */
  function mkCanvas(label) {
    var c = el("canvas", { role: "img", "aria-label": label });
    c.style.width = "100%";
    c.style.display = "block";
    root.appendChild(c);
    return c;
  }
  var c1 = mkCanvas("Jacobi fields along a geodesic and its conjugate points");
  var c2 = mkCanvas("Eigenvalues of the Hessian on broken Jacobi fields against tau");
  var c3 = mkCanvas("The index lambda(tau) as a step function");
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
    out.style.minWidth = "3.6em";
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
  slider("\u03c4", 0.05, TMAX, 0.01, state.tau, function (v) { return v.toFixed(2); }, function (v) { state.tau = v; });
  slider("K", -1, 4, 0.05, state.K, function (v) { return v.toFixed(2); }, function (v) { state.K = v; });
  slider("k", 2, 16, 1, state.k, function (v) { return String(v); }, function (v) { state.k = Math.round(v); });

  function setup(canvas, cssW, cssH) {
    var dpr = window.devicePixelRatio || 1;
    canvas.style.height = cssH + "px";
    canvas.width = Math.max(1, Math.round(cssW * dpr));
    canvas.height = Math.max(1, Math.round(cssH * dpr));
    var ctx = canvas.getContext("2d");
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, cssW, cssH);
    return ctx;
  }

  var PAD = { L: 34, R: 10 };
  function xOf(W, t) { return PAD.L + (W - PAD.L - PAD.R) * t / TMAX; }

  function title(ctx, C, text, W) {
    ctx.fillStyle = C.fg;
    var size = 12;
    ctx.font = size + "px system-ui, sans-serif";
    while (size > 9 && ctx.measureText(text).width > W - PAD.L - 4) {
      size -= 0.5;
      ctx.font = size + "px system-ui, sans-serif";
    }
    ctx.fillText(text, PAD.L, 13);
  }
  function tauLine(ctx, C, W, top, bottom) {
    var x = xOf(W, state.tau);
    ctx.strokeStyle = C.muted;
    ctx.lineWidth = 1;
    ctx.setLineDash([2, 3]);
    ctx.beginPath();
    ctx.moveTo(x, top);
    ctx.lineTo(x, bottom);
    ctx.stroke();
    ctx.setLineDash([]);
  }

  /* (a) the fan of Jacobi fields */
  function drawFan(C, W) {
    var H = Math.round(Math.max(130, Math.min(190, W * 0.3)));
    var ctx = setup(c1, W, H);
    title(ctx, C, "Jacobi fields s\u00b7sn_K(t) along \u03b3: the fan from \u03b3(0)", W);
    var top = 22, bot = H - 8, mid = (top + bot) / 2, half = (bot - top) / 2 - 2;
    var K = state.K, n = 300, i, j;
    // normalize over the whole range when the fan refocuses (K > 0), over [0, 4] otherwise,
    // so that a spreading fan is visible from the start; the drawing is clipped to the panel
    var tNorm = K > 1e-9 ? TMAX : 4, maxsn = 1e-9;
    for (i = 0; i <= n; i++) { maxsn = Math.max(maxsn, Math.abs(sn(K, tNorm * i / n))); }
    var scale = half / maxsn;
    ctx.save();
    ctx.beginPath();
    ctx.rect(0, top - 2, W, bot - top + 4);
    ctx.clip();
    var amps = [0.25, 0.5, 0.75, 1];
    for (j = 0; j < amps.length; j++) {
      for (var sg = -1; sg <= 1; sg += 2) {
        for (var pass = 0; pass < 2; pass++) {
          ctx.beginPath();
          var started = false;
          for (i = 0; i <= n; i++) {
            var t = TMAX * i / n;
            var inside = t <= state.tau;
            if ((pass === 0) !== inside) { if (pass === 0 && started) { break; } continue; }
            var x = xOf(W, t), y = mid - sg * amps[j] * sn(K, t) * scale;
            if (!started) { ctx.moveTo(x, y); started = true; } else { ctx.lineTo(x, y); }
          }
          ctx.strokeStyle = C.accent;
          ctx.globalAlpha = pass === 0 ? 0.9 : 0.25;
          ctx.lineWidth = 1.1;
          ctx.stroke();
          ctx.globalAlpha = 1;
        }
      }
    }
    ctx.restore();
    // the geodesic itself
    ctx.strokeStyle = C.fg;
    ctx.lineWidth = 2.5;
    ctx.beginPath();
    ctx.moveTo(xOf(W, 0), mid);
    ctx.lineTo(xOf(W, Math.min(state.tau, TMAX)), mid);
    ctx.stroke();
    ctx.strokeStyle = C.muted;
    ctx.lineWidth = 1.2;
    ctx.setLineDash([5, 4]);
    ctx.beginPath();
    ctx.moveTo(xOf(W, state.tau), mid);
    ctx.lineTo(xOf(W, TMAX), mid);
    ctx.stroke();
    ctx.setLineDash([]);
    // conjugate points
    var cj = conjugates(K);
    ctx.font = "11px system-ui, sans-serif";
    for (i = 0; i < cj.length; i++) {
      ctx.fillStyle = C.fg;
      ctx.beginPath();
      ctx.arc(xOf(W, cj[i]), mid, 4, 0, 2 * PI);
      ctx.fill();
      var lab = K > 0.999 && K < 1.001 ? (i === 0 ? "\u03c0" : (i + 1) + "\u03c0") : cj[i].toFixed(2);
      if (xOf(W, cj[i]) + 4 + ctx.measureText(lab).width <= W) {
        ctx.fillText(lab, xOf(W, cj[i]) + 4, mid - 7);
      }
    }
    ctx.fillStyle = C.fg;
    ctx.beginPath();
    ctx.arc(xOf(W, 0), mid, 4, 0, 2 * PI);
    ctx.fill();
    tauLine(ctx, C, W, top, bot);
  }

  /* (b) eigenvalues against tau */
  function drawEigen(C, W) {
    var H = Math.round(Math.max(170, Math.min(240, W * 0.38)));
    var ctx = setup(c2, W, H);
    title(ctx, C, "eigenvalues of E\u2217\u2217 on broken Jacobi fields, k = " + state.k, W);
    var top = 22, bot = H - 20, YMAX = 4.4;
    function Y(v) { return top + (bot - top) * (YMAX - v) / (2 * YMAX); }
    var K = state.K, k = state.k, tAdm = Math.min(TMAX, tauAdmissible(K, k) - 1e-6);
    // axes
    ctx.strokeStyle = C.muted;
    ctx.fillStyle = C.muted;
    ctx.lineWidth = 0.6;
    ctx.font = "11px system-ui, sans-serif";
    for (var v = -4; v <= 4; v += 2) {
      ctx.fillText(String(v), 6, Y(v) + 4);
    }
    ctx.beginPath();
    ctx.moveTo(PAD.L, top);
    ctx.lineTo(PAD.L, bot);
    ctx.stroke();
    ctx.strokeStyle = C.fg;
    ctx.lineWidth = 0.9;
    ctx.beginPath();
    ctx.moveTo(PAD.L, Y(0));
    ctx.lineTo(W - PAD.R, Y(0));
    ctx.stroke();
    // inadmissible region
    if (tAdm < TMAX) {
      ctx.fillStyle = C.muted;
      ctx.globalAlpha = 0.15;
      ctx.fillRect(xOf(W, tAdm), top, xOf(W, TMAX) - xOf(W, tAdm), bot - top);
      ctx.globalAlpha = 1;
      ctx.fillStyle = C.fg;
      ctx.font = "11px system-ui, sans-serif";
      var msg = "pieces too long: not fine";
      var tw = ctx.measureText(msg).width;
      var xm = Math.max(PAD.L + 3, Math.min(xOf(W, tAdm) + 3, W - PAD.R - tw - 3));
      ctx.fillText(msg, xm, bot - 6);
    }
    // curves
    ctx.save();
    ctx.beginPath();
    ctx.rect(PAD.L, top, W - PAD.L - PAD.R, bot - top);
    ctx.clip();
    var n = 260;
    for (var m = 1; m < k; m++) {
      ctx.beginPath();
      var crosses = false;
      for (var i = 0; i <= n; i++) {
        var t = 0.02 + (tAdm - 0.02) * i / n;
        var mu = 2 * (cs(K, t / k) - Math.cos(m * PI / k));
        if (mu < 0) { crosses = true; }
        var x = xOf(W, t), y = Y(Math.max(-YMAX - 1, Math.min(YMAX + 1, mu)));
        if (i === 0) { ctx.moveTo(x, y); } else { ctx.lineTo(x, y); }
      }
      ctx.strokeStyle = crosses ? C.accent : C.muted;
      ctx.lineWidth = crosses ? 1.6 : 1;
      ctx.stroke();
    }
    // zero crossings = conjugate points
    var cj = conjugates(K);
    for (var j = 0; j < cj.length; j++) {
      if (cj[j] < tAdm && j + 1 < k) {
        ctx.fillStyle = C.accent;
        ctx.beginPath();
        ctx.arc(xOf(W, cj[j]), Y(0), 3.5, 0, 2 * PI);
        ctx.fill();
      }
    }
    ctx.restore();
    tauLine(ctx, C, W, top, bot);
    // current eigenvalues
    if (state.tau < tAdm) {
      var ev = eigen(K, k, state.tau);
      ctx.fillStyle = C.fg;
      for (var e = 0; e < ev.length; e++) {
        if (Math.abs(ev[e]) <= YMAX) {
          ctx.beginPath();
          ctx.arc(xOf(W, state.tau), Y(ev[e]), 2.5, 0, 2 * PI);
          ctx.fill();
        }
      }
    }
  }

  /* (c) the step function lambda(tau) */
  function drawIndex(C, W) {
    var K = state.K;
    var cj = conjugates(K);
    var lmax = Math.max(1, cj.length);
    var H = 40 + 16 * lmax;
    var ctx = setup(c3, W, H);
    title(ctx, C, "index \u03bb(\u03c4) = number of negative eigenvalues", W);
    var top = 22, bot = H - 16;
    function Y(l) { return bot - (bot - top) * l / lmax; }
    ctx.strokeStyle = C.muted;
    ctx.fillStyle = C.muted;
    ctx.lineWidth = 0.6;
    ctx.font = "11px system-ui, sans-serif";
    for (var l = 0; l <= lmax; l++) { ctx.fillText(String(l), 14, Y(l) + 4); }
    ctx.beginPath();
    ctx.moveTo(PAD.L, top);
    ctx.lineTo(PAD.L, bot);
    ctx.lineTo(W - PAD.R, bot);
    ctx.stroke();
    var edges = [0].concat(cj.filter(function (c) { return c < TMAX; })).concat([TMAX]);
    ctx.strokeStyle = C.fg;
    ctx.lineWidth = 2.2;
    for (var j = 0; j + 1 < edges.length; j++) {
      ctx.beginPath();
      ctx.moveTo(xOf(W, edges[j]), Y(j));
      ctx.lineTo(xOf(W, edges[j + 1]), Y(j));
      ctx.stroke();
      if (j > 0) {
        ctx.fillStyle = C.bg;
        ctx.beginPath();
        ctx.arc(xOf(W, edges[j]), Y(j), 3.5, 0, 2 * PI);
        ctx.fill();
        ctx.lineWidth = 1.2;
        ctx.stroke();
        ctx.lineWidth = 2.2;
        ctx.fillStyle = C.fg;
        ctx.beginPath();
        ctx.arc(xOf(W, edges[j]), Y(j - 1), 3.5, 0, 2 * PI);
        ctx.fill();
      }
    }
    tauLine(ctx, C, W, top, bot);
    // tau axis labels
    ctx.fillStyle = C.muted;
    for (var t = 0; t <= TMAX; t += 2) { ctx.fillText(String(t), xOf(W, t) - 3, H - 3); }
  }

  function draw() {
    var C = colors();
    root.style.color = C.fg;
    var W = root.clientWidth || 320;
    drawFan(C, W);
    drawEigen(C, W);
    drawIndex(C, W);
    var K = state.K, k = state.k, tau = state.tau;
    var lam = indexByCount(K, tau);
    var tAdm = tauAdmissible(K, k);
    var cj = conjugates(K).filter(function (c) { return c < tau - 1e-12; });
    var neg = null;
    if (tau < tAdm) {
      neg = eigen(K, k, tau).filter(function (x) { return x < 0; }).length;
    }
    var onConj = conjugates(K).some(function (c) { return Math.abs(c - tau) < 0.006; });
    var txt = "\u03c4 = " + tau.toFixed(2) + ". Conjugate points of \u03b3(0) in (0, \u03c4): " +
      (cj.length ? cj.map(function (c) { return c.toFixed(2); }).join(", ") : "none") +
      " (each of multiplicity 1 on a surface, n \u2212 1 on S\u207f). ";
    if (neg === null) {
      txt += "With k = " + k + " pieces the subdivision is not fine for this \u03c4: increase k.";
    } else {
      txt += "Negative eigenvalues with k = " + k + " pieces: " + neg + ". Index \u03bb(\u03c4) = " + lam + ".";
    }
    if (onConj) { txt += " At a conjugate point one eigenvalue is 0: E\u2217\u2217 is degenerate (Theorem 14.1)."; }
    readout.textContent = txt;
  }

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
