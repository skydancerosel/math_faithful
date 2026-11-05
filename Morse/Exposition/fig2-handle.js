/*
 * fig2-handle.js -- interactive figure for Chapter 2 (Milnor, Morse Theory, section 3).
 *
 * The proof of Theorem 3.2 for n = 2, lambda = 1, c = 0, in Morse coordinates (x, y):
 *   f = -x^2 + y^2,   F = f - mu(x^2 + 2 y^2).
 * Slider s in [0, 1]: the gradient flow of F used in Theorem 3.1 (Assertion 3) pushes the sample
 * points of M^{c+eps} down into F <= c - eps.  Slider s in [1, 2]: Milnor's three-case deformation
 * r_t, t = s - 1 (Assertion 4), pushes the handle onto M^{c-eps} u e^1.
 *
 * Plain JavaScript, no libraries.  Finds <div id="handle-figure">.
 * Colours come from the CSS variables --fg, --bg, --accent, --muted (with fallbacks).
 */
(function () {
  'use strict';

  var ID = 'handle-figure';
  var WIN = 1.5; // the window is [-WIN, WIN]^2 in Morse coordinates

  function cssVar(el, name, fallback) {
    var v = '';
    try {
      v = window.getComputedStyle(el).getPropertyValue(name);
    } catch (e) {
      v = '';
    }
    v = (v || '').trim();
    return v || fallback;
  }

  function el(tag, attrs, parent) {
    var e = document.createElement(tag);
    if (attrs) {
      for (var k in attrs) {
        if (Object.prototype.hasOwnProperty.call(attrs, k)) {
          if (k === 'style') e.style.cssText = attrs[k];
          else if (k === 'text') e.textContent = attrs[k];
          else e.setAttribute(k, attrs[k]);
        }
      }
    }
    if (parent) parent.appendChild(e);
    return e;
  }

  // ---------------------------------------------------------------- the model

  function lam(t) { return t > 0 ? Math.exp(-1 / t) : 0; }
  function step(r, p, q) { var a = lam(r - p); return a / (a + lam(q - r)); }

  // mu(r) = (6 eps / 5 I) int_r^inf beta,  beta = 1 on [eps/5, 9 eps/5], 0 outside (0, 2 eps)
  function Model(eps) {
    var n = 2000, dr = 2 * eps / n;
    var beta = new Float64Array(n + 1), tail = new Float64Array(n + 1);
    for (var i = 0; i <= n; i++) {
      var r = i * dr;
      beta[i] = step(r, 0, eps / 5) * (1 - step(r, 9 * eps / 5, 2 * eps));
    }
    tail[n] = 0;
    for (var k = n - 1; k >= 0; k--) tail[k] = tail[k + 1] + 0.5 * (beta[k] + beta[k + 1]) * dr;
    var I = tail[0], c = 6 * eps / (5 * I);
    this.eps = eps;
    this.mu = function (r) {
      if (r <= 0) return c * tail[0];
      if (r >= 2 * eps) return 0;
      var u = r / dr, j = Math.floor(u), w = u - j;
      return c * (tail[j] * (1 - w) + tail[j + 1] * w);
    };
    this.dmu = function (r) {
      if (r <= 0 || r >= 2 * eps) return 0;
      var u = r / dr, j = Math.floor(u), w = u - j;
      return -c * (beta[j] * (1 - w) + beta[j + 1] * w);
    };
  }
  Model.prototype.f = function (x, y) { return -x * x + y * y; };
  Model.prototype.F = function (x, y) { return -x * x + y * y - this.mu(x * x + 2 * y * y); };
  Model.prototype.vel = function (x, y) { // -grad F / |grad F|^2
    var d = this.dmu(x * x + 2 * y * y);
    var gx = -2 * x * (1 + d), gy = 2 * y * (1 - 2 * d);
    var n2 = gx * gx + gy * gy;
    return [-gx / n2, -gy / n2];
  };
  // Theorem 3.1 for F: follow -grad F/|grad F|^2 for time F(q) + eps (to the level c - eps = -eps)
  Model.prototype.path = function (x, y, nsteps) {
    var T = this.F(x, y) + this.eps, pts = [x, y];
    if (T <= 0) return pts;
    var h = T / nsteps;
    for (var s = 0; s < nsteps; s++) {
      var k1 = this.vel(x, y);
      var k2 = this.vel(x + 0.5 * h * k1[0], y + 0.5 * h * k1[1]);
      var k3 = this.vel(x + 0.5 * h * k2[0], y + 0.5 * h * k2[1]);
      var k4 = this.vel(x + h * k3[0], y + h * k3[1]);
      x += h / 6 * (k1[0] + 2 * k2[0] + 2 * k3[0] + k4[0]);
      y += h / 6 * (k1[1] + 2 * k2[1] + 2 * k3[1] + k4[1]);
      pts.push(x, y);
    }
    return pts;
  };
  // Milnor's r_t of Assertion 4 (r_0 = identity, r_1 = retraction)
  Model.prototype.milnor = function (x, y, t) {
    var xi = x * x, eta = y * y, eps = this.eps;
    if (xi <= eps) return [x, (1 - t) * y, 1];
    if (xi <= eta + eps) {
      if (eta === 0) return [x, y, 2];
      var s = (1 - t) + t * Math.sqrt((xi - eps) / eta);
      return [x, s * y, 2];
    }
    return [x, y, 3];
  };

  // marching squares, for the level curve F = -eps
  var SEG = {
    1: [[3, 0]], 2: [[0, 1]], 3: [[3, 1]], 4: [[1, 2]], 6: [[0, 2]], 7: [[3, 2]],
    8: [[2, 3]], 9: [[0, 2]], 11: [[1, 2]], 12: [[1, 3]], 13: [[0, 1]], 14: [[3, 0]]
  };
  function frac(level, va, vb) { var d = vb - va; return d === 0 ? 0.5 : (level - va) / d; }
  function levelSegments(fun, level, N) {
    var W = N + 1, d = 2 * WIN / N, v = new Float64Array(W * W), out = [];
    for (var j = 0; j < W; j++) for (var i = 0; i < W; i++) v[i + j * W] = fun(-WIN + i * d, -WIN + j * d);
    for (var jj = 0; jj < N; jj++) {
      for (var ii = 0; ii < N; ii++) {
        var v00 = v[ii + jj * W], v10 = v[ii + 1 + jj * W], v11 = v[ii + 1 + (jj + 1) * W], v01 = v[ii + (jj + 1) * W];
        var c = (v00 > level ? 1 : 0) | (v10 > level ? 2 : 0) | (v11 > level ? 4 : 0) | (v01 > level ? 8 : 0);
        if (c === 0 || c === 15) continue;
        var segs = SEG[c];
        if (c === 5 || c === 10) {
          var centre = 0.25 * (v00 + v10 + v11 + v01);
          if (c === 5) segs = centre > level ? [[0, 1], [2, 3]] : [[3, 0], [1, 2]];
          else segs = centre > level ? [[3, 0], [1, 2]] : [[0, 1], [2, 3]];
        }
        var x0 = -WIN + ii * d, y0 = -WIN + jj * d;
        for (var s = 0; s < segs.length; s++) {
          for (var e = 0; e < 2; e++) {
            var ed = segs[s][e];
            if (ed === 0) out.push(x0 + frac(level, v00, v10) * d, y0);
            else if (ed === 1) out.push(x0 + d, y0 + frac(level, v10, v11) * d);
            else if (ed === 2) out.push(x0 + frac(level, v01, v11) * d, y0 + d);
            else out.push(x0, y0 + frac(level, v00, v01) * d);
          }
        }
      }
    }
    return out;
  }

  // ---------------------------------------------------------------- figure

  function build(root) {
    var state = { s: 0, eps: 0.3, playing: false };
    var model, samples, handleCurve, bgCanvas = null, bgKey = '';
    var NSTEPS = 60;

    var wrap = el('div', { style: 'max-width:600px;margin:0 auto;font:14px/1.4 system-ui,-apple-system,Segoe UI,sans-serif;' }, root);
    var canvas = el('canvas', { style: 'display:block;width:100%;height:auto;border-radius:6px;', 'aria-label': 'The handle and the deformation of Theorem 3.2' }, wrap);
    var readout = el('div', { style: 'margin:8px 2px 4px;min-height:2.8em;' }, wrap);
    var controls = el('div', { style: 'display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:6px 14px;align-items:end;' }, wrap);

    function slider(label, min, max, stepv, value, onInput, fmt) {
      var box = el('label', { style: 'display:flex;flex-direction:column;gap:2px;' }, controls);
      var head = el('span', null, box);
      var input = el('input', { type: 'range', min: String(min), max: String(max), step: String(stepv), value: String(value), style: 'width:100%;' }, box);
      function show() { head.textContent = label + ' = ' + fmt(parseFloat(input.value)); }
      input.addEventListener('input', function () { onInput(parseFloat(input.value)); show(); schedule(); });
      show();
      return { input: input, show: show };
    }

    var ss = slider('deformation s', 0, 2, 0.005, state.s, function (v) { state.s = v; state.playing = false; btn.textContent = 'play'; }, function (v) { return v.toFixed(2); });
    slider('\u03b5', 0.08, 0.5, 0.01, state.eps, function (v) { state.eps = v; setup(); }, function (v) { return v.toFixed(2); });
    var btn = el('button', { type: 'button', text: 'play', style: 'font:inherit;padding:4px 12px;border-radius:5px;border:1px solid currentColor;background:transparent;color:inherit;cursor:pointer;justify-self:start;' }, controls);

    var lastT = 0;
    btn.addEventListener('click', function () {
      state.playing = !state.playing;
      btn.textContent = state.playing ? 'pause' : 'play';
      if (state.playing) {
        if (state.s >= 2) state.s = 0;
        lastT = 0;
        (window.requestAnimationFrame || function (cb) { return setTimeout(cb, 16); })(tick);
      }
    });
    function tick(ts) {
      if (!state.playing) return;
      var now = typeof ts === 'number' ? ts : Date.now();
      if (!lastT) lastT = now;
      var dt = Math.min(0.05, (now - lastT) / 1000);
      lastT = now;
      state.s = Math.min(2, state.s + dt * 0.45);
      ss.input.value = String(state.s);
      ss.show();
      draw();
      if (state.s >= 2) { state.playing = false; btn.textContent = 'play'; return; }
      (window.requestAnimationFrame || function (cb) { return setTimeout(cb, 16); })(tick);
    }

    function setup() {
      model = new Model(state.eps);
      samples = [];
      var h = 0.15;
      for (var x = -WIN + h / 2; x < WIN; x += h) {
        for (var y = -WIN + h / 2; y < WIN; y += h) {
          if (model.f(x, y) > model.eps) continue; // only points of M^{c+eps}
          var kind = model.f(x, y) <= -model.eps ? 0 : (model.F(x, y) <= -model.eps ? 1 : 2);
          samples.push({ kind: kind, path: model.path(x, y, NSTEPS) });
        }
      }
      handleCurve = levelSegments(function (x, y) { return model.F(x, y); }, -model.eps, 160);
      bgKey = '';
      schedule();
    }

    var pending = false;
    function schedule() {
      if (pending) return;
      pending = true;
      (window.requestAnimationFrame || function (cb) { return setTimeout(cb, 16); })(function () {
        pending = false;
        draw();
      });
    }

    function position(sm, s) {
      var p = sm.path, m = p.length / 2 - 1;
      if (s <= 1) {
        if (m === 0) return [p[0], p[1]];
        var u = s * m, j = Math.min(Math.floor(u), m - 1), w = u - j;
        return [p[2 * j] * (1 - w) + p[2 * j + 2] * w, p[2 * j + 1] * (1 - w) + p[2 * j + 3] * w];
      }
      var r = model.milnor(p[2 * m], p[2 * m + 1], s - 1);
      return [r[0], r[1]];
    }

    function background(S, dpr, fg, accent, muted, bg) {
      var key = S + '|' + dpr + '|' + state.eps + '|' + fg + accent + muted + bg;
      if (bgCanvas && key === bgKey) return bgCanvas;
      bgKey = key;
      bgCanvas = document.createElement('canvas');
      bgCanvas.width = Math.round(S * dpr);
      bgCanvas.height = Math.round(S * dpr);
      var c = bgCanvas.getContext('2d');
      c.setTransform(dpr, 0, 0, dpr, 0, 0);
      c.fillStyle = bg;
      c.fillRect(0, 0, S, S);
      var cell = 2, n = Math.ceil(S / cell), eps = model.eps;
      var paths = [[], [], []]; // band, handle, M^{c-eps}
      for (var j = 0; j < n; j++) {
        var y = WIN - (j + 0.5) * cell / S * 2 * WIN;
        for (var i = 0; i < n; i++) {
          var x = -WIN + (i + 0.5) * cell / S * 2 * WIN;
          var fv = model.f(x, y);
          if (fv <= -eps) paths[2].push(i, j);
          else if (model.F(x, y) <= -eps) paths[1].push(i, j);
          else if (fv <= eps) paths[0].push(i, j);
        }
      }
      var cols = [[muted, 0.16], [accent, 0.24], [fg, 0.30]];
      for (var k = 0; k < 3; k++) {
        c.globalAlpha = cols[k][1];
        c.fillStyle = cols[k][0];
        c.beginPath();
        var P = paths[k];
        for (var q = 0; q < P.length; q += 2) c.rect(P[q] * cell, P[q + 1] * cell, cell, cell);
        c.fill();
      }
      c.globalAlpha = 1;
      return bgCanvas;
    }

    function draw() {
      var fg = cssVar(root, '--fg', '#1f1f1d');
      var bg = cssVar(root, '--bg', '#fcfcfb');
      var accent = cssVar(root, '--accent', '#2a78d6');
      var muted = cssVar(root, '--muted', '#8a8984');

      var S = Math.max(200, Math.min(wrap.clientWidth || root.clientWidth || 360, 600));
      var dpr = window.devicePixelRatio || 1;
      if (canvas.width !== Math.round(S * dpr)) {
        canvas.width = Math.round(S * dpr);
        canvas.height = Math.round(S * dpr);
      }
      canvas.style.height = S + 'px';
      var ctx = canvas.getContext('2d');
      ctx.setTransform(1, 0, 0, 1, 0, 0);
      ctx.drawImage(background(S, dpr, fg, accent, muted, bg), 0, 0);
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0);

      function px(x) { return (x + WIN) / (2 * WIN) * S; }
      function py(y) { return (WIN - y) / (2 * WIN) * S; }
      var eps = model.eps, k, t;

      // hyperbolas f = c - eps (fg) and f = c + eps (muted)
      ctx.lineWidth = 1.2;
      for (var which = 0; which < 2; which++) {
        ctx.strokeStyle = which === 0 ? fg : muted;
        for (var sg = -1; sg <= 1; sg += 2) {
          ctx.beginPath();
          for (k = 0; k <= 120; k++) {
            t = -WIN + k * 2 * WIN / 120;
            var h = Math.sqrt(t * t + eps);
            var X = which === 0 ? sg * h : t, Y = which === 0 ? t : sg * h;
            if (k === 0) ctx.moveTo(px(X), py(Y)); else ctx.lineTo(px(X), py(Y));
          }
          ctx.stroke();
        }
      }
      // boundary of the handle, F = c - eps
      ctx.strokeStyle = accent;
      ctx.lineWidth = 1.4;
      ctx.beginPath();
      for (k = 0; k < handleCurve.length; k += 4) {
        ctx.moveTo(px(handleCurve[k]), py(handleCurve[k + 1]));
        ctx.lineTo(px(handleCurve[k + 2]), py(handleCurve[k + 3]));
      }
      ctx.stroke();
      // circle of radius sqrt(2 eps) and ellipse xi + 2 eta = 2 eps (dashed)
      var r2 = Math.sqrt(2 * eps), r1 = Math.sqrt(eps), sc = S / (2 * WIN);
      ctx.strokeStyle = muted;
      ctx.lineWidth = 1;
      ctx.beginPath();
      ctx.arc(px(0), py(0), r2 * sc, 0, 2 * Math.PI);
      ctx.stroke();
      if (ctx.setLineDash) ctx.setLineDash([5, 4]);
      ctx.beginPath();
      for (k = 0; k <= 100; k++) {
        t = k * 2 * Math.PI / 100;
        var ex = px(r2 * Math.cos(t)), ey = py(r1 * Math.sin(t));
        if (k === 0) ctx.moveTo(ex, ey); else ctx.lineTo(ex, ey);
      }
      ctx.stroke();
      if (ctx.setLineDash) ctx.setLineDash([]);
      // the cell e^1
      ctx.strokeStyle = fg;
      ctx.lineWidth = 3.5;
      ctx.beginPath();
      ctx.moveTo(px(-r1), py(0));
      ctx.lineTo(px(r1), py(0));
      ctx.stroke();

      // sample points
      var s = state.s, order = [0, 1, 2];
      for (var o = 0; o < 3; o++) {
        var kind = order[o];
        for (var q = 0; q < samples.length; q++) {
          var sm = samples[q];
          if (sm.kind !== kind) continue;
          var p = position(sm, s);
          var X0 = px(p[0]), Y0 = py(p[1]);
          if (X0 < -5 || X0 > S + 5 || Y0 < -5 || Y0 > S + 5) continue;
          ctx.beginPath();
          ctx.arc(X0, Y0, kind === 0 ? 2.2 : 3, 0, 2 * Math.PI);
          if (kind === 0) {
            ctx.fillStyle = bg; ctx.fill();
            ctx.strokeStyle = muted; ctx.lineWidth = 1; ctx.stroke();
          } else {
            ctx.fillStyle = kind === 1 ? fg : accent; ctx.fill();
            ctx.strokeStyle = bg; ctx.lineWidth = 0.8; ctx.stroke();
          }
        }
      }
      // the critical point
      ctx.fillStyle = fg;
      ctx.beginPath();
      ctx.arc(px(0), py(0), 3, 0, 2 * Math.PI);
      ctx.fill();
      ctx.strokeStyle = muted;
      ctx.lineWidth = 1;
      ctx.strokeRect(0.5, 0.5, S - 1, S - 1);

      var txt;
      if (s <= 0) txt = 's = 0: sample points of M\u1d9c\u207a\u1d4b (blue: in the band f\u207b\u00b9[c\u2212\u03b5, c+\u03b5]; black: in the handle H; hollow: in M\u1d9c\u207b\u1d4b).';
      else if (s < 1) txt = 'Assertion 3 (Theorem 3.1 for F): points flow down the gradient lines of F, at unit speed in F, towards the level F = c\u2212\u03b5.';
      else if (s === 1) txt = 's = 1: everything lies in F\u207b\u00b9(\u2212\u221e, c\u2212\u03b5] = M\u1d9c\u207b\u1d4b \u222a H.';
      else if (s < 2) txt = 'Assertion 4: Milnor\u2019s r\u209c, t = ' + (s - 1).toFixed(2) + '. Case 1 (\u03be \u2264 \u03b5) squeezes onto the cell, Case 2 slides onto f = c\u2212\u03b5, Case 3 (M\u1d9c\u207b\u1d4b) stays put.';
      else txt = 's = 2: everything lies in M\u1d9c\u207b\u1d4b \u222a e\u00b9, which is a deformation retract of M\u1d9c\u207a\u1d4b.';
      readout.textContent = txt;
    }

    if (window.addEventListener) window.addEventListener('resize', schedule);
    setup();
  }

  function init() {
    var root = document.getElementById(ID);
    if (!root || root.getAttribute('data-ready') === '1') return;
    root.setAttribute('data-ready', '1');
    build(root);
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init);
  else init();
})();
