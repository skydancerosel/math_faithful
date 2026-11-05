/*
 * fig1-morse.js -- interactive figure for Chapter 1 (Milnor, Morse Theory, section 2).
 *
 * Contour lines of f(x, y) = a x^2 + b y^2 + g (x^3 - 3 x y^2) near the critical point 0,
 * the sublevel set {f < 0} shaded, and, when the critical point is non-degenerate, the Morse
 * coordinates (y1, y2) obtained by Milnor's completing-the-square step, drawn as a curved grid.
 *
 * Plain JavaScript, no libraries.  Finds <div id="morse-figure"> and builds a canvas with sliders.
 * Colours come from the CSS variables --fg, --bg, --accent, --muted (with fallbacks).
 */
(function () {
  'use strict';

  var ID = 'morse-figure';

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

  // ---------------------------------------------------------------- mathematics

  function fval(x, y, a, b, g) {
    return a * x * x + b * y * y + g * (x * x * x - 3 * x * y * y);
  }

  // Morse coordinates from the proof of Lemma 2.2.  For this cubic,
  // H11 = a + g x, H12 = -g y, H22 = b - g x and f = sum x_i x_j H_ij.
  // Pivot on the larger of |a|, |b|.  Returns [y1, y2, valid].
  function morse(x, y, a, b, g) {
    var H11 = a + g * x, H12 = -g * y, H22 = b - g * x;
    var D = H11 * H22 - H12 * H12;
    var piv, piv0, u, v;
    if (Math.abs(a) >= Math.abs(b)) {
      piv = H11; piv0 = a; u = x; v = y;
    } else {
      piv = H22; piv0 = b; u = y; v = x;
    }
    var rc = 0.45 * Math.min(Math.abs(a), Math.abs(b)) / Math.max(g, 1e-9);
    var valid = (piv * piv0 > 0) && (Math.abs(piv) > 0.3 * Math.abs(piv0)) &&
      (D * a * b > 0) && (Math.abs(D) > 0.3 * Math.abs(a * b)) && (x * x + y * y < rc * rc);
    if (!valid) return [NaN, NaN, false];
    var y1 = Math.sqrt(Math.abs(piv)) * (u + v * H12 / piv);
    var y2 = Math.sqrt(Math.abs(D / piv)) * v;
    return [y1, y2, true];
  }

  // marching squares on an (N+1) x (N+1) vertex grid; vals[i + j*(N+1)]
  var SEG = {
    1: [[3, 0]], 2: [[0, 1]], 3: [[3, 1]], 4: [[1, 2]], 6: [[0, 2]], 7: [[3, 2]],
    8: [[2, 3]], 9: [[0, 2]], 11: [[1, 2]], 12: [[1, 3]], 13: [[0, 1]], 14: [[3, 0]]
  };

  function contour(ctx, vals, N, level, X0, Y0, dx, dy, toPx) {
    var W = N + 1;
    ctx.beginPath();
    for (var j = 0; j < N; j++) {
      for (var i = 0; i < N; i++) {
        var v00 = vals[i + j * W], v10 = vals[i + 1 + j * W];
        var v11 = vals[i + 1 + (j + 1) * W], v01 = vals[i + (j + 1) * W];
        if (v00 !== v00 || v10 !== v10 || v11 !== v11 || v01 !== v01) continue; // NaN
        var c = (v00 > level ? 1 : 0) | (v10 > level ? 2 : 0) | (v11 > level ? 4 : 0) | (v01 > level ? 8 : 0);
        if (c === 0 || c === 15) continue;
        var segs;
        if (c === 5 || c === 10) {
          var centre = 0.25 * (v00 + v10 + v11 + v01);
          if (c === 5) segs = centre > level ? [[0, 1], [2, 3]] : [[3, 0], [1, 2]];
          else segs = centre > level ? [[3, 0], [1, 2]] : [[0, 1], [2, 3]];
        } else {
          segs = SEG[c];
        }
        var x0 = X0 + i * dx, y0 = Y0 + j * dy;
        for (var s = 0; s < segs.length; s++) {
          var p = edgePoint(segs[s][0], x0, y0, dx, dy, v00, v10, v11, v01, level);
          var q = edgePoint(segs[s][1], x0, y0, dx, dy, v00, v10, v11, v01, level);
          var P = toPx(p[0], p[1]), Q = toPx(q[0], q[1]);
          ctx.moveTo(P[0], P[1]);
          ctx.lineTo(Q[0], Q[1]);
        }
      }
    }
    ctx.stroke();
  }

  function frac(level, va, vb) {
    var d = vb - va;
    return d === 0 ? 0.5 : (level - va) / d;
  }

  function edgePoint(e, x0, y0, dx, dy, v00, v10, v11, v01, level) {
    if (e === 0) return [x0 + frac(level, v00, v10) * dx, y0];
    if (e === 1) return [x0 + dx, y0 + frac(level, v10, v11) * dy];
    if (e === 2) return [x0 + frac(level, v01, v11) * dx, y0 + dy];
    return [x0, y0 + frac(level, v00, v01) * dy];
  }

  // ---------------------------------------------------------------- figure

  function build(root) {
    var state = { a: -1, b: 0.6, g: 0.6, zoom: 0.55, grid: true };

    var wrap = el('div', { style: 'max-width:600px;margin:0 auto;font:14px/1.4 system-ui,-apple-system,Segoe UI,sans-serif;' }, root);
    var canvas = el('canvas', { style: 'display:block;width:100%;height:auto;border-radius:6px;', 'aria-label': 'Contour plot of f near a critical point' }, wrap);
    var readout = el('div', { style: 'margin:8px 2px 4px;min-height:2.8em;' }, wrap);
    var presets = el('div', { style: 'display:flex;flex-wrap:wrap;gap:6px;margin:4px 0 8px;' }, wrap);
    var controls = el('div', { style: 'display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:6px 14px;' }, wrap);

    function slider(label, min, max, step, value, onInput, fmt) {
      var box = el('label', { style: 'display:flex;flex-direction:column;gap:2px;' }, controls);
      var head = el('span', null, box);
      var input = el('input', { type: 'range', min: String(min), max: String(max), step: String(step), value: String(value), style: 'width:100%;' }, box);
      function show() { head.textContent = label + ' = ' + fmt(parseFloat(input.value)); }
      input.addEventListener('input', function () { onInput(parseFloat(input.value)); show(); schedule(); });
      show();
      return { input: input, show: show };
    }

    function fmt2(v) { return (v >= 0 ? '' : '\u2212') + Math.abs(v).toFixed(2); }
    function zoomR(z) { return 0.05 * Math.pow(30, z); } // window half-width, 0.05 ... 1.5

    var sa = slider('a', -1, 1, 0.01, state.a, function (v) { state.a = v; }, fmt2);
    var sb = slider('b', -1, 1, 0.01, state.b, function (v) { state.b = v; }, fmt2);
    var sg = slider('cubic term \u03b3', 0, 1.5, 0.01, state.g, function (v) { state.g = v; }, fmt2);
    var sz = slider('window half-width R', 0, 1, 0.005, state.zoom, function (v) { state.zoom = v; }, function (v) { return zoomR(v).toFixed(3); });

    var cbBox = el('label', { style: 'display:flex;align-items:center;gap:6px;' }, controls);
    var cb = el('input', { type: 'checkbox' }, cbBox);
    cb.checked = state.grid;
    el('span', { text: 'show Morse coordinates' }, cbBox);
    cb.addEventListener('change', function () { state.grid = cb.checked; schedule(); });

    function preset(name, a, b, g) {
      var btn = el('button', { type: 'button', text: name, style: 'font:inherit;padding:3px 10px;border-radius:5px;border:1px solid currentColor;background:transparent;color:inherit;cursor:pointer;' }, presets);
      btn.addEventListener('click', function () {
        state.a = a; state.b = b; state.g = g;
        sa.input.value = String(a); sb.input.value = String(b); sg.input.value = String(g);
        sa.show(); sb.show(); sg.show();
        schedule();
      });
    }
    preset('pit (index 0)', 1, 0.6, 0.6);
    preset('pass (index 1)', -1, 0.6, 0.6);
    preset('peak (index 2)', -1, -0.6, 0.6);
    preset('monkey saddle', 0, 0, 1);

    var pending = false;
    function schedule() {
      if (pending) return;
      pending = true;
      (window.requestAnimationFrame || function (cb2) { return setTimeout(cb2, 16); })(function () {
        pending = false;
        draw();
      });
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
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0);

      var a = state.a, b = state.b, g = state.g;
      if (Math.abs(a) < 0.005) a = 0;
      if (Math.abs(b) < 0.005) b = 0;
      var R = zoomR(state.zoom);
      function toPx(x, y) { return [(x + R) / (2 * R) * S, (R - y) / (2 * R) * S]; }

      ctx.globalAlpha = 1;
      ctx.fillStyle = bg;
      ctx.fillRect(0, 0, S, S);

      // shading of {f < 0}
      var cell = 3, nc = Math.ceil(S / cell);
      ctx.globalAlpha = 0.16;
      ctx.fillStyle = accent;
      ctx.beginPath();
      for (var pj = 0; pj < nc; pj++) {
        var yy = R - (pj + 0.5) * cell / S * 2 * R;
        for (var pi = 0; pi < nc; pi++) {
          var xx = -R + (pi + 0.5) * cell / S * 2 * R;
          if (fval(xx, yy, a, b, g) < 0) ctx.rect(pi * cell, pj * cell, cell, cell);
        }
      }
      ctx.fill();
      ctx.globalAlpha = 1;

      // contour data
      var N = 110, W = N + 1, d = 2 * R / N;
      var F = new Float64Array(W * W);
      var maxAbs = 0;
      for (var j = 0; j < W; j++) {
        for (var i = 0; i < W; i++) {
          var v = fval(-R + i * d, -R + j * d, a, b, g);
          F[i + j * W] = v;
          if (Math.abs(v) > maxAbs) maxAbs = Math.abs(v);
        }
      }

      // axes
      ctx.strokeStyle = muted;
      ctx.globalAlpha = 0.5;
      ctx.lineWidth = 1;
      ctx.beginPath();
      ctx.moveTo(0, S / 2); ctx.lineTo(S, S / 2);
      ctx.moveTo(S / 2, 0); ctx.lineTo(S / 2, S);
      ctx.stroke();
      ctx.globalAlpha = 1;

      // contours of f, quadratically spaced so that small ones near 0 are visible
      if (maxAbs > 0) {
        var L = 0.9 * maxAbs;
        ctx.strokeStyle = muted;
        ctx.lineWidth = 1;
        for (var k = 1; k <= 9; k++) {
          var lev = L * (k / 9) * (k / 9);
          contour(ctx, F, N, lev, -R, -R, d, d, toPx);
          contour(ctx, F, N, -lev, -R, -R, d, d, toPx);
        }
        ctx.strokeStyle = fg;
        ctx.lineWidth = 1.8;
        contour(ctx, F, N, 0, -R, -R, d, d, toPx);
      }

      // Morse coordinates
      var nondeg = (a !== 0 && b !== 0);
      var gridDrawn = false;
      if (nondeg && state.grid) {
        var Y1 = new Float64Array(W * W), Y2 = new Float64Array(W * W);
        var m = 0;
        for (var jj = 0; jj < W; jj++) {
          for (var ii = 0; ii < W; ii++) {
            var r = morse(-R + ii * d, -R + jj * d, a, b, g);
            Y1[ii + jj * W] = r[0];
            Y2[ii + jj * W] = r[1];
            if (r[2]) m = Math.max(m, Math.abs(r[0]), Math.abs(r[1]));
          }
        }
        if (m > 0) {
          gridDrawn = true;
          ctx.strokeStyle = accent;
          ctx.lineWidth = 1.1;
          for (var q = -6; q <= 6; q++) {
            contour(ctx, Y1, N, q * m / 6.5, -R, -R, d, d, toPx);
            contour(ctx, Y2, N, q * m / 6.5, -R, -R, d, d, toPx);
          }
        }
      }

      // the critical point
      ctx.fillStyle = fg;
      ctx.beginPath();
      ctx.arc(S / 2, S / 2, 3.5, 0, 2 * Math.PI);
      ctx.fill();

      // frame
      ctx.strokeStyle = muted;
      ctx.lineWidth = 1;
      ctx.strokeRect(0.5, 0.5, S - 1, S - 1);

      // readout
      var neg = (a < 0 ? 1 : 0) + (b < 0 ? 1 : 0);
      var nul = (a === 0 ? 1 : 0) + (b === 0 ? 1 : 0);
      var txt = 'Hessian at 0: diag(' + fmt2(2 * a) + ', ' + fmt2(2 * b) + ').  Index \u03bb = ' + neg +
        ', nullity = ' + nul + '.  ';
      if (nondeg) {
        txt += (gridDrawn ? 'Non-degenerate: the curved grid is the Morse chart, in which f = ' :
          (state.grid ? 'Non-degenerate (the Morse chart is too small to draw at this scale): in Morse coordinates f = ' : 'Non-degenerate: in Morse coordinates f = ')) +
          (a < 0 && b < 0 ? '\u2212(y\u00b9)\u00b2 \u2212 (y\u00b2)\u00b2.' : (a < 0 || b < 0 ? '\u2212(y\u00b9)\u00b2 + (y\u00b2)\u00b2.' : '(y\u00b9)\u00b2 + (y\u00b2)\u00b2.'));
      } else {
        txt += 'Degenerate: no Morse chart; the cubic term shapes the picture at every scale.';
      }
      readout.textContent = txt + '  Window [\u2212R, R]\u00b2 with R = ' + R.toFixed(3) + '.';
    }

    if (window.addEventListener) window.addEventListener('resize', schedule);
    draw();
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
