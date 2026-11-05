/* fig3-torus.js: interactive figure for Chapter 3 (Milnor, "Morse Theory", sections 4-5).
 *
 * A Morse function on the torus, V(phi, psi) = (1 - cos k phi)/2 + B (1 - cos k psi)/2
 * - kappa cos(phi - psi - delta).  The program finds the critical points numerically,
 * classifies them by index, checks the Morse inequalities of the torus (C0 >= 1,
 * C1 - C0 >= 1, C0 - C1 + C2 = 0) and shades a sublevel set M^a.
 *
 * Plain JavaScript, no libraries.  Looks for <div id="torus-figure">.  Colours come from the
 * CSS variables --fg, --bg, --accent, --muted (with fallbacks).
 */
(function () {
  'use strict';

  var TWO_PI = 2 * Math.PI;

  /* ------------------------------------------------------------------ mathematics */

  function model(p) {
    var k = p.k, B = p.B, kap = p.kap, del = p.del;
    return {
      V: function (x, y) {
        return 0.5 * (1 - Math.cos(k * x)) + 0.5 * B * (1 - Math.cos(k * y)) -
          kap * Math.cos(x - y - del);
      },
      grad: function (x, y) {
        var s = kap * Math.sin(x - y - del);
        return [0.5 * k * Math.sin(k * x) + s, 0.5 * B * k * Math.sin(k * y) - s];
      },
      hess: function (x, y) { /* returns [Vxx, Vxy, Vyy] */
        var c = kap * Math.cos(x - y - del);
        return [0.5 * k * k * Math.cos(k * x) + c, -c, 0.5 * B * k * k * Math.cos(k * y) + c];
      }
    };
  }

  function wrapAngle(a) {
    a = a % TWO_PI;
    return a < 0 ? a + TWO_PI : a;
  }

  function torusDist(a, b) {
    var d = Math.abs(wrapAngle(a) - wrapAngle(b));
    return Math.min(d, TWO_PI - d);
  }

  /* Damped Newton iteration for grad V = 0. Returns [x, y] in [0, 2pi)^2 or null. */
  function newton(m, x, y) {
    for (var it = 0; it < 80; it++) {
      var g = m.grad(x, y), h = m.hess(x, y);
      var det = h[0] * h[2] - h[1] * h[1];
      if (!isFinite(det) || Math.abs(det) < 1e-14) return null;
      var dx = (h[2] * g[0] - h[1] * g[1]) / det;
      var dy = (-h[1] * g[0] + h[0] * g[1]) / det;
      var st = Math.sqrt(dx * dx + dy * dy);
      if (st > 0.08) { dx *= 0.08 / st; dy *= 0.08 / st; }
      x -= dx; y -= dy;
      var g2 = m.grad(x, y);
      if (Math.abs(g2[0]) + Math.abs(g2[1]) < 1e-12) return [wrapAngle(x), wrapAngle(y)];
    }
    return null;
  }

  /* Critical points: grid cells in which both partial derivatives change sign are refined by
   * Newton's method (from the cell centre, and from its corners if the centre fails). */
  function criticalPoints(p) {
    var m = model(p), n = 96, h = TWO_PI / n, off = 1e-3, i, j;
    var gx = new Float64Array(n * n), gy = new Float64Array(n * n), pts = [];
    for (i = 0; i < n; i++) {
      for (j = 0; j < n; j++) {
        var g = m.grad(i * h + off, j * h + off);
        gx[i * n + j] = g[0];
        gy[i * n + j] = g[1];
      }
    }
    function add(z) {
      if (!z) return false;
      for (var q = 0; q < pts.length; q++) {
        if (torusDist(pts[q].x, z[0]) < 1e-5 && torusDist(pts[q].y, z[1]) < 1e-5) return true;
      }
      var hh = m.hess(z[0], z[1]);
      var det = hh[0] * hh[2] - hh[1] * hh[1], tr = hh[0] + hh[2];
      var sc = Math.abs(hh[0]) + Math.abs(hh[2]) + 2 * Math.abs(hh[1]) + 1e-12;
      pts.push({
        x: z[0], y: z[1],
        index: det < 0 ? 1 : (tr > 0 ? 0 : 2),
        degenerate: Math.abs(det) < 2e-3 * sc * sc,
        v: m.V(z[0], z[1])
      });
      return true;
    }
    for (i = 0; i < n; i++) {
      for (j = 0; j < n; j++) {
        var i2 = (i + 1) % n, j2 = (j + 1) % n;
        var a0 = gx[i * n + j], a1 = gx[i2 * n + j], a2 = gx[i * n + j2], a3 = gx[i2 * n + j2];
        var b0 = gy[i * n + j], b1 = gy[i2 * n + j], b2 = gy[i * n + j2], b3 = gy[i2 * n + j2];
        if (Math.min(a0, a1, a2, a3) > 0 || Math.max(a0, a1, a2, a3) < 0) continue;
        if (Math.min(b0, b1, b2, b3) > 0 || Math.max(b0, b1, b2, b3) < 0) continue;
        var cx = (i + 0.5) * h + off, cy = (j + 0.5) * h + off;
        var z = newton(m, cx, cy);
        if (!z || torusDist(z[0], cx) > 2 * h || torusDist(z[1], cy) > 2 * h) {
          add(z);
          add(newton(m, i * h + off, j * h + off));
          add(newton(m, (i + 1) * h + off, j * h + off));
          add(newton(m, i * h + off, (j + 1) * h + off));
          add(newton(m, (i + 1) * h + off, (j + 1) * h + off));
        } else {
          add(z);
        }
      }
    }
    return pts;
  }

  function counts(pts, level) {
    var c = [0, 0, 0], degenerate = false;
    for (var q = 0; q < pts.length; q++) {
      if (level === undefined || pts[q].v <= level) c[pts[q].index] += 1;
      if (pts[q].degenerate) degenerate = true;
    }
    return { c: c, degenerate: degenerate };
  }

  /* Export the mathematics for testing under Node; do nothing else there. */
  if (typeof module !== 'undefined' && module.exports) {
    module.exports = { model: model, criticalPoints: criticalPoints, counts: counts };
  }
  if (typeof document === 'undefined') return;

  /* ------------------------------------------------------------------ drawing helpers */

  function cssVar(el, name, fallback) {
    var v = '';
    try { v = window.getComputedStyle(el).getPropertyValue(name); } catch (e) { v = ''; }
    v = (v || '').trim();
    return v || fallback;
  }

  var probe = null;
  function toRGB(c) {
    if (!probe) { probe = document.createElement('canvas'); probe.width = 1; probe.height = 1; }
    var cx = probe.getContext('2d');
    cx.clearRect(0, 0, 1, 1);
    cx.fillStyle = '#808080';
    cx.fillStyle = c;
    cx.fillRect(0, 0, 1, 1);
    var d = cx.getImageData(0, 0, 1, 1).data;
    return [d[0], d[1], d[2]];
  }

  function mix(a, b, t) {
    return [a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t, a[2] + (b[2] - a[2]) * t];
  }

  function make(tag, style, text) {
    var e = document.createElement(tag);
    if (style) e.style.cssText = style;
    if (text !== undefined) e.textContent = text;
    return e;
  }

  /* ------------------------------------------------------------------ the figure */

  function init() {
    var root = document.getElementById('torus-figure');
    if (!root || root.getAttribute('data-built')) return;
    root.setAttribute('data-built', '1');

    var state = { k: 3, B: 1, kap: 0, del: 0, level: 0.35 };
    var pts = [], vmin = 0, vmax = 1, grid = null, N = 120;
    var O = -Math.PI / 6; /* the square shows [O, O + 2pi]^2, a fundamental domain */

    var box = make('div', 'max-width:640px;margin:0 auto;font:14px/1.45 system-ui,-apple-system,' +
      'Segoe UI,Roboto,sans-serif;color:var(--fg,#222);');
    var canvas = make('canvas', 'display:block;width:100%;');
    var legend = make('div', 'margin:6px 0 2px;font-size:13px;');
    var readout = make('div', 'margin:4px 0 8px;font-size:13px;');
    var presets = make('div', 'display:flex;flex-wrap:wrap;gap:6px;margin:6px 0;');
    var controls = make('div', 'display:grid;grid-template-columns:1fr;gap:4px;');
    box.appendChild(canvas);
    box.appendChild(legend);
    box.appendChild(readout);
    box.appendChild(presets);
    box.appendChild(controls);
    root.appendChild(box);

    function button(label, onClick) {
      var b = make('button', 'font:inherit;font-size:13px;padding:4px 10px;border-radius:4px;' +
        'border:1px solid var(--muted,#888);background:var(--bg,#fff);color:var(--fg,#222);' +
        'cursor:pointer;', label);
      b.type = 'button';
      b.addEventListener('click', onClick);
      presets.appendChild(b);
    }

    var sliders = {};
    function slider(key, label, min, max, step, fmt, heavy) {
      var row = make('label', 'display:block;font-size:13px;');
      var head = make('div', 'display:flex;justify-content:space-between;');
      var name = make('span', '', label);
      var val = make('span', 'font-variant-numeric:tabular-nums;');
      head.appendChild(name);
      head.appendChild(val);
      var input = make('input', 'width:100%;margin:2px 0 4px;accent-color:var(--accent,#c0392b);');
      input.type = 'range';
      input.min = String(min);
      input.max = String(max);
      input.step = String(step);
      input.value = String(state[key]);
      input.setAttribute('aria-label', label);
      input.addEventListener('input', function () {
        state[key] = parseFloat(input.value);
        val.textContent = fmt(state[key]);
        if (heavy) recompute(); else draw();
      });
      val.textContent = fmt(state[key]);
      row.appendChild(head);
      row.appendChild(input);
      controls.appendChild(row);
      sliders[key] = { input: input, val: val, fmt: fmt };
    }

    function setState(s) {
      for (var key in s) {
        if (Object.prototype.hasOwnProperty.call(s, key)) {
          state[key] = s[key];
          if (sliders[key]) {
            sliders[key].input.value = String(s[key]);
            sliders[key].val.textContent = sliders[key].fmt(s[key]);
          }
        }
      }
      recompute();
    }

    button('Double pendulum', function () { setState({ k: 1, B: 0.5, kap: 0, del: 0 }); });
    button('Two rotors', function () { setState({ k: 3, B: 1, kap: 0, del: 0 }); });

    var f2 = function (v) { return v.toFixed(2); };
    slider('k', 'wells per rotor k', 1, 3, 1, function (v) { return String(v); }, true);
    slider('B', 'second barrier B', 0.2, 1.5, 0.05, f2, true);
    slider('kap', 'coupling \u03ba', -3, 3, 0.05, f2, true);
    slider('del', 'phase \u03b4', 0, 3.14, 0.02, f2, true);
    slider('level', 'level a (fraction of the range of V)', 0, 1, 0.005, f2, false);

    function recompute() {
      var m = model(state), i, j;
      grid = new Float64Array((N + 1) * (N + 1));
      vmin = Infinity; vmax = -Infinity;
      for (i = 0; i <= N; i++) {
        for (j = 0; j <= N; j++) {
          var v = m.V(O + i * TWO_PI / N, O + j * TWO_PI / N);
          grid[i * (N + 1) + j] = v;
          if (v < vmin) vmin = v;
          if (v > vmax) vmax = v;
        }
      }
      pts = criticalPoints(state);
      for (i = 0; i < pts.length; i++) {
        vmin = Math.min(vmin, pts[i].v);
        vmax = Math.max(vmax, pts[i].v);
      }
      if (vmax - vmin < 1e-9) vmax = vmin + 1e-9;
      draw();
    }

    function draw() {
      var fg = cssVar(root, '--fg', '#222222');
      var bg = cssVar(root, '--bg', '#ffffff');
      var accent = cssVar(root, '--accent', '#c0392b');
      var muted = cssVar(root, '--muted', '#888888');
      var fgRGB = toRGB(fg), bgRGB = toRGB(bg), acRGB = toRGB(accent);

      var W = Math.max(260, Math.min(640, box.clientWidth || root.clientWidth || 360));
      var ML = 44, MR = 8, MT = 8, MB = 32;
      var S = W - ML - MR;
      var H = S + MT + MB;
      var dpr = window.devicePixelRatio || 1;
      canvas.width = Math.round(W * dpr);
      canvas.height = Math.round(H * dpr);
      canvas.style.height = H + 'px';
      var ctx = canvas.getContext('2d');
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
      ctx.clearRect(0, 0, W, H);

      var level = vmin + state.level * (vmax - vmin);
      var m = model(state);

      /* heat map of V, fading into the background where V is low; sublevel set tinted */
      var R = 128;
      var off = document.createElement('canvas');
      off.width = R; off.height = R;
      var octx = off.getContext('2d');
      var img = octx.createImageData(R, R);
      for (var py = 0; py < R; py++) {
        for (var px = 0; px < R; px++) {
          var x = O + (px + 0.5) / R * TWO_PI, y = O + (R - py - 0.5) / R * TWO_PI;
          var v = m.V(x, y);
          var t = (v - vmin) / (vmax - vmin);
          var col = mix(bgRGB, fgRGB, 0.06 + 0.62 * t);
          if (v <= level) col = mix(col, acRGB, 0.38);
          var o = 4 * (py * R + px);
          img.data[o] = col[0]; img.data[o + 1] = col[1]; img.data[o + 2] = col[2];
          img.data[o + 3] = 255;
        }
      }
      octx.putImageData(img, 0, 0);
      ctx.imageSmoothingEnabled = true;
      ctx.drawImage(off, ML, MT, S, S);

      function sx(x) { return ML + (x - O) / TWO_PI * S; }
      function sy(y) { return MT + S - (y - O) / TWO_PI * S; }
      function rx(x) { return O + wrapAngle(x - O); } /* representative in [O, O + 2pi) */

      /* boundary of the sublevel set: marching squares on the periodic grid */
      ctx.save();
      ctx.beginPath();
      ctx.rect(ML, MT, S, S);
      ctx.clip();
      ctx.strokeStyle = accent;
      ctx.lineWidth = 1.6;
      ctx.beginPath();
      var hcell = TWO_PI / N;
      for (var i = 0; i < N; i++) {
        for (var j = 0; j < N; j++) {
          var v0 = grid[i * (N + 1) + j], v1 = grid[(i + 1) * (N + 1) + j];
          var v2 = grid[(i + 1) * (N + 1) + j + 1], v3 = grid[i * (N + 1) + j + 1];
          var e = [];
          var x0 = O + i * hcell, y0 = O + j * hcell;
          if ((v0 <= level) !== (v1 <= level)) e.push([x0 + hcell * (level - v0) / (v1 - v0), y0]);
          if ((v1 <= level) !== (v2 <= level)) e.push([x0 + hcell, y0 + hcell * (level - v1) / (v2 - v1)]);
          if ((v3 <= level) !== (v2 <= level)) e.push([x0 + hcell * (level - v3) / (v2 - v3), y0 + hcell]);
          if ((v0 <= level) !== (v3 <= level)) e.push([x0, y0 + hcell * (level - v0) / (v3 - v0)]);
          if (e.length >= 2) {
            ctx.moveTo(sx(e[0][0]), sy(e[0][1]));
            ctx.lineTo(sx(e[1][0]), sy(e[1][1]));
          }
          if (e.length === 4) {
            ctx.moveTo(sx(e[2][0]), sy(e[2][1]));
            ctx.lineTo(sx(e[3][0]), sy(e[3][1]));
          }
        }
      }
      ctx.stroke();
      ctx.restore();

      /* frame and ticks */
      ctx.strokeStyle = fg;
      ctx.lineWidth = 1;
      ctx.strokeRect(ML + 0.5, MT + 0.5, S - 1, S - 1);
      ctx.fillStyle = fg;
      ctx.font = '12px system-ui, sans-serif';
      ctx.textAlign = 'center';
      ctx.textBaseline = 'top';
      var labels = ['0', '\u03c0/2', '\u03c0', '3\u03c0/2'];
      for (var q = 0; q <= 3; q++) {
        ctx.fillText(labels[q], sx(q * Math.PI / 2), MT + S + 4);
      }
      ctx.fillText('\u03c6', ML + S / 2 + S / 8, MT + S + 17);
      ctx.textAlign = 'right';
      ctx.textBaseline = 'middle';
      for (q = 0; q <= 3; q++) {
        ctx.fillText(labels[q], ML - 4, sy(q * Math.PI / 2));
      }
      ctx.textAlign = 'left';
      ctx.fillText('\u03c8', 2, MT + S / 2 - S / 8);

      /* critical points; a marker straddling an edge is drawn on both glued sides */
      var r = Math.max(4, S / 75);
      function drawMarker(P, X, Y) {
        if (P.degenerate) {
          ctx.strokeStyle = muted;
          ctx.lineWidth = 2;
          ctx.beginPath();
          ctx.arc(X, Y, 2.2 * r, 0, TWO_PI);
          ctx.stroke();
        }
        if (P.index === 0) {
          ctx.fillStyle = accent;
          ctx.strokeStyle = bg;
          ctx.lineWidth = 1.5;
          ctx.beginPath();
          ctx.arc(X, Y, r, 0, TWO_PI);
          ctx.fill();
          ctx.stroke();
        } else if (P.index === 1) {
          ctx.strokeStyle = bg;
          ctx.lineWidth = 4;
          ctx.beginPath();
          ctx.moveTo(X - r, Y - r); ctx.lineTo(X + r, Y + r);
          ctx.moveTo(X - r, Y + r); ctx.lineTo(X + r, Y - r);
          ctx.stroke();
          ctx.strokeStyle = fg;
          ctx.lineWidth = 2;
          ctx.stroke();
        } else {
          ctx.fillStyle = bg;
          ctx.strokeStyle = fg;
          ctx.lineWidth = 1.6;
          ctx.beginPath();
          ctx.moveTo(X, Y - 1.25 * r);
          ctx.lineTo(X + 1.1 * r, Y + 0.75 * r);
          ctx.lineTo(X - 1.1 * r, Y + 0.75 * r);
          ctx.closePath();
          ctx.fill();
          ctx.stroke();
        }
      }
      ctx.save();
      ctx.beginPath();
      ctx.rect(ML, MT, S, S);
      ctx.clip();
      for (q = 0; q < pts.length; q++) {
        var P = pts[q], X0 = sx(rx(P.x)), Y0 = sy(rx(P.y));
        var xs = [X0], ys = [Y0];
        if (X0 - ML < 2.5 * r) xs.push(X0 + S);
        if (ML + S - X0 < 2.5 * r) xs.push(X0 - S);
        if (Y0 - MT < 2.5 * r) ys.push(Y0 + S);
        if (MT + S - Y0 < 2.5 * r) ys.push(Y0 - S);
        for (var a1 = 0; a1 < xs.length; a1++) {
          for (var b1 = 0; b1 < ys.length; b1++) drawMarker(P, xs[a1], ys[b1]);
        }
      }
      ctx.restore();

      legend.innerHTML =
        '<span style="color:' + accent + '">\u25cf</span> minimum (index 0) &nbsp; ' +
        '<b>\u2715</b> saddle (index 1) &nbsp; \u25b3 maximum (index 2) &nbsp; ' +
        '<span style="color:' + accent + '">\u2014</span> boundary of M<sup>a</sup>';

      var all = counts(pts), below = counts(pts, level);
      var C = all.c, b = below.c;
      function ok(flag) {
        return flag ? '<span style="color:' + fg + '">holds</span>' :
          '<b style="color:' + accent + '">fails</b>';
      }
      var html = 'C<sub>0</sub> = ' + C[0] + ' minima, C<sub>1</sub> = ' + C[1] +
        ' saddles, C<sub>2</sub> = ' + C[2] + ' maxima.<br>' +
        'C<sub>0</sub> \u2265 1: ' + ok(C[0] >= 1) + '; ' +
        'C<sub>1</sub> \u2212 C<sub>0</sub> = ' + (C[1] - C[0]) + ' \u2265 1: ' + ok(C[1] - C[0] >= 1) +
        '; C<sub>0</sub> \u2212 C<sub>1</sub> + C<sub>2</sub> = ' + (C[0] - C[1] + C[2]) +
        ' (must be 0): ' + ok(C[0] - C[1] + C[2] === 0) + '.<br>';
      if (all.degenerate) {
        html += '<span style="color:' + muted + '">A critical point (ringed) is nearly degenerate: ' +
          'V is close to not being a Morse function here, and the counts are about to change.</span><br>';
      }
      html += 'Level a = ' + level.toFixed(3) + ': below it lie ' + b[0] + ' minima, ' + b[1] +
        ' saddles, ' + b[2] + ' maxima, so \u03c7(M<sup>a</sup>) = ' + (b[0] - b[1] + b[2]) + '.';
      readout.innerHTML = html;
    }

    recompute();
    var pending = false;
    window.addEventListener('resize', function () {
      if (pending) return;
      pending = true;
      window.requestAnimationFrame(function () { pending = false; draw(); });
    });
    if (window.matchMedia) {
      try {
        window.matchMedia('(prefers-color-scheme: dark)').addEventListener('change', draw);
      } catch (e) { /* older browsers: ignore */ }
    }
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }
})();
