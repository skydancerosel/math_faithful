/* fig4-evolute.js: interactive figure for Chapter 4 (Milnor, "Morse Theory", section 6).
 *
 * Focal points of an ellipse (the wall of an oval room, semi-axes a = 10 m and b) and the
 * normals from a point p.  The feet of the normals are the critical points of
 * L_p(theta) = |x(theta) - p|^2; a foot has index 1 exactly when the centre of curvature there
 * lies between the foot and p (Milnor's Lemma 6.9).  The evolute is the set of focal points;
 * crossing it, two critical points merge and disappear.
 *
 * Plain JavaScript, no libraries.  Looks for <div id="evolute-figure">.  Colours come from the
 * CSS variables --fg, --bg, --accent, --muted (with fallbacks).
 */
(function () {
  'use strict';

  var TWO_PI = 2 * Math.PI;
  var SOUND = 343; /* speed of sound in air at 20 C, m/s */
  var A = 10;      /* semi-major axis, m */

  /* ------------------------------------------------------------------ mathematics */

  function wall(a, b, t) { return [a * Math.cos(t), b * Math.sin(t)]; }

  function inwardNormal(a, b, t) {
    var s = Math.sqrt(a * a * Math.sin(t) * Math.sin(t) + b * b * Math.cos(t) * Math.cos(t));
    return [-b * Math.cos(t) / s, -a * Math.sin(t) / s];
  }

  /* centre of curvature at x(t): the focal point of (M, x(t)) */
  function centre(a, b, t) {
    var c = a * a - b * b, ct = Math.cos(t), st = Math.sin(t);
    return [c / a * ct * ct * ct, -c / b * st * st * st];
  }

  /* (1/2) dL/dt and (1/2) d^2L/dt^2 for L(t) = |x(t) - p|^2 */
  function halfDL(a, b, p, t) {
    return (b * b - a * a) * Math.sin(t) * Math.cos(t) + a * p[0] * Math.sin(t) -
      b * p[1] * Math.cos(t);
  }
  function halfD2L(a, b, p, t) {
    return (b * b - a * a) * Math.cos(2 * t) + a * p[0] * Math.cos(t) + b * p[1] * Math.sin(t);
  }

  /* feet of the normals from p, with the Morse index of L_p there */
  function normals(a, b, p) {
    var n = 2880, h = TWO_PI / n, off = 0.000731, feet = [];
    for (var i = 0; i < n; i++) {
      /* the grid is shifted so that symmetric roots do not fall on grid points */
      var t0 = off + i * h, t1 = t0 + h;
      var g0 = halfDL(a, b, p, t0), g1 = halfDL(a, b, p, t1);
      if (g0 === 0 || g0 * g1 < 0) {
        var lo = t0, hi = t1, flo = g0;
        for (var k = 0; k < 60; k++) {
          var mid = 0.5 * (lo + hi), fm = halfDL(a, b, p, mid);
          if (flo * fm <= 0) { hi = mid; } else { lo = mid; flo = fm; }
        }
        var t = (0.5 * (lo + hi)) % TWO_PI, q = wall(a, b, t);
        var dup = false;
        for (var j = 0; j < feet.length; j++) {
          var dt = Math.abs(feet[j].t - t);
          if (Math.min(dt, TWO_PI - dt) < 1e-7) dup = true;
        }
        if (dup) continue;
        var d2 = halfD2L(a, b, p, t);
        feet.push({
          t: t, q: q, c: centre(a, b, t),
          d: Math.sqrt((q[0] - p[0]) * (q[0] - p[0]) + (q[1] - p[1]) * (q[1] - p[1])),
          index: d2 < 0 ? 1 : 0,
          degenerate: Math.abs(d2) < 2e-3 * a * a
        });
      }
    }
    return feet;
  }

  /* F(p) - F0 < 0 inside the evolute, > 0 outside; returned relative to F0 */
  function evoluteSide(a, b, p) {
    var F = Math.pow(a * Math.abs(p[0]), 2 / 3) + Math.pow(b * Math.abs(p[1]), 2 / 3);
    var F0 = Math.pow(a * a - b * b, 2 / 3);
    return (F - F0) / F0;
  }

  if (typeof module !== 'undefined' && module.exports) {
    module.exports = { normals: normals, centre: centre, evoluteSide: evoluteSide };
  }
  if (typeof document === 'undefined') return;

  /* ------------------------------------------------------------------ helpers */

  function cssVar(el, name, fallback) {
    var v = '';
    try { v = window.getComputedStyle(el).getPropertyValue(name); } catch (e) { v = ''; }
    v = (v || '').trim();
    return v || fallback;
  }

  function make(tag, style, text) {
    var e = document.createElement(tag);
    if (style) e.style.cssText = style;
    if (text !== undefined) e.textContent = text;
    return e;
  }

  /* ------------------------------------------------------------------ the figure */

  function init() {
    var root = document.getElementById('evolute-figure');
    if (!root || root.getAttribute('data-built')) return;
    root.setAttribute('data-built', '1');

    var state = { b: 6, px: 3, py: 2, s: 0 };

    var box = make('div', 'max-width:640px;margin:0 auto;font:14px/1.45 system-ui,-apple-system,' +
      'Segoe UI,Roboto,sans-serif;color:var(--fg,#222);');
    var room = make('canvas', 'display:block;width:100%;touch-action:none;cursor:crosshair;');
    var graph = make('canvas', 'display:block;width:100%;margin-top:6px;');
    var readout = make('div', 'margin:6px 0 8px;font-size:13px;');
    var presets = make('div', 'display:flex;flex-wrap:wrap;gap:6px;margin:6px 0;');
    var controls = make('div', 'display:grid;grid-template-columns:1fr;gap:4px;');
    box.appendChild(room);
    box.appendChild(graph);
    box.appendChild(readout);
    box.appendChild(presets);
    box.appendChild(controls);
    root.appendChild(box);

    var sliders = {};
    function slider(key, label, min, max, step, fmt) {
      var row = make('label', 'display:block;font-size:13px;');
      var head = make('div', 'display:flex;justify-content:space-between;');
      head.appendChild(make('span', '', label));
      var val = make('span', 'font-variant-numeric:tabular-nums;');
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
        draw();
      });
      val.textContent = fmt(state[key]);
      row.appendChild(head);
      row.appendChild(input);
      controls.appendChild(row);
      sliders[key] = { input: input, val: val, fmt: fmt };
    }
    function sync(key) {
      sliders[key].input.value = String(state[key]);
      sliders[key].val.textContent = sliders[key].fmt(state[key]);
    }
    function preset(label, s) {
      var btn = make('button', 'font:inherit;font-size:13px;padding:4px 10px;border-radius:4px;' +
        'border:1px solid var(--muted,#888);background:var(--bg,#fff);color:var(--fg,#222);' +
        'cursor:pointer;', label);
      btn.type = 'button';
      btn.addEventListener('click', function () {
        for (var key in s) {
          if (Object.prototype.hasOwnProperty.call(s, key)) { state[key] = s[key]; sync(key); }
        }
        draw();
      });
      presets.appendChild(btn);
    }

    var m1 = function (v) { return v.toFixed(1) + ' m'; };
    var m2 = function (v) { return v.toFixed(2) + ' m'; };
    slider('px', 'listener p, first coordinate', -11.5, 11.5, 0.05, m2);
    slider('py', 'listener p, second coordinate', -11.5, 11.5, 0.05, m2);
    slider('b', 'half-width of the room b (a = 10 m)', 3, 9.5, 0.1, m1);
    slider('s', 'wavefront: distance travelled from the wall', 0, 12, 0.05, m2);
    preset('Centre', { b: 6, px: 0, py: 0 });
    preset('p = (5, 0)', { b: 6, px: 5, py: 0 });
    preset('A focus, (8, 0)', { b: 6, px: 8, py: 0 });
    preset('p = (3, 2)', { b: 6, px: 3, py: 2 });

    var view = null; /* current world-to-screen map of the room canvas */

    function draw() {
      var fg = cssVar(root, '--fg', '#222222');
      var bg = cssVar(root, '--bg', '#ffffff');
      var accent = cssVar(root, '--accent', '#c0392b');
      var muted = cssVar(root, '--muted', '#888888');
      var a = A, b = state.b, p = [state.px, state.py];
      var feet = normals(a, b, p);
      var dpr = window.devicePixelRatio || 1;

      /* ---------- the room ---------- */
      var W = Math.max(260, Math.min(640, box.clientWidth || root.clientWidth || 360));
      var Xmax = 11.5, Ymax = Math.max(1.2 * b, 7.5);
      var H = Math.round(W * Ymax / Xmax);
      room.width = Math.round(W * dpr);
      room.height = Math.round(H * dpr);
      room.style.height = H + 'px';
      var ctx = room.getContext('2d');
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
      ctx.clearRect(0, 0, W, H);
      var k = W / (2 * Xmax);
      view = { W: W, H: H, k: k };
      function sx(X) { return W / 2 + X * k; }
      function sy(Y) { return H / 2 - Y * k; }
      var t, i, P, Q;

      /* floor and wall */
      ctx.beginPath();
      for (i = 0; i <= 240; i++) {
        t = i / 240 * TWO_PI;
        P = wall(a, b, t);
        if (i === 0) ctx.moveTo(sx(P[0]), sy(P[1])); else ctx.lineTo(sx(P[0]), sy(P[1]));
      }
      ctx.closePath();
      ctx.globalAlpha = 0.08;
      ctx.fillStyle = muted;
      ctx.fill();
      ctx.globalAlpha = 1;
      ctx.strokeStyle = fg;
      ctx.lineWidth = 2.5;
      ctx.stroke();

      /* wavefront: the parallel curve at distance s along the inward normals */
      if (state.s > 0.001) {
        ctx.beginPath();
        for (i = 0; i <= 720; i++) {
          t = i / 720 * TWO_PI;
          P = wall(a, b, t);
          var nu = inwardNormal(a, b, t);
          var X = P[0] + state.s * nu[0], Y = P[1] + state.s * nu[1];
          if (i === 0) ctx.moveTo(sx(X), sy(Y)); else ctx.lineTo(sx(X), sy(Y));
        }
        ctx.strokeStyle = muted;
        ctx.lineWidth = 1.3;
        ctx.stroke();
      }

      /* evolute = focal set */
      ctx.beginPath();
      for (i = 0; i <= 720; i++) {
        t = i / 720 * TWO_PI;
        P = centre(a, b, t);
        if (i === 0) ctx.moveTo(sx(P[0]), sy(P[1])); else ctx.lineTo(sx(P[0]), sy(P[1]));
      }
      ctx.setLineDash([5, 4]);
      ctx.strokeStyle = accent;
      ctx.lineWidth = 1.5;
      ctx.stroke();
      ctx.setLineDash([]);

      /* normals from p, feet, centres of curvature */
      for (i = 0; i < feet.length; i++) {
        var f = feet[i], col = f.index === 1 ? fg : accent;
        ctx.beginPath();
        ctx.moveTo(sx(p[0]), sy(p[1]));
        ctx.lineTo(sx(f.q[0]), sy(f.q[1]));
        ctx.setLineDash(f.index === 1 ? [6, 4] : []);
        ctx.strokeStyle = col;
        ctx.lineWidth = 2;
        ctx.stroke();
        ctx.setLineDash([]);
        ctx.beginPath();
        ctx.arc(sx(f.q[0]), sy(f.q[1]), 3.5, 0, TWO_PI);
        ctx.fillStyle = col;
        ctx.fill();
        ctx.beginPath();
        ctx.arc(sx(f.c[0]), sy(f.c[1]), 4.5, 0, TWO_PI);
        ctx.fillStyle = bg;
        ctx.fill();
        ctx.lineWidth = 1.6;
        ctx.strokeStyle = col;
        ctx.stroke();
      }

      /* the listener */
      ctx.beginPath();
      ctx.arc(sx(p[0]), sy(p[1]), 7, 0, TWO_PI);
      ctx.fillStyle = accent;
      ctx.fill();
      ctx.lineWidth = 2;
      ctx.strokeStyle = bg;
      ctx.stroke();
      ctx.beginPath();
      ctx.arc(sx(p[0]), sy(p[1]), 9, 0, TWO_PI);
      ctx.lineWidth = 1;
      ctx.strokeStyle = fg;
      ctx.stroke();
      ctx.fillStyle = fg;
      ctx.font = '12px system-ui, sans-serif';
      ctx.textAlign = 'left';
      ctx.textBaseline = 'top';
      ctx.fillText('drag p', 6, 4);

      /* ---------- distance along the wall ---------- */
      var GW = W, GH = Math.round(Math.max(150, 0.42 * W));
      graph.width = Math.round(GW * dpr);
      graph.height = Math.round(GH * dpr);
      graph.style.height = GH + 'px';
      var g = graph.getContext('2d');
      g.setTransform(dpr, 0, 0, dpr, 0, 0);
      g.clearRect(0, 0, GW, GH);
      var ML = 40, MR = 10, MT = 8, MB = 34, PW = GW - ML - MR, PH = GH - MT - MB;
      var dist = [], dmax = 0;
      for (i = 0; i <= 360; i++) {
        t = i / 360 * TWO_PI;
        Q = wall(a, b, t);
        var dd = Math.sqrt((Q[0] - p[0]) * (Q[0] - p[0]) + (Q[1] - p[1]) * (Q[1] - p[1]));
        dist.push(dd);
        if (dd > dmax) dmax = dd;
      }
      var top = Math.max(5, 5 * Math.ceil(dmax / 5));
      function gx(tt) { return ML + tt / TWO_PI * PW; }
      function gy(dd) { return MT + PH - dd / top * PH; }
      g.strokeStyle = muted;
      g.lineWidth = 1;
      g.strokeRect(ML + 0.5, MT + 0.5, PW - 1, PH - 1);
      g.fillStyle = fg;
      g.font = '11px system-ui, sans-serif';
      g.textAlign = 'center';
      g.textBaseline = 'top';
      var tl = ['0', '\u03c0/2', '\u03c0', '3\u03c0/2', '2\u03c0'];
      for (i = 0; i <= 4; i++) g.fillText(tl[i], gx(i * Math.PI / 2), MT + PH + 3);
      g.fillText('position \u03b8 on the wall', ML + PW / 2, MT + PH + 18);
      g.textAlign = 'right';
      g.textBaseline = 'middle';
      for (var yv = 0; yv <= top; yv += (top > 20 ? 10 : 5)) g.fillText(String(yv), ML - 4, gy(yv));
      g.save();
      g.translate(11, MT + PH / 2);
      g.rotate(-Math.PI / 2);
      g.textAlign = 'center';
      g.fillText('distance (m)', 0, 0);
      g.restore();
      g.beginPath();
      for (i = 0; i <= 360; i++) {
        if (i === 0) g.moveTo(gx(i / 360 * TWO_PI), gy(dist[i]));
        else g.lineTo(gx(i / 360 * TWO_PI), gy(dist[i]));
      }
      g.strokeStyle = fg;
      g.lineWidth = 1.6;
      g.stroke();
      for (i = 0; i < feet.length; i++) {
        var F2 = feet[i], X2 = gx(F2.t), Y2 = gy(F2.d);
        g.beginPath();
        if (F2.index === 0) {
          g.arc(X2, Y2, 4.5, 0, TWO_PI);
          g.fillStyle = accent;
          g.fill();
        } else {
          g.moveTo(X2, Y2 - 6);
          g.lineTo(X2 + 5, Y2 + 3.5);
          g.lineTo(X2 - 5, Y2 + 3.5);
          g.closePath();
          g.fillStyle = bg;
          g.fill();
          g.strokeStyle = fg;
          g.lineWidth = 1.5;
          g.stroke();
        }
      }

      /* ---------- readout ---------- */
      var c0 = 0, c1 = 0, degenerate = false, delays = [];
      var sorted = feet.slice().sort(function (u, v) { return u.d - v.d; });
      for (i = 0; i < sorted.length; i++) {
        if (sorted[i].index === 0) c0++; else c1++;
        if (sorted[i].degenerate) degenerate = true;
        delays.push((2000 * sorted[i].d / SOUND).toFixed(1) + (sorted[i].index === 1 ? ' (index 1)' : ''));
      }
      var side = evoluteSide(a, b, p);
      var inRoom = (p[0] * p[0]) / (a * a) + (p[1] * p[1]) / (b * b) < 1;
      var where = Math.abs(side) < 0.01 ? 'on (or very near) the evolute' :
        (side < 0 ? 'inside the evolute' : 'outside the evolute');
      var html = 'p = (' + p[0].toFixed(2) + ', ' + p[1].toFixed(2) + ') m is ' + where + '. ' +
        'Normals from p: <b>' + feet.length + '</b> (' + c0 + ' of index 0, solid; ' + c1 +
        ' of index 1, dashed). C<sub>0</sub> \u2212 C<sub>1</sub> = ' + (c0 - c1) + '.<br>';
      if (degenerate || Math.abs(side) < 0.01) {
        html += '<span style="color:' + muted + '">p is close to a focal point: L<sub>p</sub> has a ' +
          'nearly degenerate critical point, and two normals are about to merge.</span><br>';
      }
      if (inRoom) {
        html += 'Echo delays, 2|p \u2212 q| / (343 m/s): ' + delays.join(', ') + ' ms.';
      } else {
        html += 'p is outside the room: the normals are still the critical points of L<sub>p</sub>, ' +
          'but they are not echoes.';
      }
      readout.innerHTML = html;
    }

    /* dragging p */
    var dragging = false;
    function moveTo(ev) {
      if (!view) return;
      var rect = room.getBoundingClientRect();
      var X = (ev.clientX - rect.left - view.W / 2) / view.k;
      var Y = (view.H / 2 - (ev.clientY - rect.top)) / view.k;
      state.px = Math.max(-11.5, Math.min(11.5, Math.round(X * 20) / 20));
      state.py = Math.max(-11.5, Math.min(11.5, Math.round(Y * 20) / 20));
      sync('px');
      sync('py');
      draw();
    }
    room.addEventListener('pointerdown', function (ev) {
      dragging = true;
      try { room.setPointerCapture(ev.pointerId); } catch (e) { /* ignore */ }
      moveTo(ev);
      ev.preventDefault();
    });
    room.addEventListener('pointermove', function (ev) { if (dragging) moveTo(ev); });
    room.addEventListener('pointerup', function () { dragging = false; });
    room.addEventListener('pointercancel', function () { dragging = false; });

    draw();
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
