/* fig7-geodesics.js: interactive figure for Chapter 7 (Milnor, "Morse Theory", section 10).
 *
 * The unit sphere with base point p.  Thin curves: radial geodesics t -> exp_p(t v).  Dashed
 * circle: the shell S_t(p), drawn with a small right-angle mark where it crosses the highlighted
 * geodesic (Gauss lemma).  Thick curve: gamma(t) = exp_p(t v) for the chosen direction v and
 * length t; the part up to the antipode -p is minimal (accent colour), the part beyond is not
 * (dashed).  The inset plots the length t against the distance rho(p, gamma(t)) = min(t, 2 pi - t).
 *
 * Plain JavaScript, no libraries.  Looks for <div id="geodesics-figure">.  Colours come from the
 * CSS variables --fg, --bg, --accent, --muted (with fallbacks).
 */
(function () {
  'use strict';

  var root = document.getElementById('geodesics-figure');
  if (!root) return;

  var PI = Math.PI, TWO_PI = 2 * Math.PI;

  function cssVar(name, fallback) {
    var v = '';
    try { v = getComputedStyle(root).getPropertyValue(name); } catch (e) { v = ''; }
    v = v ? v.trim() : '';
    return v || fallback;
  }

  function palette() {
    return {
      fg: cssVar('--fg', '#1f1f1d'),
      bg: cssVar('--bg', '#ffffff'),
      accent: cssVar('--accent', '#2a78d6'),
      muted: cssVar('--muted', '#8a8984')
    };
  }

  /* ------------------------------------------------------------------ geometry */

  /* exp_p(t v) on the unit sphere, p = (0, 0, 1), v = (cos phi, sin phi, 0). */
  function geo(phi, t) {
    var s = Math.sin(t);
    return [s * Math.cos(phi), s * Math.sin(phi), Math.cos(t)];
  }

  /* Velocity of the unit-speed geodesic above at time t. */
  function geoVel(phi, t) {
    var c = Math.cos(t);
    return [c * Math.cos(phi), c * Math.sin(phi), -Math.sin(t)];
  }

  /* Orthographic view: the north pole is tipped towards the viewer by the angle a.
     Returns [screen x, screen y (up), depth (>= 0 means visible)]. */
  function proj(P, a) {
    var ca = Math.cos(a), sa = Math.sin(a);
    return [P[0], -P[1] * sa + P[2] * ca, P[1] * ca + P[2] * sa];
  }

  /* ------------------------------------------------------------------ DOM */

  var state = { dir: 70, len: 2.0, tilt: 25 };

  var box = document.createElement('div');
  box.style.maxWidth = '720px';
  box.style.margin = '0 auto';
  box.style.font = '14px/1.45 system-ui, -apple-system, "Segoe UI", sans-serif';
  root.appendChild(box);

  var canvas = document.createElement('canvas');
  canvas.style.display = 'block';
  canvas.style.width = '100%';
  canvas.setAttribute('role', 'img');
  canvas.setAttribute('aria-label',
    'Geodesics from a point p of the unit sphere, and the distance from p along one of them');
  box.appendChild(canvas);

  var readout = document.createElement('div');
  readout.style.margin = '0.45rem 0 0.5rem';
  readout.setAttribute('aria-live', 'polite');
  box.appendChild(readout);

  function addSlider(key, label, min, max, step, fmt) {
    var row = document.createElement('label');
    row.style.display = 'flex';
    row.style.flexWrap = 'wrap';
    row.style.alignItems = 'center';
    row.style.gap = '0.5rem';
    row.style.margin = '0.2rem 0';
    var name = document.createElement('span');
    name.textContent = label;
    name.style.minWidth = '5.5rem';
    var input = document.createElement('input');
    input.type = 'range';
    input.min = String(min);
    input.max = String(max);
    input.step = String(step);
    input.value = String(state[key]);
    input.style.flex = '1 1 150px';
    input.style.minWidth = '120px';
    var val = document.createElement('span');
    val.style.minWidth = '4.2rem';
    val.style.fontVariantNumeric = 'tabular-nums';
    val.textContent = fmt(state[key]);
    input.addEventListener('input', function () {
      state[key] = parseFloat(input.value);
      val.textContent = fmt(state[key]);
      draw();
    });
    row.appendChild(name);
    row.appendChild(input);
    row.appendChild(val);
    box.appendChild(row);
  }

  addSlider('len', 'length t', 0, 6.28, 0.01, function (x) { return x.toFixed(2); });
  addSlider('dir', 'direction', 0, 360, 1, function (x) { return Math.round(x) + '°'; });
  addSlider('tilt', 'tilt', 0, 80, 1, function (x) { return Math.round(x) + '°'; });

  /* ------------------------------------------------------------------ drawing helpers */

  /* Stroke a polyline on the sphere: solid (or with visDash) where visible, faint where hidden. */
  function strokeCurve(ctx, pts, view, colour, width, visDash, hidAlpha) {
    var n = pts.length, S = [], V = [], i, j;
    if (n < 2) return;
    for (i = 0; i < n; i++) {
      var q = proj(pts[i], view.a);
      S.push([view.cx + view.R * q[0], view.cy - view.R * q[1]]);
      V.push(q[2] >= 0);
    }
    var start = 0;
    for (i = 1; i <= n; i++) {
      if (i === n || V[i] !== V[start]) {
        var end = Math.min(i, n - 1);
        if (end > start) {
          ctx.save();
          ctx.beginPath();
          ctx.moveTo(S[start][0], S[start][1]);
          for (j = start + 1; j <= end; j++) ctx.lineTo(S[j][0], S[j][1]);
          ctx.strokeStyle = colour;
          ctx.lineCap = 'round';
          if (V[start]) {
            ctx.lineWidth = width;
            ctx.setLineDash(visDash || []);
          } else {
            ctx.lineWidth = Math.max(1, 0.65 * width);
            ctx.setLineDash([2, 3]);
            ctx.globalAlpha = hidAlpha;
          }
          ctx.stroke();
          ctx.restore();
        }
        start = i;
      }
    }
  }

  function screen(P, view) {
    var q = proj(P, view.a);
    return { x: view.cx + view.R * q[0], y: view.cy - view.R * q[1], vis: q[2] >= 0 };
  }

  function dot(ctx, s, r, fill, stroke) {
    ctx.beginPath();
    ctx.arc(s.x, s.y, r, 0, TWO_PI);
    ctx.fillStyle = fill;
    ctx.fill();
    ctx.lineWidth = 1.3;
    ctx.strokeStyle = stroke;
    ctx.stroke();
  }

  function samples(f, a, b, n) {
    var out = [];
    for (var i = 0; i <= n; i++) out.push(f(a + (b - a) * i / n));
    return out;
  }

  /* ------------------------------------------------------------------ the two panels */

  function drawSphere(ctx, view, col) {
    var phi0 = state.dir * PI / 180, t = state.len, k;

    ctx.beginPath();
    ctx.arc(view.cx, view.cy, view.R, 0, TWO_PI);
    ctx.save();
    ctx.globalAlpha = 0.07;
    ctx.fillStyle = col.muted;
    ctx.fill();
    ctx.restore();
    ctx.lineWidth = 1.2;
    ctx.strokeStyle = col.fg;
    ctx.stroke();

    /* fan of radial geodesics from p */
    for (k = 0; k < 12; k++) {
      var ph = (30 * k + 15) * PI / 180;
      strokeCurve(ctx, samples(function (s) { return geo(ph, s); }, 0, PI, 90), view,
        col.muted, 0.9, null, 0.35);
    }

    /* the shell S_t(p): the circle at angular distance t from p */
    var sinT = Math.sin(t);
    if (Math.abs(sinT) > 0.01) {
      strokeCurve(ctx, samples(function (f) { return geo(f, t); }, 0, TWO_PI, 160), view,
        col.muted, 1.4, [6, 4], 0.4);
    }

    /* highlighted geodesic: minimal part and non-minimal part */
    var tMin = Math.min(t, PI);
    if (tMin > 0.001) {
      strokeCurve(ctx, samples(function (s) { return geo(phi0, s); }, 0, tMin, 160), view,
        col.accent, 3, null, 0.7);
    }
    if (t > PI) {
      strokeCurve(ctx, samples(function (s) { return geo(phi0, s); }, PI, t, 160), view,
        col.fg, 2.6, [7, 5], 0.6);
    }

    /* right-angle mark between the geodesic and the shell (Gauss lemma) */
    var G = geo(phi0, t);
    var g = screen(G, view);
    if (Math.abs(sinT) > 0.05 && g.vis) {
      /* T: velocity of the geodesic; E: unit tangent of the shell; both tangent at G, and
         orthogonal: T.E = cos t (-cos phi sin phi + sin phi cos phi) = 0. */
      var T = geoVel(phi0, t);
      var E = [-Math.sin(phi0), Math.cos(phi0), 0];
      var h = 0.09;
      var A = [G[0] - h * T[0], G[1] - h * T[1], G[2] - h * T[2]];
      var B = [A[0] + h * E[0], A[1] + h * E[1], A[2] + h * E[2]];
      var C = [G[0] + h * E[0], G[1] + h * E[1], G[2] + h * E[2]];
      var a1 = screen(A, view), b1 = screen(B, view), c1 = screen(C, view);
      ctx.beginPath();
      ctx.moveTo(a1.x, a1.y);
      ctx.lineTo(b1.x, b1.y);
      ctx.lineTo(c1.x, c1.y);
      ctx.lineWidth = 1.2;
      ctx.strokeStyle = col.fg;
      ctx.setLineDash([]);
      ctx.stroke();
    }

    /* points */
    var p = screen([0, 0, 1], view), mp = screen([0, 0, -1], view);
    ctx.font = '13px system-ui, -apple-system, "Segoe UI", sans-serif';
    ctx.textBaseline = 'middle';
    dot(ctx, p, 4, p.vis ? col.fg : col.bg, col.fg);
    ctx.fillStyle = col.fg;
    ctx.fillText('p', p.x + 7, p.y - 8);
    dot(ctx, mp, 4, mp.vis ? col.fg : col.bg, col.fg);
    ctx.fillStyle = col.fg;
    ctx.fillText(mp.vis ? '−p' : '−p (behind)', mp.x + 7, mp.y + 9);
    dot(ctx, g, 4.5, g.vis ? (t > PI ? col.fg : col.accent) : col.bg,
      t > PI ? col.fg : col.accent);
    ctx.fillStyle = col.fg;
    ctx.fillText('γ(t)', g.x + 8, g.y);
  }

  function drawPlot(ctx, box2, col) {
    var x0 = box2.x, y0 = box2.y, w = box2.w, h = box2.h;
    function X(t) { return x0 + w * t / TWO_PI; }
    function Y(v) { return y0 + h - h * v / TWO_PI; }
    var t = state.len;

    ctx.save();
    ctx.globalAlpha = 0.08;
    ctx.fillStyle = col.fg;
    ctx.fillRect(X(PI), y0, X(TWO_PI) - X(PI), h);
    ctx.restore();

    ctx.lineWidth = 1;
    ctx.strokeStyle = col.muted;
    ctx.setLineDash([]);
    ctx.strokeRect(x0, y0, w, h);

    ctx.beginPath();
    ctx.moveTo(X(0), Y(0));
    ctx.lineTo(X(TWO_PI), Y(TWO_PI));
    ctx.setLineDash([5, 4]);
    ctx.strokeStyle = col.muted;
    ctx.lineWidth = 1.3;
    ctx.stroke();

    ctx.beginPath();
    ctx.moveTo(X(0), Y(0));
    ctx.lineTo(X(PI), Y(PI));
    ctx.setLineDash([]);
    ctx.strokeStyle = col.accent;
    ctx.lineWidth = 2.6;
    ctx.stroke();

    ctx.beginPath();
    ctx.moveTo(X(PI), Y(PI));
    ctx.lineTo(X(TWO_PI), Y(0));
    ctx.setLineDash([7, 5]);
    ctx.strokeStyle = col.fg;
    ctx.lineWidth = 2.2;
    ctx.stroke();
    ctx.setLineDash([]);

    var rho = Math.min(t, TWO_PI - t);
    ctx.beginPath();
    ctx.moveTo(X(t), y0);
    ctx.lineTo(X(t), y0 + h);
    ctx.strokeStyle = col.muted;
    ctx.lineWidth = 1;
    ctx.stroke();
    dot(ctx, { x: X(t), y: Y(t) }, 3, col.bg, col.muted);
    dot(ctx, { x: X(t), y: Y(rho) }, 4.5, t > PI ? col.fg : col.accent, t > PI ? col.fg : col.accent);

    ctx.fillStyle = col.fg;
    ctx.font = '12px system-ui, -apple-system, "Segoe UI", sans-serif';
    ctx.textBaseline = 'top';
    ctx.textAlign = 'center';
    ctx.fillText('0', X(0), y0 + h + 4);
    ctx.fillText('π', X(PI), y0 + h + 4);
    ctx.fillText('2π', X(TWO_PI), y0 + h + 4);
    ctx.fillText('length t', x0 + w / 2, y0 + h + 18);
    ctx.textAlign = 'left';
    ctx.textBaseline = 'alphabetic';
    ctx.fillStyle = col.accent;
    ctx.fillText('distance ρ(p, γ(t))', x0 + 6, y0 + 15);
    ctx.fillStyle = col.muted;
    ctx.fillText('length of γ on [0, t]', x0 + 6, y0 + 31);
    ctx.textAlign = 'start';
  }

  function updateReadout() {
    var t = state.len, rho = Math.min(t, TWO_PI - t), msg;
    if (Math.abs(t - PI) < 0.006) {
      msg = 't = π: γ(t) = −p. Every geodesic of length π from p ends here ' +
        '(the first conjugate point); the shell has collapsed to a point.';
    } else if (t < PI) {
      msg = 'length ' + t.toFixed(2) + ' = distance ' + rho.toFixed(2) +
        ': this geodesic is minimal (Theorem 10.4 for short t; on the sphere, up to π).';
    } else {
      msg = 'length ' + t.toFixed(2) + ' > distance ' + rho.toFixed(2) +
        ': not minimal. The other arc of the same great circle has length 2π − t = ' +
        (TWO_PI - t).toFixed(2) + '.';
    }
    readout.textContent = msg;
  }

  /* ------------------------------------------------------------------ layout */

  function draw() {
    var col = palette();
    var W = Math.max(280, Math.min(720, box.clientWidth || root.clientWidth || 600));
    var wide = W >= 540;
    var sphereSize = wide ? Math.min(0.56 * W, 400) : W;
    var plotW = wide ? W - sphereSize - 50 : W - 60;
    var plotH = wide ? sphereSize - 70 : Math.round(0.55 * W);
    var H = wide ? sphereSize : sphereSize + plotH + 60;

    var dpr = window.devicePixelRatio || 1;
    canvas.width = Math.round(W * dpr);
    canvas.height = Math.round(H * dpr);
    canvas.style.height = H + 'px';
    var ctx = canvas.getContext('2d');
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, W, H);

    var view = { cx: sphereSize / 2, cy: sphereSize / 2, R: 0.42 * sphereSize,
      a: state.tilt * PI / 180 };
    drawSphere(ctx, view, col);

    var plotBox = wide
      ? { x: sphereSize + 30, y: 22, w: plotW, h: plotH }
      : { x: 40, y: sphereSize + 12, w: plotW, h: plotH };
    drawPlot(ctx, plotBox, col);
    updateReadout();
  }

  draw();
  window.addEventListener('resize', draw);
  if (window.matchMedia) {
    var mq = window.matchMedia('(prefers-color-scheme: dark)');
    if (mq.addEventListener) mq.addEventListener('change', draw);
    else if (mq.addListener) mq.addListener(draw);
  }
})();
