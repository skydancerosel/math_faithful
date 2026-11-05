/*
 * fig5-lefschetz.js - interactive figure for Chapter 5 (Milnor, "Morse Theory", section 7).
 *
 * Left panel: the normal space at q = 0. For the complex curve w = z^2/2 in C^2 it is the
 * w-plane, and the focal points of (M, q) form the circle |P| = 1. For the real paraboloid
 * h = (x^2 + y^2)/2 in R^3 it is the h-axis, with one double focal point at height 1.
 * Drag the observer p (or use the sliders).
 * Right panel: banded contour map of the distance from p to the surface, over the parameter
 * plane, with the critical points of L_p marked. The complex curve never shows index 2.
 *
 * Plain JavaScript, no libraries. Colours come from the CSS variables --fg, --bg, --accent,
 * --muted (with fallbacks).
 */
(function () {
  'use strict';

  var LIM = 2.4;          // half-width of both panels, in model units
  var SPAN = 3.4;         // distance range covered by the contour bands
  var NBANDS = 16;

  function cssVar(el, name, fallback) {
    var v = getComputedStyle(el).getPropertyValue(name);
    v = v ? v.trim() : '';
    return v || fallback;
  }

  var colorCtx = null;
  function rgb(str) {
    if (!colorCtx) colorCtx = document.createElement('canvas').getContext('2d');
    colorCtx.fillStyle = '#000000';
    colorCtx.fillStyle = str;
    var s = colorCtx.fillStyle;
    if (s.charAt(0) === '#') {
      return [parseInt(s.substr(1, 2), 16), parseInt(s.substr(3, 2), 16), parseInt(s.substr(5, 2), 16)];
    }
    var m = s.match(/[\d.]+/g) || [0, 0, 0];
    return [Number(m[0]), Number(m[1]), Number(m[2])];
  }
  function mix(a, b, t) {
    return [Math.round(a[0] + (b[0] - a[0]) * t), Math.round(a[1] + (b[1] - a[1]) * t),
      Math.round(a[2] + (b[2] - a[2]) * t)];
  }
  function css(c) { return 'rgb(' + c[0] + ',' + c[1] + ',' + c[2] + ')'; }

  function el(tag, attrs, parent) {
    var e = document.createElement(tag);
    if (attrs) {
      for (var k in attrs) {
        if (k === 'style') e.style.cssText = attrs[k];
        else if (k === 'text') e.textContent = attrs[k];
        else e.setAttribute(k, attrs[k]);
      }
    }
    if (parent) parent.appendChild(e);
    return e;
  }

  function fmt(x) { return (Math.abs(x) < 0.005 ? 0 : x).toFixed(2); }

  function init() {
    var root = document.getElementById('lefschetz-figure');
    if (!root || root.getAttribute('data-ready')) return;
    root.setAttribute('data-ready', '1');

    var state = { mode: 'complex', R: 1.6, theta: 0.6, h: 1.6 };

    var wrap = el('div', {
      style: 'font-family: system-ui, -apple-system, "Segoe UI", sans-serif; font-size: 14px;' +
        'color: var(--fg, #0b0b0b); max-width: 760px; margin: 0.5em 0;'
    }, root);

    // mode buttons
    var bar = el('div', { style: 'display:flex; flex-wrap:wrap; gap:8px; margin-bottom:8px;' }, wrap);
    var btnC = el('button', { type: 'button', text: 'Complex curve w = z\u00b2/2' }, bar);
    var btnR = el('button', { type: 'button', text: 'Real paraboloid h = (x\u00b2+y\u00b2)/2' }, bar);
    [btnC, btnR].forEach(function (b) {
      b.style.cssText = 'font: inherit; padding: 6px 10px; border-radius: 6px; cursor: pointer;' +
        'border: 1px solid var(--muted, #898781); background: var(--bg, #fcfcfb); color: var(--fg, #0b0b0b);';
    });

    var panels = el('div', { style: 'display:flex; flex-wrap:wrap; gap:12px;' }, wrap);
    var boxL = el('div', {}, panels);
    var capL = el('div', { style: 'font-size:13px; margin-bottom:4px; color: var(--fg, #0b0b0b);' }, boxL);
    var canL = el('canvas', { role: 'img', 'aria-label': 'Normal space at q with focal points and the observer p' }, boxL);
    var boxR = el('div', {}, panels);
    var capR = el('div', { style: 'font-size:13px; margin-bottom:4px; color: var(--fg, #0b0b0b);' }, boxR);
    var canR = el('canvas', { role: 'img', 'aria-label': 'Contour map of the distance from p, with critical points' }, boxR);
    canL.style.touchAction = 'none';
    canL.style.cursor = 'crosshair';

    // sliders
    var ctl = el('div', { style: 'display:grid; grid-template-columns: auto 1fr auto; gap:6px 10px; align-items:center; margin-top:10px; max-width: 560px;' }, wrap);
    function slider(label, min, max, step) {
      var lab = el('label', { text: label, style: 'white-space:nowrap;' }, ctl);
      var inp = el('input', { type: 'range', min: min, max: max, step: step, style: 'width:100%;' }, ctl);
      var out = el('span', { style: 'font-variant-numeric: tabular-nums; min-width: 3.5em; text-align:right;' }, ctl);
      return { lab: lab, inp: inp, out: out };
    }
    var sR = slider('distance |P|', 0, 2.4, 0.01);
    var sT = slider('direction arg P (\u00b0)', 0, 360, 1);
    var sH = slider('height P', -2.4, 2.4, 0.01);

    var read = el('div', { style: 'margin-top:10px; line-height:1.45; font-size:13.5px;', 'aria-live': 'polite' }, wrap);

    var size = 320;
    var dpr = Math.max(1, Math.min(2, window.devicePixelRatio || 1));
    var off = document.createElement('canvas');

    function layout() {
      var W = root.clientWidth || 360;
      size = W >= 600 ? Math.min(370, Math.floor((W - 12) / 2)) : Math.min(W, 420);
      size = Math.max(220, size);
      [canL, canR].forEach(function (c) {
        c.width = Math.round(size * dpr);
        c.height = Math.round(size * dpr);
        c.style.width = size + 'px';
        c.style.height = size + 'px';
        c.style.display = 'block';
        c.style.borderRadius = '6px';
      });
      draw();
    }

    function colors() {
      var fg = cssVar(root, '--fg', '#0b0b0b');
      var bg = cssVar(root, '--bg', '#fcfcfb');
      var accent = cssVar(root, '--accent', '#eb6834');
      var muted = cssVar(root, '--muted', '#898781');
      return { fg: fg, bg: bg, accent: accent, muted: muted,
        fgR: rgb(fg), bgR: rgb(bg), acR: rgb(accent), muR: rgb(muted) };
    }

    // model -> canvas coordinates (CSS pixels)
    function toPx(x, y) { return [(x + LIM) / (2 * LIM) * size, (LIM - y) / (2 * LIM) * size]; }
    function fromPx(px, py) { return [px / size * 2 * LIM - LIM, LIM - py / size * 2 * LIM]; }

    function P() { return [state.R * Math.cos(state.theta), state.R * Math.sin(state.theta)]; }

    // squared distance from p to the surface point with parameter (x, y)
    function Lfun(x, y) {
      if (state.mode === 'complex') {
        var p = P();
        var zr = x * x - y * y, zi = 2 * x * y;           // z^2
        var dr = zr / 2 - p[0], di = zi / 2 - p[1];      // z^2/2 - P
        return x * x + y * y + dr * dr + di * di;
      }
      var r2 = x * x + y * y, d = r2 / 2 - state.h;
      return r2 + d * d;
    }

    function label(ctx, text, x, y, c, align) {
      ctx.font = '12px system-ui, -apple-system, "Segoe UI", sans-serif';
      ctx.textAlign = align || 'left';
      ctx.textBaseline = 'middle';
      var w = ctx.measureText(text).width;
      var x0 = align === 'center' ? x - w / 2 : (align === 'right' ? x - w : x);
      ctx.fillStyle = c.bg;
      ctx.globalAlpha = 0.85;
      ctx.fillRect(x0 - 3, y - 8, w + 6, 16);
      ctx.globalAlpha = 1;
      ctx.fillStyle = c.fg;
      ctx.fillText(text, x, y);
    }

    function marker(ctx, kind, x, y, c) {
      var q = toPx(x, y);
      ctx.lineWidth = 2;
      if (kind === 'min') {
        ctx.beginPath(); ctx.arc(q[0], q[1], 6.5, 0, 2 * Math.PI); ctx.fillStyle = c.bg; ctx.fill();
        ctx.beginPath(); ctx.arc(q[0], q[1], 4.5, 0, 2 * Math.PI); ctx.fillStyle = c.fg; ctx.fill();
      } else if (kind === 'saddle') {
        ctx.strokeStyle = c.bg; ctx.lineWidth = 6;
        ctx.beginPath(); ctx.moveTo(q[0] - 6, q[1] - 6); ctx.lineTo(q[0] + 6, q[1] + 6);
        ctx.moveTo(q[0] - 6, q[1] + 6); ctx.lineTo(q[0] + 6, q[1] - 6); ctx.stroke();
        ctx.strokeStyle = c.fg; ctx.lineWidth = 2.5; ctx.stroke();
      } else if (kind === 'max') {
        ctx.beginPath(); ctx.moveTo(q[0], q[1] - 9); ctx.lineTo(q[0] + 8, q[1] + 6); ctx.lineTo(q[0] - 8, q[1] + 6);
        ctx.closePath(); ctx.fillStyle = c.bg; ctx.fill();
        ctx.beginPath(); ctx.moveTo(q[0], q[1] - 6); ctx.lineTo(q[0] + 5.5, q[1] + 4); ctx.lineTo(q[0] - 5.5, q[1] + 4);
        ctx.closePath(); ctx.fillStyle = c.fg; ctx.fill();
      } else { // degenerate
        ctx.beginPath(); ctx.arc(q[0], q[1], 5.5, 0, 2 * Math.PI); ctx.strokeStyle = c.fg; ctx.lineWidth = 2; ctx.stroke();
      }
    }

    function drawLeft(c) {
      var ctx = canL.getContext('2d');
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
      ctx.fillStyle = c.bg; ctx.fillRect(0, 0, size, size);
      var shade = css(mix(c.bgR, c.muR, 0.16));
      var o = toPx(0, 0), unit = size / (2 * LIM);
      ctx.strokeStyle = css(mix(c.bgR, c.muR, 0.6)); ctx.lineWidth = 1;
      if (state.mode === 'complex') {
        capL.textContent = 'Normal plane at q (the w-axis, a copy of \u2102)';
        ctx.fillStyle = shade; ctx.fillRect(0, 0, size, size);
        ctx.beginPath(); ctx.arc(o[0], o[1], unit, 0, 2 * Math.PI); ctx.fillStyle = c.bg; ctx.fill();
        ctx.beginPath(); ctx.moveTo(0, o[1]); ctx.lineTo(size, o[1]); ctx.moveTo(o[0], 0); ctx.lineTo(o[0], size);
        ctx.strokeStyle = css(mix(c.bgR, c.muR, 0.6)); ctx.stroke();
        ctx.beginPath(); ctx.arc(o[0], o[1], unit, 0, 2 * Math.PI); ctx.strokeStyle = c.accent; ctx.lineWidth = 2.5; ctx.stroke();
        label(ctx, 'index 0', o[0], o[1] + 0.5 * unit, c, 'center');
        label(ctx, 'index 1 (saddle)', 8, 14, c, 'left');
        label(ctx, 'focal circle |P| = 1', o[0] + 0.62 * unit, o[1] + 1.15 * unit, c, 'left');
        label(ctx, 'Re P', size - 6, o[1] + 12, c, 'right');
        label(ctx, 'Im P', o[0] + 6, size - 12, c, 'left');
        var p = toPx(P()[0], P()[1]);
        ctx.beginPath(); ctx.arc(p[0], p[1], 8.5, 0, 2 * Math.PI); ctx.fillStyle = c.bg; ctx.fill();
        ctx.beginPath(); ctx.arc(p[0], p[1], 6.5, 0, 2 * Math.PI); ctx.fillStyle = c.accent; ctx.fill();
        label(ctx, 'p', p[0] + 11, p[1] - 10, c, 'left');
      } else {
        capL.textContent = 'Cross-section of the paraboloid; the normal line at q is vertical';
        // shade the part of the normal line beyond the double focal point
        var f = toPx(0, 1);
        ctx.fillStyle = shade; ctx.fillRect(0, 0, size, f[1]);
        ctx.beginPath(); ctx.moveTo(0, o[1]); ctx.lineTo(size, o[1]); ctx.moveTo(o[0], 0); ctx.lineTo(o[0], size);
        ctx.strokeStyle = css(mix(c.bgR, c.muR, 0.6)); ctx.lineWidth = 1; ctx.stroke();
        ctx.beginPath();
        for (var i = 0; i <= 200; i++) {
          var x = -LIM + 2 * LIM * i / 200, pt = toPx(x, x * x / 2);
          if (i === 0) ctx.moveTo(pt[0], pt[1]); else ctx.lineTo(pt[0], pt[1]);
        }
        ctx.strokeStyle = c.fg; ctx.lineWidth = 2; ctx.stroke();
        // osculating circle at q: centre (0, 1), radius 1
        ctx.beginPath(); ctx.arc(f[0], f[1], unit, 0, 2 * Math.PI);
        ctx.setLineDash([4, 4]); ctx.strokeStyle = css(mix(c.bgR, c.muR, 0.9)); ctx.lineWidth = 1; ctx.stroke(); ctx.setLineDash([]);
        ctx.beginPath(); ctx.arc(f[0], f[1], 5, 0, 2 * Math.PI); ctx.strokeStyle = c.accent; ctx.lineWidth = 2.5; ctx.stroke();
        label(ctx, 'double focal point', f[0] + 10, f[1] + 2, c, 'left');
        label(ctx, 'index 2 (maximum)', 8, 14, c, 'left');
        label(ctx, 'index 0', 8, o[1] + 16, c, 'left');
        var ph = toPx(0, state.h);
        ctx.beginPath(); ctx.arc(ph[0], ph[1], 8.5, 0, 2 * Math.PI); ctx.fillStyle = c.bg; ctx.fill();
        ctx.beginPath(); ctx.arc(ph[0], ph[1], 6.5, 0, 2 * Math.PI); ctx.fillStyle = c.accent; ctx.fill();
        label(ctx, 'p', ph[0] - 12, ph[1] - 10, c, 'right');
      }
      // q
      ctx.beginPath(); ctx.arc(o[0], o[1], 4, 0, 2 * Math.PI); ctx.fillStyle = c.fg; ctx.fill();
      label(ctx, 'q', o[0] - 10, o[1] + 12, c, 'right');
    }

    function drawRight(c) {
      var n = Math.max(120, Math.round(size));
      off.width = n; off.height = n;
      var octx = off.getContext('2d');
      var img = octx.createImageData(n, n);
      var D = new Float64Array(n * n), dmin = Infinity;
      var i, j, k = 0;
      for (j = 0; j < n; j++) {
        var y = LIM - (j + 0.5) / n * 2 * LIM;
        for (i = 0; i < n; i++, k++) {
          var x = -LIM + (i + 0.5) / n * 2 * LIM;
          var d = Math.sqrt(Lfun(x, y));
          D[k] = d;
          if (d < dmin) dmin = d;
        }
      }
      var pal = [];
      for (var b = 0; b <= NBANDS; b++) pal.push(mix(c.bgR, c.acR, 0.06 + 0.66 * b / NBANDS));
      var B = new Int16Array(n * n);
      for (k = 0; k < n * n; k++) {
        var s = Math.min(1, Math.max(0, (D[k] - dmin) / SPAN));
        B[k] = Math.min(NBANDS, Math.floor(Math.sqrt(s) * NBANDS));
      }
      var iso = [];
      for (b = 0; b <= NBANDS; b++) iso.push(mix(pal[b], c.bgR, 0.55));
      for (j = 0; j < n; j++) {
        for (i = 0; i < n; i++) {
          k = j * n + i;
          var edge = (i + 1 < n && B[k + 1] !== B[k]) || (j + 1 < n && B[k + n] !== B[k]);
          var col = edge ? iso[B[k]] : pal[B[k]];
          img.data[4 * k] = col[0]; img.data[4 * k + 1] = col[1]; img.data[4 * k + 2] = col[2]; img.data[4 * k + 3] = 255;
        }
      }
      octx.putImageData(img, 0, 0);
      var ctx = canR.getContext('2d');
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
      ctx.imageSmoothingEnabled = true;
      ctx.drawImage(off, 0, 0, size, size);
      var o = toPx(0, 0);
      ctx.strokeStyle = css(mix(c.bgR, c.muR, 0.5)); ctx.lineWidth = 1;
      ctx.beginPath(); ctx.moveTo(0, o[1]); ctx.lineTo(size, o[1]); ctx.moveTo(o[0], 0); ctx.lineTo(o[0], size); ctx.stroke();

      var lines = [];
      if (state.mode === 'complex') {
        capR.textContent = 'Distance from p to the curve, over the z-plane';
        var R = state.R;
        if (Math.abs(R - 1) < 0.015) {
          marker(ctx, 'degenerate', 0, 0, c);
          label(ctx, 'q: degenerate (p is focal)', o[0] + 10, o[1] - 14, c, 'left');
          lines.push('q is a degenerate critical point: p lies on the focal circle.');
        } else if (R < 1) {
          marker(ctx, 'min', 0, 0, c);
          label(ctx, 'q: minimum', o[0] + 10, o[1] - 14, c, 'left');
          lines.push('Critical points of L_p: q only, a minimum (index 0).');
        } else {
          marker(ctx, 'saddle', 0, 0, c);
          var rr = Math.sqrt(2 * (R - 1)), a = state.theta / 2;
          var z1 = [rr * Math.cos(a), rr * Math.sin(a)];
          marker(ctx, 'min', z1[0], z1[1], c);
          marker(ctx, 'min', -z1[0], -z1[1], c);
          var m1 = toPx(z1[0], z1[1]), m2 = toPx(-z1[0], -z1[1]);
          label(ctx, 'min', m1[0] + 10, m1[1] - 12, c, 'left');
          label(ctx, 'min', m2[0] - 10, m2[1] + 14, c, 'right');
          label(ctx, 'q: saddle', o[0] + 10, o[1] + 16, c, 'left');
          lines.push('Critical points of L_p: q is a saddle (index 1); two minima at z = \u00b1' +
            fmt(rr) + '\u00b7e^(i\u00b7' + fmt(a) + ').');
        }
        read.innerHTML = '';
        el('div', { text: 'Hessian of L_p at q: eigenvalues 2(1 \u2212 |P|) = ' + fmt(2 * (1 - R)) +
          ' and 2(1 + |P|) = ' + fmt(2 * (1 + R)) + '.' }, read);
        el('div', { text: lines[0] }, read);
        el('div', { text: 'However far p moves, the second eigenvalue stays \u2265 2: the index is at most 1 = k.',
          style: 'color: var(--muted, #898781);' }, read);
      } else {
        capR.textContent = 'Distance from p to the paraboloid, over the (x, y)-plane';
        var h = state.h;
        if (Math.abs(h - 1) < 0.015) {
          marker(ctx, 'degenerate', 0, 0, c);
          label(ctx, 'q: degenerate (p is focal)', o[0] + 10, o[1] - 14, c, 'left');
          lines.push('q is a degenerate critical point: p is the double focal point.');
        } else if (h < 1) {
          marker(ctx, 'min', 0, 0, c);
          label(ctx, 'q: minimum', o[0] + 10, o[1] - 14, c, 'left');
          lines.push('Critical points of L_p: q only, a minimum (index 0).');
        } else {
          var r = Math.sqrt(2 * (h - 1)), u = size / (2 * LIM);
          ctx.beginPath(); ctx.arc(o[0], o[1], r * u, 0, 2 * Math.PI);
          ctx.setLineDash([5, 4]); ctx.strokeStyle = c.fg; ctx.lineWidth = 2; ctx.stroke(); ctx.setLineDash([]);
          marker(ctx, 'max', 0, 0, c);
          label(ctx, 'q: maximum', o[0] + 12, o[1] - 14, c, 'left');
          label(ctx, 'ring of minima', o[0], Math.min(size - 10, o[1] + r * u + 14), c, 'center');
          lines.push('Critical points of L_p: q is a local maximum (index 2); a circle of minima of radius ' + fmt(r) + '.');
        }
        read.innerHTML = '';
        el('div', { text: 'Hessian of L_p at q: both eigenvalues equal 2(1 \u2212 P) = ' + fmt(2 * (1 - h)) + '.' }, read);
        el('div', { text: lines[0] }, read);
        el('div', { text: 'Both principal curvatures have the same sign, so beyond the focal point the index jumps to 2.',
          style: 'color: var(--muted, #898781);' }, read);
      }
    }

    function syncControls() {
      var cx = state.mode === 'complex';
      [sR, sT].forEach(function (s) { s.lab.style.display = s.inp.style.display = s.out.style.display = cx ? '' : 'none'; });
      sH.lab.style.display = sH.inp.style.display = sH.out.style.display = cx ? 'none' : '';
      sR.inp.value = state.R; sR.out.textContent = fmt(state.R);
      var deg = ((state.theta * 180 / Math.PI) % 360 + 360) % 360;
      sT.inp.value = Math.round(deg); sT.out.textContent = Math.round(deg) + '\u00b0';
      sH.inp.value = state.h; sH.out.textContent = fmt(state.h);
      btnC.style.fontWeight = cx ? '600' : '400';
      btnR.style.fontWeight = cx ? '400' : '600';
      btnC.setAttribute('aria-pressed', cx ? 'true' : 'false');
      btnR.setAttribute('aria-pressed', cx ? 'false' : 'true');
      btnC.style.borderColor = cx ? 'var(--accent, #eb6834)' : 'var(--muted, #898781)';
      btnR.style.borderColor = cx ? 'var(--muted, #898781)' : 'var(--accent, #eb6834)';
    }

    function draw() {
      var c = colors();
      syncControls();
      drawLeft(c);
      drawRight(c);
    }

    // interaction
    var dragging = false;
    function setFromEvent(ev) {
      var r = canL.getBoundingClientRect();
      var m = fromPx(ev.clientX - r.left, ev.clientY - r.top);
      if (state.mode === 'complex') {
        state.R = Math.min(LIM, Math.sqrt(m[0] * m[0] + m[1] * m[1]));
        state.theta = Math.atan2(m[1], m[0]);
      } else {
        state.h = Math.max(-LIM, Math.min(LIM, m[1]));
      }
      draw();
    }
    canL.addEventListener('pointerdown', function (ev) {
      dragging = true;
      if (canL.setPointerCapture) canL.setPointerCapture(ev.pointerId);
      setFromEvent(ev);
      ev.preventDefault();
    });
    canL.addEventListener('pointermove', function (ev) { if (dragging) setFromEvent(ev); });
    canL.addEventListener('pointerup', function () { dragging = false; });
    canL.addEventListener('pointercancel', function () { dragging = false; });

    sR.inp.addEventListener('input', function () { state.R = Number(sR.inp.value); draw(); });
    sT.inp.addEventListener('input', function () { state.theta = Number(sT.inp.value) * Math.PI / 180; draw(); });
    sH.inp.addEventListener('input', function () { state.h = Number(sH.inp.value); draw(); });
    btnC.addEventListener('click', function () { state.mode = 'complex'; draw(); });
    btnR.addEventListener('click', function () { state.mode = 'real'; draw(); });

    var timer = null;
    window.addEventListener('resize', function () {
      if (timer) clearTimeout(timer);
      timer = setTimeout(layout, 120);
    });
    if (window.matchMedia) {
      var mq = window.matchMedia('(prefers-color-scheme: dark)');
      if (mq.addEventListener) mq.addEventListener('change', draw);
    }
    layout();
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init);
  else init();
})();
