/*
 * fig6-transport.js - interactive figure for Chapter 6 (Milnor, "Morse Theory", sections 8-9).
 *
 * Parallel transport on the unit sphere along a circle of latitude phi0, traversed eastward.
 * A vector starts pointing north; by the solution of the transport equations in \u00a78 of the
 * chapter, after travelling t radians of longitude it is
 *     V(t) = cos(t sin phi0) * north + sin(t sin phi0) * east,
 * i.e. it has turned clockwise (seen from outside) by t sin phi0. After a full circuit the turn is
 * 360 sin phi0 degrees, and 360 (1 - sin phi0) degrees is the area of the cap above the circle.
 *
 * Plain JavaScript, no libraries. Colours from the CSS variables --fg, --bg, --accent, --muted.
 */
(function () {
  'use strict';

  var DEG = Math.PI / 180;
  var SIDEREAL_HOURS = 23.9345;

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
    return 'rgb(' + Math.round(a[0] + (b[0] - a[0]) * t) + ',' + Math.round(a[1] + (b[1] - a[1]) * t) +
      ',' + Math.round(a[2] + (b[2] - a[2]) * t) + ')';
  }
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

  // vectors
  function sph(phi, lam) { return [Math.cos(phi) * Math.cos(lam), Math.cos(phi) * Math.sin(lam), Math.sin(phi)]; }
  function north(phi, lam) { return [-Math.sin(phi) * Math.cos(lam), -Math.sin(phi) * Math.sin(lam), Math.cos(phi)]; }
  function east(lam) { return [-Math.sin(lam), Math.cos(lam), 0]; }
  function dot(a, b) { return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]; }
  function add(a, b, s) { return [a[0] + s * b[0], a[1] + s * b[1], a[2] + s * b[2]]; }

  function init() {
    var root = document.getElementById('transport-figure');
    if (!root || root.getAttribute('data-ready')) return;
    root.setAttribute('data-ready', '1');

    var state = { lat: 48.85, travelled: 120, tilt: 30, turn: 60, follow: false, playing: false };
    var START_LON = 0;

    var wrap = el('div', {
      style: 'font-family: system-ui, -apple-system, "Segoe UI", sans-serif; font-size: 14px;' +
        'color: var(--fg, #0b0b0b); max-width: 640px; margin: 0.5em 0;'
    }, root);
    var canvas = el('canvas', { role: 'img', 'aria-label': 'Sphere with a vector parallel transported along a circle of latitude' }, wrap);
    canvas.style.display = 'block';
    canvas.style.borderRadius = '6px';

    var leg = el('div', { style: 'display:flex; flex-wrap:wrap; gap:4px 16px; margin-top:8px; font-size:13px;' }, wrap);
    [['var(--fg, #0b0b0b)', 'start vector (north)'], ['var(--accent, #eb6834)', 'transported vector'],
      ['var(--muted, #898781)', 'local north at the current point']].forEach(function (it) {
      var item = el('span', { style: 'display:inline-flex; align-items:center; gap:6px;' }, leg);
      el('span', { style: 'display:inline-block; width:16px; height:3px; border-radius:2px; background:' + it[0] + ';' }, item);
      el('span', { text: it[1] }, item);
    });

    var ctl = el('div', { style: 'display:grid; grid-template-columns: auto 1fr auto; gap:6px 10px; align-items:center; margin-top:10px;' }, wrap);
    function slider(label, min, max, step, value) {
      var lab = el('label', { text: label, style: 'white-space:nowrap;' }, ctl);
      var inp = el('input', { type: 'range', min: min, max: max, step: step, value: value, style: 'width:100%;' }, ctl);
      var out = el('span', { style: 'font-variant-numeric: tabular-nums; min-width: 4em; text-align:right;' }, ctl);
      return { lab: lab, inp: inp, out: out };
    }
    var sLat = slider('latitude', -85, 85, 0.05, state.lat);
    var sTrav = slider('longitude travelled', 0, 360, 1, state.travelled);
    var sTilt = slider('view: tilt', -20, 85, 1, state.tilt);
    var sTurn = slider('view: turn', -180, 180, 1, state.turn);

    var row = el('div', { style: 'display:flex; flex-wrap:wrap; gap:10px; align-items:center; margin-top:8px;' }, wrap);
    var play = el('button', { type: 'button', text: 'play' }, row);
    play.style.cssText = 'font: inherit; padding: 5px 12px; border-radius: 6px; cursor: pointer;' +
      'border: 1px solid var(--muted, #898781); background: var(--bg, #fcfcfb); color: var(--fg, #0b0b0b);';
    var followLab = el('label', { style: 'display:flex; gap:6px; align-items:center; cursor:pointer;' }, row);
    var follow = el('input', { type: 'checkbox' }, followLab);
    el('span', { text: 'camera follows the pendulum' }, followLab);

    var read = el('div', { style: 'margin-top:10px; line-height:1.45; font-size:13.5px;', 'aria-live': 'polite' }, wrap);

    var size = 360;
    var dpr = Math.max(1, Math.min(2, window.devicePixelRatio || 1));

    function layout() {
      var W = root.clientWidth || 360;
      size = Math.max(240, Math.min(W, 460));
      canvas.width = Math.round(size * dpr);
      canvas.height = Math.round(size * dpr);
      canvas.style.width = size + 'px';
      canvas.style.height = size + 'px';
      draw();
    }

    function view() {
      var A = (state.follow ? START_LON + state.travelled + 20 : state.turn) * DEG;
      var E = state.tilt * DEG;
      return {
        v: [Math.cos(E) * Math.cos(A), Math.cos(E) * Math.sin(A), Math.sin(E)],
        r: [-Math.sin(A), Math.cos(A), 0],
        u: [-Math.sin(E) * Math.cos(A), -Math.sin(E) * Math.sin(A), Math.cos(E)]
      };
    }

    function draw() {
      var fg = cssVar(root, '--fg', '#0b0b0b');
      var bg = cssVar(root, '--bg', '#fcfcfb');
      var accent = cssVar(root, '--accent', '#eb6834');
      var muted = cssVar(root, '--muted', '#898781');
      var fgR = rgb(fg), bgR = rgb(bg), mutedR = rgb(muted), accR = rgb(accent);
      var ctx = canvas.getContext('2d');
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
      ctx.fillStyle = bg;
      ctx.fillRect(0, 0, size, size);

      var V = view();
      var cx = size / 2, cy = size / 2, R = size * 0.40;
      function P(p) { return [cx + R * dot(p, V.r), cy - R * dot(p, V.u), dot(p, V.v)]; }

      // globe
      ctx.beginPath(); ctx.arc(cx, cy, R, 0, 2 * Math.PI);
      ctx.fillStyle = mix(bgR, mutedR, 0.10); ctx.fill();
      ctx.strokeStyle = mix(bgR, mutedR, 0.7); ctx.lineWidth = 1; ctx.stroke();

      function curve(fn, n, styleFront, styleBack) {
        var prev = null;
        for (var i = 0; i <= n; i++) {
          var q = P(fn(i / n));
          if (prev) {
            var front = prev[2] >= 0 && q[2] >= 0;
            var st = front ? styleFront : styleBack;
            if (st) {
              ctx.beginPath(); ctx.moveTo(prev[0], prev[1]); ctx.lineTo(q[0], q[1]);
              ctx.strokeStyle = st.color; ctx.lineWidth = st.width;
              ctx.setLineDash(st.dash || []); ctx.stroke();
            }
          }
          prev = q;
        }
        ctx.setLineDash([]);
      }
      var gridFront = { color: mix(bgR, mutedR, 0.45), width: 0.8 };
      for (var la = -60; la <= 60; la += 30) {
        (function (phi) {
          curve(function (s) { return sph(phi, 2 * Math.PI * s); }, 120, gridFront, null);
        })(la * DEG);
      }
      for (var lo = 0; lo < 360; lo += 30) {
        (function (lam) {
          curve(function (s) { return sph(-Math.PI / 2 + Math.PI * s, lam); }, 80, gridFront, null);
        })(lo * DEG);
      }

      var phi0 = state.lat * DEG, s0 = Math.sin(phi0), lam0 = START_LON * DEG;
      var T = state.travelled * DEG;
      // full circle of latitude, then the travelled arc on top
      curve(function (s) { return sph(phi0, 2 * Math.PI * s); }, 240,
        { color: mix(bgR, fgR, 0.55), width: 1.4 }, { color: mix(bgR, fgR, 0.25), width: 1, dash: [3, 3] });
      if (T > 0) {
        curve(function (s) { return sph(phi0, lam0 + T * s); }, Math.max(8, Math.round(240 * T / (2 * Math.PI))),
          { color: accent, width: 3 }, { color: mix(bgR, accR, 0.45), width: 2, dash: [4, 3] });
      }

      var L = 0.28;
      function arrow(p, w, color, width, faded) {
        var a = P(p), b = P(add(p, w, L));
        var alpha = (a[2] < 0 || faded) ? 0.3 : 1;
        ctx.globalAlpha = alpha;
        ctx.strokeStyle = color; ctx.fillStyle = color; ctx.lineWidth = width;
        ctx.beginPath(); ctx.moveTo(a[0], a[1]); ctx.lineTo(b[0], b[1]); ctx.stroke();
        var dx = b[0] - a[0], dy = b[1] - a[1], len = Math.sqrt(dx * dx + dy * dy);
        if (len > 2) {
          var ux = dx / len, uy = dy / len, h = Math.min(9, 0.45 * len);
          ctx.beginPath();
          ctx.moveTo(b[0], b[1]);
          ctx.lineTo(b[0] - h * ux + 0.55 * h * uy, b[1] - h * uy - 0.55 * h * ux);
          ctx.lineTo(b[0] - h * ux - 0.55 * h * uy, b[1] - h * uy + 0.55 * h * ux);
          ctx.closePath(); ctx.fill();
        }
        ctx.globalAlpha = 1;
      }
      function transported(t) {
        // solution of the transport equations: turned clockwise by t * sin(phi0) from north
        var lam = lam0 + t, n = north(phi0, lam), e = east(lam);
        var c = Math.cos(t * s0), s = Math.sin(t * s0);
        return [c * n[0] + s * e[0], c * n[1] + s * e[1], c * n[2] + s * e[2]];
      }

      // trail every 30 degrees
      for (var k = 30; k < state.travelled; k += 30) {
        var tk = k * DEG;
        arrow(sph(phi0, lam0 + tk), transported(tk), mix(bgR, fgR, 0.45), 1.2, true);
      }
      // start: initial vector (pointing north)
      var pStart = sph(phi0, lam0);
      arrow(pStart, north(phi0, lam0), fg, 2, false);
      // current point: local north (reference) and transported vector
      var pCur = sph(phi0, lam0 + T);
      arrow(pCur, north(phi0, lam0 + T), muted, 1.3, false);
      arrow(pCur, transported(T), accent, 3, false);
      var c0 = P(pStart), c1 = P(pCur);
      ctx.globalAlpha = c0[2] < 0 ? 0.35 : 1;
      ctx.beginPath(); ctx.arc(c0[0], c0[1], 3.5, 0, 2 * Math.PI); ctx.fillStyle = fg; ctx.fill();
      ctx.globalAlpha = c1[2] < 0 ? 0.35 : 1;
      ctx.beginPath(); ctx.arc(c1[0], c1[1], 4.5, 0, 2 * Math.PI); ctx.fillStyle = accent; ctx.fill();
      ctx.globalAlpha = 1;
      // pole label
      var np = P([0, 0, 1]);
      ctx.font = '12px system-ui, -apple-system, "Segoe UI", sans-serif';
      ctx.textAlign = 'left'; ctx.textBaseline = 'middle';
      if (np[2] >= 0) { ctx.fillStyle = fg; ctx.fillText('N', np[0] + 5, np[1] - 6); }
      var sp = P([0, 0, -1]);
      if (sp[2] >= 0) { ctx.fillStyle = fg; ctx.fillText('S', sp[0] + 5, sp[1] + 6); }

      // read-out
      var turned = state.travelled * s0;
      var full = 360 * s0;
      var cap = 360 * (1 - s0);
      var perHour = full / SIDEREAL_HOURS;
      function f1(x) { return (Math.abs(x) < 0.05 ? 0 : x).toFixed(1); }
      read.innerHTML = '';
      el('div', { text: 'After ' + Math.round(state.travelled) + '\u00b0 of longitude the vector has turned ' +
        f1(Math.abs(turned)) + '\u00b0 ' + (turned >= 0 ? 'clockwise' : 'counterclockwise') +
        ' from local north (' + Math.round(state.travelled) + '\u00b0 \u00d7 sin ' + state.lat.toFixed(2) + '\u00b0).' }, read);
      el('div', { text: 'After a full circuit: ' + f1(Math.abs(full)) + '\u00b0 ' + (full >= 0 ? 'clockwise' : 'counterclockwise') +
        '. Curvature \u00d7 area of the cap above the circle: ' + f1(cap) + '\u00b0, and ' + f1(cap) +
        '\u00b0 + (' + f1(full) + '\u00b0 clockwise) = 360\u00b0.' }, read);
      el('div', { style: 'color: var(--muted, #898781);',
        text: Math.abs(s0) < 1e-3 ? 'At the equator a Foucault pendulum does not turn.' :
          'A Foucault pendulum here turns ' + f1(Math.abs(perHour)) + '\u00b0 per hour, once in ' +
          (SIDEREAL_HOURS / Math.abs(s0)).toFixed(1) + ' hours.' }, read);

      sLat.out.textContent = state.lat.toFixed(2) + '\u00b0';
      sTrav.out.textContent = Math.round(state.travelled) + '\u00b0';
      sTilt.out.textContent = Math.round(state.tilt) + '\u00b0';
      sTurn.out.textContent = state.follow ? 'follow' : Math.round(state.turn) + '\u00b0';
      sTurn.inp.disabled = state.follow;
    }

    sLat.inp.addEventListener('input', function () { state.lat = Number(sLat.inp.value); draw(); });
    sTrav.inp.addEventListener('input', function () { state.travelled = Number(sTrav.inp.value); draw(); });
    sTilt.inp.addEventListener('input', function () { state.tilt = Number(sTilt.inp.value); draw(); });
    sTurn.inp.addEventListener('input', function () { state.turn = Number(sTurn.inp.value); draw(); });
    follow.addEventListener('change', function () { state.follow = follow.checked; draw(); });

    var last = null;
    function step(ts) {
      if (!state.playing) { last = null; return; }
      if (last !== null) {
        state.travelled += (ts - last) / 1000 * 45; // 45 degrees of longitude per second
        if (state.travelled >= 360) { state.travelled = 360; state.playing = false; play.textContent = 'play'; }
        sTrav.inp.value = state.travelled;
        draw();
      }
      last = ts;
      if (state.playing) window.requestAnimationFrame(step);
    }
    play.addEventListener('click', function () {
      state.playing = !state.playing;
      play.textContent = state.playing ? 'pause' : 'play';
      if (state.playing) {
        if (state.travelled >= 360) state.travelled = 0;
        last = null;
        window.requestAnimationFrame(step);
      }
    });

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
