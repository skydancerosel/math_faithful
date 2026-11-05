/*
 * fig1-torus.js -- interactive figure for Chapter 1 (Milnor, Morse Theory, section 1).
 *
 * Milnor's Diagram 1: a torus standing upright on a horizontal plane V, its height function f and
 * the critical points p, q, r, s.  The water level a is a slider: the sublevel set M^a is shaded
 * as water, the level curve f = a is drawn where it is visible, and the readout says what M^a is.
 * A second slider turns the torus.
 *
 * The surface is drawn by the painter's algorithm (quadrilaterals sorted by depth, orthographic
 * view); a point of the level curve is drawn only if the ray from it towards the viewer does not
 * enter the solid torus.
 *
 * Plain JavaScript, no libraries.  Finds <div id="torus-levels-figure"> and builds a canvas with
 * sliders.  Colours come from the CSS variables --fg, --bg, --accent, --muted (with fallbacks).
 */
(function () {
  'use strict';

  var ID = 'torus-levels-figure';
  var R = 2.0, RHO = 0.8, C0 = R + RHO;
  var CRIT = [
    { name: 'p', h: 0, u: -Math.PI / 2, v: 0 },
    { name: 'q', h: 2 * RHO, u: -Math.PI / 2, v: Math.PI },
    { name: 'r', h: 2 * R, u: Math.PI / 2, v: Math.PI },
    { name: 's', h: 2 * R + 2 * RHO, u: Math.PI / 2, v: 0 }
  ];
  var CRITCOL = '#eb6834';

  function cssVar(el, name, fallback) {
    var v = '';
    try { v = window.getComputedStyle(el).getPropertyValue(name); } catch (e) { v = ''; }
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

  function rgb(c, fallback) {
    var m = /^#([0-9a-f]{3}|[0-9a-f]{6})$/i.exec(c);
    if (m) {
      var h = m[1];
      if (h.length === 3) h = h[0] + h[0] + h[1] + h[1] + h[2] + h[2];
      return [parseInt(h.slice(0, 2), 16), parseInt(h.slice(2, 4), 16), parseInt(h.slice(4, 6), 16)];
    }
    m = /rgba?\(\s*([\d.]+)[\s,]+([\d.]+)[\s,]+([\d.]+)/i.exec(c);
    if (m) return [+m[1], +m[2], +m[3]];
    return fallback;
  }

  // ---------------------------------------------------------------- geometry

  function surface(u, v) {
    var w = R + RHO * Math.cos(v);
    return [w * Math.cos(u), RHO * Math.sin(v), C0 + w * Math.sin(u)];
  }
  function normal(u, v) {
    return [Math.cos(v) * Math.cos(u), Math.sin(v), Math.cos(v) * Math.sin(u)];
  }
  function dot(a, b) { return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]; }
  function cross(a, b) { return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]; }
  function unit(a) { var n = Math.sqrt(dot(a, a)); return [a[0] / n, a[1] / n, a[2] / n]; }

  function makeView(az, elev) {
    var a = az * Math.PI / 180, e = elev * Math.PI / 180;
    var d = [Math.sin(a) * Math.cos(e), Math.cos(a) * Math.cos(e), Math.sin(e)];   // towards viewer
    var f = [-d[0], -d[1], -d[2]];
    var right = unit(cross(f, [0, 0, 1]));
    var up = cross(right, f);
    var light = unit([d[0] - 0.5, d[1] + 0.2, d[2] + 0.9]);
    return { d: d, right: right, up: up, light: light };
  }
  function project(view, P) { return [dot(P, view.right), dot(P, view.up)]; }

  // does the ray from the surface point P towards the viewer stay outside the solid torus?
  function visible(view, P) {
    var d = view.d;
    for (var k = 1; k <= 220; k++) {
      var t = 0.015 + (k - 1) * 0.045;
      var x = P[0] + t * d[0], y = P[1] + t * d[1], z = P[2] + t * d[2] - C0;
      var s = Math.sqrt(x * x + z * z) - R;
      if (s * s + y * y - RHO * RHO < -1e-4) return false;
    }
    return true;
  }

  // the level curve f = a: two branches over v; their meeting points (|w| = 1) found by bisection
  function levelCurve(a) {
    function wv(v) { return (a - C0) / (R + RHO * Math.cos(v)); }
    var n = 700, vs = [], i;
    for (i = 0; i <= n; i++) vs.push(-Math.PI + 2 * Math.PI * i / n);
    var extra = [];
    for (i = 0; i < n; i++) {
      var o1 = Math.abs(wv(vs[i])) <= 1, o2 = Math.abs(wv(vs[i + 1])) <= 1;
      if (o1 !== o2) {
        var lo = vs[i], hi = vs[i + 1];
        for (var k = 0; k < 50; k++) {
          var mid = (lo + hi) / 2;
          if ((Math.abs(wv(mid)) <= 1) === o1) lo = mid; else hi = mid;
        }
        extra.push(o1 ? lo : hi);
      }
    }
    vs = vs.concat(extra).sort(function (x, y) { return x - y; });
    var branches = [[], []];
    for (i = 0; i < vs.length; i++) {
      var w = wv(vs[i]);
      if (Math.abs(w) > 1 + 1e-12) { branches[0].push(null); branches[1].push(null); continue; }
      w = Math.max(-1, Math.min(1, w));
      var u1 = Math.asin(w);
      branches[0].push(surface(u1, vs[i]));
      branches[1].push(surface(Math.PI - u1, vs[i]));
    }
    return branches;
  }

  // ---------------------------------------------------------------- figure

  function describe(a, snapped) {
    var q = 2 * RHO, r = 2 * R, s = 2 * R + 2 * RHO;
    if (snapped === 'p') return 'a = f(p) = 0: M^a is the single point p, where the torus touches V.';
    if (snapped === 'q') return 'a = f(q): the level curve is a figure eight crossing itself at q. Just above, M^a is a cylinder.';
    if (snapped === 'r') return 'a = f(r): the level curve is a figure eight crossing itself at r. Just above, a second 1-cell has been attached.';
    if (snapped === 's') return 'a = f(s): M^a is the whole torus; the level set is the single point s.';
    if (a < 0) return 'a < f(p): M^a is empty.';
    if (a < q) return 'f(p) < a < f(q): M^a is a disk, of the homotopy type of a point: a 0-cell was attached at p.';
    if (a < r) return 'f(q) < a < f(r): M^a is a cylinder, of the homotopy type of a circle: a 1-cell was attached at q.';
    if (a < s) return 'f(r) < a < f(s): M^a is a torus with a disk removed, of the homotopy type of a figure eight: a second 1-cell was attached at r.';
    return 'a > f(s): M^a is the whole torus: a 2-cell was attached at s.';
  }

  function build(root) {
    var state = { a: 2.8, az: 32 };

    var wrap = el('div', { style: 'max-width:600px;margin:0 auto;font:14px/1.4 system-ui,-apple-system,Segoe UI,sans-serif;' }, root);
    var canvas = el('canvas', { style: 'display:block;width:100%;height:auto;border-radius:6px;', 'aria-label': 'A torus standing on a plane, flooded to the height a' }, wrap);
    var readout = el('div', { style: 'margin:8px 2px 4px;min-height:2.8em;' }, wrap);
    var presets = el('div', { style: 'display:flex;flex-wrap:wrap;gap:6px;margin:4px 0 8px;' }, wrap);
    var controls = el('div', { style: 'display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:6px 14px;' }, wrap);

    var snapName = null;
    function snap(v) {
      snapName = null;
      for (var i = 0; i < CRIT.length; i++) {
        if (Math.abs(v - CRIT[i].h) < 0.04) { snapName = CRIT[i].name; return CRIT[i].h; }
      }
      return v;
    }

    function slider(label, min, max, step, value, onInput, fmt) {
      var box = el('label', { style: 'display:flex;flex-direction:column;gap:2px;' }, controls);
      var head = el('span', null, box);
      var input = el('input', { type: 'range', min: String(min), max: String(max), step: String(step), value: String(value), style: 'width:100%;' }, box);
      function show() { head.textContent = label + ' = ' + fmt(parseFloat(input.value)); }
      input.addEventListener('input', function () { onInput(parseFloat(input.value)); show(); schedule(); });
      show();
      return { input: input, show: show };
    }

    var sa = slider('water level a', -0.4, 6.2, 0.01, state.a, function (v) { state.a = snap(v); },
      function () { return (state.a < 0 ? '−' : '') + Math.abs(state.a).toFixed(2); });
    slider('turn', 0, 80, 1, state.az, function (v) { state.az = v; }, function (v) { return v.toFixed(0) + '°'; });

    function preset(name, a) {
      var btn = el('button', { type: 'button', text: name, style: 'font:inherit;padding:3px 10px;border-radius:5px;border:1px solid currentColor;background:transparent;color:inherit;cursor:pointer;' }, presets);
      btn.addEventListener('click', function () {
        state.a = snap(a);
        sa.input.value = String(a);
        sa.show();
        schedule();
      });
    }
    preset('disk', 0.9);
    preset('a = f(q)', 2 * RHO);
    preset('cylinder', 2.8);
    preset('a = f(r)', 2 * R);
    preset('torus minus a disk', 4.8);
    preset('torus', 6.0);

    var pending = false;
    function schedule() {
      if (pending) return;
      pending = true;
      (window.requestAnimationFrame || function (cb) { return setTimeout(cb, 16); })(function () {
        pending = false;
        draw();
      });
    }

    var NU = 96, NV = 44;

    function draw() {
      var fg = cssVar(root, '--fg', '#1f1f1d');
      var bg = cssVar(root, '--bg', '#fcfcfb');
      var accent = cssVar(root, '--accent', '#2a78d6');
      var muted = cssVar(root, '--muted', '#8a8984');
      var water = rgb(accent, [42, 120, 214]);
      water = [0.55 * water[0] + 0.45 * 200, 0.55 * water[1] + 0.45 * 220, 0.55 * water[2] + 0.45 * 245];
      var surf = [219, 216, 208];

      var W = Math.max(260, Math.min(wrap.clientWidth || root.clientWidth || 360, 600));
      var H = Math.round(W * 0.82);
      var dpr = window.devicePixelRatio || 1;
      if (canvas.width !== Math.round(W * dpr) || canvas.height !== Math.round(H * dpr)) {
        canvas.width = Math.round(W * dpr);
        canvas.height = Math.round(H * dpr);
      }
      canvas.style.height = H + 'px';
      var ctx = canvas.getContext('2d');
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
      ctx.clearRect(0, 0, W, H);

      var view = makeView(state.az, 11);
      var a = state.a;

      // mesh
      var quads = [], minx = 1e9, maxx = -1e9, i, j;
      for (i = 0; i < NU; i++) {
        for (j = 0; j < NV; j++) {
          var u0 = -Math.PI + 2 * Math.PI * i / NU, u1 = -Math.PI + 2 * Math.PI * (i + 1) / NU;
          var v0 = -Math.PI + 2 * Math.PI * j / NV, v1 = -Math.PI + 2 * Math.PI * (j + 1) / NV;
          var P = [surface(u0, v0), surface(u1, v0), surface(u1, v1), surface(u0, v1)];
          var uc = (u0 + u1) / 2, vc = (v0 + v1) / 2;
          var cen = surface(uc, vc);
          var sh = Math.max(0, dot(normal(uc, vc), view.light));
          var base = cen[2] <= a ? water : surf;
          var k = 0.42 + 0.58 * sh;
          var pts = P.map(function (X) { return project(view, X); });
          pts.forEach(function (s) { minx = Math.min(minx, s[0]); maxx = Math.max(maxx, s[0]); });
          quads.push({ depth: dot(cen, view.d), pts: pts,
            col: 'rgb(' + Math.round(base[0] * k) + ',' + Math.round(base[1] * k) + ',' + Math.round(base[2] * k) + ')' });
        }
      }
      quads.sort(function (x, y) { return x.depth - y.depth; });

      // frame: the height scale to the left of the torus, the plane below
      var x0 = minx - 0.45;
      var X0 = x0 - 1.9, X1 = maxx + 0.6;
      var yLo = project(view, [0, 0, 0])[1] - 0.9, yHi = project(view, [0, 0, 2 * C0 + 0.45])[1];
      var sc = Math.min(W / (X1 - X0), H / (yHi - yLo));
      var ox = (W - sc * (X1 - X0)) / 2;
      function px(s) { return [ox + (s[0] - X0) * sc, H - (s[1] - yLo) * sc]; }

      // the plane V
      var pw = 4.2, ph = 2.6;
      var corners = [[-pw, -ph, 0], [pw, -ph, 0], [pw, ph, 0], [-pw, ph, 0]].map(function (X) { return px(project(view, X)); });
      ctx.beginPath();
      corners.forEach(function (c, n) { if (n) ctx.lineTo(c[0], c[1]); else ctx.moveTo(c[0], c[1]); });
      ctx.closePath();
      ctx.globalAlpha = 0.14; ctx.fillStyle = fg; ctx.fill();
      ctx.globalAlpha = 0.45; ctx.strokeStyle = muted; ctx.lineWidth = 1; ctx.stroke();
      ctx.globalAlpha = 1;

      // the surface
      quads.forEach(function (q) {
        ctx.beginPath();
        q.pts.forEach(function (s, n) { var c = px(s); if (n) ctx.lineTo(c[0], c[1]); else ctx.moveTo(c[0], c[1]); });
        ctx.closePath();
        ctx.fillStyle = q.col; ctx.strokeStyle = q.col; ctx.lineWidth = 0.6;
        ctx.fill(); ctx.stroke();
      });

      // the level curve f = a
      if (a > 0 && a < 2 * C0) {
        ctx.strokeStyle = snapName ? CRITCOL : accent;
        ctx.lineWidth = 2; ctx.lineCap = 'round';
        levelCurve(a).forEach(function (br) {
          ctx.beginPath();
          var pen = false;
          br.forEach(function (X) {
            if (!X || !visible(view, X)) { pen = false; return; }
            var c = px(project(view, X));
            if (pen) ctx.lineTo(c[0], c[1]); else ctx.moveTo(c[0], c[1]);
            pen = true;
          });
          ctx.stroke();
        });
      }

      // the height scale, the critical points, the water mark
      var xs = px([x0, 0])[0];
      ctx.strokeStyle = fg; ctx.fillStyle = fg; ctx.lineWidth = 1;
      ctx.beginPath(); ctx.moveTo(xs, px([0, yLo + 0.8])[1]); ctx.lineTo(xs, px([0, yHi])[1] + 2); ctx.stroke();
      ctx.beginPath(); ctx.moveTo(xs, px([0, yHi])[1]); ctx.lineTo(xs - 4, px([0, yHi])[1] + 8); ctx.lineTo(xs + 4, px([0, yHi])[1] + 8); ctx.closePath(); ctx.fill();
      ctx.font = 'italic 14px Georgia, serif'; ctx.textAlign = 'right'; ctx.textBaseline = 'top';
      ctx.fillText('f', xs - 7, px([0, yHi])[1]);
      ctx.font = '12px system-ui, sans-serif'; ctx.textBaseline = 'middle';
      CRIT.forEach(function (c) {
        var X = surface(c.u, c.v), s = px(project(view, X));
        ctx.setLineDash([3, 3]); ctx.strokeStyle = CRITCOL; ctx.globalAlpha = 0.8; ctx.lineWidth = 0.8;
        ctx.beginPath(); ctx.moveTo(xs, s[1]); ctx.lineTo(s[0], s[1]); ctx.stroke();
        ctx.setLineDash([]); ctx.globalAlpha = 1;
        ctx.fillStyle = fg; ctx.textAlign = 'right';
        ctx.fillText('f(' + c.name + ')', xs - 6, s[1]);
        ctx.beginPath(); ctx.arc(s[0], s[1], 4, 0, 2 * Math.PI);
        ctx.fillStyle = visible(view, X) ? CRITCOL : bg; ctx.fill();
        ctx.strokeStyle = CRITCOL; ctx.lineWidth = 1.5; ctx.stroke();
        ctx.fillStyle = CRITCOL; ctx.textAlign = 'left';
        ctx.font = 'italic 15px Georgia, serif';
        ctx.fillText(c.name, s[0] + 7, s[1] + (c.name === 'r' || c.name === 'p' ? 9 : -9));
        ctx.font = '12px system-ui, sans-serif';
      });
      if (a > yLo - 1 && a <= 2 * C0 + 0.4) {
        var ya = px(project(view, [0, 0, a]))[1];
        ctx.fillStyle = accent;
        ctx.beginPath(); ctx.moveTo(xs + 1, ya); ctx.lineTo(xs + 10, ya - 5); ctx.lineTo(xs + 10, ya + 5); ctx.closePath(); ctx.fill();
        ctx.textAlign = 'left'; ctx.fillText('a', xs + 13, ya);
      }

      readout.textContent = describe(a, snapName);
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
