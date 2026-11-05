/* figA-telescope.js: interactive figure for the Appendix (Milnor, "Morse Theory", Appendix).
 *
 * Telescopes X_Sigma = {(x, tau) : x in X_floor(tau)} of increasing subsets X_i of an interval,
 * drawn in the (x, tau)-plane.
 *   Example 1 type: X = [0,1), X_i = [0, 1 - 1/(i+2)].  Every point is interior to some X_i.  The
 *     slider s runs the deformation H_s(x, tau) = (x, (1-s) tau + s f(x)), f(x) = x/(1-x), which
 *     carries X_Sigma onto the graph of f, a copy of X (Lemma 2.1).
 *   Example 3: X = [0,1], X_i = {0} u [1/(i+1), 1].  The ray over 0 is a separate path component;
 *     the slider runs the push-up (x, tau) -> (x, tau + s (N - tau)) of (T2), and the gap stays.
 *
 * Plain JavaScript, no libraries.  Looks for <div id="telescope-figure">.  Colours come from the
 * CSS variables --fg, --bg, --accent, --muted (with fallbacks).
 */
(function () {
  'use strict';

  var root = document.getElementById('telescope-figure');
  if (!root) return;

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

  /* ------------------------------------------------------------------ the two examples */

  var EXAMPLES = {
    good: {
      label: 'Xᵢ = [0, 1 − 1/(i+2)]',
      /* is (x, tau) in the telescope? */
      member: function (x, tau) {
        return x >= 0 && x <= 1 - 1 / (Math.floor(tau) + 2) + 1e-12;
      },
      /* the interval [lo, hi] of x-values at level i (one piece) */
      pieces: function (i) { return [[0, 1 - 1 / (i + 2)]]; },
      f: function (x) { return x / (1 - x); }
    },
    bad: {
      label: 'Example 3: Xᵢ = {0} ∪ [1/(i+1), 1]',
      member: function (x, tau) {
        return x === 0 || (x >= 1 / (Math.floor(tau) + 1) - 1e-12 && x <= 1);
      },
      pieces: function (i) { return [[0, 0], [1 / (i + 1), 1]]; },
      f: null
    }
  };

  var state = { ex: 'good', s: 0, levels: 6 };

  /* ------------------------------------------------------------------ DOM */

  var box = document.createElement('div');
  box.style.maxWidth = '640px';
  box.style.margin = '0 auto';
  box.style.font = '14px/1.45 system-ui, -apple-system, "Segoe UI", sans-serif';
  root.appendChild(box);

  var buttons = document.createElement('div');
  buttons.style.display = 'flex';
  buttons.style.flexWrap = 'wrap';
  buttons.style.gap = '0.4rem';
  buttons.style.marginBottom = '0.4rem';
  box.appendChild(buttons);

  var btn = {};
  function makeButton(key) {
    var b = document.createElement('button');
    b.type = 'button';
    b.textContent = EXAMPLES[key].label;
    b.style.font = 'inherit';
    b.style.padding = '0.25rem 0.6rem';
    b.style.borderRadius = '6px';
    b.style.cursor = 'pointer';
    b.addEventListener('click', function () {
      state.ex = key;
      draw();
    });
    buttons.appendChild(b);
    btn[key] = b;
  }
  makeButton('good');
  makeButton('bad');

  var canvas = document.createElement('canvas');
  canvas.style.display = 'block';
  canvas.style.width = '100%';
  canvas.setAttribute('role', 'img');
  canvas.setAttribute('aria-label',
    'Telescope of a sequence of subsets of an interval, drawn in the plane with a deformation');
  box.appendChild(canvas);

  var readout = document.createElement('div');
  readout.style.margin = '0.45rem 0 0.4rem';
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
    name.style.minWidth = '6rem';
    var input = document.createElement('input');
    input.type = 'range';
    input.min = String(min);
    input.max = String(max);
    input.step = String(step);
    input.value = String(state[key]);
    input.style.flex = '1 1 150px';
    input.style.minWidth = '120px';
    var val = document.createElement('span');
    val.style.minWidth = '3rem';
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
  addSlider('s', 'deformation s', 0, 1, 0.01, function (v) { return v.toFixed(2); });
  addSlider('levels', 'levels shown', 3, 10, 1, function (v) { return String(Math.round(v)); });

  /* ------------------------------------------------------------------ drawing */

  function draw() {
    var col = palette();
    var ex = EXAMPLES[state.ex];
    var N = Math.round(state.levels);
    var s = state.s;

    var key;
    for (key in btn) {
      if (Object.prototype.hasOwnProperty.call(btn, key)) {
        var on = key === state.ex;
        btn[key].style.background = on ? col.accent : 'transparent';
        btn[key].style.color = on ? col.bg : col.fg;
        btn[key].style.border = '1px solid ' + (on ? col.accent : col.muted);
        btn[key].setAttribute('aria-pressed', on ? 'true' : 'false');
      }
    }

    var W = Math.max(280, Math.min(640, box.clientWidth || root.clientWidth || 600));
    var H = Math.round(Math.min(0.78 * W, 460));
    var dpr = window.devicePixelRatio || 1;
    canvas.width = Math.round(W * dpr);
    canvas.height = Math.round(H * dpr);
    canvas.style.height = H + 'px';
    var ctx = canvas.getContext('2d');
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, W, H);

    var L = 44, R = 14, T = 12, B = 34;
    var pw = W - L - R, ph = H - T - B;
    function X(x) { return L + pw * (0.04 + 0.92 * x); }
    function Y(tau) { return T + ph * (1 - tau / N); }

    /* grid lines at the integer levels */
    ctx.lineWidth = 1;
    ctx.strokeStyle = col.muted;
    ctx.globalAlpha = 0.35;
    for (var k = 1; k < N; k++) {
      ctx.beginPath();
      ctx.moveTo(L, Y(k));
      ctx.lineTo(L + pw, Y(k));
      ctx.stroke();
    }
    ctx.globalAlpha = 1;

    /* the telescope, strip by strip */
    var i, j, pc;
    for (i = 0; i < N; i++) {
      pc = ex.pieces(i);
      for (j = 0; j < pc.length; j++) {
        var lo = pc[j][0], hi = pc[j][1];
        if (hi - lo > 1e-9) {
          ctx.save();
          ctx.globalAlpha = 0.18;
          ctx.fillStyle = col.accent;
          ctx.fillRect(X(lo), Y(i + 1), X(hi) - X(lo), Y(i) - Y(i + 1));
          ctx.restore();
          ctx.strokeStyle = col.accent;
          ctx.lineWidth = 1.2;
          ctx.strokeRect(X(lo), Y(i + 1), X(hi) - X(lo), Y(i) - Y(i + 1));
        } else {
          ctx.beginPath();
          ctx.moveTo(X(lo), Y(i));
          ctx.lineTo(X(lo), Y(i + 1));
          ctx.strokeStyle = col.accent;
          ctx.lineWidth = state.ex === 'bad' && lo === 0 ? 4 : 2;
          ctx.stroke();
        }
      }
    }
    if (state.ex === 'bad') {
      /* x = 1 at level 0, and the ray over 0 drawn on top */
      ctx.beginPath();
      ctx.moveTo(X(1), Y(0));
      ctx.lineTo(X(1), Y(1));
      ctx.strokeStyle = col.accent;
      ctx.lineWidth = 2;
      ctx.stroke();
    }

    /* the graph of f (Example 1) or the curve tau = 1/x - 1 (Example 3) */
    ctx.beginPath();
    var first = true, x, tau;
    for (j = 0; j <= 400; j++) {
      if (state.ex === 'good') {
        x = (j / 400) * (N / (N + 1));
        tau = ex.f(x);
      } else {
        x = 1 / (N + 1) + (j / 400) * (1 - 1 / (N + 1));
        tau = 1 / x - 1;
      }
      if (tau > N) continue;
      if (first) { ctx.moveTo(X(x), Y(tau)); first = false; } else { ctx.lineTo(X(x), Y(tau)); }
    }
    ctx.strokeStyle = col.fg;
    ctx.lineWidth = state.ex === 'good' ? 2.2 : 1.6;
    ctx.setLineDash(state.ex === 'good' ? [] : [6, 4]);
    ctx.stroke();
    ctx.setLineDash([]);

    /* sample points of X_Sigma, moved by the deformation */
    ctx.fillStyle = col.fg;
    var nx = W < 420 ? 14 : 20;
    for (var a = 0; a <= nx; a++) {
      x = a / nx;
      for (var b = 0; b < 2 * N; b++) {
        tau = (b + 0.5) / 2;
        if (!ex.member(x, tau)) continue;
        if (state.ex === 'good' && x >= 1) continue;
        var t1;
        if (state.ex === 'good') {
          t1 = (1 - s) * tau + s * ex.f(x);
        } else {
          t1 = tau + s * (N - tau);
        }
        if (t1 > N + 1e-9) continue;
        ctx.beginPath();
        ctx.arc(X(x), Y(t1), 2.2, 0, 2 * Math.PI);
        ctx.fill();
      }
    }

    /* axes */
    ctx.strokeStyle = col.muted;
    ctx.lineWidth = 1;
    ctx.strokeRect(L, T, pw, ph);
    ctx.fillStyle = col.fg;
    ctx.font = '12px system-ui, -apple-system, "Segoe UI", sans-serif';
    ctx.textAlign = 'center';
    ctx.textBaseline = 'top';
    ctx.fillText('0', X(0), T + ph + 4);
    ctx.fillText('1', X(1), T + ph + 4);
    ctx.fillText('x', X(0.5), T + ph + 16);
    ctx.textAlign = 'right';
    ctx.textBaseline = 'middle';
    for (k = 0; k <= N; k++) ctx.fillText(String(k), L - 5, Y(k));
    ctx.textAlign = 'left';
    ctx.font = 'italic 14px system-ui, -apple-system, "Segoe UI", sans-serif';
    ctx.fillText('τ', 4, T + ph / 2);
    ctx.textAlign = 'start';

    if (state.ex === 'good') {
      readout.textContent = 'Every point of X = [0,1) lies in the interior of some Xᵢ, and ' +
        'f(x) = x/(1−x) is at least i+1 off Xᵢ. At s = 1 every point of the telescope ' +
        'has slid onto the graph of f, a copy of X: the projection p is a homotopy equivalence.';
    } else {
      readout.textContent = 'The point 0 lies in every Xᵢ but in the interior of none. ' +
        'The ray over 0 never meets the rest of the telescope (pushing up does not help), so ' +
        'the telescope has two path components while [0,1] has one: p is not a homotopy ' +
        'equivalence. A graph inside the telescope would need f(x) ≥ 1/x − 1 (dashed).';
    }
  }

  draw();
  window.addEventListener('resize', draw);
  if (window.matchMedia) {
    var mq = window.matchMedia('(prefers-color-scheme: dark)');
    if (mq.addEventListener) mq.addEventListener('change', draw);
    else if (mq.addListener) mq.addListener(draw);
  }
})();
