/* Figure for Chapter 12: geodesics of SU(3) from e to q = exp(H), and their indices.
   Plain JavaScript, no libraries.  Finds <div id="su3-figure"> and draws an interactive canvas.
   Drag the picture to move q (the whole lattice H + 2*pi*Gamma moves); tap a dot to select a
   geodesic; the slider sets the largest index shown.  Colours come from the CSS variables
   --fg, --bg, --accent, --muted (with fallbacks). */
(function () {
  "use strict";
  var root = document.getElementById("su3-figure");
  if (!root) { return; }

  var TWO_PI = 2 * Math.PI;
  var S2 = Math.sqrt(2), S6 = Math.sqrt(6);
  var PAIRS = [[0, 1], [0, 2], [1, 2]];
  // roots as linear forms in the orthonormal (x, y) coordinates of t
  var ROOTS = [[S2, 0], [1 / S2, S6 / 2], [-1 / S2, S6 / 2]];

  function cssVar(name, fallback) {
    var v = "";
    try { v = getComputedStyle(root).getPropertyValue(name).trim(); } catch (e) { v = ""; }
    return v || fallback;
  }
  function el(tag, attrs, text) {
    var e = document.createElement(tag);
    if (attrs) { for (var k in attrs) { if (Object.prototype.hasOwnProperty.call(attrs, k)) { e.setAttribute(k, attrs[k]); } } }
    if (text) { e.textContent = text; }
    return e;
  }

  // theta (sum zero) <-> (x, y)
  function toXY(th) {
    return [(th[0] - th[1]) / S2, (th[0] + th[1] - 2 * th[2]) / S6];
  }
  function fromXY(x, y) {
    return [x / S2 + y / S6, -x / S2 + y / S6, -2 * y / S6];
  }
  function indexOf(th) {
    var lam = 0;
    for (var i = 0; i < 3; i++) {
      var a = Math.abs(th[PAIRS[i][0]] - th[PAIRS[i][1]]);
      lam += 2 * Math.floor(a / TWO_PI);
    }
    return lam;
  }
  function crossings(th) {
    var ts = [];
    for (var i = 0; i < 3; i++) {
      var a = Math.abs(th[PAIRS[i][0]] - th[PAIRS[i][1]]);
      for (var m = 1; TWO_PI * m < a; m++) { ts.push({ t: TWO_PI * m / a, pair: i }); }
    }
    ts.sort(function (u, v) { return u.t - v.t; });
    return ts;
  }
  function singularity(th) {
    // distance of each (th_j - th_k)/(2 pi) to the nearest integer; small means q is nearly singular
    var d = 1;
    for (var i = 0; i < 3; i++) {
      var q = (th[PAIRS[i][0]] - th[PAIRS[i][1]]) / TWO_PI;
      d = Math.min(d, Math.abs(q - Math.round(q)));
    }
    return d;
  }

  // ---------- state ----------
  var H = [0.4 * TWO_PI, -0.05 * TWO_PI, -0.35 * TWO_PI];
  var maxShow = 10;
  var halfWidth = 17;
  var selected = [1, -1, 0];

  // ---------- layout ----------
  root.innerHTML = "";
  root.style.maxWidth = "680px";
  root.style.margin = "1em auto";
  root.style.fontFamily = "inherit";
  var canvas = el("canvas");
  canvas.style.width = "100%";
  canvas.style.display = "block";
  canvas.style.touchAction = "none";
  canvas.style.borderRadius = "4px";
  root.appendChild(canvas);

  var controls = el("div");
  controls.style.display = "flex";
  controls.style.flexWrap = "wrap";
  controls.style.gap = "0.4em 1.2em";
  controls.style.alignItems = "center";
  controls.style.margin = "0.5em 0";
  controls.style.fontSize = "0.9em";
  root.appendChild(controls);

  function slider(label, min, max, step, value, onInput) {
    var wrap = el("label");
    wrap.style.display = "flex";
    wrap.style.alignItems = "center";
    wrap.style.gap = "0.4em";
    var span = el("span", null, label);
    var input = el("input", { type: "range", min: String(min), max: String(max), step: String(step), value: String(value) });
    input.style.width = "130px";
    var out = el("span", null, String(value));
    out.style.minWidth = "2em";
    input.addEventListener("input", function () { out.textContent = input.value; onInput(Number(input.value)); });
    wrap.appendChild(span); wrap.appendChild(input); wrap.appendChild(out);
    controls.appendChild(wrap);
    return input;
  }
  slider("largest index shown", 0, 16, 2, maxShow, function (v) { maxShow = v; draw(); });
  slider("zoom out", 10, 30, 1, halfWidth, function (v) { halfWidth = v; draw(); });
  var resetBtn = el("button", { type: "button" }, "reset q");
  resetBtn.addEventListener("click", function () { H = [0.4 * TWO_PI, -0.05 * TWO_PI, -0.35 * TWO_PI]; selected = [1, -1, 0]; draw(); });
  controls.appendChild(resetBtn);

  var info = el("div");
  info.style.fontSize = "0.88em";
  info.style.lineHeight = "1.45";
  root.appendChild(info);

  var tableWrap = el("div");
  tableWrap.style.overflowX = "auto";
  tableWrap.style.fontSize = "0.85em";
  root.appendChild(tableWrap);

  // ---------- drawing ----------
  var W = 400, Hpx = 400, dpr = 1;
  function resize() {
    var w = Math.max(240, Math.min(root.clientWidth || 360, 680));
    W = w; Hpx = Math.round(Math.min(w, 520));
    dpr = window.devicePixelRatio || 1;
    canvas.width = Math.round(W * dpr);
    canvas.height = Math.round(Hpx * dpr);
    canvas.style.height = Hpx + "px";
  }
  function scale() { return Math.min(W, Hpx) / (2 * halfWidth); }
  function toPx(x, y) { var s = scale(); return [W / 2 + s * x, Hpx / 2 - s * y]; }
  function fromPx(px, py) { var s = scale(); return [(px - W / 2) / s, (Hpx / 2 - py) / s]; }

  function colourFor(lam) {
    var f = Math.min(lam, 16) / 16;
    var hue = 265 - 205 * f;            // violet (index 0) to yellow-green (index 16)
    return "hsl(" + hue.toFixed(0) + ",70%," + (38 + 18 * f).toFixed(0) + "%)";
  }

  function lattice() {
    var pts = [];
    var R = 14;
    for (var n1 = -R; n1 <= R; n1++) {
      for (var n2 = -R; n2 <= R; n2++) {
        var n3 = -n1 - n2;
        var th = [H[0] + TWO_PI * n1, H[1] + TWO_PI * n2, H[2] + TWO_PI * n3];
        pts.push({ n: [n1, n2, n3], th: th, lam: indexOf(th), xy: toXY(th) });
      }
    }
    return pts;
  }

  function draw() {
    resize();
    var ctx = canvas.getContext("2d");
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    var fg = cssVar("--fg", "#222"), bg = cssVar("--bg", "#fff");
    var accent = cssVar("--accent", "#c0392b"), muted = cssVar("--muted", "#999");
    ctx.fillStyle = bg; ctx.fillRect(0, 0, W, Hpx);

    // walls th_j - th_k = 2 pi m
    var s = scale();
    for (var r = 0; r < 3; r++) {
      var a = ROOTS[r], na = Math.sqrt(a[0] * a[0] + a[1] * a[1]);
      var nx = a[0] / na, ny = a[1] / na, tx = -ny, ty = nx;
      var mMax = Math.ceil(halfWidth * 1.5 * na / TWO_PI);
      for (var m = -mMax; m <= mMax; m++) {
        var c = TWO_PI * m / na;
        var p1 = toPx(c * nx - 3 * halfWidth * tx, c * ny - 3 * halfWidth * ty);
        var p2 = toPx(c * nx + 3 * halfWidth * tx, c * ny + 3 * halfWidth * ty);
        ctx.beginPath();
        ctx.moveTo(p1[0], p1[1]); ctx.lineTo(p2[0], p2[1]);
        ctx.strokeStyle = muted;
        ctx.globalAlpha = (m === 0) ? 0.35 : 0.6;
        ctx.setLineDash(m === 0 ? [4, 4] : []);
        ctx.lineWidth = 0.8;
        ctx.stroke();
      }
    }
    ctx.setLineDash([]); ctx.globalAlpha = 1;

    var pts = lattice();
    var counts = {};
    for (var i = 0; i < pts.length; i++) { counts[pts[i].lam] = (counts[pts[i].lam] || 0) + 1; }

    // selected geodesic and its conjugate points
    var sel = null;
    for (i = 0; i < pts.length; i++) {
      if (pts[i].n[0] === selected[0] && pts[i].n[1] === selected[1]) { sel = pts[i]; }
    }
    var o = toPx(0, 0);
    if (sel) {
      var q = toPx(sel.xy[0], sel.xy[1]);
      ctx.beginPath(); ctx.moveTo(o[0], o[1]); ctx.lineTo(q[0], q[1]);
      ctx.strokeStyle = accent; ctx.lineWidth = 2.2; ctx.stroke();
      var cr = crossings(sel.th);
      for (i = 0; i < cr.length; i++) {
        var cp = toPx(cr[i].t * sel.xy[0], cr[i].t * sel.xy[1]);
        ctx.beginPath(); ctx.arc(cp[0], cp[1], 4.5, 0, TWO_PI);
        ctx.fillStyle = bg; ctx.fill();
        ctx.strokeStyle = accent; ctx.lineWidth = 1.8; ctx.stroke();
      }
    }

    // lattice points
    ctx.font = "11px sans-serif";
    for (i = 0; i < pts.length; i++) {
      var p = pts[i];
      if (p.lam > maxShow) { continue; }
      var pp = toPx(p.xy[0], p.xy[1]);
      if (pp[0] < -10 || pp[0] > W + 10 || pp[1] < -10 || pp[1] > Hpx + 10) { continue; }
      ctx.beginPath(); ctx.arc(pp[0], pp[1], 6, 0, TWO_PI);
      ctx.fillStyle = colourFor(p.lam); ctx.fill();
      ctx.strokeStyle = fg; ctx.lineWidth = (sel === p) ? 2.2 : 0.8; ctx.stroke();
      ctx.fillStyle = fg;
      ctx.fillText(String(p.lam), pp[0] + 7, pp[1] - 6);
    }
    // the origin (the identity)
    ctx.fillStyle = fg;
    ctx.fillRect(o[0] - 4, o[1] - 4, 8, 8);
    ctx.fillText("e", o[0] + 6, o[1] + 14);

    // text
    var sing = singularity(H);
    var lines = [];
    if (sing < 0.012) {
      lines.push("<b>q is (nearly) singular:</b> a wall passes through the lattice, some geodesics end at a conjugate point, and Theorem 17.3 no longer applies. Drag a little further.");
    }
    if (sel) {
      var d = [sel.th[0] - sel.th[1], sel.th[0] - sel.th[2], sel.th[1] - sel.th[2]];
      var cr2 = crossings(sel.th);
      var tl = cr2.map(function (u) { return u.t.toFixed(3); }).join(", ");
      lines.push("Selected geodesic t \u21a6 exp(tX): (\u03b8\u2081\u2212\u03b8\u2082, \u03b8\u2081\u2212\u03b8\u2083, \u03b8\u2082\u2212\u03b8\u2083)/2\u03c0 = (" +
        (d[0] / TWO_PI).toFixed(2) + ", " + (d[1] / TWO_PI).toFixed(2) + ", " + (d[2] / TWO_PI).toFixed(2) + ").");
      lines.push("Conjugate points (open circles) at t = " + (tl || "none") + "; each has multiplicity 2, so the index is 2 \u00d7 " +
        cr2.length + " = <b>" + sel.lam + "</b>.");
    }
    info.innerHTML = lines.join("<br>");

    // count table
    var html = "<table style='border-collapse:collapse;margin:0.4em 0'><tr><td style='padding:2px 6px'>index \u03bb</td>";
    var lamMax = 14, k;
    for (k = 0; k <= lamMax; k += 2) { html += "<td style='padding:2px 6px;text-align:center'>" + k + "</td>"; }
    html += "</tr><tr><td style='padding:2px 6px'>geodesics</td>";
    for (k = 0; k <= lamMax; k += 2) { html += "<td style='padding:2px 6px;text-align:center'><b>" + (counts[k] || 0) + "</b></td>"; }
    html += "</tr><tr><td style='padding:2px 6px'>1/((1\u2212t\u00b2)(1\u2212t\u2074))</td>";
    for (k = 0; k <= lamMax; k += 2) { html += "<td style='padding:2px 6px;text-align:center'>" + (Math.floor(k / 4) + 1) + "</td>"; }
    html += "</tr></table>";
    var odd = 0;
    for (var key in counts) { if (Object.prototype.hasOwnProperty.call(counts, key) && Number(key) % 2 === 1) { odd += counts[key]; } }
    html += "<div>Odd indices found: " + odd + ". Drag to move q: the dots move, the counts do not.</div>";
    tableWrap.innerHTML = html;
  }

  // ---------- interaction ----------
  var dragStart = null, startH = null, moved = false;
  function localPos(ev) {
    var rect = canvas.getBoundingClientRect();
    return [ev.clientX - rect.left, ev.clientY - rect.top];
  }
  canvas.addEventListener("pointerdown", function (ev) {
    dragStart = localPos(ev); startH = H.slice(); moved = false;
    if (canvas.setPointerCapture) { canvas.setPointerCapture(ev.pointerId); }
  });
  canvas.addEventListener("pointermove", function (ev) {
    if (!dragStart) { return; }
    var pos = localPos(ev);
    var dx = pos[0] - dragStart[0], dy = pos[1] - dragStart[1];
    if (!moved && Math.abs(dx) + Math.abs(dy) < 5) { return; }
    moved = true;
    var s = scale();
    var shift = fromXY(dx / s, -dy / s);
    H = [startH[0] + shift[0], startH[1] + shift[1], startH[2] + shift[2]];
    draw();
  });
  function endDrag(ev) {
    if (!dragStart) { return; }
    if (!moved) {
      var pos = localPos(ev), best = null, bestD = 1e9;
      var pts = lattice();
      for (var i = 0; i < pts.length; i++) {
        if (pts[i].lam > maxShow) { continue; }
        var pp = toPx(pts[i].xy[0], pts[i].xy[1]);
        var dd = Math.hypot(pp[0] - pos[0], pp[1] - pos[1]);
        if (dd < bestD) { bestD = dd; best = pts[i]; }
      }
      if (best && bestD < 24) { selected = best.n.slice(0, 2).concat([-best.n[0] - best.n[1]]); draw(); }
    }
    dragStart = null;
  }
  canvas.addEventListener("pointerup", endDrag);
  canvas.addEventListener("pointercancel", function () { dragStart = null; });
  window.addEventListener("resize", draw);
  draw();
})();
