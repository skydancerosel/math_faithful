/* Figure for Chapter 13: geodesics between antipodal points of a sphere, and the stable range.
   Plain JavaScript, no libraries.  Finds <div id="antipodes-figure">.
   Left: the sphere S^2 (the case n = 1 of S^{n+1}) with p (top) and q = -p (bottom).  The equator is
   the space of minimal geodesics (each crosses it at its midpoint).  The red curve is the geodesic
   that leaves p in the chosen direction and makes 2m+1 half-turns; its interior conjugate points are
   marked.  Drag the sphere to turn it.  Below: the groups pi_{n+k}(S^n) (Toda), with the range of
   Corollary 22.3 for the chosen n.  Colours from --fg, --bg, --accent, --muted (with fallbacks). */
(function () {
  "use strict";
  var root = document.getElementById("antipodes-figure");
  if (!root) { return; }

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

  // pi_{n+k}(S^n), n = 1..8, k = 0..7 (Toda, Composition Methods in Homotopy Groups of Spheres, 1962)
  var TABLE = {
    1: ["Z", "0", "0", "0", "0", "0", "0", "0"],
    2: ["Z", "Z", "2", "2", "12", "2", "2", "3"],
    3: ["Z", "2", "2", "12", "2", "2", "3", "15"],
    4: ["Z", "2", "2", "Z+12", "2\u00b2", "2\u00b2", "24+3", "15"],
    5: ["Z", "2", "2", "24", "2", "2", "2", "30"],
    6: ["Z", "2", "2", "24", "0", "Z", "2", "60"],
    7: ["Z", "2", "2", "24", "0", "0", "2", "120"],
    8: ["Z", "2", "2", "24", "0", "0", "2", "Z+120"]
  };

  // ---------- state ----------
  var azim = -35 * Math.PI / 180, elev = 18 * Math.PI / 180;
  var dirDeg = 70;     // direction of departure from p (angle of u on the equator)
  var halfTurns = 3;   // 2m + 1
  var nDim = 1;        // the sphere is S^{n+1}; the drawing shows the case n = 1

  // ---------- layout ----------
  root.innerHTML = "";
  root.style.maxWidth = "680px";
  root.style.margin = "1em auto";
  var canvas = el("canvas");
  canvas.style.width = "100%";
  canvas.style.display = "block";
  canvas.style.touchAction = "none";
  canvas.style.cursor = "grab";
  root.appendChild(canvas);

  var controls = el("div");
  controls.style.display = "flex";
  controls.style.flexWrap = "wrap";
  controls.style.gap = "0.35em 1.2em";
  controls.style.margin = "0.5em 0";
  controls.style.fontSize = "0.9em";
  root.appendChild(controls);

  function slider(label, min, max, step, value, fmt, onInput) {
    var wrap = el("label");
    wrap.style.display = "flex";
    wrap.style.alignItems = "center";
    wrap.style.gap = "0.4em";
    var span = el("span", null, label);
    var input = el("input", { type: "range", min: String(min), max: String(max), step: String(step), value: String(value) });
    input.style.width = "120px";
    var out = el("span", null, fmt(value));
    out.style.minWidth = "2.6em";
    input.addEventListener("input", function () { out.textContent = fmt(Number(input.value)); onInput(Number(input.value)); });
    wrap.appendChild(span); wrap.appendChild(input); wrap.appendChild(out);
    controls.appendChild(wrap);
  }
  slider("direction", 0, 359, 1, dirDeg, function (v) { return v + "\u00b0"; }, function (v) { dirDeg = v; draw(); });
  slider("half-turns", 1, 7, 2, halfTurns, function (v) { return String(v); }, function (v) { halfTurns = v; draw(); });
  slider("n (sphere S\u207f\u207a\u00b9)", 1, 7, 1, nDim, function (v) { return String(v); }, function (v) { nDim = v; draw(); });

  var info = el("div");
  info.style.fontSize = "0.88em";
  info.style.lineHeight = "1.45";
  root.appendChild(info);

  var tableWrap = el("div");
  tableWrap.style.overflowX = "auto";
  tableWrap.style.marginTop = "0.4em";
  root.appendChild(tableWrap);

  // ---------- geometry ----------
  var W = 400, H = 360, dpr = 1;
  function resize() {
    W = Math.max(240, Math.min(root.clientWidth || 360, 680));
    H = Math.round(Math.min(W * 0.78, 400));
    dpr = window.devicePixelRatio || 1;
    canvas.width = Math.round(W * dpr);
    canvas.height = Math.round(H * dpr);
    canvas.style.height = H + "px";
  }
  function project(P) {
    var x1 = Math.cos(azim) * P[0] - Math.sin(azim) * P[1];
    var y1 = Math.sin(azim) * P[0] + Math.cos(azim) * P[1];
    var z1 = P[2];
    var yv = Math.cos(elev) * z1 - Math.sin(elev) * y1;
    var dv = Math.sin(elev) * z1 + Math.cos(elev) * y1;   // > 0: near hemisphere
    var R = Math.min(W, H) * 0.38;
    return [W / 2 + R * x1, H / 2 - R * yv, dv];
  }
  function curve(ctx, pts, colour, width, dashBack) {
    var prev = null;
    for (var i = 0; i < pts.length; i++) {
      var q = project(pts[i]);
      if (prev) {
        var front = (q[2] + prev[2]) / 2 >= 0;
        ctx.beginPath();
        ctx.moveTo(prev[0], prev[1]); ctx.lineTo(q[0], q[1]);
        ctx.strokeStyle = colour;
        ctx.lineWidth = front ? width : Math.max(1, width * 0.6);
        ctx.globalAlpha = front ? 1 : 0.45;
        ctx.setLineDash(front || !dashBack ? [] : [3, 4]);
        ctx.stroke();
      }
      prev = q;
    }
    ctx.globalAlpha = 1; ctx.setLineDash([]);
  }
  function geodesicPoint(s, u, offset) {
    var r = 1 + offset * s / Math.PI;
    return [r * Math.sin(s) * u[0], r * Math.sin(s) * u[1], r * Math.cos(s)];
  }

  function conjTimes(m) {
    var out = [];
    for (var j = 1; j <= 2 * m; j++) { out.push(j + "/" + (2 * m + 1)); }
    return out.join(", ");
  }

  function draw() {
    resize();
    var ctx = canvas.getContext("2d");
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    var fg = cssVar("--fg", "#222"), bg = cssVar("--bg", "#fff");
    var accent = cssVar("--accent", "#c0392b"), muted = cssVar("--muted", "#999");
    var blue = "#2e6fba";
    ctx.fillStyle = bg; ctx.fillRect(0, 0, W, H);
    var R = Math.min(W, H) * 0.38;
    ctx.beginPath(); ctx.arc(W / 2, H / 2, R, 0, 2 * Math.PI);
    ctx.strokeStyle = fg; ctx.lineWidth = 1; ctx.stroke();

    var i, s, pts;
    // meridians = minimal geodesics
    for (i = 0; i < 12; i++) {
      var a = i * Math.PI / 6, um = [Math.cos(a), Math.sin(a)];
      pts = [];
      for (s = 0; s <= Math.PI + 1e-9; s += Math.PI / 60) { pts.push(geodesicPoint(s, um, 0)); }
      curve(ctx, pts, muted, 0.8, true);
    }
    // equator = Omega^d
    pts = [];
    for (s = 0; s <= 2 * Math.PI + 1e-9; s += Math.PI / 90) { pts.push([Math.cos(s), Math.sin(s), 0]); }
    curve(ctx, pts, blue, 2.6, true);

    // the selected geodesic
    var phi = dirDeg * Math.PI / 180, u = [Math.cos(phi), Math.sin(phi)];
    var L = halfTurns * Math.PI;
    pts = [];
    for (s = 0; s <= L + 1e-9; s += Math.PI / 90) { pts.push(geodesicPoint(s, u, 0.035)); }
    curve(ctx, pts, accent, 2.2, true);
    // midpoint of the first half-turn: the point of Omega^d = equator for the minimal geodesic in direction u
    var mid = project([u[0], u[1], 0]);
    ctx.beginPath(); ctx.arc(mid[0], mid[1], 5, 0, 2 * Math.PI);
    ctx.fillStyle = blue; ctx.fill();
    // conjugate points
    var m = (halfTurns - 1) / 2;
    for (var j = 1; j <= 2 * m; j++) {
      var c = project(geodesicPoint(j * Math.PI, u, 0.035));
      ctx.beginPath(); ctx.arc(c[0], c[1], 5.5, 0, 2 * Math.PI);
      ctx.fillStyle = bg; ctx.fill();
      ctx.strokeStyle = accent; ctx.lineWidth = 2; ctx.stroke();
    }
    // poles
    var pp = project([0, 0, 1]), qq = project([0, 0, -1]);
    ctx.fillStyle = fg;
    ctx.beginPath(); ctx.arc(pp[0], pp[1], 4, 0, 2 * Math.PI); ctx.fill();
    ctx.beginPath(); ctx.arc(qq[0], qq[1], 4, 0, 2 * Math.PI); ctx.fill();
    ctx.font = "13px sans-serif";
    ctx.fillText("p", pp[0] - 18, pp[1] - 6);
    ctx.fillText("q = \u2212p", qq[0] + 10, qq[1] + 14);
    ctx.fillStyle = blue;
    ctx.font = "12px sans-serif";
    ctx.fillText("\u03a9\u1d48 \u2245 S\u207f (equator)", 8, 18);

    // text
    var n = nDim, lam = 2 * m * n;
    var lines = [];
    lines.push("Red: the geodesic from p to q leaving in direction " + dirDeg + "\u00b0, with " + halfTurns +
      " half-turn" + (halfTurns > 1 ? "s" : "") + ": length " + halfTurns + "\u03c0, energy (" + halfTurns + "\u03c0)\u00b2." +
      (m === 0 ? " It is minimal; the blue dot is its midpoint on the equator, which identifies \u03a9\u1d48 with S\u207f." :
        " It passes through p or q " + (2 * m) + " times before the end (open circles, at t = " + conjTimes(m) +
        "), each a conjugate point of multiplicity n."));
    lines.push("On S<sup>" + (n + 1) + "</sup> (n = " + n + "): index = 2m\u00b7n = <b>" + lam + "</b>. Every non-minimal geodesic has index \u2265 \u03bb\u2080 = 2n = " +
      (2 * n) + ", and Corollary 22.3 gives \u03c0<sub>i</sub>(S<sup>" + n + "</sup>) \u2245 \u03c0<sub>i+1</sub>(S<sup>" + (n + 1) +
      "</sup>) for i \u2264 2n\u22122 = " + (2 * n - 2) + ".");
    info.innerHTML = lines.join("<br>");

    // table
    var html = "<table style='border-collapse:collapse;font-size:0.82em;margin:0 auto'>";
    html += "<tr><td></td>";
    for (var k = 0; k < 8; k++) { html += "<td style='padding:2px 5px;text-align:center'>k=" + k + "</td>"; }
    html += "</tr>";
    for (var r = 1; r <= 8; r++) {
      var rowSel = (r === n), rowNext = (r === n + 1);
      html += "<tr><td style='padding:2px 5px;text-align:right" + (rowSel || rowNext ? ";font-weight:bold" : "") + "'>S<sup>" + r + "</sup></td>";
      for (k = 0; k < 8; k++) {
        var stable = (r >= k + 2);
        var inRange = (rowSel && k <= n - 2) || (rowNext && k <= n - 2);
        var style = "padding:2px 5px;text-align:center;border:1px solid " + muted + ";";
        if (stable) { style += "background:rgba(46,111,186,0.16);"; }
        if (inRange) { style += "outline:2px solid " + accent + ";outline-offset:-2px;font-weight:bold;"; }
        html += "<td style='" + style + "'>" + TABLE[r][k] + "</td>";
      }
      html += "</tr>";
    }
    html += "</table>";
    html += "<div style='font-size:0.8em;margin-top:0.3em'>\u03c0<sub>n+k</sub>(S<sup>n</sup>) after Toda; Z = integers, m = Z/m, 2\u00b2 = Z/2\u2295Z/2, + = direct sum. " +
      "Shaded: n \u2265 k+2, where Corollary 22.3 forces the entry to equal the one below it. Outlined: the pairs given by your n.</div>";
    tableWrap.innerHTML = html;
  }

  // ---------- rotation by dragging ----------
  var last = null;
  canvas.addEventListener("pointerdown", function (ev) {
    last = [ev.clientX, ev.clientY];
    canvas.style.cursor = "grabbing";
    if (canvas.setPointerCapture) { canvas.setPointerCapture(ev.pointerId); }
  });
  canvas.addEventListener("pointermove", function (ev) {
    if (!last) { return; }
    var dx = ev.clientX - last[0], dy = ev.clientY - last[1];
    last = [ev.clientX, ev.clientY];
    azim -= dx * 0.01;
    elev = Math.max(-1.2, Math.min(1.2, elev + dy * 0.01));
    draw();
  });
  function stop() { last = null; canvas.style.cursor = "grab"; }
  canvas.addEventListener("pointerup", stop);
  canvas.addEventListener("pointercancel", stop);
  window.addEventListener("resize", draw);
  draw();
})();
