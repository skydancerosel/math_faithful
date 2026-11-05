// Chapter 15 figure: the sixteen pieces of R^16 and the eight-step chain Omega_0 > ... > Omega_8.
// R^16 with the anti-commuting complex structures J'_1..J'_8 splits into the sixteen joint eigenlines
// of theta3 = J1J2J3, theta5 = J1J4J5, theta6 = J2J4J6, theta7 = J1J6J7, drawn as a 4 x 4 grid.
// At stage k only the thetas with indices <= k are defined; lines on which they agree form one block.
// A button J_a shows how J_a permutes the blocks.  Plain JavaScript, no libraries.
// Looks for <div id="clifford-figure">.
(function () {
  "use strict";
  var root = document.getElementById("clifford-figure");
  if (!root) return;

  function cssVar(name, fallback) {
    var v = "";
    try {
      v = getComputedStyle(root).getPropertyValue(name);
      if (!v) v = getComputedStyle(document.documentElement).getPropertyValue(name);
    } catch (e) {
      v = "";
    }
    v = (v || "").trim();
    return v || fallback;
  }
  function colours() {
    return {
      fg: cssVar("--fg", "#1d1d1f"),
      bg: cssVar("--bg", "#ffffff"),
      accent: cssVar("--accent", "#1f5f99"),
      muted: cssVar("--muted", "#9a9a9a")
    };
  }

  // flip patterns: which of (theta3, theta5, theta6, theta7) anti-commute with J_a
  var FLIPS = {
    1: [0, 0, 1, 0], 2: [0, 1, 0, 1], 3: [0, 1, 1, 1], 4: [1, 0, 0, 1],
    5: [1, 0, 1, 1], 6: [1, 1, 0, 0], 7: [1, 1, 1, 0], 8: [1, 1, 1, 1]
  };
  var THETA_INDEX = [3, 5, 6, 7];
  var ORDER = [[1, 1], [1, -1], [-1, 1], [-1, -1]];

  var INFO = [
    { space: "\u03a9\u2080(16r) = O(16r)", m: 1, cls: 1, pi: "\u2124/2",
      note: "No structures yet: the whole space is one block." },
    { space: "\u03a9\u2081 = complex structures \u2245 O(16r)/U(8r)", m: 2, cls: 1, pi: "\u2124/2",
      note: "Minimal geodesics from I to \u2212I in O(n) (Lemma 24.1)." },
    { space: "\u03a9\u2082 \u2245 U(8r)/Sp(4r) (quaternionic structures)", m: 4, cls: 1, pi: "0",
      note: "J\u2081, J\u2082, J\u2081J\u2082 act like i, j, k." },
    { space: "\u03a9\u2083 \u2194 quaternionic subspaces V\u2081 = {\u03b8\u2083 = +1}", m: 4, cls: 2,
      pi: "\u2124", note: "\u03b8\u2083 splits R\u00b9\u2076 = V\u2081 \u2295 V\u2082; two minimal modules (\u03b8\u2083 = \u00b11)." },
    { space: "\u03a9\u2084 \u2194 quaternionic isometries V\u2081 \u2192 V\u2082 \u2245 Sp(2r)", m: 8, cls: 1,
      pi: "0", note: "J\u2084 exchanges V\u2081 and V\u2082 (Lemma 24.6-(4))." },
    { space: "\u03a9\u2085 \u2194 W \u2282 V\u2081 with V\u2081 = W \u2295 J\u2082W \u2245 Sp(2r)/U(2r)", m: 8, cls: 1,
      pi: "0", note: "\u03b8\u2085 cuts V\u2081 into W and J\u2082W." },
    { space: "\u03a9\u2086 \u2194 X \u2282 W with W = X \u2295 J\u2081X \u2245 U(2r)/O(2r)", m: 8, cls: 1,
      pi: "0", note: "\u03b8\u2086 cuts W into X and J\u2081X." },
    { space: "\u03a9\u2087 \u2194 subspaces X\u2081 of X \u2245 R\u00b2\u02b3 (real Grassmannians)", m: 8, cls: 2,
      pi: "\u2124", note: "\u03b8\u2087 cuts X into X\u2081 and X\u2082; two minimal modules again." },
    { space: "\u03a9\u2088 \u2194 isometries X\u2081 \u2192 X\u2082 \u2245 O(r)", m: 16, cls: 1,
      pi: "\u2124/2 = \u03c0\u2080O", note: "Back to an orthogonal group: \u03c0\u1d62O \u2245 \u03c0\u1d62\u208a\u2088O." }
  ];

  var state = { k: 8, a: 1 };

  // ---------- DOM ----------
  root.innerHTML = "";
  root.style.maxWidth = "560px";
  root.style.margin = "1em auto";

  var canvas = document.createElement("canvas");
  canvas.style.display = "block";
  canvas.style.width = "100%";
  root.appendChild(canvas);

  var controls = document.createElement("div");
  controls.style.fontSize = "14px";
  root.appendChild(controls);

  var sliderWrap = document.createElement("label");
  sliderWrap.style.display = "flex";
  sliderWrap.style.alignItems = "center";
  sliderWrap.style.gap = "8px";
  sliderWrap.style.margin = "6px 0";
  var sliderLabel = document.createElement("span");
  sliderLabel.style.minWidth = "4.5em";
  var slider = document.createElement("input");
  slider.type = "range";
  slider.min = "0";
  slider.max = "8";
  slider.step = "1";
  slider.value = String(state.k);
  slider.style.flex = "1";
  slider.style.minWidth = "0";
  sliderWrap.appendChild(sliderLabel);
  sliderWrap.appendChild(slider);
  controls.appendChild(sliderWrap);

  var buttonRow = document.createElement("div");
  buttonRow.style.display = "flex";
  buttonRow.style.flexWrap = "wrap";
  buttonRow.style.gap = "5px";
  buttonRow.style.margin = "4px 0";
  controls.appendChild(buttonRow);
  var buttons = [];
  for (var a = 1; a <= 8; a++) {
    (function (alpha) {
      var b = document.createElement("button");
      b.type = "button";
      b.textContent = "J" + String.fromCharCode(0x2080 + alpha);
      b.style.padding = "3px 9px";
      b.style.font = "inherit";
      b.style.fontSize = "13px";
      b.style.cursor = "pointer";
      b.addEventListener("click", function () {
        state.a = (state.a === alpha) ? 0 : alpha;
        draw();
      });
      buttonRow.appendChild(b);
      buttons.push(b);
    })(a);
  }

  var panel = document.createElement("div");
  panel.style.fontSize = "14px";
  panel.style.lineHeight = "1.45";
  panel.style.marginTop = "4px";
  root.appendChild(panel);

  slider.addEventListener("input", function () {
    state.k = parseInt(slider.value, 10);
    if (state.a > state.k) state.a = 0;
    draw();
  });

  // ---------- geometry ----------
  var size = 360;
  function resize() {
    var w = Math.max(260, Math.min(root.clientWidth || 360, 560));
    size = w;
    var dpr = window.devicePixelRatio || 1;
    canvas.width = Math.round(w * dpr);
    canvas.height = Math.round(w * 0.92 * dpr);
    canvas.style.height = Math.round(w * 0.92) + "px";
    canvas.getContext("2d").setTransform(dpr, 0, 0, dpr, 0, 0);
    draw();
  }

  function cellOf(eps) {
    var r = 0, c = 0;
    for (var i = 0; i < 4; i++) {
      if (ORDER[i][0] === eps[0] && ORDER[i][1] === eps[1]) r = i;
      if (ORDER[i][0] === eps[2] && ORDER[i][1] === eps[3]) c = i;
    }
    return [r, c];
  }
  function allPatterns() {
    var out = [];
    [1, -1].forEach(function (e3) {
      [1, -1].forEach(function (e5) {
        [1, -1].forEach(function (e6) {
          [1, -1].forEach(function (e7) { out.push([e3, e5, e6, e7]); });
        });
      });
    });
    return out;
  }
  function available(k) {
    return THETA_INDEX.map(function (t) { return t <= k; });
  }
  function blockKey(eps, avail) {
    var s = "";
    for (var i = 0; i < 4; i++) if (avail[i]) s += (eps[i] > 0 ? "+" : "-");
    return s;
  }
  function sgn(e) { return e > 0 ? "+" : "\u2212"; }

  function draw() {
    var c = colours();
    var ctx = canvas.getContext("2d");
    var W = size, H = Math.round(size * 0.92);
    ctx.clearRect(0, 0, W, H);
    ctx.fillStyle = c.bg;
    ctx.fillRect(0, 0, W, H);

    var k = state.k;
    var avail = available(k);
    sliderLabel.textContent = "k = " + k;
    buttons.forEach(function (b, i) {
      var alpha = i + 1;
      b.disabled = alpha > k;
      b.style.opacity = alpha > k ? "0.4" : "1";
      b.style.fontWeight = (alpha === state.a) ? "bold" : "normal";
      b.style.outline = (alpha === state.a) ? "2px solid " + c.accent : "none";
    });

    // grid placement
    var margin = 34, top = 30;
    var gw = Math.min(W - 2 * margin, H - top - 26);
    var cs = gw / 4;
    var x0 = (W - gw) / 2, y0 = top;

    // header labels (column and row sign pairs)
    ctx.fillStyle = c.muted;
    ctx.font = "11px sans-serif";
    ctx.textAlign = "center";
    ctx.textBaseline = "middle";
    ctx.fillText("(\u03b8\u2086, \u03b8\u2087)", x0 + gw / 2, y0 - 20);
    for (var j = 0; j < 4; j++) {
      ctx.fillText(sgn(ORDER[j][0]) + sgn(ORDER[j][1]), x0 + (j + 0.5) * cs, y0 - 8);
      ctx.save();
      ctx.translate(x0 - 12, y0 + (j + 0.5) * cs);
      ctx.fillText(sgn(ORDER[j][0]) + sgn(ORDER[j][1]), 0, 0);
      ctx.restore();
    }
    ctx.save();
    ctx.translate(x0 - 26, y0 + gw / 2);
    ctx.rotate(-Math.PI / 2);
    ctx.fillText("(\u03b8\u2083, \u03b8\u2085)", 0, 0);
    ctx.restore();

    // blocks
    var pats = allPatterns();
    var keys = [];
    pats.forEach(function (p) {
      var key = blockKey(p, avail);
      if (keys.indexOf(key) < 0) keys.push(key);
    });
    keys.sort(); // "+" sorts before "-": the all-plus block (containing X_1) comes first
    var nb = keys.length;
    var boxes = {};
    pats.forEach(function (p) {
      var rc = cellOf(p);
      var key = blockKey(p, avail);
      var bx = boxes[key] || { r0: 9, r1: -1, c0: 9, c1: -1 };
      bx.r0 = Math.min(bx.r0, rc[0]); bx.r1 = Math.max(bx.r1, rc[0]);
      bx.c0 = Math.min(bx.c0, rc[1]); bx.c1 = Math.max(bx.c1, rc[1]);
      boxes[key] = bx;
    });

    // cell fills by block
    pats.forEach(function (p) {
      var rc = cellOf(p);
      var key = blockKey(p, avail);
      var idx = keys.indexOf(key);
      ctx.fillStyle = c.accent;
      ctx.globalAlpha = nb === 1 ? 0.12 : 0.08 + 0.42 * (1 - idx / Math.max(1, nb - 1));
      ctx.fillRect(x0 + rc[1] * cs + 1, y0 + rc[0] * cs + 1, cs - 2, cs - 2);
      ctx.globalAlpha = 1;
      ctx.fillStyle = c.fg;
      ctx.font = Math.max(10, Math.round(cs * 0.2)) + "px monospace";
      ctx.textAlign = "center";
      ctx.textBaseline = "middle";
      ctx.fillText(p.map(sgn).join(""), x0 + (rc[1] + 0.5) * cs, y0 + (rc[0] + 0.5) * cs);
    });

    // block outlines
    keys.forEach(function (key, idx) {
      var bx = boxes[key];
      ctx.lineWidth = idx === 0 ? 3 : 1.6;
      ctx.strokeStyle = idx === 0 ? c.accent : c.fg;
      ctx.strokeRect(x0 + bx.c0 * cs + 1.5, y0 + bx.r0 * cs + 1.5,
        (bx.c1 - bx.c0 + 1) * cs - 3, (bx.r1 - bx.r0 + 1) * cs - 3);
    });

    // action of the selected J_a on blocks
    var actionText = "";
    if (state.a >= 1 && state.a <= k) {
      var f = FLIPS[state.a];
      var fl = [];
      for (var i = 0; i < 4; i++) if (avail[i] && f[i]) fl.push("\u03b8" + String.fromCharCode(0x2080 + THETA_INDEX[i]));
      if (fl.length === 0) {
        actionText = "J" + String.fromCharCode(0x2080 + state.a) +
          " commutes with every \u03b8 defined so far: it maps each block to itself.";
      } else {
        actionText = "J" + String.fromCharCode(0x2080 + state.a) + " reverses the sign of " +
          fl.join(", ") + ", so it exchanges the blocks in pairs.";
        var done = {};
        keys.forEach(function (key) {
          if (done[key]) return;
          // image block key
          var chars = key.split("");
          var q = 0;
          var img = "";
          for (var i2 = 0; i2 < 4; i2++) {
            if (!avail[i2]) continue;
            var ch = chars[q++];
            img += f[i2] ? (ch === "+" ? "-" : "+") : ch;
          }
          done[key] = true;
          done[img] = true;
          var b1 = boxes[key], b2 = boxes[img];
          var p1 = [x0 + (b1.c0 + b1.c1 + 1) / 2 * cs, y0 + (b1.r0 + b1.r1 + 1) / 2 * cs];
          var p2 = [x0 + (b2.c0 + b2.c1 + 1) / 2 * cs, y0 + (b2.r0 + b2.r1 + 1) / 2 * cs];
          drawArrow(ctx, p1, p2, c.fg);
        });
      }
    }

    // panel
    var info = INFO[k];
    var nCopies = 16 / info.m;
    var html = "";
    html += "<div><b>k = " + k + "</b>: " + info.space + "</div>";
    html += "<div>" + info.note + "</div>";
    html += "<div>minimal module: dimension m<sub>" + k + "</sub> = " + info.m +
      " (R\u00b9\u2076 is " + nCopies + (nCopies === 1 ? " copy" : " copies") + "), " +
      info.cls + (info.cls === 1 ? " isomorphism class" : " isomorphism classes") + "</div>";
    html += "<div>\u03c0<sub>" + k + "</sub>O \u2245 \u03c0<sub>0</sub>\u03a9<sub>" + k + "</sub> = " +
      info.pi + "; blocks: " + nb + "</div>";
    if (actionText) html += "<div>" + actionText + "</div>";
    else if (k >= 1) html += "<div>Tap J\u2081 \u2026 J" + String.fromCharCode(0x2080 + k) +
      " to see how it permutes the blocks.</div>";
    panel.innerHTML = html;
    panel.style.color = c.fg;
  }

  function drawArrow(ctx, p, q, colour) {
    var dx = q[0] - p[0], dy = q[1] - p[1];
    var len = Math.sqrt(dx * dx + dy * dy);
    if (len < 1) return;
    var ux = dx / len, uy = dy / len;
    var shrink = Math.min(14, len / 4);
    var a = [p[0] + ux * shrink, p[1] + uy * shrink];
    var b = [q[0] - ux * shrink, q[1] - uy * shrink];
    // gentle curve
    var mx = (a[0] + b[0]) / 2 - uy * len * 0.12, my = (a[1] + b[1]) / 2 + ux * len * 0.12;
    ctx.strokeStyle = colour;
    ctx.fillStyle = colour;
    ctx.lineWidth = 1.6;
    ctx.globalAlpha = 0.85;
    ctx.beginPath();
    ctx.moveTo(a[0], a[1]);
    ctx.quadraticCurveTo(mx, my, b[0], b[1]);
    ctx.stroke();
    head(ctx, [mx, my], b);
    head(ctx, [mx, my], a);
    ctx.globalAlpha = 1;
  }
  function head(ctx, from, to) {
    var dx = to[0] - from[0], dy = to[1] - from[1];
    var l = Math.sqrt(dx * dx + dy * dy) || 1;
    var ux = dx / l, uy = dy / l, s = 7;
    ctx.beginPath();
    ctx.moveTo(to[0], to[1]);
    ctx.lineTo(to[0] - ux * s - uy * s * 0.5, to[1] - uy * s + ux * s * 0.5);
    ctx.lineTo(to[0] - ux * s + uy * s * 0.5, to[1] - uy * s - ux * s * 0.5);
    ctx.closePath();
    ctx.fill();
  }

  window.addEventListener("resize", resize);
  resize();
})();
