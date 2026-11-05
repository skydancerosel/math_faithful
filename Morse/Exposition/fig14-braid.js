// Chapter 14 figure: the eigenvalue braid of a geodesic t -> exp(tA) from I to -I in SU(2m).
// The eigenvalues exp(i*pi*k_j*t) are drawn at radius 1 + t; two of them with k_j != k_l collide
// exactly at the conjugate points of Lemma 4.1, and each collision adds 2 to the index.
// Plain JavaScript, no libraries.  Looks for <div id="braid-figure">.
(function () {
  "use strict";
  var root = document.getElementById("braid-figure");
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
      accent: cssVar("--accent", "#c0392b"),
      muted: cssVar("--muted", "#9a9a9a")
    };
  }

  // ---------- state ----------
  var state = { m: 2, t: 0.5, ks: [3, 1, -1, -3] };

  function minimalKs(m) {
    var ks = [];
    for (var i = 0; i < m; i++) ks.push(1);
    for (var j = 0; j < m; j++) ks.push(-1);
    return ks;
  }
  function sortDesc(ks) {
    return ks.slice().sort(function (a, b) { return b - a; });
  }
  function randomNonMinimal(m) {
    var ks = minimalKs(m);
    var n = ks.length;
    var steps = 1 + Math.floor(Math.random() * Math.min(3, m + 1));
    for (var s = 0; s < steps; s++) {
      var j = Math.floor(Math.random() * n);
      var l = Math.floor(Math.random() * n);
      if (j === l) { l = (j + 1) % n; }
      if (ks[j] + 2 <= 7 && ks[l] - 2 >= -7) { ks[j] += 2; ks[l] -= 2; }
    }
    var allUnit = ks.every(function (k) { return Math.abs(k) === 1; });
    if (allUnit) { ks[0] += 2; ks[n - 1] -= 2; }
    return sortDesc(ks);
  }
  function pump(ks) {
    var k = sortDesc(ks);
    if (k[0] + 2 > 9 || k[k.length - 1] - 2 < -9) return k;
    k[0] += 2;
    k[k.length - 1] -= 2;
    return sortDesc(k);
  }

  // all collisions (t, angle) with 0 < t < 1, one per pair of indices and multiple
  function collisions(ks) {
    var out = [];
    for (var j = 0; j < ks.length; j++) {
      for (var l = j + 1; l < ks.length; l++) {
        var d = Math.abs(ks[j] - ks[l]);
        if (d === 0) continue;
        for (var s = 1; s < d / 2; s++) {
          var t = (2 * s) / d;
          out.push({ t: t, ang: Math.PI * ks[j] * t, label: "2\u00b7" + s + "/" + d });
        }
      }
    }
    return out;
  }
  function indexFormula(ks) {
    var lam = 0;
    for (var j = 0; j < ks.length; j++)
      for (var l = 0; l < ks.length; l++)
        if (ks[j] > ks[l]) lam += ks[j] - ks[l] - 2;
    return lam;
  }
  function isMinimal(ks) {
    return ks.every(function (k) { return Math.abs(k) === 1; });
  }

  // ---------- DOM ----------
  root.innerHTML = "";
  root.style.maxWidth = "560px";
  root.style.margin = "1em auto";
  root.style.fontFamily = "inherit";

  var canvas = document.createElement("canvas");
  canvas.style.display = "block";
  canvas.style.width = "100%";
  canvas.style.touchAction = "none";
  root.appendChild(canvas);

  var panel = document.createElement("div");
  panel.style.fontSize = "14px";
  panel.style.lineHeight = "1.4";
  panel.style.marginTop = "6px";
  root.appendChild(panel);

  function makeSlider(labelText, min, max, step, value, oninput) {
    var wrap = document.createElement("label");
    wrap.style.display = "flex";
    wrap.style.alignItems = "center";
    wrap.style.gap = "8px";
    wrap.style.margin = "4px 0";
    var span = document.createElement("span");
    span.style.minWidth = "5.5em";
    var input = document.createElement("input");
    input.type = "range";
    input.min = String(min);
    input.max = String(max);
    input.step = String(step);
    input.value = String(value);
    input.style.flex = "1";
    input.style.minWidth = "0";
    input.addEventListener("input", function () { oninput(parseFloat(input.value), span); });
    wrap.appendChild(span);
    wrap.appendChild(input);
    oninput(value, span);
    return { wrap: wrap, input: input, span: span };
  }

  var controls = document.createElement("div");
  root.insertBefore(controls, panel);

  var tSlider = makeSlider("t", 0, 1, 0.001, state.t, function (v, span) {
    state.t = v;
    span.textContent = "time t = " + v.toFixed(3);
    draw();
  });
  var mSlider = makeSlider("m", 1, 4, 1, state.m, function (v, span) {
    span.textContent = "m = " + v + " (SU(" + 2 * v + "))";
    if (v !== state.m) {
      state.m = v;
      state.ks = randomNonMinimal(v);
    }
    draw();
  });
  controls.appendChild(tSlider.wrap);
  controls.appendChild(mSlider.wrap);

  var buttons = document.createElement("div");
  buttons.style.display = "flex";
  buttons.style.flexWrap = "wrap";
  buttons.style.gap = "6px";
  buttons.style.margin = "4px 0";
  function makeButton(text, onclick) {
    var b = document.createElement("button");
    b.type = "button";
    b.textContent = text;
    b.style.padding = "4px 10px";
    b.style.font = "inherit";
    b.style.fontSize = "13px";
    b.style.cursor = "pointer";
    b.addEventListener("click", function () { onclick(); draw(); });
    buttons.appendChild(b);
    return b;
  }
  makeButton("minimal", function () { state.ks = minimalKs(state.m); });
  makeButton("random non-minimal", function () { state.ks = randomNonMinimal(state.m); });
  makeButton("pump: k\u2081+2, k\u2082\u2098\u22122", function () { state.ks = pump(state.ks); });
  makeButton("play", function () { play(); });
  controls.appendChild(buttons);

  var playing = null;
  function play() {
    if (playing) { cancelAnimationFrame(playing); playing = null; return; }
    var start = null;
    function step(ts) {
      if (start === null) start = ts - state.t * 6000;
      var t = (ts - start) / 6000;
      if (t >= 1) { t = 1; playing = null; } else { playing = requestAnimationFrame(step); }
      state.t = t;
      tSlider.input.value = String(t);
      tSlider.span.textContent = "time t = " + t.toFixed(3);
      draw();
    }
    playing = requestAnimationFrame(step);
  }

  // ---------- drawing ----------
  var size = 360;
  function resize() {
    var w = Math.max(260, Math.min(root.clientWidth || 360, 560));
    size = w;
    var dpr = window.devicePixelRatio || 1;
    canvas.width = Math.round(w * dpr);
    canvas.height = Math.round(w * dpr);
    canvas.style.height = w + "px";
    var ctx = canvas.getContext("2d");
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    draw();
  }

  function draw() {
    var c = colours();
    var ctx = canvas.getContext("2d");
    var w = size, h = size;
    ctx.clearRect(0, 0, w, h);
    ctx.fillStyle = c.bg;
    ctx.fillRect(0, 0, w, h);
    var cx = w / 2, cy = h / 2;
    var R = (w / 2 - 28) / 2; // radius 2 (t = 1) fits
    function P(r, ang) { return [cx + R * r * Math.cos(ang), cy - R * r * Math.sin(ang)]; }

    // rings
    ctx.lineWidth = 1;
    for (var i = 0; i <= 4; i++) {
      var tt = i / 4;
      ctx.strokeStyle = c.muted;
      ctx.globalAlpha = (i === 0 || i === 4) ? 0.8 : 0.35;
      ctx.beginPath();
      ctx.arc(cx, cy, R * (1 + tt), 0, 2 * Math.PI);
      ctx.stroke();
    }
    ctx.globalAlpha = 1;
    // current ring
    ctx.setLineDash([4, 4]);
    ctx.strokeStyle = c.accent;
    ctx.globalAlpha = 0.6;
    ctx.beginPath();
    ctx.arc(cx, cy, R * (1 + state.t), 0, 2 * Math.PI);
    ctx.stroke();
    ctx.setLineDash([]);
    ctx.globalAlpha = 1;

    var ks = state.ks;
    var distinct = [];
    ks.forEach(function (k) { if (distinct.indexOf(k) < 0) distinct.push(k); });

    // spirals: whole path faint, traversed part solid
    distinct.forEach(function (k) {
      var N = 240;
      ctx.lineWidth = 1.5;
      ctx.strokeStyle = c.muted;
      ctx.globalAlpha = 0.45;
      ctx.beginPath();
      for (var s = 0; s <= N; s++) {
        var t = s / N, p = P(1 + t, Math.PI * k * t);
        if (s === 0) ctx.moveTo(p[0], p[1]); else ctx.lineTo(p[0], p[1]);
      }
      ctx.stroke();
      ctx.globalAlpha = 1;
      ctx.lineWidth = 2.4;
      ctx.strokeStyle = c.fg;
      ctx.beginPath();
      var M = Math.max(1, Math.round(N * state.t));
      for (var q = 0; q <= M; q++) {
        var t2 = (q / M) * state.t, p2 = P(1 + t2, Math.PI * k * t2);
        if (q === 0) ctx.moveTo(p2[0], p2[1]); else ctx.lineTo(p2[0], p2[1]);
      }
      ctx.stroke();
    });

    // collisions
    var cols = collisions(ks);
    var passed = 0;
    cols.forEach(function (o) {
      var p = P(1 + o.t, o.ang);
      var done = o.t <= state.t + 1e-9;
      if (done) passed++;
      ctx.beginPath();
      ctx.arc(p[0], p[1], done ? 5.5 : 4.5, 0, 2 * Math.PI);
      if (done) {
        ctx.fillStyle = c.accent;
        ctx.fill();
        ctx.strokeStyle = c.fg;
        ctx.lineWidth = 1;
        ctx.stroke();
      } else {
        ctx.strokeStyle = c.accent;
        ctx.lineWidth = 1.5;
        ctx.stroke();
      }
    });

    // current eigenvalues; eigenvalues that coincide share one marker and one label
    var groups = [];
    distinct.forEach(function (k) {
      var mult = ks.filter(function (x) { return x === k; }).length;
      var p = P(1 + state.t, Math.PI * k * state.t);
      var txt = String(k).replace("-", "\u2212") + (mult > 1 ? "\u00d7" + mult : "");
      for (var g = 0; g < groups.length; g++) {
        if (Math.abs(groups[g].p[0] - p[0]) < 3 && Math.abs(groups[g].p[1] - p[1]) < 3) {
          groups[g].txt += ", " + txt;
          groups[g].n += mult;
          return;
        }
      }
      groups.push({ p: p, k: k, txt: txt, n: mult });
    });
    groups.forEach(function (gr) {
      var p = gr.p;
      ctx.beginPath();
      ctx.arc(p[0], p[1], 4 + gr.n, 0, 2 * Math.PI);
      ctx.fillStyle = c.bg;
      ctx.fill();
      ctx.lineWidth = 2;
      ctx.strokeStyle = c.fg;
      ctx.stroke();
      ctx.fillStyle = c.fg;
      ctx.font = "12px sans-serif";
      ctx.textAlign = "center";
      ctx.textBaseline = "middle";
      var lp = P(1 + state.t + 0.2, Math.PI * gr.k * state.t);
      ctx.fillText(gr.txt, lp[0], lp[1]);
    });

    // endpoints
    ctx.fillStyle = c.fg;
    ctx.font = "13px sans-serif";
    ctx.textAlign = "left";
    var pI = P(1, 0), pm = P(2, Math.PI);
    ctx.beginPath(); ctx.arc(pI[0], pI[1], 3, 0, 2 * Math.PI); ctx.fill();
    ctx.beginPath(); ctx.arc(pm[0], pm[1], 3, 0, 2 * Math.PI); ctx.fill();
    ctx.fillText("I", pI[0] + 6, pI[1] + 12);
    ctx.textAlign = "left";
    ctx.fillText("\u2212I", pm[0] + 4, pm[1] + 14);

    // text panel
    var lam = indexFormula(ks);
    var minimal = isMinimal(ks);
    var html = "";
    html += "<div>k = (" + ks.join(", ").replace(/-/g, "\u2212") + "), sum = " +
      ks.reduce(function (a, b) { return a + b; }, 0) + "</div>";
    html += "<div>collisions passed: <b>" + passed + "</b> of " + cols.length +
      " &nbsp;\u2192&nbsp; contribution 2 \u00d7 " + passed + " = " + 2 * passed + "</div>";
    html += "<div>index \u03bb = \u03a3<sub>k\u2c7c &gt; k\u2097</sub>(k\u2c7c \u2212 k\u2097 \u2212 2) = <b>" +
      lam + "</b> (= 2 \u00d7 " + cols.length + " collisions)</div>";
    if (minimal) {
      html += "<div>minimal geodesic: no collisions before t = 1, \u03bb = 0.</div>";
    } else {
      html += "<div>non-minimal: Milnor's bound \u03bb \u2265 2m + 2 = " + (2 * state.m + 2) +
        (lam >= 2 * state.m + 2 ? " \u2714" : " (violated?)") + "</div>";
    }
    panel.innerHTML = html;
    panel.style.color = c.fg;
  }

  window.addEventListener("resize", resize);
  resize();
})();
