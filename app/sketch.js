/* Fence sketch module.
 *
 * Semantics taken from the real work-order sheets:
 *  - "build" segments (tick marks) are new fence and count toward the total feet
 *  - "existing" segments (X marks) are neighbor/existing fence: drawn, never counted
 *  - "gate" segments (V symbol) are openings, counted per gate type (Regular / C&T)
 *  - the house sits in the middle; fence ends that touch a house wall get a MATCH
 *    marker (those are the metal posts on the sheets)
 */
'use strict';

const SVGNS = 'http://www.w3.org/2000/svg';
const STORE_KEY = 'fence-calc-sketch-v1';
const VB_RATIO = 560 / 1000;

const svg = document.getElementById('sketch');
const scene = document.getElementById('scene');
const wrap = svg.parentElement;
const popup = document.getElementById('popup');
const tbl = document.getElementById('tbl-sections');
const tbody = document.getElementById('tbody-sections');
const matGrid = document.getElementById('materials-grid');
const defPanel = document.getElementById('defaults-panel');

// ---------------------------------------------------------------- state

const HOUSE_DEFAULT = { x: 430, y: 330, w: 200, h: 130, visible: true };

// fence style, straight from the sheet's Fence table:
// rails count (2/3), finish (Standard / Good Neighbor / Cap & Trim),
// picket width (1x4/1x6), MP and WP marks
const STYLE_DEFAULT = { rails: 3, finish: 'std', picket: '1x4', mp: true, wp: true };
const FINISH_SHORT = { std: '', gn: ' GN', ct: ' C&T' };

// project-wide material choices (the sheet's column selections)
const MATERIALS_DEFAULT = {
  postMat: 'treated', postLen: '8',      // Treated/Cedar-Fir/Metal · 8FT/10FT
  railMat: 'treated', railLen: '8',      // Treat-Fir/CD S4S/Spruce · 2x4x8/10/12
  picketMat: 'cedar', picketLen: '6',    // WW/Cedar/Stained · 6FT/8FT
  capMat: 'spf',                         // SPF-Fir/Cedar (C&T jobs only)
  capLen: '12',                          // 2x6 cap board length: 10/12/14/16
  trimLen: '10',                         // 1x2 trim strip length: 10/16
  nailSystem: 'ft'                       // 'ft': Elite (nails=rolls≈6/100ft) · 'clips': South Texas
};

function styleShort(s) {
  return s.rails + 'R' + FINISH_SHORT[s.finish] + ' · ' + s.picket +
    (s.mp ? ' MP' : '') + (s.wp ? ' WP' : '');
}
function sameStyle(a, b) {
  return a.rails === b.rails && a.finish === b.finish &&
    a.picket === b.picket && !!a.mp === !!b.mp && !!a.wp === !!b.wp;
}
// style a section actually uses: its own override, or the sketch default
function effStyle(seg) { return seg.style || state.style; }

// older saves stored rails as '3r'/'2rct'/... — convert to {rails, finish}
function normalizeStyle(s) {
  if (!s) return s;
  if (typeof s.rails === 'string') {
    const m = s.rails.match(/^(\d)r(gn|ct)?$/);
    s.rails = m ? parseInt(m[1], 10) : 3;
    s.finish = m && m[2] ? m[2] : 'std';
  }
  if (!s.finish) s.finish = 'std';
  return s;
}

let state = load() || {
  house: { ...HOUSE_DEFAULT }, runs: [],
  style: { ...STYLE_DEFAULT }, materials: { ...MATERIALS_DEFAULT }, matOv: {}
};
// run: { pts:[{x,y,post?}], closed:bool, finished:bool, segs:[{type,len,gateStyle,hinge?,style?}] }
// seg types: 'build' | 'existing' | 'gate'; seg.style = per-section override or null
// state.matOv: material key -> hand-adjusted quantity (like the sheet's red numbers)

let sel = null;            // {kind:'seg'|'pt', run, idx} | null
let undoStack = [];
let redoStack = [];

function snapshot() { return JSON.stringify(state); }
function pushUndo() {
  undoStack.push(snapshot());
  if (undoStack.length > 100) undoStack.shift();
  redoStack.length = 0;
}
function undo() {
  if (!undoStack.length) return;
  redoStack.push(snapshot());
  state = JSON.parse(undoStack.pop());
  sel = null;
  render(); save();
}
function redo() {
  if (!redoStack.length) return;
  undoStack.push(snapshot());
  state = JSON.parse(redoStack.pop());
  sel = null;
  render(); save();
}

function save() {
  try { localStorage.setItem(STORE_KEY, snapshot()); } catch (e) { /* private mode */ }
}
function load() {
  try {
    const raw = localStorage.getItem(STORE_KEY);
    if (!raw) return null;
    const st = JSON.parse(raw);
    if (!st || !st.house || !Array.isArray(st.runs)) return null;
    if (!st.style) st.style = { ...STYLE_DEFAULT }; // older saves
    normalizeStyle(st.style);
    st.runs.forEach(run => run.segs.forEach(s => { if (s.style) normalizeStyle(s.style); }));
    st.materials = Object.assign({ ...MATERIALS_DEFAULT }, st.materials || {});
    if (!st.matOv) st.matOv = {};
    return st;
  } catch (e) { return null; }
}

// ---------------------------------------------------------------- geometry

function dist(a, b) { return Math.hypot(a.x - b.x, a.y - b.y); }

function distToSeg(p, a, b) {
  const dx = b.x - a.x, dy = b.y - a.y;
  const l2 = dx * dx + dy * dy;
  if (!l2) return dist(p, a);
  let t = ((p.x - a.x) * dx + (p.y - a.y) * dy) / l2;
  t = Math.max(0, Math.min(1, t));
  return dist(p, { x: a.x + t * dx, y: a.y + t * dy });
}

// fraction (clamped) of the projection of p onto segment [a,b]
function projT(p, a, b) {
  const dx = b.x - a.x, dy = b.y - a.y;
  const l2 = dx * dx + dy * dy || 1;
  const t = ((p.x - a.x) * dx + (p.y - a.y) * dy) / l2;
  return Math.max(0.02, Math.min(0.98, t));
}

// segment list of a run: [[a,b], ...]; the closing segment goes last
function segsOf(run) {
  const out = [];
  for (let i = 0; i < run.pts.length - 1; i++) out.push([run.pts[i], run.pts[i + 1]]);
  if (run.closed && run.pts.length > 2) out.push([run.pts[run.pts.length - 1], run.pts[0]]);
  return out;
}

function pointInPolygon(pts, p) {
  let inside = false;
  for (let i = 0, j = pts.length - 1; i < pts.length; j = i++) {
    const a = pts[i], b = pts[j];
    if ((a.y > p.y) !== (b.y > p.y) &&
        p.x < (b.x - a.x) * (p.y - a.y) / (b.y - a.y) + a.x) inside = !inside;
  }
  return inside;
}

// current open run (the one that accepts new points)
function currentRun() {
  const r = state.runs[state.runs.length - 1];
  return (r && !r.closed && !r.finished) ? r : null;
}

// ---------------------------------------------------------------- units (feet + inches)

// accepts: 52 | 22.6 | 22'6" | 22' 6 | 5ft 1in
function parseFeet(str) {
  str = String(str).trim().toLowerCase();
  if (!str) return null;
  const m = str.match(/^(\d+(?:\.\d+)?)\s*(?:'|ft)?\s*(?:(\d+(?:\.\d+)?)\s*(?:"|in)?)?$/);
  if (!m) return NaN;
  let ft = parseFloat(m[1]);
  if (m[2] != null) ft += parseFloat(m[2]) / 12;
  return ft;
}

function fmtFeet(len) {
  if (len == null) return '??';
  const neg = len < 0 ? '-' : '';
  len = Math.abs(len);
  let ft = Math.floor(len);
  let inch = Math.round((len - ft) * 12);
  if (inch === 12) { ft += 1; inch = 0; }
  return inch ? neg + ft + "'" + inch + '"' : neg + ft + "'";
}

// ---------------------------------------------------------------- viewBox / zoom / pan

let vb = { x: 0, y: 0, w: 1000, h: 560 };

function applyVB() {
  svg.setAttribute('viewBox', vb.x + ' ' + vb.y + ' ' + vb.w + ' ' + vb.h);
  if (typeof positionPopup === 'function') positionPopup(); // popup follows pan/zoom
}
function wpp() { // world units per screen pixel
  return vb.w / svg.getBoundingClientRect().width;
}
function toWorld(cx, cy) {
  const r = svg.getBoundingClientRect();
  return { x: vb.x + (cx - r.left) * vb.w / r.width, y: vb.y + (cy - r.top) * vb.w / r.width };
}
function zoomAtClient(cx, cy, factor) {
  const before = toWorld(cx, cy);
  const w = Math.min(4000, Math.max(220, vb.w / factor));
  vb.w = w;
  vb.h = w * VB_RATIO;
  const r = svg.getBoundingClientRect();
  vb.x = before.x - (cx - r.left) * vb.w / r.width;
  vb.y = before.y - (cy - r.top) * vb.w / r.width;
  applyVB();
}
function fitView() {
  const pts = [];
  state.runs.forEach(r => r.pts.forEach(p => pts.push(p)));
  if (state.house.visible) {
    pts.push({ x: state.house.x, y: state.house.y });
    pts.push({ x: state.house.x + state.house.w, y: state.house.y + state.house.h });
  }
  if (!pts.length) { vb = { x: 0, y: 0, w: 1000, h: 560 }; applyVB(); return; }
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
  pts.forEach(p => {
    minX = Math.min(minX, p.x); maxX = Math.max(maxX, p.x);
    minY = Math.min(minY, p.y); maxY = Math.max(maxY, p.y);
  });
  const pad = 70;
  minX -= pad; minY -= pad; maxX += pad; maxY += pad;
  let w = maxX - minX, h = maxY - minY;
  if (w / h > 1 / VB_RATIO) h = w * VB_RATIO; else w = h / VB_RATIO;
  vb = { x: (minX + maxX) / 2 - w / 2, y: (minY + maxY) / 2 - h / 2, w: w, h: w * VB_RATIO };
  applyVB();
}

svg.addEventListener('wheel', ev => {
  ev.preventDefault();
  zoomAtClient(ev.clientX, ev.clientY, Math.exp(-ev.deltaY * 0.0012));
}, { passive: false });

// ---------------------------------------------------------------- snapping

function houseEdges() {
  const h = state.house;
  return [
    { a: { x: h.x, y: h.y }, b: { x: h.x + h.w, y: h.y } },
    { a: { x: h.x + h.w, y: h.y }, b: { x: h.x + h.w, y: h.y + h.h } },
    { a: { x: h.x + h.w, y: h.y + h.h }, b: { x: h.x, y: h.y + h.h } },
    { a: { x: h.x, y: h.y + h.h }, b: { x: h.x, y: h.y } }
  ];
}

// snap p: first to a house wall, then orthogonal/45° relative to prev
function snapPoint(p, prev) {
  const out = { x: p.x, y: p.y };
  const tol = 10 * wpp();

  if (state.house.visible) {
    let best = null, bestD = tol;
    houseEdges().forEach(e => {
      const dx = e.b.x - e.a.x, dy = e.b.y - e.a.y;
      const l2 = dx * dx + dy * dy;
      let t = ((p.x - e.a.x) * dx + (p.y - e.a.y) * dy) / l2;
      t = Math.max(0, Math.min(1, t));
      const q = { x: e.a.x + t * dx, y: e.a.y + t * dy };
      const d = dist(p, q);
      if (d < bestD) { bestD = d; best = q; }
    });
    if (best) { out.x = best.x; out.y = best.y; return out; }
  }

  if (prev) {
    const dx = out.x - prev.x, dy = out.y - prev.y;
    const len = Math.hypot(dx, dy);
    if (len > 4) {
      const ang = Math.atan2(dy, dx);
      const step = Math.PI / 4;
      const snapAng = Math.round(ang / step) * step;
      if (Math.abs(ang - snapAng) < (8 * Math.PI / 180)) {
        out.x = prev.x + Math.cos(snapAng) * len;
        out.y = prev.y + Math.sin(snapAng) * len;
      }
    }
  }
  return out;
}

// is this point sitting on a house wall? (for MATCH markers)
function onHouseWall(p) {
  if (!state.house.visible) return false;
  return houseEdges().some(e => distToSeg(p, e.a, e.b) < 1.5);
}

// ---------------------------------------------------------------- hit testing

function hitTest(p, coarse) {
  const mul = coarse ? 1.7 : 1;
  const tolPt = 13 * wpp() * mul;
  const tolSeg = 10 * wpp() * mul;

  for (let r = state.runs.length - 1; r >= 0; r--) {
    const run = state.runs[r];
    for (let i = 0; i < run.pts.length; i++) {
      if (dist(p, run.pts[i]) <= tolPt) return { kind: 'pt', run: r, idx: i };
    }
  }

  if (state.house.visible) {
    const h = state.house;
    const corners = [
      { x: h.x, y: h.y, c: 'nw' }, { x: h.x + h.w, y: h.y, c: 'ne' },
      { x: h.x + h.w, y: h.y + h.h, c: 'se' }, { x: h.x, y: h.y + h.h, c: 'sw' }
    ];
    for (const c of corners) {
      if (dist(p, c) <= tolPt) return { kind: 'houseHandle', corner: c.c };
    }
  }

  let bestSeg = null, bestD = tolSeg;
  state.runs.forEach((run, r) => {
    segsOf(run).forEach((pair, i) => {
      const d = distToSeg(p, pair[0], pair[1]);
      if (d < bestD) { bestD = d; bestSeg = { kind: 'seg', run: r, idx: i }; }
    });
  });
  if (bestSeg) return bestSeg;

  if (state.house.visible) {
    const h = state.house;
    if (p.x >= h.x && p.x <= h.x + h.w && p.y >= h.y && p.y <= h.y + h.h) {
      return { kind: 'house' };
    }
  }
  return { kind: 'empty' };
}

// ---------------------------------------------------------------- mutations

function addPoint(p) {
  pushUndo();
  p.post = true; // corners are posts by default; toggle off per point if needed
  const cur = currentRun();
  if (!cur) {
    state.runs.push({ pts: [p], closed: false, finished: false, segs: [] });
  } else {
    cur.pts.push(p);
    cur.segs.push({ type: 'build', len: null, gateStyle: 'regular' });
  }
  sel = null;
  render(); save();
}

function closeRun(r) {
  const run = state.runs[r];
  if (run.closed || run.pts.length < 3) return;
  pushUndo();
  run.closed = true;
  run.segs.push({ type: 'build', len: null, gateStyle: 'regular' });
  sel = null;
  render(); save();
}

function finishRun() {
  const cur = currentRun();
  if (!cur) return;
  if (cur.pts.length < 2) { state.runs.pop(); } else { cur.finished = true; }
  render(); save();
}

function setSegType(r, i, type) {
  pushUndo();
  const seg = state.runs[r].segs[i];
  seg.type = type;
  if (type === 'gate' && seg.len == null) seg.len = 5; // typical gate on the sheets
  render(); save();
}

function setGateStyle(r, i, style) {
  pushUndo();
  state.runs[r].segs[i].gateStyle = style;
  render(); save();
}

// give one section its own fence style (rails / picket / MP / WP)
function setSegStyle(r, i, style) {
  pushUndo();
  state.runs[r].segs[i].style = style;
  render(); save();
}

// section goes back to the sketch default style
function clearSegStyle(r, i) {
  pushUndo();
  state.runs[r].segs[i].style = null;
  render(); save();
}

// this section's style becomes the sketch default and every section follows it
function applyStyleToAll(r, i) {
  pushUndo();
  state.style = { ...effStyle(state.runs[r].segs[i]) };
  state.runs.forEach(run => run.segs.forEach(s => { s.style = null; }));
  render(); save();
}

// edit the project default style (sidebar) — sections without override follow along
function patchDefaultStyle(patch) {
  pushUndo();
  Object.assign(state.style, patch);
  render(); save();
}

// project-wide material choice (sidebar)
function setMaterialOpt(key, val) {
  pushUndo();
  state.materials[key] = val;
  render(); save();
}

function setGateHinge(r, i, hinge) {
  pushUndo();
  state.runs[r].segs[i].hinge = hinge;
  render(); save();
}

// picket size like the sheet rows (1x4x6 / 1x6x6 / 1x4x8 / 1x6x8):
// width is the default style's picket, length is the project picket length
function setPicketSize(width, len) {
  pushUndo();
  state.style.picket = width;
  state.materials.picketLen = len;
  render(); save();
}

// hand adjustments over calculated material quantities (the red numbers)
function matAdjust(key, delta, calcVal) {
  pushUndo();
  const cur = (state.matOv[key] != null) ? state.matOv[key] : calcVal;
  state.matOv[key] = Math.max(0, cur + delta);
  render(); save();
}
function matReset(key) {
  pushUndo();
  delete state.matOv[key];
  render(); save();
}
function matRecalcAll() {
  if (!Object.keys(state.matOv).length) return;
  pushUndo();
  state.matOv = {};
  render(); save();
}

function setSegLen(r, i, len) {
  pushUndo();
  state.runs[r].segs[i].len = len;
  render(); save();
}

// a corner can be flagged as a post: it keeps behaving like a normal corner,
// it just draws as a post square and counts as a post
function togglePointPost(r, i) {
  pushUndo();
  const pt = state.runs[r].pts[i];
  pt.post = !pt.post;
  render(); save();
}

// right-click / long-press entry: split a build segment at the pressed spot
function trySplitAt(r, i, world) {
  const seg = state.runs[r].segs[i];
  if (!seg || seg.type !== 'build') return;
  const pair = segsOf(state.runs[r])[i];
  splitSegAt(r, i, projT(world, pair[0], pair[1]), false);
}

// split segment i of run r at fraction t; the new corner is a post and the
// feet (if set) are shared proportionally between the two halves
function splitSegAt(r, i, t, selectNew) {
  pushUndo();
  const run = state.runs[r];
  const pair = segsOf(run)[i];
  const mid = {
    x: pair[0].x + (pair[1].x - pair[0].x) * t,
    y: pair[0].y + (pair[1].y - pair[0].y) * t,
    post: true
  };
  const seg = run.segs[i];
  const first = seg.len != null ? seg.len * t : null;
  const second = seg.len != null ? seg.len - first : null;
  const clone = {
    type: seg.type, len: second, gateStyle: seg.gateStyle,
    style: seg.style ? { ...seg.style } : null
  };
  seg.len = first;
  let newIdx;
  if (run.closed && i === run.segs.length - 1) {
    run.pts.push(mid);            // closing segment: new point goes at the end
    newIdx = run.pts.length - 1;
  } else {
    run.pts.splice(i + 1, 0, mid);
    newIdx = i + 1;
  }
  run.segs.splice(i + 1, 0, clone);
  sel = (selectNew !== false) ? { kind: 'pt', run: r, idx: newIdx } : null;
  render(); save();
}

function deleteSeg(r, i) {
  pushUndo();
  const run = state.runs[r];
  const n = run.pts.length;
  if (run.closed) {
    // opening the loop at segment i; points reorder to start after it
    const pts = [], segs = [];
    for (let k = 1; k <= n; k++) pts.push(run.pts[(i + k) % n]);
    for (let k = 1; k < n; k++) segs.push(run.segs[(i + k) % n]);
    run.pts = pts; run.segs = segs;
    run.closed = false; run.finished = true;
  } else {
    const before = { pts: run.pts.slice(0, i + 1), segs: run.segs.slice(0, i), closed: false, finished: true };
    const after = { pts: run.pts.slice(i + 1), segs: run.segs.slice(i + 1), closed: false, finished: run.finished };
    const repl = [before, after].filter(x => x.pts.length >= 2);
    state.runs.splice(r, 1, ...repl);
  }
  sel = null;
  render(); save();
}

function deletePt(r, i) {
  pushUndo();
  const run = state.runs[r];
  const n = run.segs.length;
  if (run.closed) {
    // segs (i-1) and (i) merge into the survivor (i-1); feet add up
    const prevSeg = run.segs[(i - 1 + n) % n];
    const nextSeg = run.segs[i % n];
    if (prevSeg && nextSeg && prevSeg !== nextSeg) {
      prevSeg.len = (prevSeg.len != null && nextSeg.len != null) ? prevSeg.len + nextSeg.len : null;
    }
    run.pts.splice(i, 1);
    run.segs.splice(i % n, 1);
    if (run.pts.length < 3) { run.closed = false; run.segs.pop(); }
  } else {
    if (i > 0 && i < run.pts.length - 1) {
      // interior point: the two touching sections merge, feet add up
      const a = run.segs[i - 1], b = run.segs[i];
      b.len = (a.len != null && b.len != null) ? a.len + b.len : null;
      b.type = a.type;
      b.gateStyle = a.gateStyle;
    }
    run.pts.splice(i, 1);
    if (i === 0) run.segs.shift();
    else run.segs.splice(i - 1, 1);
  }
  if (run.pts.length < 2) state.runs.splice(r, 1);
  sel = null;
  render(); save();
}

// pick up drawing again from a loose end of an open run
function resumeRun(r, idx) {
  pushUndo();
  const run = state.runs[r];
  if (idx === 0 && run.pts.length > 1) {
    run.pts.reverse();
    run.segs.reverse();
  }
  run.finished = false;
  state.runs.splice(r, 1);
  state.runs.push(run); // currentRun() looks at the last run
  sel = null;
  render(); save();
}

// while drawing, tapping a loose end of another run joins the two lines
function connectRuns(r, idx) {
  pushUndo();
  const cur = state.runs[state.runs.length - 1];
  const other = state.runs[r];
  if (idx !== 0) { // connect at the tapped end
    other.pts.reverse();
    other.segs.reverse();
  }
  cur.segs.push({ type: 'build', len: null, gateStyle: 'regular' }); // bridge section
  cur.pts = cur.pts.concat(other.pts);
  cur.segs = cur.segs.concat(other.segs);
  state.runs.splice(r, 1);
  sel = null;
  render(); save();
}

function clearAll() {
  pushUndo();
  state = {
    house: { ...HOUSE_DEFAULT }, runs: [],
    style: { ...STYLE_DEFAULT }, materials: { ...MATERIALS_DEFAULT }, matOv: {}
  };
  sel = null;
  vb = { x: 0, y: 0, w: 1000, h: 560 };
  applyVB();
  const se = document.getElementById('sel-example');
  if (se) se.value = ''; // back to "Examples…" when starting from scratch
  render(); save();
}

// ---------------------------------------------------------------- pointer interaction
// one finger: tap = add point / select, drag on point/house = move, drag on empty = pan
// two fingers: pinch zoom + pan

const pointers = new Map(); // id -> {x, y, px, py}
let action = null;

svg.addEventListener('pointerdown', ev => {
  if (ev.button !== undefined && ev.button !== 0) return; // right/middle button: contextmenu handles it
  ev.preventDefault();
  try { svg.setPointerCapture(ev.pointerId); } catch (e) { /* pointer already gone */ }
  pointers.set(ev.pointerId, { x: ev.clientX, y: ev.clientY, px: ev.clientX, py: ev.clientY });

  if (pointers.size === 2) {
    if (action && action.timer) clearTimeout(action.timer);
    action = { type: 'pinch' };
    return;
  }
  if (pointers.size > 2) return;

  // tapping a measurement label selects its section (the line itself splits on tap)
  if (ev.target.tagName === 'text' && ev.target.hasAttribute('data-run')) {
    sel = { kind: 'seg', run: +ev.target.getAttribute('data-run'), idx: +ev.target.getAttribute('data-idx') };
    action = null;
    render();
    return;
  }

  const p = toWorld(ev.clientX, ev.clientY);
  const coarse = ev.pointerType !== 'mouse';
  const hit = hitTest(p, coarse);

  if (hit.kind === 'pt') {
    action = { type: 'dragPt', run: hit.run, idx: hit.idx, moved: false, pushed: false };
    if (ev.pointerType !== 'mouse') {
      // touch: press-and-hold a point opens its menu
      action.timer = setTimeout(() => {
        if (action && action.type === 'dragPt' && !action.moved) {
          sel = { kind: 'pt', run: action.run, idx: action.idx };
          action = null;
          render();
        }
      }, 500);
    }
  } else if (hit.kind === 'houseHandle') {
    action = { type: 'resizeHouse', corner: hit.corner, moved: false, pushed: false };
  } else if (hit.kind === 'house') {
    action = { type: 'dragHouse', start: p, orig: { ...state.house }, moved: false, pushed: false };
  } else if (hit.kind === 'seg') {
    if (ev.pointerType !== 'mouse') {
      // touch: press-and-hold on the line places a post (splits the section)
      action = {
        type: 'segPress', run: hit.run, idx: hit.idx, world: p, moved: false,
        timer: setTimeout(() => {
          if (action && action.type === 'segPress' && !action.moved) {
            const a = action;
            action = null;
            trySplitAt(a.run, a.idx, a.world);
          }
        }, 500)
      };
      return;
    }
    action = null;
    sel = { kind: 'seg', run: hit.run, idx: hit.idx };
    render();
  } else {
    action = { type: 'maybe', world: p, moved: false };
  }
});

svg.addEventListener('pointermove', ev => {
  const rec = pointers.get(ev.pointerId);
  if (!rec) {
    // hover cursor on desktop
    if (ev.pointerType === 'mouse') {
      const hit = hitTest(toWorld(ev.clientX, ev.clientY), false);
      svg.style.cursor = (hit.kind === 'pt' || hit.kind === 'houseHandle') ? 'move'
        : hit.kind === 'house' ? 'grab'
        : hit.kind === 'seg' ? 'copy' : 'crosshair';
    }
    return;
  }
  rec.px = rec.x; rec.py = rec.y;
  rec.x = ev.clientX; rec.y = ev.clientY;

  if (action && action.type === 'pinch') { handlePinch(); return; }
  if (!action) return;

  const movedPx = Math.hypot(rec.x - rec.px, rec.y - rec.py);
  const p = toWorld(rec.x, rec.y);

  if (action.type === 'segPress') {
    action.travel = (action.travel || 0) + movedPx;
    if (action.travel > 7) {
      clearTimeout(action.timer);
      action.moved = true;
      action.type = 'pan'; // finger slid: treat as panning
    }
    return;
  }

  if (action.type === 'maybe') {
    if (!action.moved && movedPx > 0) {
      action.travel = (action.travel || 0) + movedPx;
      if (action.travel > 7) { action.type = 'pan'; action.moved = true; }
    }
    if (action.type !== 'pan') return;
  }

  if (action.type === 'pan') {
    vb.x -= (rec.x - rec.px) * wpp();
    vb.y -= (rec.y - rec.py) * wpp();
    applyVB();
    return;
  }

  if (action.type === 'dragPt') {
    action.travel = (action.travel || 0) + movedPx;
    if (!action.moved && action.travel > 5) {
      action.moved = true;
      if (action.timer) clearTimeout(action.timer);
    }
    if (!action.moved) return;
    if (!action.pushed) { pushUndo(); action.pushed = true; }
    const run = state.runs[action.run];
    const prev = run.pts.length > 1
      ? run.pts[action.idx === 0 ? 1 : action.idx - 1]
      : null;
    const np = snapPoint(p, prev);
    // mutate in place so flags on the point (e.g. post) survive the drag
    run.pts[action.idx].x = np.x;
    run.pts[action.idx].y = np.y;
    render();
    return;
  }

  if (action.type === 'dragHouse') {
    action.travel = (action.travel || 0) + movedPx;
    if (!action.moved && action.travel > 5) action.moved = true;
    if (!action.moved) return;
    if (!action.pushed) { pushUndo(); action.pushed = true; }
    state.house.x = action.orig.x + (p.x - action.start.x);
    state.house.y = action.orig.y + (p.y - action.start.y);
    render();
    return;
  }

  if (action.type === 'resizeHouse') {
    if (!action.pushed) { pushUndo(); action.pushed = true; }
    action.moved = true;
    const h = state.house;
    const minS = 40;
    if (action.corner.includes('w')) { const r = h.x + h.w; h.x = Math.min(p.x, r - minS); h.w = r - h.x; }
    if (action.corner.includes('e')) { h.w = Math.max(minS, p.x - h.x); }
    if (action.corner.includes('n')) { const b = h.y + h.h; h.y = Math.min(p.y, b - minS); h.h = b - h.y; }
    if (action.corner.includes('s')) { h.h = Math.max(minS, p.y - h.y); }
    render();
  }
});

function handlePinch() {
  const pts = [...pointers.values()];
  if (pts.length < 2) return;
  const [a, b] = pts;
  const d0 = Math.hypot(a.px - b.px, a.py - b.py);
  const d1 = Math.hypot(a.x - b.x, a.y - b.y);
  const mid0 = { x: (a.px + b.px) / 2, y: (a.py + b.py) / 2 };
  const mid1 = { x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 };
  if (d0 > 0 && d1 > 0) zoomAtClient(mid0.x, mid0.y, d1 / d0);
  vb.x -= (mid1.x - mid0.x) * wpp();
  vb.y -= (mid1.y - mid0.y) * wpp();
  applyVB();
}

svg.addEventListener('pointerup', ev => {
  const rec = pointers.get(ev.pointerId);
  pointers.delete(ev.pointerId);
  if (!rec) return;

  if (action && action.type === 'pinch') {
    if (pointers.size < 2) action = null;
    return;
  }
  if (!action) return;
  const act = action;
  action = null;

  const p = toWorld(ev.clientX, ev.clientY);

  if (act.type === 'segPress') {
    clearTimeout(act.timer);
    if (!act.moved) { // quick tap on the line: select the section
      sel = { kind: 'seg', run: act.run, idx: act.idx };
      render();
    }
    return;
  }

  if (act.type === 'maybe' && !act.moved) {
    // plain tap on empty space: deselect first, otherwise add a point
    if (sel) { sel = null; render(); return; }
    const cur = currentRun();
    const prev = cur && cur.pts.length ? cur.pts[cur.pts.length - 1] : null;
    addPoint(snapPoint(p, prev));
    return;
  }

  if (act.type === 'dragPt' && !act.moved) {
    if (act.timer) clearTimeout(act.timer);
    const run = state.runs[act.run];
    // start point of the active run: close the shape
    const isStart = act.idx === 0 && run === currentRun() && run.pts.length > 2;
    if (isStart) { closeRun(act.run); return; }
    const isFreeEnd = !run.closed && (act.idx === 0 || act.idx === run.pts.length - 1);
    const cur = currentRun();
    // loose end, nothing being drawn: pick the line up from here
    if (isFreeEnd && !cur) { resumeRun(act.run, act.idx); return; }
    // loose end of another line while drawing: join the two lines
    if (isFreeEnd && cur && run !== cur) { connectRuns(act.run, act.idx); return; }
    // plain corner: toggle post/point (right-click the point for the menu)
    togglePointPost(act.run, act.idx);
    return;
  }

  if (act.moved && (act.type === 'dragPt' || act.type === 'dragHouse' || act.type === 'resizeHouse')) {
    render(); save();
  }
});

svg.addEventListener('pointercancel', ev => {
  pointers.delete(ev.pointerId);
  if (action && action.timer) clearTimeout(action.timer);
  if (pointers.size < 2 && action && action.type === 'pinch') action = null;
});

// right-click on the fence line: add a post there (splits the section).
// listener sits on the wrapper so the browser menu never opens over the
// canvas or the floating popup
wrap.addEventListener('contextmenu', ev => {
  ev.preventDefault();
  if (!svg.contains(ev.target)) return; // right-click on the popup: just block the menu
  const p = toWorld(ev.clientX, ev.clientY);
  const hit = hitTest(p, false);
  if (hit.kind === 'pt') {
    // right-click on a point: open its menu (delete / close shape)
    sel = { kind: 'pt', run: hit.run, idx: hit.idx };
    render();
    return;
  }
  if (hit.kind === 'seg') trySplitAt(hit.run, hit.idx, p);
});

// ---------------------------------------------------------------- render helpers

function el(name, attrs, parent) {
  const e = document.createElementNS(SVGNS, name);
  for (const k in attrs) e.setAttribute(k, attrs[k]);
  if (parent) parent.appendChild(e);
  return e;
}
function txt(content, x, y, attrs, parent) {
  const t = el('text', Object.assign({ x: x, y: y }, attrs), parent);
  t.textContent = content;
  return t;
}

const C = { red: '#D8352A', blue: '#233E93', blueSoft: '#6B7DBF', house: '#B8A24C', houseFill: '#FBF6E7' };

// approximate feet-per-world-unit from segments that already have a length
function ftPerUnit() {
  let ft = 0, px = 0;
  state.runs.forEach(run => {
    const pairs = segsOf(run);
    run.segs.forEach((s, i) => {
      if (s.len != null && pairs[i]) {
        const d = dist(pairs[i][0], pairs[i][1]);
        if (d > 5) { ft += s.len; px += d; }
      }
    });
  });
  return ft > 0 && px > 0 ? ft / px : null;
}

// outward unit normal for the label side of segment i of a run
function labelNormal(run, i) {
  const pairs = segsOf(run);
  const [a, b] = pairs[i];
  const L = dist(a, b) || 1;
  let nx = -(b.y - a.y) / L, ny = (b.x - a.x) / L;
  const mid = { x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 };
  if (run.closed && run.pts.length > 2) {
    const probe = { x: mid.x + nx * 5, y: mid.y + ny * 5 };
    if (pointInPolygon(run.pts, probe)) { nx = -nx; ny = -ny; }
  } else {
    let cx = 0, cy = 0;
    run.pts.forEach(q => { cx += q.x; cy += q.y; });
    cx /= run.pts.length; cy /= run.pts.length;
    if ((mid.x + nx * 5 - cx) ** 2 + (mid.y + ny * 5 - cy) ** 2 <
        (mid.x - nx * 5 - cx) ** 2 + (mid.y - ny * 5 - cy) ** 2) { nx = -nx; ny = -ny; }
  }
  return { nx, ny };
}

// ---------------------------------------------------------------- render

function render() {
  scene.innerHTML = '';
  renderHouse();
  state.runs.forEach((run, r) => renderRun(run, r));
  renderTable();
  renderPopup();
  const sum = computeSummary();
  const mats = computeMaterials(sum);
  renderMaterials(sum, mats);
  renderDefaults(sum, mats);
  updateToolbar();
}

function renderHouse() {
  if (!state.house.visible) return;
  const h = state.house;
  el('rect', {
    x: h.x, y: h.y, width: h.w, height: h.h,
    fill: C.houseFill, stroke: C.house, 'stroke-width': 3
  }, scene);
  txt('HOUSE', h.x + h.w / 2, h.y + h.h / 2, {
    fill: C.house, 'font-size': 15, 'font-weight': 700,
    'text-anchor': 'middle', 'dominant-baseline': 'middle', 'letter-spacing': '2'
  }, scene);
  ['nw', 'ne', 'se', 'sw'].forEach(c => {
    const x = c.includes('w') ? h.x : h.x + h.w;
    const y = c.includes('n') ? h.y : h.y + h.h;
    el('rect', {
      x: x - 5, y: y - 5, width: 10, height: 10,
      fill: '#fff', stroke: C.house, 'stroke-width': 2
    }, scene);
  });
}

function renderRun(run, r) {
  const pairs = segsOf(run);

  pairs.forEach((pair, i) => {
    const [a, b] = pair;
    const seg = run.segs[i] || { type: 'build', len: null, gateStyle: 'regular' };
    const selected = sel && sel.kind === 'seg' && sel.run === r && sel.idx === i;
    const L = dist(a, b);
    const ux = L ? (b.x - a.x) / L : 1, uy = L ? (b.y - a.y) / L : 0;
    const { nx, ny } = labelNormal(run, i);

    // invisible fat line just to make segments easy to hit on the SVG side (hit
    // testing is manual, this only helps the browser paint order stay simple)
    const main = el('line', {
      x1: a.x, y1: a.y, x2: b.x, y2: b.y,
      stroke: C.red, 'stroke-width': selected ? 4.5 : 2.5,
      'stroke-linecap': 'round',
      'stroke-dasharray': seg.type === 'gate' ? '7 6' : 'none'
    }, scene);
    if (seg.type === 'existing') main.setAttribute('opacity', '0.9');

    if (seg.type === 'build' && L > 22) {
      // tick marks = fence we build
      for (let t = 12; t < L - 8; t += 17) {
        const cx = a.x + ux * t, cy = a.y + uy * t;
        el('line', {
          x1: cx - nx * 6, y1: cy - ny * 6, x2: cx + nx * 6, y2: cy + ny * 6,
          stroke: C.red, 'stroke-width': 1.6
        }, scene);
      }
    } else if (seg.type === 'existing' && L > 20) {
      // X marks = existing fence, not counted
      for (let t = 15; t < L - 10; t += 26) {
        const cx = a.x + ux * t, cy = a.y + uy * t;
        el('line', { x1: cx - 6, y1: cy - 6, x2: cx + 6, y2: cy + 6, stroke: C.red, 'stroke-width': 1.8 }, scene);
        el('line', { x1: cx - 6, y1: cy + 6, x2: cx + 6, y2: cy - 6, stroke: C.red, 'stroke-width': 1.8 }, scene);
      }
    } else if (seg.type === 'gate') {
      // V symbol pointing outward, like the hand-drawn gates
      const mid = { x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 };
      const tip = { x: mid.x + nx * 16, y: mid.y + ny * 16 };
      el('path', {
        d: `M ${a.x} ${a.y} L ${tip.x} ${tip.y} L ${b.x} ${b.y}`,
        fill: 'none', stroke: C.red, 'stroke-width': 1.8
      }, scene);
    }

    // length label; tapping it selects the section
    const mid = { x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 };
    const off = seg.type === 'gate' ? 34 : 20;
    let label = seg.len != null ? fmtFeet(seg.len) : '??';
    if (seg.type === 'gate') label = 'GATE ' + label + (seg.gateStyle === 'ct' ? ' C/T' : '');
    txt(label, mid.x + nx * off, mid.y + ny * off, {
      fill: seg.len != null ? C.red : C.blue,
      'font-size': 15, 'font-weight': 700,
      'text-anchor': 'middle', 'dominant-baseline': 'middle',
      'font-family': '"Segoe UI", Arial, sans-serif',
      'data-run': r, 'data-idx': i, cursor: 'pointer'
    }, scene);

    // sections styled differently from the sketch default get a small tag
    if (seg.type === 'build' && seg.style && !sameStyle(seg.style, state.style)) {
      txt(styleShort(seg.style), mid.x + nx * (off + 15), mid.y + ny * (off + 15), {
        fill: C.blueSoft, 'font-size': 11, 'font-weight': 700,
        'text-anchor': 'middle', 'dominant-baseline': 'middle',
        'font-family': '"Segoe UI", Arial, sans-serif',
        'data-run': r, 'data-idx': i, cursor: 'pointer'
      }, scene);
    }
  });

  // points
  run.pts.forEach((pt, i) => {
    const isEnd = !run.closed && (i === 0 || i === run.pts.length - 1);
    const match = isEnd && onHouseWall(pt);
    const selectedPt = sel && sel.kind === 'pt' && sel.run === r && sel.idx === i;

    if (match) {
      // MATCH marker: fence dies into the house wall (metal post on the sheets)
      el('rect', {
        x: pt.x - 6, y: pt.y - 6, width: 12, height: 12,
        fill: '#fff', stroke: C.red, 'stroke-width': 2.2
      }, scene);
      txt('M', pt.x, pt.y + 1, {
        fill: C.red, 'font-size': 9, 'font-weight': 800,
        'text-anchor': 'middle', 'dominant-baseline': 'middle'
      }, scene);
    } else if (pt.post) {
      const half = selectedPt ? 7.5 : 6;
      el('rect', {
        x: pt.x - half, y: pt.y - half, width: half * 2, height: half * 2,
        fill: selectedPt ? C.red : '#fff', stroke: C.red, 'stroke-width': 2.2
      }, scene);
    } else {
      el('circle', {
        cx: pt.x, cy: pt.y, r: selectedPt ? 6 : 4.5,
        fill: selectedPt ? '#fff' : C.red,
        stroke: C.red, 'stroke-width': 2
      }, scene);
    }

    // ring on the closable starting point
    if (i === 0 && run === currentRun() && run.pts.length > 2) {
      el('circle', {
        cx: pt.x, cy: pt.y, r: 10, fill: 'none',
        stroke: C.blue, 'stroke-width': 1.6, 'stroke-dasharray': '3 3'
      }, scene);
    }
  });
}

// ---------------------------------------------------------------- table

function renderTable() {
  tbody.innerHTML = '';
  let n = 0;
  const scale = ftPerUnit();

  state.runs.forEach((run, r) => {
    const pairs = segsOf(run);
    run.segs.forEach((seg, i) => {
      n++;
      const tr = document.createElement('tr');
      if (sel && sel.kind === 'seg' && sel.run === r && sel.idx === i) tr.classList.add('sel');

      const td1 = document.createElement('td');
      const name = document.createElement('span');
      name.className = 'tramo-nombre';
      name.textContent = 'Section ' + n;
      td1.appendChild(name);
      if (seg.len == null && seg.type !== 'existing') {
        const w = document.createElement('span');
        w.className = 'falta';
        w.textContent = ' missing length';
        td1.appendChild(w);
      }
      tr.appendChild(td1);

      const td2 = document.createElement('td');
      const sm = document.createElement('select');
      [['build', 'Fence (build)'], ['existing', 'Existing (no count)'],
       ['gate-regular', 'Gate — Regular'], ['gate-ct', 'Gate — C&T']].forEach(([v, lbl]) => {
        const o = document.createElement('option');
        o.value = v; o.textContent = lbl;
        sm.appendChild(o);
      });
      sm.value = seg.type === 'gate' ? 'gate-' + (seg.gateStyle === 'ct' ? 'ct' : 'regular') : seg.type;
      sm.addEventListener('change', () => {
        if (sm.value.startsWith('gate')) {
          setSegType(r, i, 'gate');
          setGateStyle(r, i, sm.value.endsWith('ct') ? 'ct' : 'regular');
        } else {
          setSegType(r, i, sm.value);
        }
      });
      td2.appendChild(sm);
      tr.appendChild(td2);

      const td3 = document.createElement('td');
      const inp = document.createElement('input');
      inp.className = 'ft';
      inp.type = 'text';
      inp.inputMode = 'decimal';
      inp.value = seg.len != null ? fmtFeet(seg.len) : '';
      if (seg.len == null && scale && pairs[i]) {
        inp.placeholder = '≈ ' + Math.round(dist(pairs[i][0], pairs[i][1]) * scale) + "'";
      } else if (seg.len == null) {
        inp.placeholder = "ft or ft'in\"";
      }
      inp.addEventListener('change', () => {
        const v = parseFeet(inp.value);
        if (inp.value.trim() === '') setSegLen(r, i, null);
        else if (!isNaN(v)) setSegLen(r, i, v);
        else inp.value = seg.len != null ? fmtFeet(seg.len) : '';
      });
      inp.addEventListener('focus', () => { sel = { kind: 'seg', run: r, idx: i }; renderCanvasOnly(); renderPopup(); });
      td3.appendChild(inp);
      tr.appendChild(td3);

      const td4 = document.createElement('td');
      if (seg.type === 'build') {
        td4.textContent = styleShort(effStyle(seg));
        if (seg.style && !sameStyle(seg.style, state.style)) td4.className = 'hand';
      } else {
        td4.textContent = '—';
      }
      tr.appendChild(td4);

      name.addEventListener('click', () => { sel = { kind: 'seg', run: r, idx: i }; render(); });
      tr.addEventListener('mouseenter', () => { tr.classList.add('sel'); });
      tr.addEventListener('mouseleave', () => {
        if (!(sel && sel.kind === 'seg' && sel.run === r && sel.idx === i)) tr.classList.remove('sel');
      });

      tbody.appendChild(tr);
    });
  });
  tbl.style.display = n ? '' : 'none';
  // sections table hidden for now (operator request 2026-08-24) — flip to re-enable
  const SHOW_SECTIONS_TABLE = false;
  document.getElementById('sections-card').style.display = (SHOW_SECTIONS_TABLE && n) ? '' : 'none';
}

// re-draw only the canvas (used while typing in the table, to avoid rebuilding inputs)
function renderCanvasOnly() {
  scene.innerHTML = '';
  renderHouse();
  state.runs.forEach((run, r) => renderRun(run, r));
}

// ---------------------------------------------------------------- popup

function btn(label, cls, fn) {
  const b = document.createElement('button');
  b.textContent = label;
  if (cls) b.className = cls;
  b.addEventListener('click', fn);
  return b;
}

// world point the popup anchors to (the selected point, or the section middle)
function selAnchor() {
  if (!sel) return null;
  const run = state.runs[sel.run];
  if (!run) return null;
  if (sel.kind === 'pt') return run.pts[sel.idx] || null;
  const pair = segsOf(run)[sel.idx];
  if (!pair) return null;
  return { x: (pair[0].x + pair[1].x) / 2, y: (pair[0].y + pair[1].y) / 2 };
}

// place the popup near the selection, clamped inside the canvas
function positionPopup() {
  if (popup.hidden) return;
  const a = selAnchor();
  if (!a) { popup.hidden = true; return; }
  const r = svg.getBoundingClientRect();
  const wr = wrap.getBoundingClientRect();
  const k = r.width / vb.w; // screen px per world unit
  const sx = (a.x - vb.x) * k + (r.left - wr.left);
  const sy = (a.y - vb.y) * k + (r.top - wr.top);
  const pw = popup.offsetWidth, ph = popup.offsetHeight;
  let x = sx - pw / 2;
  let y = sy - ph - 16;
  x = Math.max(4, Math.min(x, wr.width - pw - 4));
  if (y < 4) y = sy + 16;              // no room above: show below
  y = Math.max(4, Math.min(y, wr.height - ph - 4));
  popup.style.left = x + 'px';
  popup.style.top = y + 'px';
}

function popupRow() {
  const d = document.createElement('div');
  d.className = 'popup-row';
  popup.appendChild(d);
  return d;
}

// small pill button ("chip") used by the popup and the defaults panel
function chip(label, on, fn, blue, icon) {
  const c = document.createElement('button');
  c.className = 'chip' + (on ? (blue ? ' on-blue' : ' on') : '');
  if (icon) {
    c.appendChild(icon);
    const sp = document.createElement('span');
    sp.textContent = label;
    c.appendChild(sp);
  } else {
    c.textContent = label;
  }
  c.addEventListener('click', fn);
  return c;
}

// cross-section drawing of the current fence style, same language as the
// sheet's Fence Style box: picket, rail blocks, cap band on top, hollow trim,
// alternating blocks for Good Neighbor — with the crew's red "N rail" note
function stylePreview(st) {
  const s = document.createElementNS(SVGNS, 'svg');
  s.setAttribute('viewBox', '0 0 150 92');
  s.setAttribute('class', 'style-preview-svg');
  s.setAttribute('aria-hidden', 'true');
  function rect(x, y, w, h, fill, stroke) {
    const r = document.createElementNS(SVGNS, 'rect');
    r.setAttribute('x', x); r.setAttribute('y', y);
    r.setAttribute('width', w); r.setAttribute('height', h);
    r.setAttribute('fill', fill);
    if (stroke) { r.setAttribute('stroke', stroke); r.setAttribute('stroke-width', '1.5'); }
    s.appendChild(r);
    return r;
  }
  function text(str, x, y, fill, size, weight) {
    const t = document.createElementNS(SVGNS, 'text');
    t.setAttribute('x', x); t.setAttribute('y', y);
    t.setAttribute('fill', fill);
    t.setAttribute('font-size', size);
    t.setAttribute('font-weight', weight || 700);
    t.setAttribute('font-family', 'Archivo, sans-serif');
    t.textContent = str;
    s.appendChild(t);
    return t;
  }
  const ct = st.finish === 'ct';
  const topY = ct ? 16 : 6;
  rect(52, topY, 14, 86 - topY, '#dbeafe', '#1e3a8a');            // picket edge-on
  if (ct) {
    rect(36, 4, 46, 9, '#1e3a8a');                                 // 2x6 cap on top
    rect(68, 17, 13, 7, 'none', '#1e3a8a');                        // 1x2 trim (hollow)
  }
  let ys = st.rails === 2 ? (ct ? [34, 70] : [14, 68]) : (ct ? [30, 52, 72] : [12, 42, 70]);
  ys.forEach((y, i) => {
    const x = (st.finish === 'gn' && i % 2 === 1) ? 20 : 68;       // GN: alternating sides
    rect(x, y, 16, 9, '#1e3a8a');
  });
  text(st.rails + ' rail', 94, 48, '#dc2626', 15, 800);
  const name = st.finish === 'ct' ? 'Cap & Trim' : st.finish === 'gn' ? 'Good Nbr' : 'Standard';
  text(name + ' · ' + st.picket, 94, 64, '#64748b', 10, 600);
  return s;
}

// "Rails  [2][3]" — labeled row of chips
function optRow(parent, label, chips) {
  const d = document.createElement('div');
  d.className = 'opt-row';
  const l = document.createElement('div');
  l.className = 'lbl';
  l.textContent = label;
  d.appendChild(l);
  const cc = document.createElement('div');
  cc.className = 'chips';
  chips.forEach(c => cc.appendChild(c));
  d.appendChild(cc);
  parent.appendChild(d);
  return d;
}

function feetRow(parent, seg) {
  const cl = document.createElement('div');
  cl.className = 'campo-len';
  const lb = document.createElement('label');
  lb.textContent = 'Feet';
  const inp = document.createElement('input');
  inp.type = 'text';
  inp.inputMode = 'decimal';
  inp.value = seg.len != null ? fmtFeet(seg.len) : '';
  inp.placeholder = "ft or ft'in\"";
  inp.addEventListener('change', () => {
    const v = parseFeet(inp.value);
    if (inp.value.trim() === '') setSegLen(sel.run, sel.idx, null);
    else if (!isNaN(v)) setSegLen(sel.run, sel.idx, v);
  });
  cl.appendChild(lb); cl.appendChild(inp);
  parent.appendChild(cl);
}

function renderPopup() {
  popup.innerHTML = '';
  popup.classList.remove('pt-popup');
  if (!sel) { popup.hidden = true; return; }

  const run = state.runs[sel.run];
  if (!run) { sel = null; popup.hidden = true; return; }

  if (sel.kind === 'pt') {
    const pt = run.pts[sel.idx];
    if (!pt) { sel = null; popup.hidden = true; return; }
    popup.classList.add('pt-popup');
    const row = popupRow();
    const t = document.createElement('span');
    t.className = 'titulo';
    t.textContent = pt.post ? 'POST' : 'POINT';
    row.appendChild(t);
    const isStart = sel.idx === 0 && run === currentRun() && run.pts.length > 2;
    if (isStart) row.appendChild(btn('Close shape', '', () => closeRun(sel.run)));
    row.appendChild(btn('Delete', 'peligro right', () => deletePt(sel.run, sel.idx)));
    popup.hidden = false;
    positionPopup();
    return;
  }

  const seg = run.segs[sel.idx];
  if (!seg) { sel = null; popup.hidden = true; return; }

  let n = 0;
  for (let r = 0; r < sel.run; r++) n += state.runs[r].segs.length;
  n += sel.idx + 1;
  const isOverride = seg.type === 'build' && seg.style && !sameStyle(seg.style, state.style);

  // title row: "SECTION 5 — 15'" + OVERRIDE badge
  const row1 = popupRow();
  const t = document.createElement('span');
  t.className = 'titulo';
  t.textContent = (seg.type === 'gate' ? 'GATE ' : 'SECTION ') + n +
    (seg.len != null ? ' — ' + fmtFeet(seg.len) : '');
  row1.appendChild(t);
  if (isOverride) {
    const bd = document.createElement('span');
    bd.className = 'badge override';
    bd.textContent = 'OVERRIDE';
    row1.appendChild(bd);
  }

  // full-width type selector
  const segFull = document.createElement('div');
  segFull.className = 'seg-full';
  segFull.appendChild(btn('Fence', seg.type === 'build' ? 'on' : '', () => setSegType(sel.run, sel.idx, 'build')));
  segFull.appendChild(btn('Existing', seg.type === 'existing' ? 'on' : '', () => setSegType(sel.run, sel.idx, 'existing')));
  segFull.appendChild(btn('Gate', seg.type === 'gate' ? 'on' : '', () => setSegType(sel.run, sel.idx, 'gate')));
  popup.appendChild(segFull);

  if (seg.type === 'gate') {
    optRow(popup, 'Type', [
      chip('Regular', seg.gateStyle !== 'ct', () => setGateStyle(sel.run, sel.idx, 'regular'), true),
      chip('Cap & Trim', seg.gateStyle === 'ct', () => setGateStyle(sel.run, sel.idx, 'ct'), true)
    ]);
    optRow(popup, 'Hinges', [
      chip('Strap kit', (seg.hinge || 'strap') === 'strap', () => setGateHinge(sel.run, sel.idx, 'strap'), true),
      chip('T kit', seg.hinge === 't', () => setGateHinge(sel.run, sel.idx, 't'), true)
    ]);
    const note = document.createElement('div');
    note.className = 'auto-note';
    note.textContent = 'Auto-adds to materials: 2 cedar posts (C&T), 2 cedar rails, 1 hinge kit.';
    popup.appendChild(note);
    feetRow(popup, seg);
    popup.appendChild(btn('Delete', 'peligro', () => deleteSeg(sel.run, sel.idx)));
  } else if (seg.type === 'build') {
    const eff = effStyle(seg);
    const patch = p => setSegStyle(sel.run, sel.idx, { ...eff, ...p });
    optRow(popup, 'Rails', [
      chip('2', eff.rails === 2, () => patch({ rails: 2 })),
      chip('3', eff.rails === 3, () => patch({ rails: 3 }))
    ]);
    optRow(popup, 'Finish', [
      chip('Std', eff.finish === 'std', () => patch({ finish: 'std' })),
      chip('GN', eff.finish === 'gn', () => patch({ finish: 'gn' })),
      chip('C&T', eff.finish === 'ct', () => patch({ finish: 'ct' }))
    ]);
    optRow(popup, 'Picket', [
      chip('1X4', eff.picket === '1x4', () => patch({ picket: '1x4' })),
      chip('1X6', eff.picket === '1x6', () => patch({ picket: '1x6' }))
    ]);
    optRow(popup, 'Options', [
      chip('MP', eff.mp, () => patch({ mp: !eff.mp }), true),
      chip('WP', eff.wp, () => patch({ wp: !eff.wp }), true)
    ]);
    if (isOverride) {
      const note = document.createElement('div');
      note.className = 'differs-note';
      note.textContent = '⚑ Differs from project default (' + styleShort(state.style) + ')';
      popup.appendChild(note);
    }
    feetRow(popup, seg);
    const grid = document.createElement('div');
    grid.className = 'action-grid';
    grid.appendChild(btn('Apply to all', '', () => applyStyleToAll(sel.run, sel.idx)));
    const resetBtn = btn('Use default', '', () => clearSegStyle(sel.run, sel.idx));
    resetBtn.disabled = !seg.style;
    grid.appendChild(resetBtn);
    grid.appendChild(btn('Split', 'ghost', () => splitSegAt(sel.run, sel.idx, 0.5)));
    grid.appendChild(btn('Delete', 'peligro', () => deleteSeg(sel.run, sel.idx)));
    popup.appendChild(grid);
  } else { // existing
    feetRow(popup, seg);
    const grid = document.createElement('div');
    grid.className = 'action-grid';
    grid.appendChild(btn('Split', 'ghost', () => splitSegAt(sel.run, sel.idx, 0.5)));
    grid.appendChild(btn('Delete', 'peligro', () => deleteSeg(sel.run, sel.idx)));
    popup.appendChild(grid);
  }

  popup.hidden = false;
  positionPopup();
}

// ---------------------------------------------------------------- summary & materials

// one pass over the drawing: everything the estimator needs downstream
function computeSummary() {
  const sum = {
    ft: 0, missing: 0, gatesReg: 0, gatesCt: 0, markedPosts: 0, matches: 0,
    hingeStrap: 0, hingeT: 0,
    byStyle: new Map() // style label -> { ft, style }
  };
  state.runs.forEach(run => {
    run.pts.forEach((pt, i) => {
      if (pt.post) sum.markedPosts++;
      const isEnd = !run.closed && (i === 0 || i === run.pts.length - 1);
      if (isEnd && onHouseWall(pt)) sum.matches++;
    });
    run.segs.forEach(seg => {
      if (seg.type === 'gate') {
        seg.gateStyle === 'ct' ? sum.gatesCt++ : sum.gatesReg++;
        seg.hinge === 't' ? sum.hingeT++ : sum.hingeStrap++;
        return;
      }
      if (seg.type === 'existing') return;
      if (seg.len == null) { sum.missing++; return; }
      sum.ft += seg.len;
      const st = effStyle(seg);
      const key = styleShort(st);
      const e = sum.byStyle.get(key) || { ft: 0, style: st };
      e.ft += seg.len;
      sum.byStyle.set(key, e);
    });
  });
  sum.gates = sum.gatesReg + sum.gatesCt;
  return sum;
}

const MAT_LABELS = {
  postMat: { treated: 'Treated', cedar: 'Cedar/Fir', metal: 'Metal' },
  railMat: { treated: 'Treat/Fir', cds4s: 'CD S4S', spruce: 'Spruce' },
  picketMat: { ww: 'WW', cedar: 'Cedar', stained: 'Stained' },
  capMat: { spf: 'SPF/Fir', cedar: 'Cedar' }
};

// MATERIALS-SPEC.md formulas — every row can be hand-adjusted (state.matOv)
function computeMaterials(sum) {
  const m = state.materials;
  const railLen = parseInt(m.railLen, 10) || 8;

  const linePosts = sum.ft > 0 ? Math.ceil(sum.ft / 8) + 2 : 0;
  const metalPosts = sum.matches;
  const cedarGatePosts = sum.gatesCt * 2;
  // client's rule: total posts / 2, rounded up
  const concrete = Math.ceil((linePosts + metalPosts + cedarGatePosts) / 2);

  let rails = 0, p14 = 0, p16 = 0, ctFt = 0, rollNails = 0;
  sum.byStyle.forEach(e => {
    rails += Math.ceil(e.ft / railLen) * e.style.rails;
    const cnt = Math.ceil(e.ft * (e.style.picket === '1x6' ? 2.05 : 3.5));
    if (e.style.picket === '1x6') p16 += cnt; else p14 += cnt;
    if (e.style.finish === 'ct') ctFt += e.ft;
    const npp = e.style.finish === 'ct' ? 6 : (e.style.rails === 3 ? 5 : 4);
    rollNails += cnt * npp;
  });
  rails += sum.gates * 6;                       // gate frames use extra 2x4
  const cedarRails = sum.gates * 2;
  const capLen = parseInt(m.capLen, 10) || 12;
  const trimLen = parseInt(m.trimLen, 10) || 10;
  const cap = ctFt > 0 ? Math.ceil(ctFt / capLen) : 0;
  const trim = ctFt > 0 ? Math.ceil(ctFt / trimLen) : 0;
  // two nail systems, one per company:
  // Elite writes Nails and Rolls as the SAME number, ≈6 per 100 ft of fence;
  // South Texas counts framing clips (26 nails) and picket coil rolls (300)
  let nailRows;
  if (m.nailSystem === 'clips') {
    const clips = rails > 0 ? Math.ceil((rails * 4 + Math.round(ctFt)) / 26) : 0;
    const rolls = rollNails > 0 ? Math.ceil(rollNails / 300) : 0;
    nailRows = [
      clips ? { key: 'clips', label: 'Nail clips', sub: '(26/clip)', value: clips } : null,
      rolls ? { key: 'rolls', label: 'Coil rolls', sub: '(300/roll)', value: rolls } : null
    ];
  } else {
    const n = sum.ft > 0 ? Math.round(sum.ft * 0.0605) : 0;
    nailRows = [
      n ? { key: 'nails', label: 'Nails', sub: '(≈6/100 ft)', value: n } : null,
      n ? { key: 'rolls', label: 'Rolls', sub: '(≈6/100 ft)', value: n } : null
    ];
  }

  const groups = [
    { title: 'POSTS', rows: [
      { key: 'posts', label: (m.postLen || '8') + 'FT post · ' + (MAT_LABELS.postMat[m.postMat] || ''), value: linePosts },
      metalPosts ? { key: 'metalPosts', label: 'Metal post', sub: '(match)', value: metalPosts } : null,
      cedarGatePosts ? { key: 'cedarPosts', label: 'Cedar post', sub: '(gates)', value: cedarGatePosts } : null,
      { key: 'concrete', label: 'Concrete bags', value: concrete }
    ].filter(Boolean) },
    { title: 'RAILS', rows: [
      { key: 'rails', label: '2x4x' + (m.railLen || '8') + ' · ' + (MAT_LABELS.railMat[m.railMat] || ''), value: rails },
      sum.gates ? { key: 'cedarRails', label: '2x4x8 · CD S4S', sub: '(gate)', value: cedarRails } : null,
      cap ? { key: 'cap', label: '2x6x' + capLen + ' Cap · ' + (MAT_LABELS.capMat[m.capMat] || ''), value: cap } : null,
      trim ? { key: 'trim', label: '1x2x' + trimLen + ' Trim · ' + (MAT_LABELS.capMat[m.capMat] || ''), value: trim } : null
    ].filter(Boolean) },
    { title: 'PICKETS', rows: [
      p14 ? { key: 'pickets14', label: '1x4x' + (m.picketLen || '6') + ' · ' + (MAT_LABELS.picketMat[m.picketMat] || ''), value: p14 } : null,
      p16 ? { key: 'pickets16', label: '1x6x' + (m.picketLen || '6') + ' · ' + (MAT_LABELS.picketMat[m.picketMat] || ''), value: p16 } : null
    ].filter(Boolean) },
    { title: 'NAILS & MISC', rows: [
      nailRows[0],
      nailRows[1],
      sum.hingeStrap ? { key: 'strap', label: 'Strap hinge kit', value: sum.hingeStrap } : null,
      sum.hingeT ? { key: 'thinge', label: 'T hinge kit', value: sum.hingeT } : null,
      metalPosts ? { key: 'dome', label: 'Dome cap', value: metalPosts } : null
    ].filter(Boolean) },
  ];
  return {
    groups,
    totalPosts: linePosts + metalPosts + cedarGatePosts,
    totalPickets: p14 + p16,
    ctFt: ctFt
  };
}

function matVal(row) {
  return state.matOv[row.key] != null ? state.matOv[row.key] : row.value;
}

function renderMaterials(sum, mats) {
  matGrid.innerHTML = '';

  // job totals up top, each figure next to its concept; with mixed styles the
  // fence footage breaks down per style, like the sheet's Fence table rows
  const totCol = document.createElement('div');
  const th = document.createElement('div');
  th.className = 'mat-group-title';
  th.textContent = 'JOB';
  totCol.appendChild(th);
  const warn = sum.missing ? ' · ⚠' + sum.missing : '';
  const totRows = [];
  if (sum.byStyle.size > 1) {
    const c = document.createElement('span');
    c.className = 'cnt';
    c.textContent = Math.round(sum.ft) + ' ft total' + warn;
    th.appendChild(c);
    sum.byStyle.forEach((e, k) => totRows.push(['Fence · ' + k, Math.round(e.ft) + ' ft']));
  } else {
    totRows.push(['Fence', Math.round(sum.ft) + ' ft' + warn]);
  }
  totRows.push(['Gates', sum.gates + (sum.gatesCt ? ' (' + sum.gatesCt + ' C&T)' : '')]);
  totRows.forEach(([k, v]) => {
    const row = document.createElement('div');
    row.className = 'mat-row';
    const name = document.createElement('div');
    name.className = 'name';
    name.textContent = k;
    row.appendChild(name);
    const qty = document.createElement('div');
    qty.className = 'qty wide';
    qty.textContent = v;
    row.appendChild(qty);
    totCol.appendChild(row);
  });
  matGrid.appendChild(totCol);

  const groupTotals = { POSTS: mats.totalPosts, PICKETS: mats.totalPickets };
  mats.groups.forEach(gr => {
    if (!gr.rows.length) return;
    const col = document.createElement('div');
    const h = document.createElement('div');
    h.className = 'mat-group-title';
    h.textContent = gr.title;
    if (groupTotals[gr.title] != null) {
      const c = document.createElement('span');
      c.className = 'cnt';
      c.textContent = groupTotals[gr.title] + ' total';
      h.appendChild(c);
    }
    col.appendChild(h);
    gr.rows.forEach(rowDef => {
      const ov = state.matOv[rowDef.key] != null;
      const row = document.createElement('div');
      row.className = 'mat-row' + (ov ? ' ov' : '');
      const name = document.createElement('div');
      name.className = 'name';
      name.textContent = rowDef.label + ' ';
      if (rowDef.sub) {
        const sm = document.createElement('small');
        sm.textContent = rowDef.sub;
        name.appendChild(sm);
      }
      row.appendChild(name);
      const minus = document.createElement('button');
      minus.className = 'step';
      minus.textContent = '−';
      minus.addEventListener('click', () => matAdjust(rowDef.key, -1, rowDef.value));
      row.appendChild(minus);
      const qty = document.createElement('div');
      qty.className = 'qty';
      qty.textContent = matVal(rowDef);
      row.appendChild(qty);
      const plus = document.createElement('button');
      plus.className = 'step';
      plus.textContent = '+';
      plus.addEventListener('click', () => matAdjust(rowDef.key, 1, rowDef.value));
      row.appendChild(plus);
      if (ov) {
        const rs = document.createElement('button');
        rs.className = 'reset';
        rs.textContent = '↺ ' + rowDef.value;
        rs.title = 'Back to the calculated value';
        rs.addEventListener('click', () => matReset(rowDef.key));
        row.appendChild(rs);
      }
      col.appendChild(row);
    });
    matGrid.appendChild(col);
  });
}

// ---------------------------------------------------------------- defaults panel

function defBlock(title, subNote) {
  const b = document.createElement('div');
  b.className = 'def-block';
  const t = document.createElement('div');
  t.className = 'def-title';
  t.textContent = title;
  if (subNote) {
    const s = document.createElement('span');
    s.className = 'sub';
    s.textContent = subNote;
    t.appendChild(s);
  }
  b.appendChild(t);
  defPanel.appendChild(b);
  return b;
}
function defRow(parent, chips, dim) {
  const r = document.createElement('div');
  r.className = 'def-row' + (dim ? ' dim' : '');
  chips.forEach(c => r.appendChild(c));
  parent.appendChild(r);
  return r;
}

function renderDefaults(sum, mats) {
  defPanel.innerHTML = '';
  const st = state.style;
  const m = state.materials;

  // header + how many sections follow the default
  let buildSecs = 0, followSecs = 0;
  const overrides = [];
  let n = 0;
  state.runs.forEach((run, r) => {
    run.segs.forEach((seg, i) => {
      n++;
      if (seg.type !== 'build') return;
      buildSecs++;
      if (!seg.style || sameStyle(seg.style, state.style)) followSecs++;
      else overrides.push({ n: n, run: r, idx: i, seg: seg });
    });
  });
  const head = document.createElement('div');
  head.className = 'head';
  const ht = document.createElement('div');
  ht.className = 'card-title';
  ht.textContent = 'PROJECT DEFAULTS';
  head.appendChild(ht);
  if (buildSecs) {
    const bd = document.createElement('span');
    bd.className = 'badge good';
    bd.textContent = followSecs + ' OF ' + buildSecs;
    head.appendChild(bd);
  }
  defPanel.appendChild(head);
  const note = document.createElement('div');
  note.className = 'panel-note';
  note.textContent = 'Every new section inherits these. Override any section from its popup.';
  defPanel.appendChild(note);

  // fence style
  const fs = defBlock('FENCE STYLE');
  defRow(fs, [
    chip('2 Rails', st.rails === 2, () => patchDefaultStyle({ rails: 2 }), true),
    chip('3 Rails', st.rails === 3, () => patchDefaultStyle({ rails: 3 }), true)
  ]);
  defRow(fs, [
    chip('Standard', st.finish === 'std', () => patchDefaultStyle({ finish: 'std' }), true),
    chip('Good Nbr', st.finish === 'gn', () => patchDefaultStyle({ finish: 'gn' }), true),
    chip('Cap & Trim', st.finish === 'ct', () => patchDefaultStyle({ finish: 'ct' }), true)
  ]);
  defRow(fs, [
    chip('1X4', st.picket === '1x4', () => patchDefaultStyle({ picket: '1x4' }), true),
    chip('1X6', st.picket === '1x6', () => patchDefaultStyle({ picket: '1x6' }), true),
    chip('MP', st.mp, () => patchDefaultStyle({ mp: !st.mp }), true),
    chip('WP', st.wp, () => patchDefaultStyle({ wp: !st.wp }), true)
  ]);
  const pv = document.createElement('div');
  pv.className = 'style-preview';
  pv.appendChild(stylePreview(st));
  fs.appendChild(pv);

  // posts
  const pb = defBlock('POSTS');
  defRow(pb, [
    chip('Treated', m.postMat === 'treated', () => setMaterialOpt('postMat', 'treated'), true),
    chip('Cedar/Fir', m.postMat === 'cedar', () => setMaterialOpt('postMat', 'cedar'), true),
    chip('Metal', m.postMat === 'metal', () => setMaterialOpt('postMat', 'metal'), true)
  ]);
  defRow(pb, [
    chip('8 FT', m.postLen === '8', () => setMaterialOpt('postLen', '8'), true),
    chip('10 FT', m.postLen === '10', () => setMaterialOpt('postLen', '10'), true)
  ]);

  // rails
  const rb = defBlock('RAILS');
  defRow(rb, [
    chip('Treat/Fir', m.railMat === 'treated', () => setMaterialOpt('railMat', 'treated'), true),
    chip('CD S4S', m.railMat === 'cds4s', () => setMaterialOpt('railMat', 'cds4s'), true),
    chip('Spruce', m.railMat === 'spruce', () => setMaterialOpt('railMat', 'spruce'), true)
  ]);
  defRow(rb, [
    chip('2x4x8', m.railLen === '8', () => setMaterialOpt('railLen', '8'), true),
    chip('2x4x10', m.railLen === '10', () => setMaterialOpt('railLen', '10'), true),
    chip('2x4x12', m.railLen === '12', () => setMaterialOpt('railLen', '12'), true)
  ]);

  // pickets — sizes shown whole, like the sheet rows (width syncs with FENCE STYLE)
  const kb = defBlock('PICKETS');
  defRow(kb, [
    chip('WW', m.picketMat === 'ww', () => setMaterialOpt('picketMat', 'ww'), true),
    chip('Cedar', m.picketMat === 'cedar', () => setMaterialOpt('picketMat', 'cedar'), true),
    chip('Stained', m.picketMat === 'stained', () => setMaterialOpt('picketMat', 'stained'), true)
  ]);
  defRow(kb, [
    chip('1x4x6', st.picket === '1x4' && m.picketLen === '6', () => setPicketSize('1x4', '6'), true),
    chip('1x6x6', st.picket === '1x6' && m.picketLen === '6', () => setPicketSize('1x6', '6'), true),
    chip('1x4x8', st.picket === '1x4' && m.picketLen === '8', () => setPicketSize('1x4', '8'), true),
    chip('1x6x8', st.picket === '1x6' && m.picketLen === '8', () => setPicketSize('1x6', '8'), true)
  ]);

  // cap & trim, unlocked only when some section actually uses a C&T finish
  const hasCt = mats.ctFt > 0 || st.finish === 'ct';
  const cb = defBlock('CAP & TRIM', hasCt ? '' : '— pick C&T to unlock');
  defRow(cb, [
    chip('SPF/Fir', m.capMat === 'spf', () => setMaterialOpt('capMat', 'spf'), true),
    chip('Cedar', m.capMat === 'cedar', () => setMaterialOpt('capMat', 'cedar'), true)
  ], !hasCt);
  defRow(cb, [
    chip('2x6x10', m.capLen === '10', () => setMaterialOpt('capLen', '10'), true),
    chip('2x6x12', m.capLen === '12', () => setMaterialOpt('capLen', '12'), true),
    chip('2x6x14', m.capLen === '14', () => setMaterialOpt('capLen', '14'), true),
    chip('2x6x16', m.capLen === '16', () => setMaterialOpt('capLen', '16'), true)
  ], !hasCt);
  defRow(cb, [
    chip('1x2x10', m.trimLen === '10', () => setMaterialOpt('trimLen', '10'), true),
    chip('1x2x16', m.trimLen === '16', () => setMaterialOpt('trimLen', '16'), true)
  ], !hasCt);

  // per-section overrides
  const ov = document.createElement('div');
  ov.className = 'ov-list';
  const ot = document.createElement('div');
  ot.className = 'def-title';
  ot.textContent = 'SECTION OVERRIDES';
  ov.appendChild(ot);
  if (!overrides.length) {
    const none = document.createElement('div');
    none.className = 'ov-none';
    none.textContent = 'Everything follows defaults.';
    ov.appendChild(none);
  } else {
    overrides.forEach(o => {
      const it = document.createElement('div');
      it.className = 'ov-item';
      const dot = document.createElement('span');
      dot.className = 'dot';
      it.appendChild(dot);
      const nm = document.createElement('span');
      nm.className = 'name';
      nm.textContent = 'Section ' + o.n + ' — ' + styleShort(o.seg.style);
      nm.addEventListener('click', () => { sel = { kind: 'seg', run: o.run, idx: o.idx }; render(); });
      it.appendChild(nm);
      const rs = document.createElement('button');
      rs.className = 'reset';
      rs.textContent = 'Reset';
      rs.addEventListener('click', () => clearSegStyle(o.run, o.idx));
      it.appendChild(rs);
      ov.appendChild(it);
    });
    const rest = document.createElement('div');
    rest.className = 'ov-none';
    rest.textContent = 'Everything else follows defaults.';
    ov.appendChild(rest);
  }
  defPanel.appendChild(ov);
}

// ---------------------------------------------------------------- toolbar

const btnNew = document.getElementById('btn-new');
const btnUndo = document.getElementById('btn-undo');
const btnRedo = document.getElementById('btn-redo');
const btnHouse = document.getElementById('btn-house');

const lnkSheet = document.getElementById('lnk-sheet');

function updateToolbar() {
  btnUndo.disabled = !undoStack.length;
  btnRedo.disabled = !redoStack.length;
  btnNew.disabled = !currentRun();
  btnHouse.classList.toggle('on', state.house.visible);
  if (state.sheetPhoto) {
    lnkSheet.hidden = false;
    lnkSheet.href = state.sheetPhoto;
  } else {
    lnkSheet.hidden = true;
  }
}

btnNew.addEventListener('click', finishRun);
btnUndo.addEventListener('click', undo);
btnRedo.addEventListener('click', redo);
document.getElementById('btn-fit').addEventListener('click', fitView);
document.getElementById('btn-recalc').addEventListener('click', matRecalcAll);
document.getElementById('btn-print').addEventListener('click', () => window.print());
btnHouse.addEventListener('click', () => {
  pushUndo();
  state.house.visible = !state.house.visible;
  render(); save();
});

// destructive button arms on first click (turns red), executes on second
function armConfirm(b, needs, fn) {
  const originalTitle = b.title;
  let timer = null;
  const disarm = () => {
    timer = null;
    b.classList.remove('peligro');
    b.title = originalTitle;
  };
  b.addEventListener('click', () => {
    if (timer) {
      clearTimeout(timer);
      disarm();
      fn();
      return;
    }
    if (!needs()) { fn(); return; }
    b.classList.add('peligro');
    b.title = 'Tap again to confirm';
    timer = setTimeout(disarm, 3000);
  });
}
armConfirm(document.getElementById('btn-clear'), () => state.runs.length > 0, clearAll);

document.addEventListener('keydown', ev => {
  const inField = /^(INPUT|SELECT|TEXTAREA)$/.test(document.activeElement.tagName);
  if ((ev.ctrlKey || ev.metaKey) && ev.key.toLowerCase() === 'z' && !inField) {
    ev.preventDefault();
    ev.shiftKey ? redo() : undo();
  } else if ((ev.ctrlKey || ev.metaKey) && ev.key.toLowerCase() === 'y' && !inField) {
    ev.preventDefault(); redo();
  } else if ((ev.key === 'Delete' || ev.key === 'Backspace') && sel && !inField) {
    ev.preventDefault();
    if (sel.kind === 'pt') deletePt(sel.run, sel.idx);
    else deleteSeg(sel.run, sel.idx);
  } else if (ev.key === 'Escape') {
    if (sel) { sel = null; render(); }
  }
});

// ---------------------------------------------------------------- examples
// One preset per real work-order sheet. Each lot is drawn on the same frame:
// house at bottom center, fence around it, sides listed clockwise from the
// house's left wall (bl = toward bottom-left corner, then left, top, right,
// br = back to the house's right wall).

const S3 = { rails: 3, finish: 'std', picket: '1x4', mp: true, wp: true };
const S3CT = { rails: 3, finish: 'ct', picket: '1x4', mp: false, wp: true };
const S2 = { rails: 2, finish: 'std', picket: '1x4', mp: false, wp: true };
const S2CT16 = { rails: 2, finish: 'ct', picket: '1x6', mp: false, wp: false };

const B = (len, style) => ({ len: len, style: style || null });          // build piece
const EX = () => ({ type: 'existing' });                                  // neighbor's fence
const G = len => ({ type: 'gate', len: len });                            // regular gate
const GC = len => ({ type: 'gate', len: len, gateStyle: 'ct' });          // cap & trim gate

// RULE (operator, 2026-08-25): only measurements WRITTEN on each sheet enter
// the drawing. Drawn-but-unmeasured pieces stay ?? — never made-up numbers.
// Stretch totals that span a gate (10211: 22'6", Twyla C&T: 11FT, Azul: 105)
// cannot be attached to a single segment, so those pieces are ?? too; the
// written total lives in the preset label pending the client's real splits.
const EXAMPLES = [
  { label: 'Starlight · 10211 Pine River — 215 ft, 1 gate', style: S3, photo: 'sheets/10211-pine-river.jpg',
    sides: { bl: [B(), G(), B()], left: [B(52)], top: [B(73.48)], right: [B(52)], br: [B(15)] } },
  // 7' / 4' gate / 7' exactly as the crew labeled them
  { label: 'Starlight · 10207 Pine River — 164 ft, 1 gate', style: S3, photo: 'sheets/10207-pine-river.jpg',
    sides: { bl: [B(22.7)], left: [B(58)], top: [B(64.86)], right: [EX()], br: [B(7), G(4), B(7)] } },
  { label: 'Starlight · 10142 Pine River — 61 ft, 1 gate', style: S3, photo: 'sheets/10142-pine-river.jpg',
    sides: { bl: [B(12.42)], left: [EX()], top: [EX()], right: [B(35)], br: [B(12.5), G()] } },
  { label: 'Starlight · 10150 Pine River — 82 ft, 1 gate', style: S3, photo: 'sheets/10150-pine-river.jpg',
    sides: { bl: [B(13)], left: [EX()], top: [EX()], right: [B(56)], br: [B(12.9), G()] } },
  // 4 = the written 13' total minus the written 9' piece (arithmetic, not a guess)
  { label: 'Starlight · 10215 Pine River — 115 ft, 1 gate', style: S3, photo: 'sheets/10215-pine-river.jpg',
    sides: { bl: [B(4), G(), B(9)], left: [EX()], top: [B(55)], right: [B(3), B(34)], br: [B(13)] } },
  { label: 'Starlight · 12822 Prairie Valley — 90 ft, 1 gate', style: S3, photo: 'sheets/12822-prairie-valley.jpg',
    sides: { bl: [B(16)], left: [EX()], top: [EX()], right: [B(19.75), B(32.25)], br: [B(), G(10), B()] } },
  { label: 'Starlight · 12826 Prairie Valley — 78 ft, 1 gate', style: S3, photo: 'sheets/12826-prairie-valley.jpg',
    sides: { bl: [B(), G(), B()], left: [EX()], top: [EX()], right: [B(46)], br: [B(15.42)] } },
  // two fence rows on the sheet: 3 Rails 91FT (85+6) + 3 Rails C&T 11FT (the
  // two unmeasured stubs flanking the gates carry the C&T style)
  { label: 'Perry · 10830 Twyla Rd — 91 ft + 11 ft C&T, 2 C&T gates', style: S3, photo: 'sheets/10830-twyla.jpg',
    sides: { bl: [GC(5), B(null, S3CT)], left: [B(85)], top: [EX()], right: [EX(), B(6)], br: [B(null, S3CT), GC(5.08)] } },
  { label: 'Perry · 10826 Twyla Rd — 11 ft C&T, 2 C&T gates', style: S3CT, photo: 'sheets/10826-twyla.jpg',
    sides: { bl: [GC(5), B()], left: [EX()], top: [EX()], right: [EX()], br: [B(), GC(5.08)] } },
  // two fence rows: 3 Rails 150FT (90+50+10?) — the sheet's C&T row is 10FT,
  // which is the 10' bottom-right piece (also explains its 2x4x10 x3 rails)
  { label: 'Perry · 10830 Saleh Corner — 150 ft + 10 ft C&T, 2 C&T gates', style: S3, photo: 'sheets/10830-saleh-corner.jpg',
    sides: { bl: [GC(5)], left: [B(90)], top: [B(50)], right: [EX()], br: [B(10, S3CT), GC(5.08)] } },
  { label: 'Perry · 1359 Azul Way — 105 ft C&T, 2 gates', style: S3CT, photo: 'sheets/1359-azul-way.jpg',
    sides: { bl: [GC(10.08), B()], left: [B(85)], top: [EX()], right: [EX()], br: [B(), GC(5)] } },
  { label: 'Perry · 9929 Paladin Ridge — 2 rails, 2 gates', style: S2, photo: 'sheets/9929-paladin-ridge.webp',
    sides: { bl: [G(5.08), B()], left: [B(93)], top: [B(45)], right: [B(96)], br: [B(), G(5)] } },
  { label: 'Perry · 14427 Chaparral Run — 2 rails, 2 gates', style: S2, photo: 'sheets/14427-chaparral-run.webp',
    sides: { bl: [G(5), B()], left: [EX()], top: [EX()], right: [B(105)], br: [B(), G(5)] } },
  // top side = 97'13" plus the 3'10" piece from the survey PIN to the corner;
  // gate widths are not written on this sketch → ??
  { label: 'South Texas · 5147 Lottchen — 325 ft 2R C&T 1x6, 2 gates', style: S2CT16,
    photo: 'sheets/5147-lottchen.webp',
    materials: { picketLen: '6', capLen: '12', capMat: 'cedar', nailSystem: 'clips' },
    sides: { bl: [GC(), B(28.21)], left: [B(77)], top: [B(97.13), B(3.83)], right: [B(90)], br: [B(28.21), GC()] } },
  // irregular 6-sided lot — custom frame instead of the standard rectangle.
  // South Texas-style materials sheet → clips nail system
  { label: 'Perry · 10518 Hot Shoe Lane (Kallison) — 752 ft, 2 gates',
    style: { rails: 3, finish: 'std', picket: '1x4', mp: false, wp: true },
    materials: { nailSystem: 'clips' },
    frame: [
      { x: 450, y: 440 },   // house left wall
      { x: 392, y: 452 },
      { x: 255, y: 458 },
      { x: 118, y: 180 },
      { x: 205, y: 58 },
      { x: 890, y: 42 },
      { x: 925, y: 390 },
      { x: 690, y: 444 },
      { x: 630, y: 440 }    // house right wall
    ],
    pieces: [[G(10)], [B(20)], [B(195)], [B(59.36)], [B(312.86)], [B(115)], [B(50)], [G(10)]] }
];

function loadPreset(p, idx) {
  pushUndo();
  const house = { x: 450, y: 320, w: 180, h: 120, visible: true };
  const AL = { x: 450, y: 440 }, BLc = { x: 280, y: 440 }, TLc = { x: 280, y: 160 };
  const TRc = { x: 810, y: 160 }, BRc = { x: 810, y: 440 }, AR = { x: 630, y: 440 };
  // default frame is a rectangle; a preset may bring its own polygon (frame +
  // one piece-array per span) for irregular lots
  const frame = p.frame || [AL, BLc, TLc, TRc, BRc, AR];
  const spans = p.pieces || [p.sides.bl, p.sides.left, p.sides.top, p.sides.right, p.sides.br];
  const pts = [{ x: frame[0].x, y: frame[0].y }];
  const segs = [];
  const sides = spans.map((pieces, i) => [frame[i], frame[i + 1], pieces]);
  sides.forEach((side, si) => {
    const a = side[0], b = side[1], pieces = side[2];
    const ws = pieces.map(pc => pc.len || 20);
    const tot = ws.reduce((s, w) => s + w, 0);
    let acc = 0;
    pieces.forEach((pc, i) => {
      segs.push({
        type: pc.type || 'build', len: pc.len != null ? pc.len : null,
        gateStyle: pc.gateStyle || 'regular', hinge: 'strap',
        style: pc.style ? { ...pc.style } : null
      });
      if (i < pieces.length - 1) {
        acc += ws[i];
        const t = acc / tot;
        pts.push({ x: a.x + (b.x - a.x) * t, y: a.y + (b.y - a.y) * t, post: true });
      }
    });
    // corner post at the side's end; the very last point is the house anchor
    pts.push(si === sides.length - 1 ? { x: b.x, y: b.y } : { x: b.x, y: b.y, post: true });
  });
  state = {
    house: house,
    runs: [{ pts: pts, closed: false, finished: true, segs: segs }],
    style: { ...p.style },
    materials: Object.assign({ ...MATERIALS_DEFAULT }, p.materials || {}),
    matOv: {},
    sheetPhoto: p.photo || null, // original work-order photo (local only, not in the public repo)
    presetIdx: idx != null ? idx : null // keeps the combo naming the project across reloads
  };
  sel = null;
  vb = { x: 0, y: 0, w: 1000, h: 560 };
  applyVB();
  render(); save();
}

const selExample = document.getElementById('sel-example');
(function () {
  const ph = document.createElement('option');
  ph.value = '';
  ph.textContent = 'Examples…';
  selExample.appendChild(ph);
  EXAMPLES.forEach((p, i) => {
    const o = document.createElement('option');
    o.value = String(i);
    o.textContent = p.label;
    selExample.appendChild(o);
  });
  selExample.addEventListener('change', () => {
    const i = parseInt(selExample.value, 10);
    if (Number.isNaN(i) || !EXAMPLES[i]) return;
    loadPreset(EXAMPLES[i], i); // replaces the drawing; Undo brings it back
  });
  // after a reload, keep naming the project the saved drawing came from
  if (state.presetIdx != null && EXAMPLES[state.presetIdx]) {
    selExample.value = String(state.presetIdx);
  }
})();

// ---------------------------------------------------------------- init

applyVB();
render();
