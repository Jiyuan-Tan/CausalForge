/**
 * Deterministic diagram layout for P6 slide figures.
 *
 * The model authors CONTENT only — a tiny line DSL of nodes and edges — and this
 * module computes all geometry: box sizes measured from the text, a layered
 * left-to-right layout, and curved edges anchored to box borders. Freehand
 * model-drawn SVG kept producing overflowing labels and missing arrows; with the
 * geometry deterministic, those defects are structurally impossible.
 *
 * DSL (one statement per line; `#` comments and blank lines ignored):
 *   node <id> | <Title> | <detail line> | <detail line…>
 *   edge <src> -> <dst>
 * ids are [a-z0-9-]+; every edge endpoint must be a declared node.
 */

export interface FigureNode {
  id: string;
  lines: string[]; // first = bold title, rest = detail lines
}

export interface FigureEdge {
  src: string;
  dst: string;
}

export interface FigureSpec {
  nodes: FigureNode[];
  edges: FigureEdge[];
}

export function parseFigureDsl(text: string): FigureSpec {
  const nodes: FigureNode[] = [];
  const edges: FigureEdge[] = [];
  const seen = new Set<string>();
  for (const [i, raw] of text.split("\n").entries()) {
    const line = raw.trim();
    if (!line || line.startsWith("#")) continue;
    const nodeMatch = /^node\s+([a-z0-9-]+)\s*\|(.+)$/.exec(line);
    const edgeMatch = /^edge\s+([a-z0-9-]+)\s*->\s*([a-z0-9-]+)\s*$/.exec(line);
    if (nodeMatch) {
      const lines = nodeMatch[2].split("|").map((s) => s.trim()).filter(Boolean);
      if (lines.length === 0) throw new Error(`figure DSL line ${i + 1}: node "${nodeMatch[1]}" has no title`);
      if (seen.has(nodeMatch[1])) throw new Error(`figure DSL line ${i + 1}: duplicate node "${nodeMatch[1]}"`);
      seen.add(nodeMatch[1]);
      nodes.push({ id: nodeMatch[1], lines });
    } else if (edgeMatch) {
      edges.push({ src: edgeMatch[1], dst: edgeMatch[2] });
    } else {
      throw new Error(`figure DSL line ${i + 1}: expected \`node <id> | <Title> | …\` or \`edge <a> -> <b>\`, got: ${line}`);
    }
  }
  if (nodes.length === 0) throw new Error("figure DSL declares no nodes");
  if (nodes.length > 10) throw new Error(`figure DSL declares ${nodes.length} nodes; at most 10 (schematics stay simple)`);
  for (const e of edges) {
    for (const end of [e.src, e.dst]) {
      if (!seen.has(end)) throw new Error(`figure DSL: edge references undeclared node "${end}"`);
    }
    if (e.src === e.dst) throw new Error(`figure DSL: self-loop on "${e.src}"`);
  }
  return { nodes, edges };
}

// ── Geometry constants (viewBox units) ──────────────────────────────────
const TITLE_SIZE = 17;
const DETAIL_SIZE = 14.5;
const LINE_H = 23;
const PAD_X = 18;
const PAD_Y = 14;
const COL_GAP = 90;
const ROW_GAP = 36;
const MARGIN = 24;
// Approximate glyph advance per font unit for a humanist sans; deliberately
// generous so measured widths overestimate and text never touches a border.
const CHAR_W = 0.62;

function textWidth(s: string, size: number, bold: boolean): number {
  return s.length * size * CHAR_W * (bold ? 1.08 : 1);
}

function esc(s: string): string {
  return s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");
}

interface Box {
  node: FigureNode;
  layer: number;
  w: number;
  h: number;
  x: number;
  y: number;
}

/** Longest-path layering: sources at layer 0, every edge goes strictly rightward.
 *  A cycle (should not appear in a schematic) falls back to declaration order. */
function layerOf(spec: FigureSpec): Map<string, number> {
  const preds = new Map<string, string[]>();
  for (const n of spec.nodes) preds.set(n.id, []);
  for (const e of spec.edges) preds.get(e.dst)!.push(e.src);
  const memo = new Map<string, number>();
  const onStack = new Set<string>();
  const depth = (id: string): number => {
    if (memo.has(id)) return memo.get(id)!;
    if (onStack.has(id)) return 0; // cycle guard
    onStack.add(id);
    const d = Math.max(0, ...preds.get(id)!.map((p) => depth(p) + 1));
    onStack.delete(id);
    memo.set(id, d);
    return d;
  };
  for (const n of spec.nodes) depth(n.id);
  return memo;
}

const FILLS = ["#ffffff", "#e7f0ef", "#f6efdb"];

/** Renders the spec to a self-contained SVG (fill-only text, viewBox, no external refs). */
export function renderFigureSvg(spec: FigureSpec): string {
  const layers = layerOf(spec);
  const boxes: Box[] = spec.nodes.map((node) => {
    const w =
      2 * PAD_X +
      Math.max(...node.lines.map((l, i) => textWidth(l, i === 0 ? TITLE_SIZE : DETAIL_SIZE, i === 0)));
    const h = 2 * PAD_Y + node.lines.length * LINE_H;
    return { node, layer: layers.get(node.id)!, w, h, x: 0, y: 0 };
  });
  const nLayers = Math.max(...boxes.map((b) => b.layer)) + 1;
  const colWidths: number[] = [];
  for (let l = 0; l < nLayers; l++) {
    colWidths[l] = Math.max(0, ...boxes.filter((b) => b.layer === l).map((b) => b.w));
  }
  const colX: number[] = [];
  let x = MARGIN;
  for (let l = 0; l < nLayers; l++) {
    colX[l] = x;
    x += colWidths[l] + COL_GAP;
  }
  const totalW = x - COL_GAP + MARGIN;
  const colHeights: number[] = [];
  for (let l = 0; l < nLayers; l++) {
    const col = boxes.filter((b) => b.layer === l);
    colHeights[l] = col.reduce((s, b) => s + b.h, 0) + ROW_GAP * Math.max(0, col.length - 1);
  }
  const totalH = Math.max(...colHeights) + 2 * MARGIN;
  for (let l = 0; l < nLayers; l++) {
    const col = boxes.filter((b) => b.layer === l);
    let y = (totalH - colHeights[l]) / 2;
    for (const b of col) {
      b.x = colX[l] + (colWidths[l] - b.w) / 2; // center within column
      b.y = y;
      y += b.h + ROW_GAP;
    }
  }
  const byId = new Map(boxes.map((b) => [b.node.id, b]));

  // Fan-in/fan-out: when several edges share a box side, spread their endpoints
  // along that side (ordered by the counterpart's vertical position) so arrows
  // stay visually distinct — three edges into a selector must read as three.
  const outPort = new Map<string, number>();
  const inPort = new Map<string, number>();
  const portKey = (e: FigureEdge) => `${e.src}->${e.dst}`;
  for (const b of boxes) {
    const outs = spec.edges
      .filter((e) => e.src === b.node.id)
      .sort((p, q) => byId.get(p.dst)!.y - byId.get(q.dst)!.y);
    outs.forEach((e, i) => outPort.set(portKey(e), b.y + (b.h * (i + 1)) / (outs.length + 1)));
    const ins = spec.edges
      .filter((e) => e.dst === b.node.id)
      .sort((p, q) => byId.get(p.src)!.y - byId.get(q.src)!.y);
    ins.forEach((e, i) => inPort.set(portKey(e), b.y + (b.h * (i + 1)) / (ins.length + 1)));
  }

  // Edge routing. Curvature is kept proportional to the actual vertical offset:
  // a near-horizontal edge renders near-straight, and only genuinely offset
  // edges bend. Edges spanning >1 column try the direct curve first and only
  // detour — just past the boxes actually in the way, not to a global bottom
  // lane — when the direct path would cut through an intermediate box.
  const CLEAR = 26; // detour clearance beyond a blocking box border
  const bezier = (p0: [number, number], p1: [number, number], p2: [number, number], p3: [number, number], t: number): [number, number] => {
    const u = 1 - t;
    return [
      u * u * u * p0[0] + 3 * u * u * t * p1[0] + 3 * u * t * t * p2[0] + t * t * t * p3[0],
      u * u * u * p0[1] + 3 * u * u * t * p1[1] + 3 * u * t * t * p2[1] + t * t * t * p3[1],
    ];
  };
  const hitsBox = (pts: [number, number][], skip: Set<string>): Box | undefined =>
    boxes.find(
      (bx) =>
        !skip.has(bx.node.id) &&
        pts.some(([px, py]) => px > bx.x - 8 && px < bx.x + bx.w + 8 && py > bx.y - 8 && py < bx.y + bx.h + 8),
    );
  const samples = (segs: [number, number][][]): [number, number][] => {
    const pts: [number, number][] = [];
    for (const [p0, p1, p2, p3] of segs) {
      for (let i = 1; i < 40; i++) pts.push(bezier(p0, p1, p2, p3, i / 40));
    }
    return pts;
  };
  // Horizontal control arm: grows with the vertical offset (up to half the span)
  // so flat edges stay flat and only real jumps curve.
  const arm = (dxSpan: number, dy: number): number =>
    Math.max(24, Math.min(dxSpan / 2, Math.abs(dy) * 0.8 + 24));
  const edgePaths: string[] = [];
  const detours: { yD: number; xMin: number; xMax: number }[] = [];
  let yLo = 0, yHi = totalH; // canvas extent, grown by detours
  for (const e of spec.edges) {
    const a = byId.get(e.src)!;
    const b = byId.get(e.dst)!;
    const x1 = a.x + a.w, y1 = outPort.get(portKey(e))!;
    const x2 = b.x, y2 = inPort.get(portKey(e))!;
    const skip = new Set([e.src, e.dst]);
    const dx = arm(x2 - x1, y2 - y1);
    const direct: [number, number][][] = [[[x1, y1], [x1 + dx, y1], [x2 - dx, y2], [x2 - 3, y2]]];
    if (b.layer - a.layer <= 1 || !hitsBox(samples(direct), skip)) {
      edgePaths.push(
        `<path d="M ${r(x1)} ${r(y1)} C ${r(x1 + dx)} ${r(y1)}, ${r(x2 - dx)} ${r(y2)}, ${r(x2 - 3)} ${r(y2)}" fill="none" stroke="#1e1e1c" stroke-width="1.8" marker-end="url(#arr)"/>`,
      );
      continue;
    }
    // Detour: clear the boxes strictly between the two layers within the edge's
    // x-range, passing whichever side (above/below) deviates least; stagger
    // lanes that would overlap an earlier detour.
    const between = boxes.filter(
      (bx) => bx.layer > a.layer && bx.layer < b.layer && bx.x + bx.w > x1 && bx.x < x2,
    );
    const topLane = Math.min(...between.map((bx) => bx.y)) - CLEAR;
    const botLane = Math.max(...between.map((bx) => bx.y + bx.h)) + CLEAR;
    const mid = (y1 + y2) / 2;
    const side = Math.abs(topLane - mid) <= Math.abs(botLane - mid) ? -1 : 1;
    const midX = (x1 + x2) / 2;
    const g1 = Math.min(60, (x2 - x1) * 0.2);
    const g2 = Math.min(110, (x2 - x1) * 0.3);
    // The candidate detour is validated as the ACTUAL pair of cubics it will be
    // drawn as — not a single midpoint probe — so a lane whose approach ramps
    // still clip a box is pushed further out.
    const detourSegs = (y: number): [number, number][][] => [
      [[x1, y1], [x1 + g1, y1], [midX - g2, y], [midX, y]],
      [[midX, y], [midX + g2, y], [x2 - g1, y2], [x2 - 3, y2]],
    ];
    let yD = side < 0 ? topLane : botLane;
    let clear = false;
    for (let tries = 0; tries < 12; tries++) {
      const clash =
        detours.some((d) => Math.abs(d.yD - yD) < 16 && d.xMax > x1 && d.xMin < x2) ||
        hitsBox(samples(detourSegs(yD)), skip) !== undefined;
      if (!clash) {
        clear = true;
        break;
      }
      yD += side * 18;
    }
    if (!clear) {
      // Exhausted candidates: start from a lane strictly beyond every box
      // (staggered per detour) and keep pushing outward until the actual pair
      // of cubics is collision-free — pushing away from all boxes converges.
      yD =
        side < 0
          ? Math.min(...boxes.map((bx) => bx.y)) - CLEAR - 18 * (detours.length + 1)
          : Math.max(...boxes.map((bx) => bx.y + bx.h)) + CLEAR + 18 * (detours.length + 1);
      // Terminates: each step moves the lane 18 further from every box and every
      // earlier lane (all finite), and once past their inflated extents both
      // predicates are false — so the emitted lane is always fully checked.
      while (
        detours.some((d) => Math.abs(d.yD - yD) < 16 && d.xMax > x1 && d.xMin < x2) ||
        hitsBox(samples(detourSegs(yD)), skip) !== undefined
      ) {
        yD += side * 18;
      }
    }
    detours.push({ yD, xMin: x1, xMax: x2 });
    yLo = Math.min(yLo, yD - 12);
    yHi = Math.max(yHi, yD + 12);
    edgePaths.push(
      `<path d="M ${r(x1)} ${r(y1)} C ${r(x1 + g1)} ${r(y1)}, ${r(midX - g2)} ${r(yD)}, ${r(midX)} ${r(yD)} C ${r(midX + g2)} ${r(yD)}, ${r(x2 - g1)} ${r(y2)}, ${r(x2 - 3)} ${r(y2)}" fill="none" stroke="#1e1e1c" stroke-width="1.8" marker-end="url(#arr)"/>`,
    );
  }
  const viewY = Math.min(0, yLo);
  // Only a detour extends the canvas — a detour-free figure keeps exactly totalH.
  const canvasH = (detours.length > 0 ? Math.max(totalH, yHi + MARGIN) : totalH) - viewY;

  const parts: string[] = [];
  parts.push(
    `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 ${Math.round(viewY)} ${Math.round(totalW)} ${Math.round(canvasH)}" role="img">`,
    `<defs><marker id="arr" viewBox="0 0 10 10" refX="8.5" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M 0 0 L 10 5 L 0 10 z" fill="#1e1e1c"/></marker></defs>`,
    ...edgePaths,
  );
  for (const b of boxes) {
    parts.push(
      `<rect x="${r(b.x)}" y="${r(b.y)}" width="${r(b.w)}" height="${r(b.h)}" rx="10" fill="${FILLS[b.layer % FILLS.length]}" stroke="#1e1e1c" stroke-width="1.5"/>`,
    );
    b.node.lines.forEach((line, i) => {
      const size = i === 0 ? TITLE_SIZE : DETAIL_SIZE;
      const y = b.y + PAD_Y + i * LINE_H + LINE_H * 0.72;
      parts.push(
        `<text stroke="none" x="${r(b.x + b.w / 2)}" y="${r(y)}" text-anchor="middle" font-family="Inter, Arial, sans-serif" font-size="${size}"${i === 0 ? ' font-weight="700"' : ""} fill="${i === 0 ? "#1e1e1c" : "#44403a"}">${esc(line)}</text>`,
      );
    });
  }
  parts.push("</svg>");
  return parts.join("\n") + "\n";
}

const r = (n: number): number => Math.round(n * 10) / 10;
