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

  // Long edges (spanning >1 column) must not cut through intermediate boxes:
  // route them through a detour lane below the columns they skip.
  const edgePaths: string[] = [];
  let laneY = totalH - MARGIN; // next free detour lane; grows the canvas as needed
  for (const e of spec.edges) {
    const a = byId.get(e.src)!;
    const b = byId.get(e.dst)!;
    const x1 = a.x + a.w, y1 = outPort.get(portKey(e))!;
    const x2 = b.x, y2 = inPort.get(portKey(e))!;
    if (b.layer - a.layer > 1) {
      laneY += 34;
      const yD = laneY;
      const midX = (x1 + x2) / 2;
      edgePaths.push(
        `<path d="M ${r(x1)} ${r(y1)} C ${r(x1 + 50)} ${r(y1)}, ${r(midX - 120)} ${r(yD)}, ${r(midX)} ${r(yD)} C ${r(midX + 120)} ${r(yD)}, ${r(x2 - 50)} ${r(y2)}, ${r(x2 - 3)} ${r(y2)}" fill="none" stroke="#1e1e1c" stroke-width="2" marker-end="url(#arr)"/>`,
      );
    } else {
      const dx = Math.max(30, (x2 - x1) / 2);
      edgePaths.push(
        `<path d="M ${r(x1)} ${r(y1)} C ${r(x1 + dx)} ${r(y1)}, ${r(x2 - dx)} ${r(y2)}, ${r(x2 - 3)} ${r(y2)}" fill="none" stroke="#1e1e1c" stroke-width="2" marker-end="url(#arr)"/>`,
      );
    }
  }
  const canvasH = laneY > totalH - MARGIN ? laneY + MARGIN : totalH;

  const parts: string[] = [];
  parts.push(
    `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${Math.round(totalW)} ${Math.round(canvasH)}" role="img">`,
    `<defs><marker id="arr" viewBox="0 0 10 10" refX="8.5" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M 0 0 L 10 5 L 0 10 z" fill="#1e1e1c"/></marker></defs>`,
    ...edgePaths,
  );
  for (const b of boxes) {
    parts.push(
      `<rect x="${r(b.x)}" y="${r(b.y)}" width="${r(b.w)}" height="${r(b.h)}" rx="8" fill="${FILLS[b.layer % FILLS.length]}" stroke="#1e1e1c" stroke-width="2"/>`,
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
