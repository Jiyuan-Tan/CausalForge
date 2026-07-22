import { readFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import { parseNoteBlocks } from "../presentation/note_parser.js";
import { createEmptyGraph } from "./store.js";
import { addEdge, addNode } from "./mutate.js";
import type { FormalizationGraph, NodeKind } from "./types.js";

/** obj_id → node id.
 *  Typed-core SEMANTIC ids ("ass:nuisance-rate", "thm:welfare-identity", "sym:A") ARE the graph
 *  node ids verbatim — the typed graph builder stores the raw core id (hyphens preserved), and the
 *  reviewer emits the same id — so pass any colon-bearing id THROUGH UNCHANGED. Mangling it (the old
 *  unconditional `replace(/-/g,"")`) turned "ass:nuisance-rate" into "ass:nuisancerate", which matched
 *  no node, so `applyVerdictsToGraph` silently dropped every hyphenated verdict → nodes stayed
 *  `passed_hash:null` → re-reviewed every pass (the convergence-killing bug).
 *  Only the LEGACY per-conjecture scheme ("T-1"→"t1","A-2"→"a2","P-1b"→"p1b") is de-hyphenated/lowercased. */
export function objIdToNodeId(objId: string): string {
  if (objId.includes(":")) return objId;
  return objId.replace(/-/g, "").toLowerCase();
}

/** Inverse of objIdToNodeId: "t1"→"T-1", "p1b"→"P-1b", "a2"→"A-2", "s1"→"S-1".
 *  Ids without a single [plats]-letter + digit prefix (e.g. "setup", "aux_foo")
 *  pass through unchanged. */
export function nodeIdToObjId(nodeId: string): string {
  const m = nodeId.match(/^([plats])(\d[\w]*)$/i);
  return m ? `${m[1].toUpperCase()}-${m[2]}` : nodeId;
}

function kindFromObjId(objId: string): NodeKind {
  if (objId.startsWith("T-")) return "theorem";
  if (objId.startsWith("L-")) return "lemma";
  if (objId.startsWith("A-")) return "assumption";
  if (objId.startsWith("S-")) return "setup";
  return "definition"; // P-
}

/** Pull the `.tex` line-range anchor out of a parsed fields map or a raw body. */
function texAnchor(fields: Record<string, string>, body: string): string {
  const key = Object.keys(fields).find((k) => /tex.*line range/i.test(k));
  const raw = key ? fields[key] : (body.match(/\*\*[^*]*tex[^*]*line range[^*]*\*\*\s*([^\n]*)/i)?.[1] ?? "");
  return raw.match(/"([^"]+)"/)?.[1] ?? raw.replace(/[`*]/g, "").trim();
}

/**
 * The STRUCTURED dependency-bearing text of a block — the only place F1-authored
 * `proof-uses` edges are read from. Deliberately NOT the whole body: a block's
 * statement / intuition / drift-watch prose may mention other obj-ids in passing
 * (e.g. "unlike A-3 …", a dropped hypothesis), and those incidental mentions must
 * NOT become edges. The licensed dependencies live in:
 *   - a T-block's `**Load-bearing hypotheses.**` list (up to the next field/header,
 *     which naturally stops before the `**Hypotheses dropped … (drift-watch)**` block);
 *   - an L-block's `*Hyp:* … *Concl:*` span;
 *   - an explicit `Depends on: …` field (P/L blocks).
 * Realized (Lean-side) dependencies come separately from `statement-uses` extraction.
 */
function dependencyText(body: string): string {
  const parts: string[] = [];
  const lb = body.match(/\*\*Load-bearing hypotheses\.?\*\*([\s\S]*?)(?=\n\s*\*\*|\n#{1,3}\s|$)/i);
  if (lb) parts.push(lb[1]);
  const hyp = body.match(/\*Hyp:\*([\s\S]*?)(?:\*Concl|$)/i);
  if (hyp) parts.push(hyp[1]);
  // Capture up to the first period so the dep LIST is read but trailing prose on
  // the same line (e.g. "… P-7. (the domain T-2 quantifies over)") is not.
  for (const m of body.matchAll(/Depends on[:.]?\s*([^.\n]*)/gi)) parts.push(m[1]);
  return parts.join("\n");
}

/** A representative NL statement for a block. */
function nlStatement(fields: Record<string, string>, body: string, title: string): string {
  for (const k of ["Statement", "Conclusion (typed)", "Conclusion", "Definition", "Signature"]) {
    if (fields[k]) return fields[k].trim();
  }
  // strip bold field-label lines (`**X.** …`) from the body for the fallback
  const stripped = body.replace(/^\s*\*\*[^*]+\*\*.*$/gm, "").trim();
  return stripped || title;
}

interface RawBlock { objId: string; title: string; body: string; }

/**
 * Scan A-/S- blocks. `parseNoteBlocks` is pinned to `^[PLT]-` by the presentation
 * contract test (and is consumed by the causalsmith stages), so A-/S- recognition
 * lives here rather than in the shared note parser. Accepts the bold form
 * `**A-2 (Title).**` / `**S-1 (Title).**` and the legacy `### A-2.` / `### S-1.`.
 */
function scanEnvAndAssumptionBlocks(md: string): RawBlock[] {
  // Title captured lazily (`.*?`) so a closing paren inside a math title does not
  // truncate the header and drop the block (mirrors note_parser's HEADER_BOLD_PL).
  const bold = /^\*\*(?<id>[AS]-\d[\w]*)\s*\((?<title>.*?)\)\s*\.?\s*\*\*\s*(?<rest>.*)$/;
  const legacy = /^#{2,4}\s+(?<id>[AS]-\d[\w]*)\.?\s*(?<title>.*?)\.?\s*$/;
  const pltBoundary =
    /^###\s+[PLT]-\d[\w]*\.?\s*.*$|^#{2,3}\s+T-block:\s*[tT]\d+\b|^\*\*[PL]-\d[\w]*\s*\(.*?\)\s*\.?\s*\*\*/;
  const out: RawBlock[] = [];
  let cur: RawBlock | null = null;
  const push = () => { if (cur) out.push(cur); cur = null; };
  for (const ln of md.split(/\r?\n/)) {
    const m = ln.match(bold) ?? ln.match(legacy);
    if (m) {
      push();
      cur = { objId: m.groups!.id, title: (m.groups!.title ?? "").trim(), body: (m.groups!.rest ?? "") + "\n" };
      continue;
    }
    if (/^## /.test(ln) || pltBoundary.test(ln)) { push(); continue; } // why: A/S bodies must stop before following P/L/T blocks.
    if (cur) cur.body += ln + "\n";
  }
  push();
  return out;
}

function withSetup(g: FormalizationGraph, id: string, mods: string[]): FormalizationGraph {
  return { ...g, nodes: g.nodes.map((n) => (n.id === id ? { ...n, setup: { required_modules: mods } } : n)) };
}
function withExternalLean(g: FormalizationGraph, id: string, decl: string): FormalizationGraph {
  return { ...g, nodes: g.nodes.map((n) => (n.id === id ? { ...n, lean: { decl_name: decl, file: null } } : n)) };
}

/**
 * Build the formalization graph from an F1 `.md` plan:
 *  - setup nodes from S-blocks (with required_modules), or one synthesized fallback;
 *  - assumption nodes from A-blocks;
 *  - definition/lemma/theorem nodes from P/L/T blocks (parseNoteBlocks);
 *  - a definition P-block with a `**reuse.** <decl>` field → a library-backed node;
 *  - a `setup-of` edge from every setup node to every theorem.
 * Dependency edges among blocks are NOT emitted here — `statement-uses` edges come
 * from F2 extraction, `proof-uses` from F3 declarations. Best-effort on a missing file.
 */
export async function buildGraphFromMd(qid: string, spec: string, mdPath: string): Promise<FormalizationGraph> {
  let g = createEmptyGraph(qid, spec);
  if (!existsSync(mdPath)) return g;
  const md = await readFile(mdPath, "utf8");

  // --- A/S blocks (graph-local scan) ---
  const setupIds: string[] = [];
  for (const b of scanEnvAndAssumptionBlocks(md)) {
    const id = objIdToNodeId(b.objId);
    if (g.nodes.some((n) => n.id === id)) continue;
    const isSetup = b.objId.startsWith("S-");
    g = addNode(g, {
      id,
      kind: isSetup ? "setup" : "assumption",
      provenance: "from-note",
      nl_statement: nlStatement({}, b.body, b.title),
      tex_anchor: texAnchor({}, b.body),
    });
    if (isSetup) {
      const mods = (b.body.match(/\*\*required modules\.?\*\*\s*([^\n]*)/i)?.[1] ?? "")
        .split(",").map((s) => s.trim()).filter(Boolean);
      g = withSetup(g, id, mods);
      setupIds.push(id);
    }
  }
  if (setupIds.length === 0) {
    g = addNode(g, { id: "setup", kind: "setup", provenance: "from-note", nl_statement: "the environment / substrate of the run", tex_anchor: "" });
    g = withSetup(g, "setup", []);
    setupIds.push("setup");
  }

  // --- P/L/T blocks via the shared note parser ---
  const plt = parseNoteBlocks(md);
  for (const b of plt) {
    const id = objIdToNodeId(b.obj_id);
    if (g.nodes.some((n) => n.id === id)) continue;
    const kind = kindFromObjId(b.obj_id);
    const reuse = kind === "definition" ? b.fields["reuse"]?.trim() : undefined;
    // A note block is `from-note` (a paper object) regardless of whether its Lean
    // realization reuses a library decl — the reuse is a fact about the Lean side,
    // recorded via `withExternalLean` (decl_name set, file null), NOT a reason to
    // demote it out of the paper / out of the review scope. (Tagging reuse defs
    // `library` set frozen=false and dropped them from review_scope + the paper —
    // the μ^bd / clip / score self-containedness + unreviewed-def gap.)
    g = addNode(g, {
      id,
      kind,
      provenance: "from-note",
      nl_statement: nlStatement(b.fields, b.body, b.title),
      tex_anchor: texAnchor(b.fields, b.body),
    });
    if (reuse) g = withExternalLean(g, id, reuse);
  }

  // --- F1-authored (declared) dependency edges ---
  // Read ONLY the block's structured dependency annotations (see `dependencyText`),
  // not its whole body — so a `proof-uses` edge means F1 LICENSED that dependency,
  // not that the obj-id was mentioned in passing. The realized dependencies are
  // cross-checked separately by `statement-uses` extraction from the Lean.
  for (const b of plt) {
    const from = objIdToNodeId(b.obj_id);
    if (!g.nodes.some((n) => n.id === from)) continue;
    const refs = new Set(dependencyText(b.body).match(/\b[PLAT]-\d[\w]*\b/g) ?? []); // why: dependency ids share the block parser's multi-suffix shape.
    for (const ref of refs) {
      const to = objIdToNodeId(ref);
      if (to !== from && g.nodes.some((n) => n.id === to)) {
        g = addEdge(g, { kind: "proof-uses", from, to, source: "declared" });
      }
    }
  }

  for (const n of g.nodes) {
    if (n.kind === "theorem") for (const sid of setupIds) {
      g = addEdge(g, { kind: "setup-of", from: sid, to: n.id, source: "declared" });
    }
  }
  return g;
}
