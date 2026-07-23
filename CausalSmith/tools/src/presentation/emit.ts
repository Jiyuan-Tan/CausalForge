import { readFile } from "node:fs/promises";
import { join } from "node:path";
import type { AnchoredEnv } from "./tex_anchors.js";
import type {
  CrosswalkEntry,
  PresentationCrosswalk,
  LeanSnippets,
  PresentationEntry,
  LeanSnippet,
  FormalLayer,
  FormalLayerItem,
} from "./types.js";
import type { NoteBlock } from "./note_parser.js";
import type { SymbolCluster } from "../formalization/crosswalk.js";
import { tryExtractDeclSnippet, extractHypothesisBinders, sorryFree } from "./lean_extract.js";
import { graphComponentSpecs } from "./graph_components.js";
import { auxiliaryNodes, isCitedNode } from "./graph_view.js";
import { matchSynthDecl } from "./synth_lean_match.js";
import { isUndeliveredNode } from "../graph/types.js";
import type { FormalizationGraph, GraphNode } from "../graph/types.js";

/**
 * Shared Lean-source reader for the emitters.
 *
 * A banked node's recorded `lean.file` can be STALE — the Lean tree is refactored after
 * banking (measured: 8/29 refs in eid_lingam, 4/17 in panel_ppml point at files that no
 * longer exist). Reading a missing file as `""` makes a RENAMED file indistinguishable
 * from a decl that genuinely has no standalone statement, which published a false
 * "No standalone Lean declaration." for 18 nodes that do have a `decl_name`. It also lets
 * `sorryFree("") === true` cast a spurious sorry-free vote into the verification badge.
 *
 * So: still never abort the bundle, but RECORD every miss so callers can report the real
 * cause and exclude a missing file from the sorry-free conjunction.
 */
function makeSrcReader(repoRoot: string, leanSubdir: string) {
  const sources = new Map<string, string>();
  const missing = new Set<string>();
  const readSrc = async (file: string): Promise<string> => {
    const p = join(repoRoot, leanSubdir, file);
    if (!sources.has(p)) {
      const text = await readFile(p, "utf8").catch(() => null);
      if (text === null) missing.add(file);
      sources.set(p, text ?? "");
    }
    return sources.get(p)!;
  };
  return { readSrc, missing };
}

// ComponentSpec moved to components.ts (shared by P3 verify + P4 emit); re-exported here for back-compat.
import type { ComponentSpec } from "./components.js";
export type { ComponentSpec };

const DISPLAY: Record<AnchoredEnv["env"], string> = {
  theoremv: "Theorem",
  assumptionv: "Assumption",
  lemmav: "Lemma",
  definitionv: "Definition",
  citedv: "Cited result",
  propositionv: "Proposition",
  remarkv: "Remark",
};

/** Paper numbering: per-environment-class counters in appearance order. */
export function paperLabels(envs: AnchoredEnv[]): Map<string, string> {
  const counters: Record<string, number> = {};
  const out = new Map<string, string>();
  for (const e of envs) {
    const d = DISPLAY[e.env];
    counters[d] = (counters[d] ?? 0) + 1;
    out.set(e.obj_id, `${d} ${counters[d]}`);
  }
  return out;
}

/** The mechanical join: paper envs ⨝ bank crosswalk ⨝ Lean source extraction. */
export async function buildBundle(args: {
  envs: AnchoredEnv[];
  crosswalk: CrosswalkEntry[];
  blocks: NoteBlock[];
  repoRoot: string;
  leanSubdir: string;
  commit: string;
  /** obj_id → mapped Lean pieces (for composite/multi-part objects). */
  components?: Record<string, ComponentSpec[]>;
  /** decl short-name → source location, for resolving component pieces that are
   *  not standalone crosswalk entries (the paper's full module index). `kind`
   *  (when present) restricts presentation-synthesized-definition matching to
   *  def-like declarations. */
  moduleDecls?: Map<string, { file: string; line: number; kind?: string }>;
  /** obj_id → causalsmith review status ("matched"/"derived"/"drift"/"unreviewed"), stamped onto
   *  each entry so the page reports the verified state honestly. Defaults to "unreviewed". */
  verdictByObj?: Map<string, { status: string }>;
}): Promise<{ crosswalk: PresentationCrosswalk; snippets: LeanSnippets; matchedSynthDecls: Set<string> }> {
  const byId = new Map(args.crosswalk.map((e) => [e.obj_id, e]));
  const blockById = new Map(args.blocks.map((b) => [b.obj_id, b]));
  const labels = paperLabels(args.envs);
  const entries: PresentationEntry[] = [];
  const snippets: Record<string, LeanSnippet> = {};
  const { readSrc, missing: missingSrc } = makeSrcReader(args.repoRoot, args.leanSubdir);
  // Resolve a component decl to its source location: crosswalk first, then the
  // paper's full module index, so a multi-part definition can reference any of
  // its Lean pieces without each piece being its own crosswalk entry.
  const resolve = (decl: string): { file: string; line: number } | null => {
    const c = args.crosswalk.find((x) => x.lean?.decl === decl);
    if (c?.lean) return { file: c.lean.file, line: c.lean.line };
    return args.moduleDecls?.get(decl) ?? null;
  };
  const matchedSynthDecls = new Set<string>();
  for (const e of args.envs) {
    const cw = byId.get(e.obj_id);
    if (!cw) {
      if (args.verdictByObj?.get(e.obj_id)?.status !== "presentation-synthesized") {
        throw new Error(`env ${e.obj_id} not in bank crosswalk`);
      }
      // A synthesized definition often already has a standalone Lean declaration in the run (the
      // notation loop synthesized it only because that decl was not `@realizes`-tagged). When the
      // definition's concept key matches a unique def-like decl EXACTLY, link and display it rather
      // than claiming "no standalone Lean declaration" — otherwise the same object appears twice
      // (unlinked printed definition + auxiliary Lean lemma).
      const hit = args.moduleDecls ? matchSynthDecl(e.title, e.obj_id, args.moduleDecls) : null;
      if (hit) {
        const src = await readSrc(hit.file);
        const snippet = tryExtractDeclSnippet(src, hit.decl, hit.line);
        if (snippet !== null) {
          matchedSynthDecls.add(hit.decl);
          snippets[e.obj_id] = {
            decl: hit.decl,
            file: hit.file,
            line: hit.line,
            statement: snippet,
            sorry_free: sorryFree(src),
            axioms: null,
          };
          entries.push({
            obj_id: e.obj_id,
            env: e.env,
            paper_label: labels.get(e.obj_id)!,
            title: e.title,
            lean: { file: hit.file, decl: hit.decl, decl_kind: hit.decl_kind, line: hit.line },
            fallback: null,
            uses: [],
            status: "matched",
            sorry_free: sorryFree(src),
          });
          continue;
        }
      }
      entries.push({
        obj_id: e.obj_id,
        env: e.env,
        paper_label: labels.get(e.obj_id)!,
        title: e.title,
        lean: null,
        fallback: "Presentation-only definition synthesized to make the verified notation self-contained; no standalone Lean declaration.",
        uses: [],
        status: "presentation-synthesized",
        sorry_free: null,
      });
      continue;
    }
    // Assemble any mapped Lean pieces (component decls / theorem hypothesis
    // binders) so a multi-part object shows all its real code, not just one decl.
    const specs = args.components?.[e.obj_id] ?? [];
    const parts: { label: string; statement: string }[] = [];
    let anyFile: { file: string; line: number } | null = null;
    let allSorryFree = true;
    for (const spec of specs) {
      const loc = resolve(spec.type === "decl" ? spec.decl : spec.theorem);
      if (!loc) continue;
      const src = await readSrc(loc.file);
      // A missing file yields "" and `sorryFree("") === true` — never let an unreadable
      // source cast a sorry-free vote into the verification badge.
      allSorryFree = allSorryFree && !missingSrc.has(loc.file) && sorryFree(src);
      anyFile = anyFile ?? { file: loc.file, line: loc.line };
      if (spec.type === "decl") {
        // A piece whose decl cannot be located here (promoted to another package and only
        // `export`ed, or moved) degrades to a placeholder — never aborts the bundle.
        const snippet = tryExtractDeclSnippet(src, spec.decl, loc.line);
        if (snippet === null) continue;
        parts.push({ label: spec.decl, statement: snippet });
      } else {
        const stmt = tryExtractDeclSnippet(src, spec.theorem, loc.line);
        if (stmt === null) continue;
        parts.push({
          label: `hypotheses of ${spec.theorem}`,
          statement: extractHypothesisBinders(stmt, spec.binders),
        });
      }
    }

    // A definition/assumption formalized by >1 Lean piece renders as a composite
    // (all pieces shown), even when it also carries a single primary decl — that
    // one decl alone would misrepresent a multi-part object. A single piece keeps
    // the standalone-decl view.
    let fallback: string | null = null;
    let entryLean = cw.lean;
    if (parts.length > 1 || (!cw.lean && parts.length === 1)) {
      snippets[e.obj_id] = {
        decl: "(composite)",
        file: anyFile!.file,
        line: anyFile!.line,
        statement: "",
        sorry_free: allSorryFree,
        axioms: null,
        components: parts,
      };
      entryLean = null; // no single representative decl (matches the lean:null convention)
      fallback = "Formalized by several Lean declarations; the pieces are shown below.";
    } else if (cw.lean) {
      const src = await readSrc(cw.lean.file);
      const snippet = tryExtractDeclSnippet(src, cw.lean.decl, cw.lean.line);
      if (snippet === null) {
        // Distinguish the two reasons the decl wasn't found. A STALE recorded path is a
        // bank/tree-refactor defect, not a statement about formalization — never report it
        // with the re-export wording, which reads as an intentional, benign situation.
        fallback = missingSrc.has(cw.lean.file)
          ? `Lean source file \`${cw.lean.file}\` was not found at the recorded path (the path is stale); declaration \`${cw.lean.decl}\` could not be displayed.`
          : `Lean declaration \`${cw.lean.decl}\` is re-exported here from another module; see the source file.`;
        entryLean = null;
      } else {
        snippets[e.obj_id] = {
          decl: cw.lean.decl,
          file: cw.lean.file,
          line: cw.lean.line,
          statement: snippet,
          sorry_free: sorryFree(src),
          axioms: null, // axiom audit deferred (v1); site badge reflects the sorry scan only
        };
      }
    } else {
      const b = blockById.get(e.obj_id);
      fallback = b
        ? `No standalone Lean declaration; the content of “${b.title}” enters Lean through the theorem hypotheses.`
        : "No standalone Lean declaration.";
    }
    const hypField = blockById.get(e.obj_id)?.fields["Load-bearing hypotheses"] ?? "";
    const envIds = new Set(args.envs.map((x) => x.obj_id));
    const uses =
      e.env === "theoremv"
        ? [...new Set([...hypField.matchAll(/\bP-\w+/g)].map((m) => m[0]))].filter((id) => envIds.has(id))
        : [];
    entries.push({
      obj_id: e.obj_id,
      env: e.env,
      paper_label: labels.get(e.obj_id)!,
      title: e.title,
      lean: entryLean,
      fallback,
      uses,
      status: args.verdictByObj?.get(e.obj_id)?.status ?? "unreviewed",
      sorry_free: snippets[e.obj_id]?.sorry_free ?? null,
    });
  }
  return {
    crosswalk: { commit: args.commit, lean_subdir: args.leanSubdir, entries },
    snippets: { commit: args.commit, snippets },
    matchedSynthDecls,
  };
}

const KIND_DISPLAY: Record<string, string> = {
  setup: "Setup",
  definition: "Definition",
  assumption: "Assumption",
  lemma: "Lemma",
  theorem: "Theorem",
  gate: "Object",
};

const FORMAL_LAYER_KIND_ORDER = ["setup", "definition", "assumption", "lemma", "theorem"] as const;

/**
 * The web-only "Formal layer" panel data, derived deterministically from the graph (no LLM):
 * every from-note object grouped by kind, with its verified NL, Lean anchor (from the crosswalk),
 * review status, and sorry-free flag (from the graph's proof state). Complete by construction —
 * the backstop that guarantees every object is reachable even if an inline \leanref is missed.
 */
export function buildFormalLayer(
  graph: FormalizationGraph,
  crosswalk: CrosswalkEntry[],
  commit: string,
  /** Current P1 statement-equivalence verdicts. These supersede stale graph review stamps. */
  equivalenceStatus?: Map<string, string>,
  /** Lean decls now homed by a matched presentation-synthesized definition — dropped from the
   *  auxiliary group so the object is not listed twice (once as the printed definition, once as an
   *  auxiliary lemma). */
  excludeAuxDecls?: ReadonlySet<string>,
): FormalLayer {
  const leanByObj = new Map(crosswalk.map((c) => [c.obj_id, c.lean]));
  const items = graph.nodes
    .filter((n) => n.provenance === "from-note" && !isUndeliveredNode(n) && FORMAL_LAYER_KIND_ORDER.includes(n.kind as never))
    .map((n) => {
      // Join key = NODE id (matches the crosswalk + the paper's data-objid so the panel row opens
      // the drawer); the alias is shown only as the human-facing label.
      const objId = n.id;
      const sorry_free =
        n.proof.state === "complete" ? true : n.proof.state === "sorry" ? false : null;
      return {
        obj_id: objId,
        kind: n.kind,
        label: `${KIND_DISPLAY[n.kind] ?? "Object"} ${n.obj_id ?? n.id}`,
        nl: n.nl?.statement ?? "",
        lean: leanByObj.get(objId) ?? null,
        status: equivalenceStatus?.get(objId) ?? n.review.status,
        sorry_free,
      };
    });
  const groups: FormalLayer["groups"] = FORMAL_LAYER_KIND_ORDER.map((kind) => ({
    kind,
    items: items.filter((i) => i.kind === kind),
  })).filter((g) => g.items.length > 0);

  // Cited group: from-note imported external results (`gate_class:"cited"`). They are intentionally
  // absent from the numbered paper environments; consumer-local scope footnotes carry the journal
  // disclosure. The web Formal-layer panel still lists each exact imported proposition so the
  // source-matched Lean dependency remains inspectable. `nl` is the verified comparator statement;
  // the Lean anchor is the assumed `def`.
  const citedItems = graph.nodes
    .filter((n) => n.provenance === "from-note" && !isUndeliveredNode(n) && isCitedNode(n))
    .map((n) => ({
      obj_id: n.id,
      kind: "cited",
      label: `Cited result ${n.obj_id ?? n.id}`,
      nl: n.nl?.statement ?? "",
      lean: leanByObj.get(n.id) ?? null,
      status: n.review.status,
      sorry_free: n.proof.state === "complete" ? true : n.proof.state === "sorry" ? false : null,
    }));
  if (citedItems.length > 0) groups.push({ kind: "cited", items: citedItems });

  // An undelivered object remains visible, but only as a remark: no Lean anchor,
  // no sorry badge, and no implication that its statement was proved here.
  const undeliveredItems = graph.nodes
    .filter((n) => n.provenance === "from-note" && isUndeliveredNode(n))
    .map((n) => ({
      obj_id: n.id,
      kind: "remark",
      label: `Remark ${n.obj_id ?? n.id}`,
      nl: n.nl?.statement ?? "",
      lean: null,
      status: "undelivered",
      sorry_free: null,
    }));
  if (undeliveredItems.length > 0) groups.push({ kind: "remark", items: undeliveredItems });

  // Auxiliary group: agent-introduced proof helpers (web-only, Lean statement only — nl left
  // blank). Appended last and rendered collapsed; completes the interactive audit trail.
  const auxItems = auxiliaryNodes(graph)
    .filter((n) => !(n.lean.decl_name && excludeAuxDecls?.has(n.lean.decl_name)))
    .map((n) => {
    const objId = n.id;
    return {
      obj_id: objId,
      kind: n.kind,
      label: `${KIND_DISPLAY[n.kind] ?? "Lemma"} ${n.lean.decl_name ?? objId}`,
      nl: "",
      lean: leanByObj.get(objId) ?? null,
      status: n.review.status,
      sorry_free: n.proof.state === "complete" ? true : n.proof.state === "sorry" ? false : null,
    };
  });
  if (auxItems.length > 0) groups.push({ kind: "auxiliary", items: auxItems });
  return { commit, groups };
}

/** True iff `name` is an arm-indexed symbol (`<base>_0` / `<base>_1`); returns its base else null. */
function armBaseOf(name: string): string | null {
  return name.endsWith("_0") || name.endsWith("_1") ? name.slice(0, -2) : null;
}

/**
 * Add a synthesized generic `<base>_a` cluster for every arm-indexed pair `<base>_0`/`<base>_1`
 * (e.g. `mu_a` ← `mu_0` ∪ `mu_1`), so the paper's generic notation `μ_a(x)` has its own realization
 * object — and so the prose can link the generic once instead of linking each arm. Originals kept.
 */
export function withArmGenerics(clusters: SymbolCluster[]): SymbolCluster[] {
  const byName = new Map(clusters.map((c) => [c.symbol, c] as const));
  const out = [...clusters];
  const added = new Set<string>();
  for (const c of clusters) {
    const base = armBaseOf(c.symbol);
    if (!base || added.has(`${base}_a`)) continue;
    if (byName.has(`${base}_0`) && byName.has(`${base}_1`)) {
      added.add(`${base}_a`);
      out.push({
        symbol: `${base}_a`,
        space: byName.get(`${base}_0`)!.space,
        members: [...byName.get(`${base}_0`)!.members, ...byName.get(`${base}_1`)!.members],
      });
    }
  }
  return out;
}

/** True iff this symbol is an arm whose generic was synthesized (so the prose links the generic). */
function isMergedArm(name: string, withGenerics: SymbolCluster[]): boolean {
  const base = armBaseOf(name);
  return base != null && withGenerics.some((c) => c.symbol === `${base}_a`);
}

/**
 * Undo a model's JSON over-escaping of LaTeX backslashes. A codex refiner that emits a body inside a
 * JSON string sometimes doubles backslashes (`\(` → `\\(`, `\mathrm` → `\\mathrm`); `JSON.parse`
 * preserves that, yielding a body that fails to compile ("Missing $ inserted" → emergency stop).
 * `\\(`/`\\)` never occur in valid LaTeX, so their presence is a reliable over-escape signal — when
 * seen, collapse every `\\` that precedes a non-space, non-digit char back to a single `\`. No-op on a
 * correctly-escaped body (the common case), so it is safe to wrap every refiner output.
 */
export function fixOverEscapedTex(s: string): string {
  if (!/\\\\[()]/.test(s)) return s; // no doubled inline-math delimiter → not over-escaped
  return s.replace(/\\\\(?=[^\s\d])/g, "\\");
}

/** Read one TeX braced argument, including nested groups and literal escaped braces. */
function readBalancedBraceGroup(tex: string, open: number): { content: string; end: number } | null {
  if (tex[open] !== "{") return null;
  let depth = 1;
  for (let i = open + 1; i < tex.length; i++) {
    // `\{` and `\}` are literal glyphs, not TeX grouping delimiters.  Skipping every escaped
    // character also handles escaped backslashes without treating their following brace specially.
    if (tex[i] === "\\") {
      i++;
      continue;
    }
    if (tex[i] === "{") depth++;
    else if (tex[i] === "}" && --depth === 0) return { content: tex.slice(open + 1, i), end: i + 1 };
  }
  return null;
}

/**
 * Make every symbol `\leanref{sym:…}{…}` math-mode-safe. The draft writes a symbol's display as
 * inline math — sometimes `$x$`, sometimes bare `x` — and may nest it inside a `\(…\)` display, where
 * a literal `$` is illegal TeX ("Missing $ inserted" → emergency stop at \end{document}). Rewriting the
 * display as `\ensuremath{x}` typesets as math in text AND is a no-op inside `\(…\)`, so the link is safe
 * in either context. Object links `\leanref{<obj>}{<phrase>}` (text display) are left untouched.
 */
export function normalizeSymbolLeanrefs(tex: string): string {
  const OPEN = "\\leanref{sym:";
  let out = "";
  let i = 0;
  for (;;) {
    const idx = tex.indexOf(OPEN, i);
    if (idx < 0) {
      out += tex.slice(i);
      break;
    }
    out += tex.slice(i, idx);
    const idGroup = readBalancedBraceGroup(tex, idx + "\\leanref".length);
    if (!idGroup) {
      out += tex.slice(idx); // malformed — pass through
      break;
    }
    const dispGroup = readBalancedBraceGroup(tex, idGroup.end);
    if (!dispGroup) {
      out += tex.slice(idx, idGroup.end); // malformed — pass through
      i = idGroup.end;
      continue;
    }
    const id = idGroup.content;
    const disp = dispGroup.content.trim();
    // Strip any existing math wrapper down to the bare math, then \ensuremath-wrap it.
    const m =
      disp.match(/^\\ensuremath\{([\s\S]*)\}$/) ?? disp.match(/^\$([\s\S]+)\$$/) ?? disp.match(/^\\\(([\s\S]*?)\\\)$/);
    const math = m ? m[1] : disp;
    out += `\\leanref{${id}}{\\ensuremath{${math}}}`;
    i = dispGroup.end;
  }
  return out;
}

/**
 * Repair stale symbol links emitted by the pre-balanced `@realizes` parser.  That parser split TeX
 * subscripts at commas and sometimes left the first `\leanref` argument unclosed, e.g.
 * `\leanref{sym:kappa_{r}{$...$}`.  A current run has the authoritative realized names from Lean;
 * when exactly one name extends the stale prefix, upgrade the target mechanically.  Ambiguous links
 * are deliberately preserved so P4's dead-link check remains loud.
 */
export function repairSymbolLeanrefTargets(tex: string, symbolNames: string[]): string {
  const exact = new Set(symbolNames);
  const resolve = (name: string): string | null => {
    if (exact.has(name)) return name;
    const prefixes = [name, ...(name.endsWith("}") ? [name.slice(0, -1)] : [])];
    const candidates = symbolNames.filter((candidate) => prefixes.some((prefix) => candidate.startsWith(prefix)));
    return candidates.length === 1 ? candidates[0] : null;
  };

  // First close legacy malformed arg1s.  The display starts at `{$`, `{\ensuremath`, or `{\(`;
  // before it, the stale partial name is an unambiguous prefix of the Lean-realized name.
  let legacyOut = "";
  let i = 0;
  const mark = "\\leanref{sym:";
  for (;;) {
    const idx = tex.indexOf(mark, i);
    if (idx < 0) {
      legacyOut += tex.slice(i);
      break;
    }
    legacyOut += tex.slice(i, idx);
    const nameStart = idx + mark.length;
    const display = ["{$", "{\\ensuremath", "{\\("]
      .map((needle) => ({ pos: tex.indexOf(needle, nameStart), needle }))
      .filter((x) => x.pos >= 0)
      .sort((a, b) => a.pos - b.pos)[0];
    if (!display) {
      legacyOut += tex.slice(idx);
      break;
    }
    const raw = tex.slice(nameStart, display.pos);
    const replacement = resolve(raw);
    // `\leanref{` has already opened arg1: its raw suffix must therefore contain one MORE closing
    // brace than opening brace when it is valid.  A nonnegative balance is the legacy unclosed form.
    const braceBalance = [...raw].reduce((n, ch) => n + (ch === "{" ? 1 : ch === "}" ? -1 : 0), 0);
    if (replacement && braceBalance >= 0) {
      legacyOut += `${mark}${replacement}}`;
      i = display.pos;
    } else {
      legacyOut += tex.slice(idx, display.pos + 1);
      i = display.pos + 1;
    }
  }

  let out = "";
  i = 0;
  for (;;) {
    const idx = legacyOut.indexOf(mark, i);
    if (idx < 0) {
      out += legacyOut.slice(i);
      break;
    }
    out += legacyOut.slice(i, idx);
    const idGroup = readBalancedBraceGroup(legacyOut, idx + "\\leanref".length);
    const dispGroup = idGroup ? readBalancedBraceGroup(legacyOut, idGroup.end) : null;
    if (!idGroup || !dispGroup) {
      out += legacyOut.slice(idx);
      break;
    }
    const name = idGroup.content.slice("sym:".length);
    const replacement = resolve(name);
    out += replacement ? `\\leanref{sym:${replacement}}{${dispGroup.content}}` : legacyOut.slice(idx, dispGroup.end);
    i = dispGroup.end;
  }
  return out;
}

/**
 * Promote a symbol `\leanref` that LEADS a `\(…\)` display to a standalone link, re-wrapping only the
 * remainder. The draft often writes a symbol's first mention as `\(\leanref{sym:x}{…}\)` (the symbol IS
 * the whole display) or `\(\leanref{sym:x}{…}=…\)` (symbol then its defining equation). Nested inside the
 * `\(…\)`, the link is NOT clickable on the web (it is stripped to bare math) and is plain text in the
 * PDF. Pulling the leading leanref out — its display is `\ensuremath{…}`, which typesets as math in text
 * mode — makes the symbol itself clickable, while any remaining equation stays in its own `\(…\)`. Only
 * the LEADING position is promoted; a link mid-equation cannot be split cleanly, so it is left for the
 * web-side unwrap. Idempotent (a leanref already outside `\(…\)` is untouched); run AFTER
 * `normalizeSymbolLeanrefs` so the display is already `\ensuremath`.
 */
export function promoteSymbolLeanrefs(tex: string): string {
  const SYM = "\\leanref{sym:";
  let out = "";
  let i = 0;
  for (;;) {
    const open = tex.indexOf("\\(", i);
    if (open < 0) {
      out += tex.slice(i);
      break;
    }
    const close = tex.indexOf("\\)", open + 2); // \(…\) cannot nest → first \) closes it
    if (close < 0) {
      out += tex.slice(i);
      break;
    }
    const inner = tex.slice(open + 2, close);
    const afterLead = inner.replace(/^\s*/, "");
    if (afterLead.startsWith(SYM)) {
      // Both arguments can contain nested TeX groups (e.g. `sym:kappa_{r}`).
      const idGroup = readBalancedBraceGroup(afterLead, "\\leanref".length);
      const dispGroup = idGroup ? readBalancedBraceGroup(afterLead, idGroup.end) : null;
      if (dispGroup) {
        const refText = afterLead.slice(0, dispGroup.end);
        const rest = afterLead.slice(dispGroup.end).replace(/^\s+/, "");
        out += tex.slice(i, open) + refText + (rest.trim() !== "" ? `\\(${rest}\\)` : "");
        i = close + 2;
        continue;
      }
    }
    out += tex.slice(i, close + 2); // this \(…\) has no leading symbol link → leave untouched
    i = close + 2;
  }
  return out;
}

/**
 * The symbols the DRAFT (P2) should link inline in the prose via `\leanref{sym:<name>}{<notation>}`:
 * every realized symbol EXCEPT the arms whose generic was synthesized (link the generic `μ_a`, not
 * `μ_0`/`μ_1` separately). Each target carries a short description (the joined `@realizes` hints) so
 * the drafter can recognise which notation it is wrapping. No file reads — derived from the tags.
 */
export function symbolProseTargets(
  clusters: SymbolCluster[],
): { objId: string; name: string; description: string }[] {
  const all = withArmGenerics(clusters);
  return all
    .filter((c) => c.members.length > 0 && !isMergedArm(c.symbol, all))
    .map((c) => {
      const hints = [...new Set(c.members.map((m) => m.hint).filter((h): h is string => !!h))];
      const decls = [...new Set(c.members.map((m) => m.decl))].join(", ");
      return {
        objId: `sym:${c.symbol}`,
        name: c.symbol,
        description: hints.length > 0 ? hints.join("; ") : `realized by ${decls}`,
      };
    });
}

/**
 * Build drawer entries + composite snippets + Formal-layer items for the Lean `@realizes` symbol
 * clusters (e.g. `μ_a`, `e_P`, `τ_P`): each core symbol is realized by the CONJUNCTION of several
 * Lean declarations (a carrier-type field plus the predicates that pin its range/semantics), so it
 * is shown as a composite whose components are those realizing decls — every `@realizes` tag in the
 * Lean thus appears on the website. A symbol carries no body block (env "symbol", `lean: null`);
 * the site exempts it from the data-objid integrity check, exactly like an auxiliary lemma.
 * Members are deduped by decl (one component per decl, joining the per-clause `@realizes` hints).
 */
export async function buildSymbolRealizations(args: {
  clusters: SymbolCluster[];
  repoRoot: string;
  leanSubdir: string;
}): Promise<{
  entries: PresentationEntry[];
  snippets: Record<string, LeanSnippet>;
  items: FormalLayerItem[];
}> {
  const entries: PresentationEntry[] = [];
  const snippets: Record<string, LeanSnippet> = {};
  const items: FormalLayerItem[] = [];
  const { readSrc, missing: missingSrc } = makeSrcReader(args.repoRoot, args.leanSubdir);
  const clusters = withArmGenerics(args.clusters);

  for (const c of clusters) {
    if (c.members.length === 0) continue; // symbol with no `@realizes` tag — nothing to show
    const objId = `sym:${c.symbol}`;
    // Dedup by decl: a symbol may be tagged on several CLAUSES of the same decl (e.g. `e_P` on two
    // WellFormedLaw clauses) — one component per distinct decl, joining their clause hints.
    const byDecl = new Map<string, { decl: string; file: string; line: number; hints: string[] }>();
    for (const m of c.members) {
      const g = byDecl.get(m.decl) ?? { decl: m.decl, file: m.file, line: m.line, hints: [] };
      if (m.hint) g.hints.push(m.hint);
      byDecl.set(m.decl, g);
    }
    const parts: { label: string; statement: string }[] = [];
    let allSorryFree = true;
    let anyFile: { file: string; line: number } | null = null;
    for (const g of byDecl.values()) {
      const src = await readSrc(g.file);
      // Missing file ⇒ "" ⇒ sorryFree("")===true; exclude it from the badge conjunction.
      allSorryFree = allSorryFree && !missingSrc.has(g.file) && sorryFree(src);
      anyFile = anyFile ?? { file: g.file, line: g.line };
      const label = g.hints.length > 0 ? `${g.decl} — ${g.hints.join("; ")}` : g.decl;
      const snippet = tryExtractDeclSnippet(src, g.decl, g.line);
      if (snippet === null) continue; // promoted/re-exported decl — skip this piece, don't abort
      parts.push({ label, statement: snippet });
    }
    snippets[objId] = {
      decl: "(symbol)",
      file: anyFile!.file,
      line: anyFile!.line,
      statement: "",
      sorry_free: allSorryFree,
      axioms: null,
      components: parts,
    };
    const declList = [...byDecl.keys()].join(", ");
    entries.push({
      obj_id: objId,
      env: "symbol",
      paper_label: c.symbol,
      title: c.space ?? null,
      lean: null,
      fallback: `Realized in Lean by ${byDecl.size} declaration${byDecl.size === 1 ? "" : "s"} (${declList}); the pieces are shown below.`,
      uses: [],
      status: "matched",
      sorry_free: allSorryFree,
    });
    items.push({
      obj_id: objId,
      kind: "symbol",
      label: c.symbol,
      nl: c.space ? `${c.space} — realized by ${declList}` : `realized by ${declList}`,
      lean: null,
      status: "matched",
      sorry_free: allSorryFree,
    });
  }
  return { entries, snippets, items };
}

/**
 * Build drawer entries + snippets for from-note objects presented ONLY in prose — referenced by
 * an inline `\leanref`, not rendered as a formal block. The Lean piece set comes from the graph
 * (own decl + statement-uses neighbours); the source text is extracted at those anchors. Each
 * entry carries the node's verified `status`, so the drawer opens it exactly like a formal block.
 * `citedv` marks a source-matched external dependency that is intentionally web-only; nodes with
 * no Lean decl get an NL-only fallback (honest).
 */
export async function buildProseEntries(args: {
  objIds: string[];
  graph: FormalizationGraph;
  crosswalk: CrosswalkEntry[];
  repoRoot: string;
  leanSubdir: string;
  moduleDecls?: Map<string, { file: string; line: number }>;
  /** Entry env tag — "prose" (default, a from-note object linked inline), "auxiliary" (an
   *  agent-introduced proof helper surfaced web-only), or "citedv" (a source-matched external
   *  dependency surfaced web-only). All are drawer-openable. */
  env?: "prose" | "auxiliary" | "citedv";
}): Promise<{ entries: PresentationEntry[]; snippets: Record<string, LeanSnippet> }> {
  const entryEnv = args.env ?? "prose";
  const byKey = new Map<string, GraphNode>();
  for (const n of args.graph.nodes) {
    byKey.set(n.id, n);
    if (n.obj_id) byKey.set(n.obj_id, n);
  }
  const { readSrc, missing: missingSrc } = makeSrcReader(args.repoRoot, args.leanSubdir);
  const resolve = (decl: string): { file: string; line: number } | null => {
    const c = args.crosswalk.find((x) => x.lean?.decl === decl);
    if (c?.lean) return { file: c.lean.file, line: c.lean.line };
    return args.moduleDecls?.get(decl) ?? null;
  };
  const entries: PresentationEntry[] = [];
  const snippets: Record<string, LeanSnippet> = {};
  for (const objId of [...new Set(args.objIds)]) {
    const node = byKey.get(objId);
    if (!node) continue; // unknown ids are caught by P4 validation, not here
    const label = `${KIND_DISPLAY[node.kind] ?? "Object"} ${node.obj_id ?? node.id}`;
    const decls = graphComponentSpecs(args.graph, objId)
      .filter((s) => s.type === "decl")
      .map((s) => (s as { type: "decl"; decl: string }).decl);
    let lean: PresentationEntry["lean"] = null;
    let fallback: string | null = null;
    if (decls.length === 1) {
      const loc = resolve(decls[0]);
      const src = loc ? await readSrc(loc.file) : null;
      const snippet = loc && src !== null ? tryExtractDeclSnippet(src, decls[0], loc.line) : null;
      if (loc && src !== null && snippet !== null) {
        snippets[objId] = {
          decl: decls[0],
          file: loc.file,
          line: loc.line,
          statement: snippet,
          sorry_free: sorryFree(src),
          axioms: null,
        };
        lean = {
          file: loc.file,
          decl: decls[0],
          decl_kind: node.kind === "theorem" || node.kind === "lemma" ? node.kind : "def",
          line: loc.line,
        };
      }
    } else if (decls.length > 1) {
      const parts: { label: string; statement: string }[] = [];
      let anyFile: { file: string; line: number } | null = null;
      let allSorryFree = true;
      for (const decl of decls) {
        const loc = resolve(decl);
        if (!loc) continue;
        const src = await readSrc(loc.file);
        const snippet = tryExtractDeclSnippet(src, decl, loc.line);
        if (snippet === null) continue; // promoted/re-exported decl — skip this piece
        allSorryFree = allSorryFree && sorryFree(src);
        anyFile = anyFile ?? loc;
        parts.push({ label: decl, statement: snippet });
      }
      if (parts.length > 0) {
        snippets[objId] = {
          decl: "(composite)",
          file: anyFile!.file,
          line: anyFile!.line,
          statement: "",
          sorry_free: allSorryFree,
          axioms: null,
          components: parts,
        };
        fallback = "Formalized by several Lean declarations; the pieces are shown below.";
      }
    }
    if (!lean && !snippets[objId]) {
      // Do NOT claim "no standalone Lean declaration" when the node HAS decls whose
      // recorded source files are simply missing — that publishes a false statement
      // about the formalization. Report the stale path instead.
      const staleFiles = [...new Set(
        decls.map((d) => resolve(d)?.file).filter((f): f is string => !!f && missingSrc.has(f)),
      )];
      fallback =
        fallback ??
        (staleFiles.length > 0
          ? `Lean source not found at the recorded path(s) ${staleFiles.map((f) => `\`${f}\``).join(", ")} (the paths are stale); declaration(s) ${decls.map((d) => `\`${d}\``).join(", ")} could not be displayed.`
          : "No standalone Lean declaration.");
    }
    entries.push({
      obj_id: objId,
      env: entryEnv,
      paper_label: label,
      title: null,
      lean,
      fallback,
      uses: [],
      status: node.review.status,
      sorry_free: snippets[objId]?.sorry_free ?? null,
    });
  }
  return { entries, snippets };
}

/**
 * Referee-facing assumption-faithfulness table plus the totality check: no
 * Lean hypothesis of a presented theorem may be silently dropped (the paper
 * must not weaken assumptions), and every referenced P-object must be an
 * environment in the paper.
 */
export function assumptionTable(
  blocks: NoteBlock[],
  envs: AnchoredEnv[],
  snippets: Record<string, LeanSnippet>,
): { md: string; problems: string[] } {
  const envIds = new Set(envs.map((e) => e.obj_id));
  // Objects presented in the paper: the frozen formal environments PLUS the
  // note's definitional blocks (P-blocks with no Lean anchor are not frozen
  // envs but ARE presented in the setup prose / notation table). A hypothesis
  // may reference either; only a ref to neither is a genuine dangling pointer.
  const presentedIds = new Set([...envIds, ...blocks.map((b) => b.obj_id)]);
  const labels = paperLabels(envs);
  const problems: string[] = [];
  const rows: string[] = [
    "| Theorem | Hypothesis | Source objects | Status |",
    "|---|---|---|---|",
  ];
  for (const t of envs.filter((e) => e.env === "theoremv")) {
    const block = blocks.find((b) => b.obj_id === t.obj_id);
    const hypField = block?.fields["Load-bearing hypotheses"] ?? "";
    // Hypotheses are listed one per line as either the legacy bold form
    // `**H1 (…)** text` or the current causalsmith form `- H1 (…): text` (plain,
    // optionally bulleted). Match an `H<n>` label at the start of each line
    // (after any `-`, `>`, `*`/`**` decoration) and take the remainder as text.
    const hyps = hypField
      .split("\n")
      .map((line) => line.match(/^[\s>*-]*\s*(H\d+)\b\.?\s*\*{0,2}\s*:?\s*(.*)$/))
      .filter((m): m is RegExpMatchArray => m !== null)
      .map((m) => ({ label: m[1].trim(), text: m[2].trim() }));
    // Fallback for the shared-assumption-lattice note format (no per-theorem `Load-bearing
    // hypotheses` field): the theorem references its standing assumptions inline as `ass:<id>` in the
    // note body/Statement, resolved to the global `A-` assumption blocks/envs. Derive the hypothesis
    // rows from those refs so the totality gate reflects the assumptions that ARE documented, rather
    // than demanding a per-theorem `H1/H2` field this note convention never emits.
    if (hyps.length === 0) {
      // Search the note block (body + fields, where standing assumptions appear bare as
      // `ass:bounded-outcome`) AND the frozen paper env body (where they appear as
      // `\ref{obj:ass:margin-window}` — `\bass:` matches inside the `obj:` prefix). A headline
      // lower-bound theorem documents its hypotheses in the paper env (`Under Assumption~\ref{…}`,
      // plus law-class membership) even when its symbolic note Statement carries no ref.
      // Structured note bodies duplicate every `**Field.** value`, including explicit drift-watch
      // fields such as "Hypothesis dropped ...". Scanning that raw body resurrects a deliberately
      // removed assumption as a live reference. Prefer the structured fields when present and omit
      // fields whose heading marks dropped/non-load-bearing material; retain the raw-body fallback
      // only for older unstructured note blocks.
      const fields = Object.entries(block?.fields ?? {});
      const liveNoteText = fields.length > 0
        ? fields
            .filter(([name]) => !/(?:hypothesis\s+dropped|non[- ]load[- ]bearing|drift[- ]watch)/i.test(name))
            .map(([, value]) => value)
            .join(" ")
        : (block?.body ?? "");
      const searchText = `${liveNoteText} ${t.body}`;
      for (const ref of [...new Set([...searchText.matchAll(/\bass:[\w-]+/g)].map((m) => m[0]))]) {
        hyps.push({ label: ref, text: ref });
      }
    }
    if (hyps.length === 0) {
      // Theorems that present their hypotheses as an itemized `\textbf{(Name.)} …`
      // list in the frozen env body, with class-membership expressed via
      // `\ref{obj:def:…}` (e.g. `p∈S_{k,q}`, `P∈\mathcal P_\beta`) rather than a
      // bare `ass:` ref, carry no `ass:`-token the scan above can find — yet these
      // ARE the theorem's load-bearing hypotheses. Extract each labelled item.
      for (const m of t.body.matchAll(
        /\\item\s+\\textbf\{\(([^)]+?)\.?\)\}\s*([\s\S]*?)(?=\\item|\\end\{itemize\}|$)/g,
      )) {
        hyps.push({ label: m[1].trim(), text: m[2].replace(/\s+/g, " ").trim() });
      }
    }
    // every H-binder in the Lean statement must appear in the note's hypothesis list.
    // A COMPOSITE theorem carries `statement: ""` (its content lives in the part
    // decls), so scan the component statements instead — otherwise the totality
    // check silently exempts every composite theorem.
    const snip = snippets[t.obj_id];
    const stmt =
      snip?.statement && snip.statement.trim().length > 0
        ? snip.statement
        : (snip?.components ?? []).map((c) => c.statement).join("\n");
    const leanHypNames = [...stmt.matchAll(/[(\{]\s*(H\d+)\b/g)].map((m) => m[1]);
    if (hyps.length === 0) {
      if (!snip || leanHypNames.length > 0) {
        problems.push(`${t.obj_id}: no load-bearing hypotheses found in the note`);
      } else {
        // A current Lean snippet with no conventionally named H-binders is evidence that the
        // theorem is hypothesis-free at the assumption-table layer. Parameters and explicit side
        // conditions such as `(m) (hm : 3 ≤ m)` remain visible in the frozen theorem statement;
        // inventing an H-row would falsely turn them into external assumptions.
        rows.push(
          `| ${labels.get(t.obj_id)} (${t.obj_id}) | — | — | ${envIds.has(t.obj_id) ? "presented" : "missing"} |`,
        );
      }
    }
    const noteHypNames = new Set(hyps.map((h) => h.label.match(/^H\d+/)?.[0] ?? h.label));
    for (const name of leanHypNames) {
      if (!noteHypNames.has(name)) {
        problems.push(`${t.obj_id}: Lean hypothesis ${name} missing from the assumption table`);
      }
    }
    for (const h of hyps) {
      const refs = [...new Set([...h.text.matchAll(/\b(?:P-\w+|ass:[\w-]+)/g)].map((m) => m[0]))];
      for (const r of refs) {
        if (!presentedIds.has(r)) problems.push(`${t.obj_id}/${h.label}: references ${r} which is not presented in the paper`);
      }
      const refLabels = refs.map((r) => (envIds.has(r) ? `${labels.get(r)} (${r})` : r)).join(", ");
      rows.push(
        `| ${labels.get(t.obj_id)} (${t.obj_id}) | ${h.label} | ${refLabels || "—"} | ${envIds.has(t.obj_id) ? "presented" : "missing"} |`,
      );
    }
  }
  const md = [
    "# Assumption-faithfulness table",
    "",
    "Machine-generated map from each presented theorem's Lean hypotheses to the paper's assumption environments. Lean is ground truth; this table is the referee-facing check that the paper neither strengthens nor weakens the verified statement.",
    "",
    ...rows,
    "",
  ].join("\n");
  return { md, problems };
}
