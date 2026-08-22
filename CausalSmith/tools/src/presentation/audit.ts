import { readFile, writeFile, appendFile, mkdir } from "node:fs/promises";

import { join } from "node:path";
import type { StageIO } from "./pipeline.js";
import { PRESENTATION_PROSE_POLICY_VERSION, presentationPrompt, promptFingerprint } from "./prompt_io.js";
import { notationForArtifact, parseOutline } from "./stage_util.js";
import { canonicalizeProofTitle, hashEnvBody, normalizeCrefs, type AnchoredEnv, type LintProblem } from "./tex_anchors.js";
import { fixOverEscapedTex } from "./emit.js";
import { FormalLayerSource, blocksToTex } from "./formal_layer.js";
import { bankAcceptedDir } from "./paths.js";
import { saveGraph, graphPath } from "../graph/store.js";
import { extractDeclSnippet, extractFullDeclSource } from "./lean_extract.js";
import { parseLeanDecls } from "../formalization/crosswalk.js";
import { ensureComponentsForEnvs, assembleComponentText, componentSignature } from "./components.js";
import { parseNoteBlocks } from "./note_parser.js";
import { writeJsonAtomic } from "./json_io.js";
import { loadJsonCache } from "./cache.js";
import { loadInformalDerivations } from "./bank.js";
import { resolveLeanDeclaration, resolvedLeanAbsolutePath } from "./declaration_resolver.js";
export { resolveLeanDeclaration } from "./declaration_resolver.js";
import {
  refineStatement,
  parseJsonLoose,
  mapLimit,
  type StatementCheck,
  type RefineRunner,
} from "./gates.js";

/**
 * Per-artifact Lean-equivalence audits, co-located with the stage that PRODUCES the artifact
 * (design: "the review of a produced artifact belongs directly after that stage"):
 *   • `runStatementAudit` runs at P1 — the moment the frozen statements are rendered — and reconciles
 *     each paper env body against its Lean declaration, refining drift toward Lean and persisting the
 *     validated body back onto the graph (`nl.frozen_body`) and the formal layer.
 *   • `runProofAudit` runs at P2 — the moment the appendix proofs are rendered — and reconciles each
 *     proof's prose against its machine-verified Lean proof.
 * P3 keeps only the WHOLE-PAPER gates (overclaim, citation support, anchor lint, rubric). Both audits
 * are built on the pure, unit-tested `refineStatement` kernel from gates.ts.
 */

const MAX_ROUNDS = 2;
/** Max concurrent codex audits. Each statement/proof is checked against its OWN Lean decl, so the
 *  audits (and the pure refine loops) are independent and run concurrently. */
const AUDIT_CONCURRENCY = 6;

/** Claims about algorithms, computability, or complexity are especially easy for a
 * batched reviewer to credit to a nearby sibling theorem instead of the declaration
 * actually mapped to the paper environment. Give those statements an individual,
 * source-reading audit so declaration-local support remains the criterion. */
export function requiresIndividualStatementAudit(body: string): boolean {
  return /\b(?:comput(?:able|ability|ation)|algorithm(?:ic)?|complexity|operation(?:-count|s)?|running\s+time|runtime)\b|O\s*\(/i.test(body);
}

/** Content key for one statement's equivalence verdict. One definition for BOTH the pre-audit
 *  lookup and the post-refinement stamp — the two used to be hand-written 137 lines apart.
 *  why: Lean edits, trust-boundary edits, or a verdict-POLICY change (v2 = over-assumption is
 *  drift) must invalidate verdicts; citation-erasure-v1 covers the cited-dependency prompt. */
export function equivalenceAuditKey(parts: {
  envBody: string; mapping: string; leanStatement: string; refDefs: string; citedDependencies: string;
}): string {
  // (2026-08-21, no bump) IMPLEMENTATION PACKAGING clause added to both equivalence prompts:
  // it only widens FAITHFUL, and the cache short-circuits faithful verdicts only, so replay
  // of cached verdicts is sound — a bump would just re-buy ~all faithful verdicts.
  // equivalence-v3: the statement auditor now receives the contract DIGEST instead of
  // the full authoring contracts (with a small added flag-in-schema remit) — a
  // deliberate one-time re-audit sweep per bundle at its next P1 entry. This key has
  // NO prompt fingerprint: future contract_digest.txt edits self-invalidate only
  // proof_audit and the P1 notation cache; statement-equivalence (and the P3 gate
  // caches, which deliberately did not sweep for this change) need a hand bump here.
  return hashEnvBody(`${parts.envBody}|${parts.mapping}|${parts.leanStatement}|${parts.refDefs}|citation-erasure-v1|equivalence-v3|${parts.citedDependencies}`);
}

/** Keyed on the audit PROMPT (and prose policy version): the verdict depends on what the auditor
 *  is asked to check, so widening the gate — by prompt edit or policy bump — must not read a
 *  verdict cached under the narrower standard; an unchanged proof would silently keep its stale
 *  `faithful`. The prompt fingerprint makes prompt-only widenings self-invalidating (same pattern
 *  as P1's promptFp), removing the "did any run execute since the bump?" timing dependence. */
export function proofAuditCacheKey(parts: {
  proofTex: string; leanPointer: string; leanProofCacheSource: string; notationTable: string; auditPromptFp: string;
  /** The canonical statement env the proof is judged against (formal-layer body; "" when
   *  unavailable). Without it, fixing a statement never invalidated a cached proof verdict
   *  that had failed AGAINST the broken statement (observed: \ne-typo verdict replay). */
  targetStatement: string;
}): string {
  return hashEnvBody(`${PRESENTATION_PROSE_POLICY_VERSION}|${parts.auditPromptFp}|${parts.targetStatement}|${parts.proofTex}|${parts.leanPointer}|${parts.leanProofCacheSource}|${proofAuditSemanticNotation(parts.notationTable)}`);
}

/** Proof validity depends on symbol spelling and reader-facing meaning, not on
 * notation-table row placement or the outline section that owns the symbol. */
export function proofAuditSemanticNotation(notationTable: string): string {
  const semanticRows: string[] = [];
  for (const raw of notationTable.split("\n")) {
    const line = raw.trim();
    if (!line) continue;
    if (line.startsWith("|") && line.endsWith("|")) {
      const cells = line.slice(1, -1).split("|").map((cell) => cell.replace(/\s+/g, " ").trim());
      if (cells.length >= 4 && !/^[-: ]+$/.test(cells.join("")) &&
          cells[1].toLowerCase() !== "paper notation")
        semanticRows.push(`${cells[1]}|${cells[0]}|${cells[2]}`);
    }
  }
  return semanticRows.sort((a, b) => a.localeCompare(b)).join("\n");
}

const ask = async (out: Promise<{ stdout: string; stderr: string }>) =>
  parseJsonLoose((await out).stdout);

function decodeLooseJsonString(s: string): string {
  let out = "";
  for (let i = 0; i < s.length; i++) {
    if (s[i] !== "\\" || i + 1 >= s.length) {
      out += s[i];
      continue;
    }
    const next = s[++i];
    // This decoder runs on the RAW-LaTeX fallback path (the strict JSON parse
    // already failed), so JSON escape semantics must NOT be applied blindly:
    // `\n`/`\t`/`\b`/`\f`/`\r` followed by a letter are TeX commands (`\nabla`,
    // `\to`, `\beta`, `\frac`, `\rho`) and decoding them injected control
    // characters into the frozen statement layer. Decode the whitespace escapes
    // only when NOT followed by a letter; keep everything letter-led verbatim.
    const standard: Record<string, string> = {
      "\\": "\\", '"': '"', "/": "/", n: "\n", r: "\r", t: "\t", b: "\b", f: "\f",
    };
    const letterFollows = /^[A-Za-z]/.test(s.slice(i + 1, i + 2));
    if (next === "\\" || next === '"' || next === "/") out += standard[next];
    else if ("nrtbf".includes(next) && !letterFollows) out += standard[next];
    else if (next === "u" && /^[0-9a-fA-F]{4}$/.test(s.slice(i + 1, i + 5))) {
      out += String.fromCharCode(Number.parseInt(s.slice(i + 1, i + 5), 16));
      i += 4;
    } else {
      // GPT sometimes emits raw LaTeX escapes such as `\(` inside a JSON string. They are
      // invalid JSON but unambiguous LaTeX, so preserve the unknown escape verbatim.
      out += `\\${next}`;
    }
  }
  return out;
}

/** A cached Lean-source reader (one read per file across an audit run). */
function leanSourceReader(repoRoot: string, leanSubdir: string) {
  const cache = new Map<string, string>();
  return async (file: string) => {
    if (!cache.has(file)) cache.set(file, await readFile(join(repoRoot, leanSubdir, file), "utf8"));
    return cache.get(file)!;
  };
}

/** Parse a model-authored LaTeX refinement. The normal JSON path stays authoritative; the
 * fallback recovers only the common invalid-JSON shape where LaTeX commands use raw backslashes. */
export function parseLatexRefinement(
  raw: string,
  bodyField: "refined_body" | "refined_proof",
): { body?: string; changed?: boolean; note?: string } | null {
  const normal = parseJsonLoose(raw) as Record<string, unknown> | null;
  if (normal && typeof normal[bodyField] === "string") {
    return {
      body: normal[bodyField] as string,
      changed: normal.changed === true,
      note: typeof normal.note === "string" ? normal.note : undefined,
    };
  }
  const startRe = new RegExp(`"${bodyField}"\\s*:\\s*"`);
  const start = startRe.exec(raw);
  if (!start) return null;
  const bodyStart = start.index + start[0].length;
  const tail = raw.slice(bodyStart);
  const boundary = /"\s*,\s*"changed"\s*:\s*(true|false)/.exec(tail);
  if (!boundary) return null;
  const afterChanged = tail.slice(boundary.index + boundary[0].length);
  const note = /,\s*"note"\s*:\s*"([\s\S]*)"\s*}\s*$/.exec(afterChanged);
  return {
    body: decodeLooseJsonString(tail.slice(0, boundary.index)),
    changed: boundary[1] === "true",
    note: note ? decodeLooseJsonString(note[1]) : undefined,
  };
}

/**
 * One-hop definition index for a refiner: give it the actual definition bodies its Lean statement
 * references (e.g. `clipBias`'s formula), not just a name to self-fetch. Returns `unfold(leanText)`.
 */
async function buildRefDefUnfolder(
  repoRoot: string,
  leanSubdir: string,
  leanSource: (file: string) => Promise<string>,
): Promise<(leanText: string) => Promise<string>> {
  const inlineKinds = new Set(["def", "abbrev", "structure"]);
  const refDeclByName = new Map<string, { file: string; line: number; declKind: string }>();
  try {
    for (const d of await parseLeanDecls(join(repoRoot, leanSubdir), {})) {
      if (inlineKinds.has(d.declKind) && !refDeclByName.has(d.name)) {
        refDeclByName.set(d.name, { file: d.file, line: d.line, declKind: d.declKind });
      }
    }
  } catch {
    /* best-effort: the refiner still has lean-lsp to self-fetch */
  }
  return async (leanText: string): Promise<string> => {
    const names = new Set(leanText.match(/[A-Za-z_][A-Za-z0-9_']*/g) ?? []);
    const inlined: string[] = [];
    for (const nm of names) {
      if (inlined.length >= 12) break;
      const loc = refDeclByName.get(nm);
      if (!loc) continue;
      try {
        const snip = extractDeclSnippet(await leanSource(loc.file), nm, loc.line);
        if (snip) inlined.push(`-- ${nm} (${loc.declKind}) in ${loc.file}\n${snip}`);
      } catch {
        /* skip a decl whose body can't be extracted */
      }
    }
    return inlined.join("\n\n");
  };
}

/** Append a human-readable drift report (the Lean re-audit caught an under-specified statement/proof). */
async function appendDriftReport(
  outDir: string,
  objId: string,
  before: string,
  after: string,
  rounds: number,
  note?: string,
): Promise<void> {
  const dir = join(outDir, "logs");
  await mkdir(dir, { recursive: true });
  await appendFile(
    join(dir, "graph_nl_drift.md"),
    `\n## ${objId} — refined toward Lean in ${rounds} round(s)\n` +
      (note ? `_${note}_\n` : "") +
      `\n**Before:**\n\n\`\`\`\n${before.trim()}\n\`\`\`\n\n**After (tightened toward Lean):**\n\n\`\`\`\n${after.trim()}\n\`\`\`\n`,
    "utf8",
  );
}

/**
 * P1 STATEMENT EQUIVALENCE AUDIT. Compares each frozen env body (from formal_layer.json) against its
 * Lean declaration; refines drift toward Lean (≤MAX_ROUNDS, fresh audits), and persists every faithful
 * body durably onto the graph (`nl.frozen_body`/`frozen_title`) and the formal layer (block body +
 * re-derived `.tex`). Returns the obj_ids still drifting after refinement — the P1 caller
 * halts on a non-empty result (the frozen layer disagrees with Lean beyond what auto-refinement could
 * tighten — adjudicate or fix the graph). Lean is trusted; the graph NL was only the draft.
 */
export async function runStatementAudit(io: StageIO): Promise<LintProblem[]> {
  const { deps } = io.ctx;
  const { repoRoot } = io.ctx;
  const leanSubdir = io.bank.leanSubdir;
  const leanSource = leanSourceReader(repoRoot, leanSubdir);
  const notation = parseOutline(await readFile(join(io.outDir, "outline.md"), "utf8")).notation;
  const reviewsPath = join(io.outDir, "logs", "reviews.jsonl");
  await mkdir(join(io.outDir, "logs"), { recursive: true });
  const layerPath = join(io.outDir, "formal_layer.json");
  const layerSrc0 = FormalLayerSource.parse(JSON.parse(await readFile(layerPath, "utf8")));
  const citedTextByObjId = new Map(layerSrc0.blocks.map((b) => [
    b.obj_id,
    b.cited_dependencies.length === 0
      ? "(none — no Lean premise may be erased)"
      : b.cited_dependencies.map((d) =>
          `- ${d.node_id}: ${d.statement.replace(/\s+/g, " ").trim()} [${d.cite_id}; ${d.locator ?? "locator unavailable"}; status ${d.status}]`,
        ).join("\n"),
  ] as const));
  // Env source = the formal-layer env blocks (P1 just wrote them). Same shape the P3 gate used to
  // parse out of paper.tex, but here the JSON layer is the source of truth (no paper.tex yet).
  const envs: AnchoredEnv[] = layerSrc0.blocks
    .filter((b) => b.env)
    .map((b, i) => ({ env: b.env!, obj_id: b.obj_id, title: b.title, body: b.body, order: i }));
  if (envs.length === 0) return [];


  // Verdict cache keyed by (env body, decl pointer): a statement already judged faithful is skipped on
  // rerun unless its frozen body or its crosswalk mapping changed.
  const cachePath = join(io.outDir, "equivalence_cache.json");
  const cache = await loadJsonCache<Record<string, { key: string; verdict: string; detail?: string }>>(cachePath);

  // Component sets (shared cache with P4): a bundled / hypothesis-only assumption is verified against
  // ALL its Lean pieces, not the single first-wins crosswalk anchor. Graph-first discovery (matches P4).
  const aliasToNodeId = new Map<string, string>();
  for (const n of io.bank.graph.nodes) if (n.obj_id) aliasToNodeId.set(n.obj_id, n.id);
  const { components: componentsMap, complete: componentReceipts, moduleDecls } = await ensureComponentsForEnvs({
    envs,
    crosswalk: io.bank.crosswalk,
    repoRoot,
    leanSubdir,
    cachePath: join(io.outDir, "components_cache.json"),
    deps,
    noteBlocks: new Map(
      parseNoteBlocks(io.bank.noteMd).map((b) => [aliasToNodeId.get(b.obj_id) ?? b.obj_id, b.body]),
    ),
    graph: io.bank.graph,
  });
  const unfoldReferencedDefs = await buildRefDefUnfolder(repoRoot, leanSubdir, leanSource);

  const equivalence = async (s: StatementCheck): Promise<{ verdict: string; detail?: string }> => {
    const v = (await ask(
      deps.runCodex({
        prompt: await presentationPrompt("statement_equivalence", {
          obj_id: s.obj_id,
          env_body: s.envBody,
          lean_statement: s.leanStatement,
          lean_pointer: s.leanPointer,
          notation_table: notation,
          cited_dependencies: s.citedDependencies ?? "(none — no Lean premise may be erased)",
        }),
        cwd: repoRoot,
        // Theorems/lemmas carry the quantifier/rate/witness structure where deep reasoning pays;
        // definitions/assumptions are short structural comparisons — medium suffices (cost economy).
        reasoningEffort: s.isMainResult ? "high" : "medium",
        leanLsp: true,
      }),
    )) as { verdict?: string; detail?: string } | null;
    return { verdict: v?.verdict ?? "drift", detail: v?.detail ?? "unparseable auditor output" };
  };

  const refDefsByObjId = new Map<string, string>();
  // LOCK RESPECT: an env whose current layer body is exactly its node's persisted
  // nl.frozen_body (modulo the mechanical cref normalization render0 applies) was
  // ALREADY validated when it froze — by a prior audit pass or by operator
  // adjudication. Re-auditing it every run defeats the lock's purpose ("a re-run
  // stays tight"): a stale or stricter verdict rewrites the frozen body and
  // oscillates against the notation reviewer (observed: repeated stripping of
  // reviewer-required notation displays). Audit only bodies that CHANGED.
  const canonBody = (t: string) => normalizeCrefs(t).replace(/\s+/g, " ").trim();
  const frozenBodyById = new Map(
    io.bank.graph.nodes.filter((n) => n.nl.frozen_body).map((n) => [n.id, canonBody(n.nl.frozen_body!)] as const),
  );
  const lockedVerbatim = (e: AnchoredEnv) => frozenBodyById.get(e.obj_id) === canonBody(e.body);
  const statements: (StatementCheck & { cacheKey: string; mapping: string; env: string; locked: boolean })[] = [];
  // Envs whose CURRENT body already holds a cached faithful verdict — validated, so they are
  // frozen below like any other faithful body (a verdict cached before this freeze policy
  // existed would otherwise leave the body loose and re-rendered on the next prompt edit).
  const cachedFaithful: AnchoredEnv[] = [];
  for (const e of envs) {
    const cw = io.bank.crosswalk.find((c) => c.obj_id === e.obj_id);
    const comps = componentsMap[e.obj_id] ?? [];
    const componentReceipt = componentReceipts[e.obj_id] === true;
    if (comps.length > 0 && !componentReceipt) {
      throw new Error(`P1 component mapping for ${e.obj_id} is missing its completeness receipt`);
    }
    let leanStatement: string | null = null;
    let leanPointer = "";
    let mapping = "";
    if (comps.length > 0) {
      const assembled = await assembleComponentText({
        specs: comps,
        crosswalk: io.bank.crosswalk,
        moduleDecls,
        repoRoot,
        leanSubdir,
      });
      if (assembled.text) {
        leanStatement = assembled.text;
        mapping = `components:${componentSignature(comps)}:` + assembled.resolved
          .map((r) => `${r.file}:${r.decl}:${r.line}:${hashEnvBody(r.snippet)}`).sort().join("|");
        leanPointer =
          `Formalized by ${comps.length} Lean piece(s) — ` +
          comps
            .map((c) => (c.type === "decl" ? c.decl : `hypotheses {${c.binders.join(", ")}} of ${c.theorem}`))
            .join("; ") +
          `. Read each in ${leanSubdir} before judging; every paper clause must map to SOME piece.`;
      }
    }
    if (leanStatement === null && cw?.lean) {
      const resolved = await resolveLeanDeclaration(repoRoot, leanSubdir, cw.lean);
      leanStatement = resolved.snippet;
      mapping = `${resolved.file}:${resolved.decl}:${resolved.line}`;
      const abs = await resolvedLeanAbsolutePath(repoRoot, resolved.file);
      leanPointer = `file: ${abs}\ndeclaration: ${resolved.decl} (around line ${resolved.line})\nRead the file with your tools; do not guess its contents.`;
      if (resolved.relocated) {
        io.state.notes.push(
          `P1: resolved re-exported Lean declaration for ${e.obj_id}: ${cw.lean.file}:${cw.lean.decl} -> ` +
          `${resolved.file}:${resolved.decl}:${resolved.line} (${resolved.resolution})`,
        );
      }
    }
    if (leanStatement === null) {
      const graphNode = io.bank.graph.nodes.find((n) => n.id === e.obj_id || n.obj_id === e.obj_id);
      // Presentation-synthesized definitions have no bank crosswalk/graph identity and
      // are legitimately prose-only. A bank-backed formal object is never silently
      // downgraded to note-only because discovery returned [] or a stale partial cache.
      if (cw || graphNode) {
        const receipt = componentReceipt ? "complete component discovery returned no pieces" : "no complete component discovery receipt";
        throw new Error(`P1 formal object ${e.obj_id} has neither a resolved Lean declaration nor nonempty resolved components (${receipt})`);
      }
      continue;
    }
    const refDefs = await unfoldReferencedDefs(leanStatement);
    refDefsByObjId.set(e.obj_id, refDefs);
    const citedDependencies = citedTextByObjId.get(e.obj_id) ?? "(none — no Lean premise may be erased)";
    const key = equivalenceAuditKey({ envBody: e.body, mapping, leanStatement, refDefs, citedDependencies });
    if (cache[e.obj_id]?.key === key && cache[e.obj_id].verdict === "faithful") {
      cachedFaithful.push(e);
      continue;
    }
    statements.push({
      obj_id: e.obj_id,
      envBody: e.body,
      leanStatement,
      leanPointer,
      isMainResult: e.env === "theoremv" || e.env === "lemmav",
      cacheKey: key,
      mapping,
      env: e.env,
      citedDependencies,
      // LOCK SEMANTICS: a locked env is audited like any other (a Lean edit after the
      // freeze changes the cache key above, forcing a fresh verdict), but on genuine
      // drift it is NEVER auto-refined — the frozen body is P3-validated or operator-
      // adjudicated, so the disagreement halts for adjudication instead (Phase 2).
      locked: lockedVerbatim(e),
    });
  }

  // Tiered batch pre-audit (mirrors the F2.5 reviewer). THEOREMS get individual high-effort calls.
  // LEMMAS batch ≤3 at HIGH effort. DEFINITIONS/ASSUMPTIONS batch ≤5 at MEDIUM. A batch verdict
  // pre-empts the individual call; anything missing falls through to its own individual call.
  const LEMMA_BATCH = 3;
  const SHALLOW_BATCH = 5;
  const batchVerdicts = new Map<string, { verdict: string; detail?: string }>();
  const groupsOf = <T>(arr: T[], size: number): T[][] => {
    const out: T[][] = [];
    for (let i = 0; i < arr.length; i += size) {
      const g = arr.slice(i, i + size);
      if (g.length >= 2) out.push(g); // a singleton is cheaper as an individual call
    }
    return out;
  };
  const batchJobs: { group: typeof statements; effort: "high" | "medium" }[] = [
    ...groupsOf(statements.filter((s) => s.env === "lemmav" && !s.citedDependencies?.startsWith("- ")), LEMMA_BATCH).map((group) => ({ group, effort: "high" as const })),
    ...groupsOf(statements.filter((s) =>
      !s.isMainResult &&
      !s.citedDependencies?.startsWith("- ") &&
      !requiresIndividualStatementAudit(s.envBody)
    ), SHALLOW_BATCH).map((group) => ({ group, effort: "medium" as const })),
  ];
  await mapLimit(batchJobs, AUDIT_CONCURRENCY, async ({ group, effort }) => {
    const block = group
      .map(
        (s) =>
          `--- ${s.obj_id} ---\nPaper environment body:\n${s.envBody}\n\nLean statement:\n${s.leanStatement}\n\nLean source location:\n${s.leanPointer}`,
      )
      .join("\n\n");
    try {
      const parsed = (await ask(
        deps.runCodex({
          prompt: await presentationPrompt("statement_equivalence_batch", { statements_block: block, notation_table: notation }),
          cwd: repoRoot,
          reasoningEffort: effort,
          leanLsp: true,
        }),
      )) as { results?: { obj_id?: string; verdict?: string; detail?: string }[] } | null;
      for (const r of parsed?.results ?? []) {
        if (r.obj_id && (r.verdict === "faithful" || r.verdict === "drift")) {
          batchVerdicts.set(r.obj_id, { verdict: r.verdict, detail: r.detail });
          const st = statements.find((x) => x.obj_id === r.obj_id);
          if (st) cache[r.obj_id] = { key: st.cacheKey, verdict: r.verdict, detail: r.detail };
        }
      }
      // Persist each batch's verdicts as they land (atomic write; concurrent workers are
      // safe, same pattern as the proof audit): the sweep used to write the cache ONCE at
      // the end, so an interruption (Slurm expiry, 2026-08-20) lost hours of paid audits.
      await writeJsonAtomic(cachePath, cache);
    } catch {
      /* group falls through to individual calls */
    }
  });

  const refineRunner: RefineRunner = async (c) => {
    const raw = (await deps.runCodex({
        prompt: await presentationPrompt("refine_statement", {
          obj_id: c.obj_id,
          env_body: c.envBody,
          lean_statement: c.leanStatement,
          lean_pointer: c.leanPointer,
          drift_detail: c.driftDetail,
          notation_table: notationForArtifact(notation, `${c.envBody}\n${refDefsByObjId.get(c.obj_id) ?? ""}`),
          referenced_defs: refDefsByObjId.get(c.obj_id) || "(none indexed — read the Lean via your tools)",
          cited_dependencies: c.citedDependencies ?? "(none — no Lean premise may be erased)",
        }),
        cwd: repoRoot,
        reasoningEffort: "high",
        leanLsp: true,
      })).stdout;
    const v = parseLatexRefinement(raw, "refined_body");
    const refined_body = typeof v?.body === "string" ? fixOverEscapedTex(v.body) : c.envBody;
    return {
      refinedBody: refined_body,
      changed: v?.changed === true && refined_body.trim().length > 0 && refined_body.trim() !== c.envBody.trim(),
      note: v?.note,
    };
  };

  // Phase 1 — initial audits in PARALLEL (each statement vs its own Lean is independent).
  const eqProblems: LintProblem[] = [];
  const audited = await mapLimit(statements, AUDIT_CONCURRENCY, async (s) => {
    const v0 = batchVerdicts.get(s.obj_id) ?? (await equivalence(s));
    cache[s.obj_id] = { key: s.cacheKey, verdict: v0.verdict, detail: v0.detail };
    await writeJsonAtomic(cachePath, cache); // incremental persistence — see the batch loop note
    return { s, v0 };
  });
  // Phase 2 — refine the drifting statements in PARALLEL (refineStatement is PURE; writes are serialized).
  // A LOCKED drifting statement is not refined: rewriting a validated frozen body caused the
  // audit↔reviewer display-stripping oscillation, and silently accepting it would ship a stale
  // claim over changed Lean. Halt loudly with the drift detail for operator adjudication.
  for (const { s: ls, v0 } of audited) {
    if (ls.locked && v0.verdict !== "faithful") {
      eqProblems.push({
        gate: "locked-env-drift",
        objId: ls.obj_id,
        detail: `${ls.obj_id}: locked (frozen) body disagrees with the current Lean statement — ${v0.detail ?? v0.verdict}. Adjudicate: update nl.frozen_body to match the Lean, or fix the Lean/crosswalk; the audit never auto-rewrites a locked body.`,
      });
    }
  }
  const refinedResults = await mapLimit(
    audited.filter(({ s: fs, v0 }) => v0.verdict !== "faithful" && !fs.locked),
    AUDIT_CONCURRENCY,
    async ({ s }) => ({
      s,
      refined: await refineStatement({
        check: s,
        notation,
        maxRounds: MAX_ROUNDS,
        reaudit: (sc) => equivalence(sc), // fresh audits on the refined body (no cache)
        refine: refineRunner,
      }),
    }),
  );
  // Phase 3 — apply re-freeze writes SERIALLY (formal_layer.json + graph are shared).
  const layerSrc = FormalLayerSource.parse(JSON.parse(await readFile(layerPath, "utf8")));
  let bankGraphDirty = false;
  let layerDirty = false;
  // FREEZE EVERY FAITHFUL BODY, not only refined ones. A body that passed on its first audit used
  // to stay loose, so the next render-prompt (or global contract) edit re-rendered it — wording
  // drift with no Lean change — which re-keyed its statement audit, every proof audit citing it,
  // and every section placing it: one prompt commit became a near-full re-run (sa_plm, 2026-08-21).
  // Validated ⇒ locked: P1 reuses the body verbatim; a LEAN change still re-audits it (the verdict
  // key holds the Lean source) and halts as locked-env-drift for adjudication. To push a prompt
  // improvement into an already-frozen paper, re-enter with `--from P1 --refresh-frozen-bodies`.
  const freezeFaithful = (objId: string, body: string): void => {
    const node = io.bank.graph.nodes.find((n) => n.id === objId);
    if (!node || node.delivery?.status === "undelivered") return;
    const trimmed = body.trim();
    if (node.nl.frozen_body === trimmed) return;
    node.nl.frozen_body = trimmed;
    node.nl.frozen_title = layerSrc.blocks.find((b) => b.obj_id === objId)?.title ?? null;
    bankGraphDirty = true;
  };
  for (const e of cachedFaithful) freezeFaithful(e.obj_id, e.body);
  for (const { s, v0 } of audited) if (v0.verdict === "faithful") freezeFaithful(s.obj_id, s.envBody);
  for (const { s, refined } of refinedResults) {
    if (refined.body.trim() !== s.envBody.trim()) {
      // Persist the refiner's BEST attempt (faithful or not) into the source of truth — a
      // tightened-but-still-drifting body is a better starting point for the next re-audit than the
      // stale original. Update block.body; re-derive the read-only .tex below.
      const blk = layerSrc.blocks.find((b) => b.obj_id === s.obj_id);
      if (blk) {
        blk.body = refined.body.trim();
        layerDirty = true;
      }
      // DURABLE persistence: once FAITHFUL, write the validated body back onto the graph node so a P1
      // re-run reproduces it VERBATIM (the locked-env path) instead of re-deriving and reverting.
      if (refined.faithful) {
        const node = io.bank.graph.nodes.find((n) => n.id === s.obj_id);
        if (node) {
          node.nl.frozen_body = refined.body.trim();
          node.nl.frozen_title = blk?.title ?? null;
          bankGraphDirty = true;
        }
      }
      cache[s.obj_id] = {
        key: equivalenceAuditKey({ envBody: refined.body, mapping: s.mapping, leanStatement: s.leanStatement, refDefs: refDefsByObjId.get(s.obj_id) ?? "", citedDependencies: s.citedDependencies ?? "" }), // why: the refined faithful verdict is tied to the exact Lean source, trust boundary, and verdict policy audited.
        verdict: refined.faithful ? "faithful" : "drift",
        detail: refined.detail,
      };
      await appendDriftReport(io.outDir, s.obj_id, s.envBody, refined.body, refined.rounds, refined.note);
      await appendFile(
        reviewsPath,
        JSON.stringify({ kind: "refine", obj_id: s.obj_id, rounds: refined.rounds, faithful: refined.faithful, note: refined.note }) + "\n",
        "utf8",
      );
      io.state.notes.push(
        `P1: refined ${s.obj_id} toward Lean fidelity (${refined.rounds} round(s)` +
          (refined.faithful ? "" : "; STILL DRIFTING — best attempt persisted, re-audit/adjudicate") +
          `) — see logs/graph_nl_drift.md`,
      );
    }
    if (!refined.faithful) {
      eqProblems.push({ gate: "equivalence", detail: `${s.obj_id}: ${refined.detail ?? "drift"}` });
    }
  }
  if (layerDirty) {
    await writeFile(layerPath, JSON.stringify(layerSrc, null, 2) + "\n", "utf8");
    await writeFile(
      join(io.outDir, "formal_layer.tex"),
      "% DERIVED from formal_layer.json — read-only, do not edit.\n" + blocksToTex(layerSrc.blocks) + "\n",
      "utf8",
    );
  }
  if (bankGraphDirty) {
    await saveGraph(
      graphPath(bankAcceptedDir(repoRoot, io.ctx.qid, io.ctx.spec), io.ctx.qid, io.ctx.spec),
      io.bank.graph,
    );
    io.state.notes.push("P1: persisted audit-faithful statement body/bodies to the bank graph (nl.frozen_body) — a re-run reuses them verbatim instead of re-rendering.");
  }
  await writeJsonAtomic(cachePath, cache); // why: the equivalence cache is the P4 trust anchor — a corrupt write must not survive.
  await appendFile(reviewsPath, JSON.stringify({ kind: "equivalence", problems: eqProblems }) + "\n", "utf8");
  return eqProblems;
}

/**
 * P2 PROOF EQUIVALENCE AUDIT. Reconciles each rendered appendix proof's PROSE against its
 * machine-verified Lean proof. The Lean proof type-checks, so revising the prose toward it is always
 * safe (no laundering — the prose only describes a verified object). Audits each proof, REFINES the
 * unfaithful ones (≤MAX_ROUNDS, persist-best), and rewrites `proofs/<obj_id>.tex`. Returns the final
 * proof text for EVERY proof (so the P2 assembly uses the refined versions) plus the obj_ids that are
 * still unfaithful after refinement — the P2 caller halts on a non-empty `problems` (re-render or
 * adjudicate). `proofTargets` are the (obj_id, env-kind, leanFile/decl) tuples P2 already resolved.
 */
/**
 * Lean routes (`% lean: declA, declB`) the refinement dropped, compared as declaration names with
 * their occurrence counts — so reordering, spacing, and a route moving to another line all count as
 * PRESENT, while deleting one of two identically-anchored branches still counts as dropped.
 *
 * The refiner rewrites toward Lean and only removes prose; it never supplies a conclusion the
 * auditor reported missing. A refinement that drops an anchored step has deleted content tied to a
 * declaration, and the auditor re-reports the same omission next cycle.
 *
 * Deliberately kept to one pattern: an escaped `\%` is not a route, and no other TeX context
 * is modelled. A false positive here keeps the input proof, which then HALTS for adjudication
 * rather than assembling silently, so the failure mode is loud and a scrubbing pass is not worth
 * the complexity.
 */
export function droppedLeanRoutes(before: string, after: string): string[] {
  const decls = (tex: string): Map<string, number> => {
    const counts = new Map<string, number>();
    for (const m of tex.matchAll(/(?<!\\)%\s*lean:\s*([^\n]+)/g))
      for (const raw of m[1].split(",")) {
        const name = raw.trim().replace(/[.;]+$/, "");
        if (name) counts.set(name, (counts.get(name) ?? 0) + 1);
      }
    return counts;
  };
  const kept = decls(after);
  return [...decls(before)].filter(([name, n]) => (kept.get(name) ?? 0) < n).map(([name]) => name);
}

export async function runProofAudit(
  io: StageIO,
  proofTargets: { obj_id: string; isMain: boolean; lean: { file: string; decl: string } }[],
): Promise<{ refined: Map<string, string>; problems: LintProblem[] }> {
  const { deps, repoRoot } = io.ctx;
  const leanSubdir = io.bank.leanSubdir;
  const leanSource = leanSourceReader(repoRoot, leanSubdir);
  const notation = parseOutline(await readFile(join(io.outDir, "outline.md"), "utf8")).notation;
  // The refiner re-authors (and expands) proof prose, so it gets the same subordinated
  // D-stage derivation the P2 renderer gets. The AUDITOR does not — its Lean-vs-prose
  // verdict must stay independent of the untrusted derivation.
  const informalDerivations = await loadInformalDerivations(repoRoot, io.ctx.qid, io.ctx.spec);
  // Citable paper environments, each annotated with the Lean declaration it realizes,
  // so the refiner can map a proof step's `% lean:` route onto a paper label and CITE
  // the lemma instead of re-deriving content the paper already states. Without this
  // the refiner cannot cite promoted helper lemmas at all (inventing crefs is banned).
  const declByNode = new Map((io.bank.graph?.nodes ?? [])
    .filter((n) => n.lean?.decl_name)
    .map((n) => [n.id, n.lean!.decl_name] as const));
  const allLayerBlocks = await readFile(join(io.outDir, "formal_layer.json"), "utf8")
    .then((raw) => (JSON.parse(raw).blocks ?? []) as { obj_id: string; env: string; title?: string | null; body: string }[])
    .catch(() => null);
  const citableBlocks = allLayerBlocks === null
    ? null
    : allLayerBlocks.filter((b) => b.env === "lemmav" || b.env === "definitionv" || b.env === "algorithmv" || b.env === "theoremv");
  // Per-proof view: exclude the result under proof itself — otherwise the refiner could
  // "repair" a flagged step by citing the very theorem being proved (circular).
  // Full bodies only for envs the proof/findings actually engage (a {obj:…} mention,
  // or the proof's `% lean:` routes naming the env's realized declaration); the rest
  // appear as an id/title/decl index — sending every body was measured at 59% of each
  // refine input (2026-08-20 token audit), and the index plus the formal_layer.tex
  // inventory (openable via tools) preserves discoverability of citable helpers.
  const citableHelperEnvsFor = (objId: string, referenceText: string): string => {
    if (citableBlocks === null) return "(no formal layer available)";
    const full: string[] = [];
    const index: string[] = [];
    for (const b of citableBlocks) {
      if (b.obj_id === objId) continue;
      const decl = declByNode.get(b.obj_id);
      // Bare-id disjunct: audit issues name envs without braces ("should cite
      // lem:aux-bound"); obj ids are kind-namespaced, so collisions are negligible.
      const engaged = referenceText.includes(b.obj_id) ||
        (decl != null && referenceText.includes(decl));
      if (engaged) {
        const head = decl ? `% realizes Lean declaration: ${decl}\n` : "";
        full.push(`${head}\\begin{${b.env}}{${b.obj_id}}${b.title ? `[${b.title}]` : ""}\n${b.body}\n\\end{${b.env}}`);
      } else {
        index.push(`- ${b.obj_id} [${b.env}]${b.title ? ` ${b.title}` : ""}${decl ? ` (realizes ${decl})` : ""}`);
      }
    }
    const indexBlock = index.length > 0
      ? `INDEX of further citable environments — bodies are in ${join(io.outDir, "formal_layer.tex")}; open it with your tools before citing any of them:\n${index.join("\n")}`
      : "";
    return [full.join("\n\n"), indexBlock].filter(Boolean).join("\n\n") || "(no citable helper environments)";
  };
  const reviewsPath = join(io.outDir, "logs", "reviews.jsonl");
  await mkdir(join(io.outDir, "logs"), { recursive: true });
  const unfoldReferencedDefs = await buildRefDefUnfolder(repoRoot, leanSubdir, leanSource);

  // Verdict cache keyed by (proof body, decl pointer): a proof already judged faithful is skipped.
  const cachePath = join(io.outDir, "proof_audit_cache.json");
  const cache = await loadJsonCache<Record<string, { key: string; verdict: string; issues?: string[] }>>(cachePath);
  const saveCache = () => writeJsonAtomic(cachePath, cache); // why: proofAudit workers save concurrently under mapLimit — interleaved plain writes can corrupt the cache.

  const auditPromptFp = await promptFingerprint("proof_audit");
  // UNFILTERED lookup: propositionv proofs are audited too (isMainProofEnv), and the
  // citable list excludes them — a filtered lookup would leave their targetStatement
  // permanently "", replaying stale verdicts across statement fixes.
  const targetStatementFor = (objId: string): string =>
    allLayerBlocks?.find((b) => b.obj_id === objId)?.body ?? "";
  const proofAudit = async (p: { obj_id: string; proofTex: string; leanPointer: string; leanProofSource: string; leanProofCacheSource: string; notationTable: string; tier: "main" | "auxiliary" }) => {
    const key = proofAuditCacheKey({ ...p, auditPromptFp, targetStatement: targetStatementFor(p.obj_id) });
    const hit = cache[p.obj_id];
    const cacheable = p.leanProofCacheSource.length > 0;
    if (cacheable && hit?.key === key) return { verdict: hit.verdict, issues: hit.issues };
    const v = (await ask(
      deps.runCodex({
        prompt: await presentationPrompt("proof_audit", {
          obj_id: p.obj_id,
          proof_tex: p.proofTex,
          lean_proof_source: `${p.leanPointer}\n\nLean excerpt:\n${p.leanProofSource || "(snippet unavailable — read the file via tools)"}`,
          notation_table: p.notationTable,
          // Check 6 audits claims the proof makes ABOUT other objects ("recall from <env> that …"),
          // which can only be judged by opening those environments.
          paper_path: join(io.outDir, "formal_layer.tex"), // canonical env inventory NOW; paper.tex lags for newly promoted envs
        }),
        cwd: repoRoot,
        reasoningEffort: p.tier === "main" ? "high" : "medium",
        leanLsp: true,
      }),
    )) as { verdict?: string; issues?: string[] } | null;
    const out = { verdict: v?.verdict ?? "unfaithful", issues: v?.issues ?? ["unparseable auditor output"] };
    if (cacheable) {
      cache[p.obj_id] = { key, ...out };
      await saveCache();
    }
    return out;
  };

  const proofRefine: RefineRunner = async (c) => {
    // Scope both context blocks to this proof: helpers it engages (plus an index of
    // the rest), and only the notation rows appearing in the artifact the refiner
    // actually sees — the same filter the statement-equivalence path already trusts.
    const helperEnvs = citableHelperEnvsFor(c.obj_id, `${c.envBody}\n${c.driftDetail}`);
    const refineArtifact = [c.envBody, c.driftDetail, refDefsByObjId.get(c.obj_id) ?? "",
      targetStatementFor(c.obj_id), helperEnvs].join("\n");
    const raw = (await deps.runCodex({
        prompt: await presentationPrompt("refine_proof", {
          obj_id: c.obj_id,
          proof_tex: c.envBody,
          lean_proof_source: c.leanPointer,
          referenced_defs: refDefsByObjId.get(c.obj_id) || "(none indexed — read the Lean via your tools)",
          audit_issues: c.driftDetail,
          helper_lemma_envs: helperEnvs,
          informal_derivation: informalDerivations.get(c.obj_id) ?? "(none recorded for this result)",
          notation_table: notationForArtifact(notation, refineArtifact),
        }),
        cwd: repoRoot,
        reasoningEffort: "high",
        leanLsp: true,
      })).stdout;
    const v = parseLatexRefinement(raw, "refined_proof");
    const refined = typeof v?.body === "string" ? fixOverEscapedTex(v.body) : c.envBody;
    return {
      refinedBody: refined,
      changed: v?.changed === true && refined.trim().length > 0 && refined.trim() !== c.envBody.trim(),
      note: v?.note,
    };
  };

  const refDefsByObjId = new Map<string, string>();
  type Target = { obj_id: string; proofTex: string; leanPointer: string; leanProofSource: string; leanProofCacheSource: string; notationTable: string; isMain: boolean };
  const targets: Target[] = [];
  for (const pt of proofTargets) {
    const proofTex = await readFile(join(io.outDir, "proofs", `${pt.obj_id}.tex`), "utf8").catch(() => null);
    if (proofTex === null) continue; // statement-only / no rendered proof
    const resolved = await resolveLeanDeclaration(repoRoot, leanSubdir, { ...pt.lean, line: 0 });
    const resolvedPath = await resolvedLeanAbsolutePath(repoRoot, resolved.file);
    const leanPointer = `file: ${resolvedPath}\ndeclaration: ${resolved.decl}\nRead the file with your tools; do not guess its contents.`;
    // Best-effort def unfold for the refiner: extract the decl snippet, then unfold its referenced defs.
    let leanProofSource = "";
    let leanProofCacheSource = "";
    try {
      const exactDecl = extractFullDeclSource(await readFile(resolvedPath, "utf8"), resolved.decl, 0);
      leanProofSource = exactDecl;
      leanProofCacheSource = exactDecl;
      if (exactDecl) refDefsByObjId.set(pt.obj_id, await unfoldReferencedDefs(exactDecl));
    } catch {
      /* refiner still has lean-lsp to self-fetch */
    }
    targets.push({
      obj_id: pt.obj_id,
      proofTex: proofTex.trim(),
      leanPointer,
      leanProofSource,
      leanProofCacheSource,
      // Only the notation rows the auditor can encounter in THIS proof's material —
      // the full table averaged 32-42% of every proof_audit input (2026-08-20 token
      // audit); the filter is the one already trusted on the equivalence path. The
      // filtered table enters proofAuditCacheKey via notationTable, so this change
      // re-keys verdicts once per bundle (a deliberate one-time re-audit sweep).
      notationTable: notationForArtifact(notation,
        `${proofTex}\n${leanProofSource}\n${targetStatementFor(pt.obj_id)}`),
      isMain: pt.isMain,
    });
  }

  // Refine the non-(cached-faithful) proofs in PARALLEL (refineStatement is pure — no writes).
  const refinedResults = await mapLimit(targets, AUDIT_CONCURRENCY, async (pt) => {
    const refined = await refineStatement({
      check: { obj_id: pt.obj_id, envBody: pt.proofTex, leanStatement: pt.leanPointer, leanPointer: pt.leanPointer, isMainResult: pt.isMain },
      notation: pt.notationTable,
      maxRounds: MAX_ROUNDS,
      reaudit: async (sc) => {
        const r = await proofAudit({
          obj_id: sc.obj_id,
          proofTex: sc.envBody,
          leanPointer: sc.leanPointer,
          leanProofSource: pt.leanProofSource,
          leanProofCacheSource: pt.leanProofCacheSource,
          notationTable: pt.notationTable,
          tier: sc.isMainResult ? "main" : "auxiliary",
        });
        return { verdict: r.verdict, detail: (r.issues ?? []).join("; ") || "unfaithful" };
      },
      refine: proofRefine,
    });
    return { pt, refined };
  });

  // Persist-best SERIALLY (proofs/<id>.tex is the source of truth; P2 assembly re-reads the map below).
  const refined = new Map<string, string>();
  const problems: LintProblem[] = [];
  for (const { pt, refined: r } of refinedResults) {
    // Canonical title on BOTH the in-memory map and disk: stamping the verdict cache
    // against a body that differs from what the next run reads from disk costs a
    // redundant re-audit per title-repaired proof. Compare CANONICALLY so a faithful
    // proof whose only difference is a legacy title is not rewritten or drift-reported
    // (P2's entry points heal titles on read).
    let newBody = canonicalizeProofTitle(pt.obj_id, r.body.trim());
    // A refinement may reword an anchored step; it may not delete one. When it does, keep the
    // input — and treat the retained proof as UNFAITHFUL regardless of the discarded body's
    // verdict. The verdict below describes the text that was thrown away; inheriting it would
    // let an unaudited proof reach assembly, which is worse than the deletion being guarded.
    let faithful = r.faithful;
    const lost = droppedLeanRoutes(pt.proofTex, newBody);
    if (lost.length > 0) {
      newBody = canonicalizeProofTitle(pt.obj_id, pt.proofTex);
      faithful = false;
      io.state.notes.push(
        `P2: refinement of ${pt.obj_id} discarded — it dropped Lean-anchored step(s) (${lost.join("; ")}); ` +
          `kept the input proof, which halts for adjudication rather than assembling an unaudited body.`,
      );
    }
    refined.set(pt.obj_id, newBody);
    if (newBody !== canonicalizeProofTitle(pt.obj_id, pt.proofTex)) {
      await writeFile(join(io.outDir, "proofs", `${pt.obj_id}.tex`), newBody + "\n", "utf8");
      await appendDriftReport(io.outDir, `${pt.obj_id} (proof)`, pt.proofTex, newBody, r.rounds, r.note);
    }
    await appendFile(
      reviewsPath,
      JSON.stringify({
        kind: "proof-refine",
        obj_id: pt.obj_id,
        rounds: r.rounds,
        faithful,
        ...(lost.length > 0 ? { discarded: true, discarded_verdict: r.faithful, dropped_routes: lost } : {}),
        note: r.note,
      }) + "\n",
      "utf8",
    );
    if (!faithful) {
      problems.push({
        gate: "proof-audit",
        detail: `${pt.obj_id}: ${lost.length > 0
          ? `refinement discarded for dropping Lean-anchored step(s) (${lost.join("; ")}); the input proof stands unaudited`
          : r.detail ?? "unfaithful"}`,
      });
      io.state.notes.push(
        `P2: proof ${pt.obj_id} refined toward Lean (${r.rounds} round(s)); STILL unfaithful — best attempt persisted, will halt for adjudication`,
      );
    }
  }
  await saveCache();
  return { refined, problems };
}
