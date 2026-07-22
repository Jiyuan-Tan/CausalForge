import { readFile, writeFile, appendFile, mkdir } from "node:fs/promises";
import { join } from "node:path";
import type { StageIO } from "./pipeline.js";
import { presentationPrompt } from "./prompt_io.js";
import { parseOutline } from "./stage_util.js";
import { hashEnvBody, type AnchoredEnv, type LintProblem } from "./tex_anchors.js";
import { fixOverEscapedTex } from "./emit.js";
import { FormalLayerSource, blocksToTex, hashBody } from "./formal_layer.js";
import { bankAcceptedDir } from "./paths.js";
import { saveGraph, graphPath } from "../graph/store.js";
import { extractDeclSnippet, extractFullDeclSource } from "./lean_extract.js";
import { parseLeanDecls } from "../formalization/crosswalk.js";
import { ensureComponentsForEnvs, assembleComponentText, componentSignature } from "./components.js";
import { parseNoteBlocks } from "./note_parser.js";
import { writeJsonAtomic } from "./json_io.js";
import { repairLatexStringsDeep } from "../discovery/core/latex_serialization.js";
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

function notationForArtifact(notation: string, artifact: string): string {
  const tokens = new Set(artifact.match(/\\[A-Za-z]+|[A-Za-z][A-Za-z0-9_']{1,}/g) ?? []);
  const rows = notation.split("\n").filter((row) =>
    (row.match(/\\[A-Za-z]+|[A-Za-z][A-Za-z0-9_']{1,}/g) ?? []).some((token) => tokens.has(token)),
  );
  return rows.length > 0 ? rows.join("\n") : "(no artifact-specific notation rows)";
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
    const standard: Record<string, string> = {
      "\\": "\\", '"': '"', "/": "/", n: "\n", r: "\r", t: "\t", b: "\b", f: "\f",
    };
    if (next in standard) out += standard[next];
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

const pointerFor = (repoRoot: string, leanSubdir: string, cw: { file: string; decl: string; line: number }) =>
  `file: ${join(repoRoot, leanSubdir, cw.file)}\ndeclaration: ${cw.decl} (around line ${cw.line})\nRead the file with your tools; do not guess its contents.`;

/** A cached Lean-source reader (one read per file across an audit run). */
function leanSourceReader(repoRoot: string, leanSubdir: string) {
  const cache = new Map<string, string>();
  return async (file: string) => {
    if (!cache.has(file)) cache.set(file, await readFile(join(repoRoot, leanSubdir, file), "utf8"));
    return cache.get(file)!;
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
 * body_hash, re-derived `.tex`). Returns the obj_ids still drifting after refinement — the P1 caller
 * halts on a non-empty result (the frozen layer disagrees with Lean beyond what auto-refinement could
 * tighten — adjudicate or fix the graph). Lean is trusted; the graph NL was only the draft.
 */
export async function runStatementAudit(io: StageIO): Promise<LintProblem[]> {
  const { deps } = io.ctx;
  const { repoRoot } = io.ctx;
  const leanSubdir = io.bank.leanSubdir;
  const notation = parseOutline(await readFile(join(io.outDir, "outline.md"), "utf8")).notation;
  const reviewsPath = join(io.outDir, "reviews.jsonl");
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

  const leanSource = leanSourceReader(repoRoot, leanSubdir);

  // Verdict cache keyed by (env body, decl pointer): a statement already judged faithful is skipped on
  // rerun unless its frozen body or its crosswalk mapping changed.
  const cachePath = join(io.outDir, "equivalence_cache.json");
  const cache: Record<string, { key: string; verdict: string; detail?: string }> = JSON.parse(
    await readFile(cachePath, "utf8").catch(() => "{}"),
  );
  repairLatexStringsDeep(cache);

  // Component sets (shared cache with P4): a bundled / hypothesis-only assumption is verified against
  // ALL its Lean pieces, not the single first-wins crosswalk anchor. Graph-first discovery (matches P4).
  const aliasToNodeId = new Map<string, string>();
  for (const n of io.bank.graph.nodes) if (n.obj_id) aliasToNodeId.set(n.obj_id, n.id);
  const { components: componentsMap, moduleDecls } = await ensureComponentsForEnvs({
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
        prompt: await presentationPrompt("p3_equivalence", {
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
  const statements: (StatementCheck & { cacheKey: string; mapping: string; env: string })[] = [];
  for (const e of envs) {
    const cw = io.bank.crosswalk.find((c) => c.obj_id === e.obj_id);
    const comps = componentsMap[e.obj_id] ?? [];
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
      if (assembled) {
        leanStatement = assembled;
        mapping = `components:${componentSignature(comps)}`;
        leanPointer =
          `Formalized by ${comps.length} Lean piece(s) — ` +
          comps
            .map((c) => (c.type === "decl" ? c.decl : `hypotheses {${c.binders.join(", ")}} of ${c.theorem}`))
            .join("; ") +
          `. Read each in ${leanSubdir} before judging; every paper clause must map to SOME piece.`;
      }
    }
    if (leanStatement === null && cw?.lean) {
      try {
        leanStatement = extractDeclSnippet(await leanSource(cw.lean.file), cw.lean.decl, cw.lean.line);
        mapping = `${cw.lean.file}:${cw.lean.decl}:${cw.lean.line}`;
        leanPointer = pointerFor(repoRoot, leanSubdir, cw.lean);
      } catch {
        io.state.notes.push(
          `P1: skipped equivalence for ${e.obj_id} — Lean decl ${cw.lean.decl} (${cw.lean.file}) not locatable`,
        );
      }
    }
    if (leanStatement === null) continue; // no components, no single decl → note-only
    const refDefs = await unfoldReferencedDefs(leanStatement);
    refDefsByObjId.set(e.obj_id, refDefs);
    const citedDependencies = citedTextByObjId.get(e.obj_id) ?? "(none — no Lean premise may be erased)";
    const key = hashEnvBody(`${e.body}|${mapping}|${leanStatement}|${refDefs}|citation-erasure-v1|equivalence-v2|${citedDependencies}`); // why: Lean edits, trust-boundary edits, or a verdict-POLICY change (v2 = over-assumption is drift) must invalidate verdicts.
    if (cache[e.obj_id]?.key === key && cache[e.obj_id].verdict === "faithful") continue;
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
          prompt: await presentationPrompt("p3_equivalence_batch", { statements_block: block, notation_table: notation }),
          cwd: repoRoot,
          reasoningEffort: effort,
          leanLsp: true,
        }),
      )) as { results?: { obj_id?: string; verdict?: string; detail?: string }[] } | null;
      for (const r of parsed?.results ?? []) {
        if (r.obj_id && (r.verdict === "faithful" || r.verdict === "drift")) {
          batchVerdicts.set(r.obj_id, { verdict: r.verdict, detail: r.detail });
        }
      }
    } catch {
      /* group falls through to individual calls */
    }
  });

  const refineRunner: RefineRunner = async (c) => {
    const raw = (await deps.runCodex({
        prompt: await presentationPrompt("p3_refine_statement", {
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
  const audited = await mapLimit(statements, AUDIT_CONCURRENCY, async (s) => ({
    s,
    v0: batchVerdicts.get(s.obj_id) ?? (await equivalence(s)),
  }));
  for (const { s, v0 } of audited) cache[s.obj_id] = { key: s.cacheKey, verdict: v0.verdict, detail: v0.detail };
  // Phase 2 — refine the drifting statements in PARALLEL (refineStatement is PURE; writes are serialized).
  const refinedResults = await mapLimit(
    audited.filter(({ v0 }) => v0.verdict !== "faithful"),
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
  for (const { s, refined } of refinedResults) {
    if (refined.body.trim() !== s.envBody.trim()) {
      // Persist the refiner's BEST attempt (faithful or not) into the source of truth — a
      // tightened-but-still-drifting body is a better starting point for the next re-audit than the
      // stale original. Update block.body + body_hash; re-derive the read-only .tex below.
      const blk = layerSrc.blocks.find((b) => b.obj_id === s.obj_id);
      if (blk) {
        blk.body = refined.body.trim();
        blk.body_hash = hashBody(blk.body);
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
        key: hashEnvBody(`${refined.body}|${s.mapping}|${s.leanStatement}|${refDefsByObjId.get(s.obj_id) ?? ""}|citation-erasure-v1|equivalence-v2|${s.citedDependencies ?? ""}`), // why: refined faithful verdict is tied to the exact Lean source, trust boundary, and verdict policy audited.
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
    io.state.notes.push("P1: persisted refined statement(s) to the bank graph (nl.frozen_body) — a re-run now stays tight.");
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
export async function runProofAudit(
  io: StageIO,
  proofTargets: { obj_id: string; isMain: boolean; lean: { file: string; decl: string } }[],
): Promise<{ refined: Map<string, string>; problems: LintProblem[] }> {
  const { deps, repoRoot } = io.ctx;
  const leanSubdir = io.bank.leanSubdir;
  const notation = parseOutline(await readFile(join(io.outDir, "outline.md"), "utf8")).notation;
  const reviewsPath = join(io.outDir, "reviews.jsonl");
  const leanSource = leanSourceReader(repoRoot, leanSubdir);
  const unfoldReferencedDefs = await buildRefDefUnfolder(repoRoot, leanSubdir, leanSource);

  // Verdict cache keyed by (proof body, decl pointer): a proof already judged faithful is skipped.
  const cachePath = join(io.outDir, "proof_audit_cache.json");
  const cache: Record<string, { key: string; verdict: string; issues?: string[] }> = JSON.parse(
    await readFile(cachePath, "utf8").catch(() => "{}"),
  );
  repairLatexStringsDeep(cache);
  const saveCache = () => writeJsonAtomic(cachePath, cache); // why: proofAudit workers save concurrently under mapLimit — interleaved plain writes can corrupt the cache.

  const proofAudit = async (p: { obj_id: string; proofTex: string; leanPointer: string; leanProofSource: string; leanProofCacheSource: string; notationTable: string; tier: "main" | "auxiliary" }) => {
    const key = hashEnvBody(`${p.proofTex}|${p.leanPointer}|${p.leanProofCacheSource}|${p.notationTable}`);
    const hit = cache[p.obj_id];
    const cacheable = p.leanProofCacheSource.length > 0;
    if (cacheable && hit?.key === key) return { verdict: hit.verdict, issues: hit.issues };
    const v = (await ask(
      deps.runCodex({
        prompt: await presentationPrompt("p3_proof_audit", {
          obj_id: p.obj_id,
          proof_tex: p.proofTex,
          lean_proof_source: `${p.leanPointer}\n\nLean excerpt:\n${p.leanProofSource || "(snippet unavailable — read the file via tools)"}`,
          notation_table: p.notationTable,
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
    const raw = (await deps.runCodex({
        prompt: await presentationPrompt("p3_refine_proof", {
          obj_id: c.obj_id,
          proof_tex: c.envBody,
          lean_proof_source: c.leanPointer,
          referenced_defs: refDefsByObjId.get(c.obj_id) || "(none indexed — read the Lean via your tools)",
          audit_issues: c.driftDetail,
          notation_table: notation,
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
    const leanPointer = `file: ${join(repoRoot, leanSubdir, pt.lean.file)}\ndeclaration: ${pt.lean.decl}\nRead the file with your tools; do not guess its contents.`;
    // Best-effort def unfold for the refiner: extract the decl snippet, then unfold its referenced defs.
    let leanProofSource = "";
    let leanProofCacheSource = "";
    try {
      const fullLeanSource = await leanSource(pt.lean.file);
      const exactDecl = extractFullDeclSource(fullLeanSource, pt.lean.decl, 0);
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
      notationTable: notationForArtifact(notation, `${proofTex}\n${leanProofSource}`),
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
    const newBody = r.body.trim();
    refined.set(pt.obj_id, newBody);
    if (newBody !== pt.proofTex) {
      await writeFile(join(io.outDir, "proofs", `${pt.obj_id}.tex`), newBody + "\n", "utf8");
      await appendDriftReport(io.outDir, `${pt.obj_id} (proof)`, pt.proofTex, newBody, r.rounds, r.note);
    }
    await appendFile(
      reviewsPath,
      JSON.stringify({ kind: "proof-refine", obj_id: pt.obj_id, rounds: r.rounds, faithful: r.faithful, note: r.note }) + "\n",
      "utf8",
    );
    if (!r.faithful) {
      problems.push({ gate: "proof-audit", detail: `${pt.obj_id}: ${r.detail ?? "unfaithful"}` });
      io.state.notes.push(
        `P2: proof ${pt.obj_id} refined toward Lean (${r.rounds} round(s)); STILL unfaithful — best attempt persisted, will halt for adjudication`,
      );
    }
  }
  await saveCache();
  return { refined, problems };
}
