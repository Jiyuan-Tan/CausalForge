import { readFile, appendFile } from "node:fs/promises";
import { MODELS } from "../models.js";
import { existsSync } from "node:fs";
import path from "node:path";
import { applyVerdictsToGraph } from "../graph/refresh.js";
import { reviewTargets, convergenceTargets, incrementalSymbolRows } from "../graph/review_scope.js";
import { renderDependencyBlock, type GraphSkeletonRow } from "../graph/skeleton.js";
import { nodeIdToObjId } from "../graph/from_note.js";
import { statementHash } from "../graph/hash.js";
// Generic Lean-source utility (decl-snippet extractor) — a dependency-free leaf, shared with
// causalsmith's P3 equivalence gate. The reviewer embeds the EXTRACTED Lean text per target so the
// model compares actual code against the NL (instead of being handed decl names + file paths to
// self-fetch for 25 targets — the skim that let the a1 over-claim slip through).
import { extractDeclSnippet } from "../presentation/lean_extract.js";
import { buildSymbolClusters, parseLeanDecls } from "./crosswalk.js";
import { resolveCitedTarget, type CitedMatchTarget } from "./citation_fetch.js";
import { PlanSchema, type Citation, type Plan } from "./plan/schema.js";
import { CoreSchema } from "../discovery/core/schema.js";
import { citedEvidenceHash, deliveryEvidenceHash } from "./delivery_audit.js";
import { planPath, promptPath } from "../paths.js";
import type { CitedReviewReceipt, DeliveryReviewReceipt } from "../types.js";
import { isUndeliveredNode, type FormalizationGraph } from "../graph/types.js";
import type { CodexRunInput } from "../shared/codex.js";
import type { ClaudeRunInput } from "../workers/claude.js";
import { dispatchAgent, dispatchClaudeAgent } from "../framework/agent_dispatch.js";
import {
  gradeReviewerOutput,
  mapLimit,
  mergeOutputs,
  normalizeReviewerObjId,
  parseJsonObject,
  resolveVerdictIds,
  symbolInScope,
  toVerdictArray,
  verdictClass,
  type ReviewerOutput,
  type ReviewerResult,
} from "./reviewer_verdicts.js";

/** Max concurrent reviewer agents (one codex — or codex+claude in convergence — per target). Mirrors
 *  causalsmith's P3 equivalence gate: one FOCUSED agent per object beats handing a single agent the
 *  whole batch and trusting its internal attention split (which satisfices and skims). 6 keeps the
 *  process/file-handle count well under the cluster caps even when convergence doubles the per-unit calls. */
const REVIEW_CONCURRENCY = 6;

/**
 * The unified faithfulness gate over the dirty frontier. Reviews frozen-theorem statement drift + new assumptions in any frozen theorem's
 * uses-closure, writes verdicts back to node.review, and reports blocking findings / escalation.
 * `delta` mode runs a single reviewer; `convergence` runs dual (Codex + Claude) and merges.
 */
export async function runReviewer(args: {
  ctx: { repoRoot: string; qid: string; specialization: string };
  deps: {
    runCodex: (o: CodexRunInput) => Promise<{ stdout: string; stderr: string }>;
    runClaude?: (o: ClaudeRunInput) => Promise<string>;
  };
  graph: FormalizationGraph;
  skeleton: GraphSkeletonRow[];
  dirty: string[];
  hashes: Record<string, string>;
  mode: "delta" | "convergence";
  /** Absolute path to the Lean module dir — used to extract each target's actual Lean decl text
   *  into the prompt (so the model compares real code vs NL, not decl-name pointers). */
  leanDir?: string;
  // AUDIT-FORM: texPath is still passed by bin/formalization callers, but reviewer prompt construction does not consume it.
  texPath?: string;
  corePath?: string;
  promptPath?: string;
  /** If set, append each call's targets + raw model output(s) to `<debugLogDir>/_reviewer_calls.log`
   *  for observability (diagnosing reviewer-output parse issues + reasoning cost). */
  debugLogDir?: string;
}): Promise<ReviewerResult> {
  // Delta = the incremental dirty/not-cleared frontier; convergence (final F4) = the FULL frozen
  // surface unconditionally, so the dual-model gate re-verifies headline claims even when delta
  // reviews already marked them matched (otherwise it would run with empty targets, vacuously).
  const { statementTargets, assumptionTargets, definitionTargets, lemmaTargets, deliveryTargets } =
    args.mode === "convergence" ? convergenceTargets(args.graph) : reviewTargets(args.graph, args.dirty);
  const deliveryObjIds = new Set(deliveryTargets.map(nodeIdToObjId));
  const targetObjIds = new Set(
    [...statementTargets, ...definitionTargets, ...assumptionTargets, ...lemmaTargets, ...deliveryTargets].map(nodeIdToObjId),
  );
  const targetRows = args.skeleton.filter((r) => targetObjIds.has(r.obj_id));
  const rowIds = new Set(targetRows.map((row) => row.obj_id));
  const missingRows = [...targetObjIds].filter((id) => !rowIds.has(id));
  if (missingRows.length > 0) {
    return {
      graph: args.graph,
      ok: false,
      escalate: { kind: "missing-review-target", reason: `review skeleton omitted required target(s): ${missingRows.join(", ")}` },
      blocking: missingRows,
      driftNotes: {},
      substrateGates: [],
      deliveryReviewReceipts: [],
    };
  }

  const failReview = (kind: string, reason: string, blocking: string[] = [...targetObjIds]): ReviewerResult => ({
    graph: args.graph,
    ok: false,
    escalate: { kind, reason },
    blocking,
    driftNotes: {},
    substrateGates: [],
    deliveryReviewReceipts: [],
  });
  let typedCore: ReturnType<typeof CoreSchema.parse> | null = null;
  if (args.corePath) {
    try {
      typedCore = CoreSchema.parse(JSON.parse(await readFile(args.corePath, "utf8")));
    } catch (err) {
      return failReview(
        "missing-review-evidence",
        `typed core could not be read/parsed: ${err instanceof Error ? err.message : String(err)}`,
      );
    }
  }

  // Do NOT short-circuit past the SYMBOL tier just because the node frontier is clean: an in-scope core
  // symbol that is UNTAGGED / never-reviewed / previously non-passing is unfinished work the pipeline
  // must keep surfacing until it is tagged (else a settled node graph silently "covers" a tagging gap
  // forever). Only checked when there are no node targets — otherwise the review runs regardless.
  let needsSymbolReview = false;
  if (targetRows.length === 0 && typedCore && args.leanDir) {
    try {
      const inScope = (typedCore.symbols ?? [])
        .filter(symbolInScope)
        .map((s) => ({ name: s.name as string, space: (s.space || s.type) as string }));
      if (inScope.length) {
        const sr = args.graph.symbolReview ?? {};
        // Build the clusters (file reads only, no model call) so we can detect a CORRUPT pass — an
        // untagged symbol (empty cluster) wrongly recorded `matched`/`equivalent`. Without this, a
        // settled node graph would short-circuit and cover such a gap forever.
        const clusters = await buildSymbolClusters(args.leanDir, inScope);
        needsSymbolReview = clusters.some((c) => {
          const e = sr[`sym:${c.symbol}`];
          if (!e || /untagged/i.test(e.verdict) || verdictClass(e.verdict) !== "pass") return true;
          return !c.members.length; // empty cluster ⇒ can only be `untagged`; a stored pass is corrupt
        });
      }
    } catch (err) {
      return failReview(
        "missing-review-evidence",
        `symbol pre-review cluster scan failed: ${err instanceof Error ? err.message : String(err)}`,
      );
    }
  }
  // Nothing to review (delta pass, every frozen node matched AND every in-scope symbol tagged+matched)
  // → return `ok` WITHOUT spending a model call. Convergence always has the frozen surface.
  if (targetRows.length === 0 && !needsSymbolReview) {
    return { graph: args.graph, ok: true, escalate: null, blocking: [], driftNotes: {}, substrateGates: [], deliveryReviewReceipts: [] };
  }

  // repoRoot IS the CausalSmith package dir, so resolve via the shared promptPath helper
  // (tools/src/<phase>/prompts/<subfolder>/<name>). A hardcoded "CausalSmith/tools/..." prefix
  // double-nests to CausalSmith/CausalSmith/... → file missing → base silently empty.
  const promptFile = args.promptPath ?? promptPath(args.ctx.repoRoot, "proof_reviewer.txt");
  if (!existsSync(promptFile)) return failReview("missing-review-evidence", `reviewer prompt missing: ${promptFile}`);
  const base = await readFile(promptFile, "utf8");
  if (!base.trim()) return failReview("missing-review-evidence", `reviewer prompt is empty: ${promptFile}`);

  // Embed each target's NL (F1 note block, from the graph) AND its EXTRACTED Lean text side by side,
  // exactly like causalsmith's P3 equivalence gate — so the model compares real code against the NL
  // instead of being handed a decl name + file paths to self-fetch for the whole batch. The single
  // overloaded reviewer that skimmed 25 pointer-targets is what let the a1 over-claim pass.
  const nlByObjId = new Map(
    args.graph.nodes.map((n) => [nodeIdToObjId(n.id), n.nl?.statement?.trim() ?? ""]),
  );
  const leanCache = new Map<string, string>();
  const leanSrc = async (file: string): Promise<string> => {
    if (!args.leanDir) return "";
    if (!leanCache.has(file)) {
      leanCache.set(file, await readFile(path.join(args.leanDir, file), "utf8").catch(() => ""));
    }
    return leanCache.get(file)!;
  };
  // ONE-HOP DEF INDEX: name → location of every research def/abbrev/structure, so a target's
  // extracted Lean (e.g. a `LawClass` bundle whose fields are `WellFormedLaw P`, `OverlapDecay …`)
  // can have those referenced from-note definitions auto-UNFOLDED onto the page. Without this the
  // reviewer sees only field TYPE NAMES and must self-fetch each body — the "judge by name" gap.
  const inlineKinds = new Set(["def", "abbrev", "structure"]);
  const declByName = new Map<string, { file: string; line: number; declKind: string }>();
  const fileDeclLines = new Map<string, number[]>(); // file → sorted decl start lines (all kinds)
  if (args.leanDir) {
    for (const d of await parseLeanDecls(args.leanDir, { includeLemmas: true })) {
      if (inlineKinds.has(d.declKind) && !declByName.has(d.name)) {
        declByName.set(d.name, { file: d.file, line: d.line, declKind: d.declKind });
      }
      if (!fileDeclLines.has(d.file)) fileDeclLines.set(d.file, []);
      fileDeclLines.get(d.file)!.push(d.line);
    }
    for (const arr of fileDeclLines.values()) arr.sort((a, b) => a - b);
  }
  // CITED match targets: load the F1 plan, find `gate_class:"cited"` nodes, and resolve each against
  // its `cite:` source (verbatim-first, best-effort arXiv fetch). These nodes are `kind:"assumption"`
  // defs, so they review IN THE ASSUMPTION TIER — the cited block below is appended to their target
  // prompt so the same shallow-tier call that audits assumptions also runs the source-match.
  const citedObjIds = new Set(
    args.graph.nodes
      .filter((node) => node.gate?.gate_class === "cited" && !isUndeliveredNode(node))
      .map((node) => nodeIdToObjId(node.id)),
  );
  const citedByObjId = new Map<string, {
    nodeId: string;
    leanName: string;
    target: CitedMatchTarget;
    citation: Citation;
  }>();
  let citedPlan: Plan | null = null;
  try {
    const pf = planPath(args.ctx.repoRoot, args.ctx.qid, args.ctx.specialization);
    if (existsSync(pf)) {
      const parsed = PlanSchema.safeParse(JSON.parse(await readFile(pf, "utf8")));
      if (parsed.success) {
        citedPlan = parsed.data;
        const citById = new Map(parsed.data.citations.map((c) => [c.id, c] as const));
        for (const [id, n] of Object.entries(parsed.data.nodes)) {
          if (n.gate_class !== "cited" || n.delivery_status === "undelivered" || !n.source) continue;
          const cit = citById.get(n.source);
          // Key by the obj-id alias — skeleton rows are keyed by `nodeIdToObjId(id)`, not the raw
          // plan/core node id, so we must match the same form (else the cited block never injects).
          if (cit) citedByObjId.set(nodeIdToObjId(id), {
            nodeId: id,
            leanName: n.lean_name,
            target: await resolveCitedTarget(cit),
            citation: cit,
          });
        }
      }
    }
  } catch {
    /* no plan / parse failure → no cited augmentation; gated behavior is unchanged */
  }
  // GATED substrate-gate EXEMPTION: a from-note theorem/lemma/def whose Lean statement carries a
  // registered `gate_class:"gated"` node as a hypothesis is a sorry-free CONDITIONAL on disclosed
  // substrate-debt (registered via bin/gate.ts, tracked in SUBSTRATE_DEBT.md). Both the F2.5 delta
  // review and the F4 convergence review must EXEMPT those hypotheses from the equivalence /
  // added-premise / laundering check — their presence is expected + sanctioned, not drift. We build
  // consumer-objId → gated-dep list from the graph's dependency edges (gate.ts adds proof-uses edges
  // consumer→gate). Anti-laundering stays the ORCHESTRATOR's job (gate.ts requires the gate be an
  // INPUT fact, never the consumer's conclusion); the reviewer no longer re-adjudicates a gated hyp.
  const gatedByObjId = new Map<string, { objId: string; decl: string | null; nl: string }[]>();
  {
    const nodeById = new Map(args.graph.nodes.map((n) => [n.id, n] as const));
    for (const e of args.graph.edges) {
      if (e.kind !== "proof-uses" && e.kind !== "statement-uses") continue;
      const g = nodeById.get(e.to);
      if (!g || g.kind !== "gate" || g.gate?.gate_class !== "gated") continue;
      const consumerObjId = nodeIdToObjId(e.from);
      const gObjId = nodeIdToObjId(g.id);
      const list = gatedByObjId.get(consumerObjId) ?? [];
      if (!list.some((x) => x.objId === gObjId)) {
        list.push({ objId: gObjId, decl: g.lean?.decl_name ?? null, nl: g.nl?.statement?.trim() ?? "" });
      }
      gatedByObjId.set(consumerObjId, list);
    }
  }
  // UNDELIVERED ROLE AUDIT (F4 only): omission legality is a semantic/presentation judgment, not a
  // Lean-statement judgment. Embed the core's own contribution framing and the graph's complete
  // reverse uses-closure so BOTH convergence reviewers can independently decide whether the node is
  // genuinely secondary (or cited), rather than trusting the declared `delivery.role` field. A node
  // can be mathematically substantial or locally `crux:true` and still be secondary; conversely, a
  // declared `secondary` label cannot hide a headline, headline-support, or a dependency of anything
  // delivered.
  let coreContributionContext = "(core contribution framing unavailable — fail closed if role cannot be adjudicated)";
  if (typedCore) {
      const showCoreField = (value: unknown): string => {
        if (typeof value === "string") return value.trim() || "(missing)";
        if (value == null) return "(missing)";
        try { return JSON.stringify(value); } catch { return String(value); }
      };
      coreContributionContext = [
        `TLDR: ${showCoreField(typedCore.tldr)}`,
        `HONEST_SCOPE: ${showCoreField(typedCore.honest_scope)}`,
        `PROJECT_JUSTIFICATION: ${showCoreField(typedCore.project_justification)}`,
      ].join("\n");
  }
  const nodeByIdForDelivery = new Map(args.graph.nodes.map((n) => [n.id, n] as const));
  const reverseUses = new Map<string, string[]>();
  for (const e of args.graph.edges) {
    if (e.kind !== "statement-uses" && e.kind !== "proof-uses") continue;
    const xs = reverseUses.get(e.to) ?? [];
    xs.push(e.from);
    reverseUses.set(e.to, xs);
  }
  const deliveredConsumersOf = (id: string): string[] => {
    const seen = new Set<string>();
    const stack = [...(reverseUses.get(id) ?? [])];
    const delivered: string[] = [];
    while (stack.length) {
      const cur = stack.pop()!;
      if (seen.has(cur)) continue;
      seen.add(cur);
      const n = nodeByIdForDelivery.get(cur);
      if (n && !isUndeliveredNode(n)) delivered.push(`${n.id} (${n.kind})`);
      stack.push(...(reverseUses.get(cur) ?? []));
    }
    return delivered.sort();
  };
  let evidenceFailure: string | null = null;
  const targetBlocks = await Promise.all(
    targetRows.map(async (r) => {
      const nl = nlByObjId.get(r.obj_id) || r.title || "(no NL on the graph node)";
      if (deliveryObjIds.has(r.obj_id)) {
        const n = args.graph.nodes.find((x) => nodeIdToObjId(x.id) === r.obj_id);
        const consumers = n ? deliveredConsumersOf(n.id) : [];
        const cited = n?.kind === "gate" && n.gate?.gate_class === "cited";
        return [
          `### ${r.obj_id} (undelivered-delivery-role audit — NOT a Lean statement/proof review)`,
          `NODE CLAIM: ${nl}`,
          `DECLARED (evidence only; DO NOT trust as the verdict): status=${n?.delivery?.status ?? "missing"}; role=${n?.delivery?.role ?? "missing"}; kind=${n?.kind ?? r.kind}; cited=${cited}; reason=${n?.delivery?.reason ?? "missing"}`,
          "CORE CONTRIBUTION EVIDENCE (authoritative framing; decide whether the claim is a headline or headline-support from this content, not from the declared role):",
          coreContributionContext,
          "DELIVERED REVERSE USES-CLOSURE (all delivered statement/proof consumers, direct or transitive):",
          consumers.length ? consumers.map((x) => `  - ${x}`).join("\n") : "  (none)",
          "AUDIT RULE: emit one statement_verdicts entry for this obj_id. `matched` ONLY if you independently conclude all three: (1) it is a genuinely secondary theorem OR a cited node; (2) it is neither a headline nor headline-support; and (3) no delivered result consumes it directly or transitively. The node's proved status, mathematical size, or plan `crux` flag alone does not make it a headline; judge its role in the core's advertised contribution. Emit `drift` if any condition fails or the evidence is ambiguous. On drift set escalate.kind=`delivery-role-conflict` and explain which advertised contribution or delivered consumer makes omission illegal. Never request a Lean declaration merely because this audit target has no Lean anchor.",
        ].join("\n");
      }
      let lean = "(no Lean anchor — judge against the NL + sources)";
      const graphNode = args.graph.nodes.find((node) => nodeIdToObjId(node.id) === r.obj_id);
      const externalReuse = graphNode?.provenance === "library";
      if (!r.lean && !externalReuse) {
        evidenceFailure ??= `${r.obj_id}: local delivered target has no Lean anchor`;
      }
      if (r.lean?.decl) {
        const src = await leanSrc(r.lean.file || "Basic.lean");
        if (src) {
          // A pure-reuse node anchors to a Causalean decl (e.g. `Causalean.Stat.IIDSample`)
          // whose source is NOT in the research file — `extractDeclSnippet` THROWS on a
          // miss, so guard it: fall back to NL-judgment against the cited decl rather than
          // crashing the loop. (Also covers a stale/short-vs-qualified name mismatch.)
          try {
            const snippet = extractDeclSnippet(src, r.lean.decl, r.lean.line ?? 0);
            if (snippet) lean = snippet;
            else if (!externalReuse) evidenceFailure ??= `${r.obj_id}: decl ${r.lean.decl} not found in ${r.lean.file}`;
          } catch (err) {
            if (!externalReuse) {
              evidenceFailure ??= `${r.obj_id}: failed to extract ${r.lean.decl} from ${r.lean.file}: ${err instanceof Error ? err.message : String(err)}`;
            }
          }
        } else if (!externalReuse) {
          evidenceFailure ??= `${r.obj_id}: Lean source file missing or unreadable: ${r.lean.file || "Basic.lean"}`;
        }
      }
      // ONE-HOP UNFOLD: append the bodies of the from-note def/structure decls this target's Lean
      // REFERENCES (its bundle fields / named sub-defs), so the reviewer judges against the actual
      // definitions instead of trusting a field's type NAME (e.g. `overlapDecay : OverlapDecay P …`
      // is not self-evidently the paper's tail inequality — its body must be on the page). One hop
      // only (referenced-of-referenced is not expanded); capped to keep the prompt bounded.
      let referencedBlock = "";
      if (args.leanDir && r.lean?.decl && lean && !lean.startsWith("(")) {
        // Scan the target decl's PRECISE span (its start line → next decl's line) for referenced
        // names — NOT the displayed `lean` snippet, which `extractDeclSnippet` can over-extract into
        // the following decl (pulling in that decl's dependencies). Then strip comments so docstrings
        // don't inject names; field TYPES on code lines (`wf : WellFormedLaw P`) are what we unfold.
        const tFile = r.lean.file || "Basic.lean";
        const tLine = r.lean.line ?? 0;
        const starts = fileDeclLines.get(tFile) ?? [];
        const selfStart = [...starts].reverse().find((l) => l <= tLine + 1) ?? tLine;
        const nextLine = starts.find((l) => l > selfStart) ?? Number.MAX_SAFE_INTEGER;
        const span = (await leanSrc(tFile)).split(/\r?\n/).slice(Math.max(0, selfStart - 1), nextLine - 1).join("\n");
        const code = span.replace(/\/-[\s\S]*?-\//g, " ").replace(/--[^\n]*/g, " ");
        const names = new Set(code.match(/[A-Za-z_][A-Za-z0-9_']*/g) ?? []);
        names.delete(r.lean.decl);
        const inlined: string[] = [];
        for (const nm of names) {
          if (inlined.length >= 12) break;
          const loc = declByName.get(nm);
          if (!loc) continue;
          const src = await leanSrc(loc.file);
          if (!src) continue;
          try {
            const snip = extractDeclSnippet(src, nm, loc.line);
            if (snip) inlined.push(`-- ${nm} (${loc.declKind}) in ${loc.file}\n${snip}`);
          } catch {
            /* skip a decl whose body can't be extracted */
          }
        }
        if (inlined.length) {
          referencedBlock =
            "\nREFERENCED DEFINITIONS (one-hop unfold of the named defs/fields above — judge against THESE bodies, do not assume a field is faithful from its type name):\n```lean\n" +
            inlined.join("\n\n") +
            "\n```";
        }
      }
      // CITED nodes: append the source-match block. This node is ASSUMED (not proven); the task is to
      // verify the Lean def faithfully ENCODES the cited statement of record, and emit a `cited-*`
      // verdict into substrate_gates. Runs in this same assumption-tier call.
      const cited = citedByObjId.get(r.obj_id);
      const okStatus = cited?.target.mode === "fetched" ? "cited-verified" : "cited-verified-attested";
      const citedBlock = cited
        ? [
            "",
            `CITED SOURCE TO MATCH — this is a \`gate_class:"cited"\` node: it is ASSUMED, never proven here. Verify the LEAN def above faithfully ENCODES the statement of record below (${cited.citation.authors} ${cited.citation.year}, ${cited.citation.id} @ ${cited.citation.locator}):`,
            cited.target.mode === "unverifiable"
              ? `(no fetchable source and no verbatim statement — emit check_status "cited-source-unverifiable")`
              : cited.target.mode === "fetched"
                // Fetched mode returns the paper's FULL TeX source (all .tex members concatenated);
                // a head slice is preamble/abstract and near-never contains the cited statement.
                // Give a larger window and an HONEST fallback: statement-not-in-excerpt must grade
                // unverifiable, never a guessed verified/mismatch against unrelated text.
                ? `(EXCERPT of the fetched paper's TeX SOURCE — theorem numbers are usually auto-generated, so "${cited.citation.locator}" may not appear literally; locate the statement of record by its content. If it is NOT present in this excerpt, emit check_status "cited-source-unverifiable" — do NOT infer a verdict from surrounding text.)\n` +
                  "```\n" + cited.target.text.slice(0, 12000) + "\n```"
                : "```\n" + cited.target.text.slice(0, 4000) + "\n```",
            `SELF-CONTAINEDNESS: the def must ENCODE every distinguishing hypothesis the cited statement relies on — in particular any regularity/model class that separates it from this paper's own class — as a defined predicate or explicit binder, NOT as a free abstract variable nor an undefined class named only in prose/the docstring. A cited claim about "the risk over class X" whose X is not a defined object is not self-contained.`,
            `Emit ONE substrate_gates entry: { name:"${r.lean?.decl ?? r.obj_id}", gate_class:"cited", source:{cite_id:"${cited.citation.id}", locator:"${cited.citation.locator}"}, check_status }. check_status = "${okStatus}" if the def faithfully AND self-containedly encodes the statement; "cited-mismatch" if the quantifiers/constants/direction differ or it is vacuous; "cited-underspecified" if a distinguishing hypothesis/class is named but not encoded (a free variable or undefined class). Both cited-mismatch and cited-underspecified BLOCK banking.`,
          ].join("\n")
        : "";
      // GATED EXEMPTION block: list this target's registered `gated` substrate-gate hypotheses and
      // instruct the reviewer to judge the statement MODULO them (do not treat them as added premises
      // / drift / content-gate). Applies in both delta (F2.5) and convergence (F4) modes.
      const gatedDeps = gatedByObjId.get(r.obj_id) ?? [];
      const gatedBlock = gatedDeps.length
        ? [
            "",
            "GATED SUBSTRATE-DEBT HYPOTHESES — the Lean statement above is a sorry-free CONDITIONAL on the",
            "disclosed substrate-gate(s) listed below. They are ASSUMED inputs (registered via bin/gate.ts,",
            "recorded in SUBSTRATE_DEBT.md), NOT part of the paper's stated hypotheses. EXEMPT them: judge the",
            "statement MODULO these binders — their presence as `_of_gate`-style hypotheses is EXPECTED and",
            "SANCTIONED, so do NOT flag them as an added premise, drift, laundering, or content-gate, and do",
            "NOT require the note to state them. Judge equivalence of the REMAINING (non-gated) statement only.",
            ...gatedDeps.map((d) => `  • ${d.decl ?? d.objId}${d.nl ? ` — ${d.nl}` : ""}`),
          ].join("\n")
        : "";
      return [
        `### ${r.obj_id} (${r.kind}) — Lean anchor: ${r.lean ? `\`${r.lean.decl}\` in ${r.lean.file}` : "(unlinked)"}`,
        `NL (paper statement — the F1 note block; this is what a reader sees):`,
        nl,
        `LEAN (the actual extracted ${r.kind === "definition" || r.kind === "assumption" ? "definition" : "statement"} — judge equivalence against THIS):`,
        "```lean",
        lean,
        "```",
        referencedBlock,
        citedBlock,
        gatedBlock,
      ].filter(Boolean).join("\n");
    }),
  );
  if (evidenceFailure) return failReview("missing-review-evidence", evidenceFailure);

  // SYMBOL CLUSTERS (JSON-side ground truth + the Lean decls that JOINTLY realize each symbol) for the
  // SETUP/ENVIRONMENT check. A symbol's space is typically carried by a CONJUNCTION — a carrier-type
  // structure field (`propensity : 𝒳 → ℝ`) PLUS a predicate that pins its range (`WellFormedLaw`,
  // `Positivity`) — so grading the field decl alone false-flags the faithful carrier idiom as drift.
  // We hand the reviewer each symbol's full `@realizes`-tagged cluster and ask it to judge the
  // CONJUNCTION; `drift` is correct only when the space is constrained NOWHERE. Best-effort.
  let symbolClusterHeader = "";
  let symbolRows: { id: string; row: string }[] = [];
  // sym:id → hash of its `@realizes` cluster for THIS pass. Used to (a) skip matched-and-unchanged
  // symbols in delta mode and (b) persist each reviewed symbol's verdict+hash for the next pass.
  const symbolHashById = new Map<string, string>();
  if (typedCore && args.leanDir) {
    try {
      // Cluster-review only SETUP-WORLD symbols whose space is a proper numeric
      // RANGE/SET ({0,1}, (0,1), [-1,1], [0,1/2], 𝒳×{0,1}×[-1,1], …) — those have a
      // space to VIOLATE at the realization level (the observation/law/policy world).
      // The range regex matches a bracket/brace/paren immediately followed by an
      // optional sign + DIGIT, so it accepts `{0,1}`/`[-1,1]`/`(0,1)` but NOT the
      // bare-type scalars `ℝ_{>=0}`/`ℝ_{>0}` (brace then `>`), `ℝ`, `ℕ` — those carry
      // any constraint via per-theorem hypotheses, which the statement/assumption
      // review already checks (clustering them re-flags the faithful `carrier-ℝ +
      // 0≤α hyp` idiom — the old false-positive class). `role: "derived"` symbols
      // (computed exponents/schedule sequences like h_n, q_n) are likewise excluded:
      // their interval bound is carried by an admissibility lemma, not a world field.
      // Composite/product spaces (`𝒳 × {0,1} × …`) are reviewed via their component symbols, not the
      // tuple; `role:"derived"` schedule sequences (h_n/q_n) carry their bound in a lemma, not a def.
      // `symbolInScope` (module-level) encodes exactly this filter — shared with the pre-review gate so
      // a settled node graph can never "cover" (skip) an in-scope symbol that is still untagged.
      const syms = (typedCore.symbols ?? [])
        .filter(symbolInScope)
        .map((s) => ({ name: s.name as string, space: (s.space || s.type) as string }));
      if (syms.length) {
        const clusters = await buildSymbolClusters(args.leanDir, syms);
        const built = clusters.map((c) => {
          const head = `- sym:${c.symbol} : ${c.space ?? "(no space)"}`;
          const row = !c.members.length
            ? `${head}\n    realized_by: (UNTAGGED — no \`@realizes ${c.symbol}\` tag found. There is NO member to verify against, so the ONLY valid verdict is \`untagged\`: NEVER \`matched\`/\`equivalent\` (that is "verified against nothing", even for a computed quantity — def-by-construction needs a TAGGED def member) and NEVER \`drift\` (a missing tag is a tagging gap, not a mismatch). In your \`note\`, you MUST NAME the specific Lean decl that realizes this symbol — SEARCH the Lean dir (Grep/lean-lsp) for the \`def\` that computes it, the structure field that carries it, or the theorem/def binder/parameter that introduces it, and state the file + decl name. The scaffolder tags EXACTLY what you name, so a vague note ("tag the decls realizing X") is unactionable.)`
            : `${head}\n    realized_by (judge the CONJUNCTION of these):\n${c.members
                .map((m) => `      • ${m.decl} (${m.declKind}) in ${m.file}${m.hint ? `  — ${m.hint}` : ""}`)
                .join("\n")}`;
          const id = `sym:${c.symbol}`;
          const hash = statementHash(row);
          symbolHashById.set(id, hash);
          return { id, row, hash, empty: !c.members.length };
        });
        // INCREMENTAL (delta): review only symbols that are NEW, previously non-passing, or whose cluster
        // changed since the last PASS. `untagged` is NOT a pass for this purpose — a tagging gap is unfinished
        // work that must be re-surfaced every pass until the symbol is tagged (else the pipeline "covers" it:
        // a symbol stuck untagged would be silently skipped forever). Only a genuine `matched`/`equivalent`
        // (against real members) is skipped-when-unchanged. Convergence (F4) reviews ALL symbols regardless.
        const reviewed = incrementalSymbolRows(
          built,
          args.graph.symbolReview,
          args.mode,
          (v) => verdictClass(v) === "pass" && !/untagged/i.test(String(v)),
        );
        // Force-surface any EMPTY-cluster (untagged) symbol the incremental filter would skip: an empty
        // cluster can ONLY be `untagged`, so a stored pass (`equivalent`/`matched`) on it is CORRUPT and
        // must be re-reviewed — this self-heals a symbol wrongly cleared in a prior pass, never covers it.
        const reviewedIds = new Set(reviewed.map((s) => s.id));
        symbolRows = [...reviewed, ...built.filter((b) => b.empty && !reviewedIds.has(b.id))]
          .map((s) => ({ id: s.id, row: s.row }));
        if (symbolRows.length) {
          symbolClusterHeader = [
            "SYMBOL CLUSTER(S) (SETUP/ENVIRONMENT TARGETS). Each core symbol below is shown with its JSON-declared",
            "SPACE and the cluster of Lean decls that JOINTLY realize it (via `@realizes` tags). For EACH, emit ONE",
            "`statement_verdicts` entry keyed `sym:<symbol>`, grading the CONJUNCTION of that symbol's cluster",
            "against the space: `matched` if the members TOGETHER constrain the symbol to its space (a carrier",
            "type like `ℝ`/`Bool` + an accompanying predicate/standing-hypothesis clause IS faithful —",
            "subtypes are NOT required, and are wrong when witness measures must be built over `ℝ`). A member",
            "that is a `def` COMPUTING the symbol realizes its range BY CONSTRUCTION → `matched`; do NOT `drift`",
            "a computed `def` for lacking an explicit subtype/`≥0` clause (its range follows from the formula).",
            "This def-by-construction rule applies ONLY when the cluster HAS a tagged `def` member — a symbol",
            "marked UNTAGGED (no members) is ALWAYS `untagged`, NEVER matched/equivalent-by-construction.",
            "`drift` ONLY if the space is enforced by NO member — a FREE carrier (`A:ℝ`, a field or bound var)",
            "with no constraining predicate anywhere. VERIFY each member's hint against the cited decl in the Lean dir (the hint",
            "is the scaffolder's claim, not ground truth); treat `untagged name-match` members as candidates",
            "to confirm, not as authoritative.",
          ].join("\n");
        }
      }
    } catch (err) {
      return failReview(
        "missing-review-evidence",
        `symbol review cluster construction failed: ${err instanceof Error ? err.message : String(err)}`,
      );
    }
  }

  // Shared prompt HEADER — identical for every per-target call; each unit appends its single target.
  const header = [
    base,
    "",
    "SOURCES (the NL + Lean text is embedded with the target below; open these only to UNFOLD a named",
    "predicate/def the Lean references — e.g. a bundle field `cond_exch : ConditionalExchangeability`",
    "is NOT self-evidently equal to its English name; read the def to see what it actually requires):",
    // The typed core.json is the SINGLE source of truth (the `.tex` is just its deterministic render —
    // not fed here, to avoid double-feeding the same content).
    args.corePath ? `- Typed core.json (the spec — node statements + proof_tex; also the SYMBOL table with each symbol's declared space, for SETUP/ENVIRONMENT TARGETS): ${args.corePath}` : "",
    args.leanDir ? `- Lean directory — for a SETUP/ENVIRONMENT TARGET, the SYMBOL CLUSTER block names each symbol's realizing decls (\`@realizes\` tags); open them here to VERIFY each clause hint against the actual Lean: ${args.leanDir}` : "",
  ].filter(Boolean).join("\n");

  // ── TIERED PER-OBJECT DISPATCH (mirrors causalsmith's P3 equivalence gate) ──
  // The reviewer used to hand ALL targets to one codex and trust it to split attention — the
  // satisficing skim that let the a1 over-claim slip through. Instead fan out by object, with the
  // attention budget tiered by stakes:
  //   • THEOREM (the headline claim)     → its OWN high-effort call; never batched.
  //   • LEMMA                            → high-effort, batched in small groups of ≤3 (load-bearing).
  //   • DEFINITION / ASSUMPTION          → medium-effort, batched ≤5 (cheap structural checks).
  //   • SYMBOL CLUSTER (setup/env)       → medium-effort, batched ≤5.
  // A batch verdict PRE-EMPTS the individual call; anything a batch drops/omits (or any singleton)
  // falls through to its own HIGH-effort individual call — the faithfulness floor (never silent-pass).
  const EMPTY: ReviewerOutput = { status: "ok", statement_verdicts: [], assumption_verdicts: [], substrate_gates: [], escalate: null };

  const idAliases = new Map<string, string>();
  const graphIdByObjId = new Map<string, string>();
  for (const n of args.graph.nodes) {
    const canonical = nodeIdToObjId(n.id);
    graphIdByObjId.set(canonical, n.id);
    for (const alias of [n.id, canonical, (n as { obj_id?: string }).obj_id]) {
      if (alias) idAliases.set(alias, canonical);
    }
  }
  // Every name a verdict may legitimately arrive under: canonical target ids, symbol-row ids,
  // and node aliases. Used to resolve prose-string verdicts at the parse boundary (see
  // resolveVerdictIds) — mergeOutputs cannot recover an obj_id after the fact.
  const recognizedIds = [
    ...new Set([...targetObjIds, ...symbolRows.map((r) => r.id), ...idAliases.keys()]),
  ];

  const deliveryHashByObjId = new Map<string, string>();
  if (deliveryTargets.length > 0) {
    try {
      if (!args.corePath) throw new Error("typed core path is missing");
      const core = CoreSchema.parse(JSON.parse(await readFile(args.corePath, "utf8")));
      const plan = PlanSchema.parse(JSON.parse(await readFile(planPath(args.ctx.repoRoot, args.ctx.qid, args.ctx.specialization), "utf8")));
      for (const id of deliveryTargets) {
        deliveryHashByObjId.set(nodeIdToObjId(id), deliveryEvidenceHash(core, plan, args.graph, id));
      }
    } catch (err) {
      return {
        graph: args.graph,
        ok: false,
        escalate: { kind: "delivery-audit-evidence", reason: `cannot bind F4 delivery review evidence: ${err instanceof Error ? err.message : String(err)}` },
        blocking: [...deliveryObjIds],
        driftNotes: {},
        substrateGates: [],
        deliveryReviewReceipts: [],
      };
    }
  }
  const deliveryReviewReceipts: DeliveryReviewReceipt[] = [];
  const citedReviewReceipts: CitedReviewReceipt[] = [];

  // Self-contained prompt from N target rows (NL+Lean blocks side by side) …
  const targetPrompt = (items: { row: GraphSkeletonRow; block: string }[]): string =>
    [
      header,
      "",
      "TARGET(S) — each shows the NL and the EXTRACTED Lean side by side. Compare them DIRECTLY; you",
      "must still unfold any named sub-def the Lean refers to before deciding equivalence:",
      "",
      items.map((it) => it.block).join("\n\n"),
      "",
      renderDependencyBlock(items.map((it) => it.row)),
      "",
      "Return ONLY the JSON object specified in the prompt.",
    ].filter(Boolean).join("\n");
  // … and from N symbol-cluster rows.
  const symbolPrompt = (rows: { id: string; row: string }[]): string =>
    [header, "", symbolClusterHeader, rows.map((r) => r.row).join("\n"), "", "Return ONLY the JSON object specified in the prompt."]
      .filter(Boolean).join("\n");

  // Run one tier unit. F2.5 is always Codex-only. F4 (convergence) dual-reviews EVERY unit
  // with the Claude peer — the `dualReview` flag on the unit structs records the intended
  // per-tier policy but is deliberately not enforced yet (see `_dualReview` below).
  // A parse failure surfaces a gate-level escalate (no
  // obj_id → routes to the orchestrator, not an F2 re-scaffold of one object); the other units'
  // verdicts still apply.
  const runUnit = async (
    label: string,
    prompt: string,
    effort: "high" | "medium",
    // Reserved, deliberately unused: EVERY convergence unit is dual-reviewed today (the tested
    // contract — see "convergence keeps Claude" in proof_reviewer.test.ts). If F4 credit cost
    // ever demands shedding the Claude peer for routine lemma/symbol tiers, gate on this flag —
    // the unit structs below already carry the intended per-tier values.
    _dualReview: boolean,
    expectedIds: string[],
  ): Promise<ReviewerOutput> => {
    // multiAgent:false — this reviewer fans out ×REVIEW_CONCURRENCY (F2.5/F4/convergence);
    // concurrent codex multi-agent sessions deadlock the shared app-server daemon, and the
    // reviewer prompt explicitly does NOT delegate, so codex's native sub-agents are pure
    // downside here (see CodexRunInput.multiAgent).
    // F2.5 delta + F4 convergence reviewer. Switched codexMechanical (gpt-5.6-terra) → codexKernel
    // (gpt-5.5): 5.6-terra hallucinated non-defects on the crosswalk (misread `∀ᶠ n` as `∀ n`, called a
    // present hypothesis missing, flagged a faithful `0<c→P` antecedent as vacuous), churning futile F2
    // scaffold reroutes. The 5.5 kernel tier is the reliable reviewer for this faithfulness grading.
    // texPath/leanDir are optional on args; drop unset ones rather than logging "undefined".
    const dispatchSources: string[] = [
      promptFile,
      ...(args.texPath ? [args.texPath] : []),
      args.corePath ?? "(no core)",
      ...(args.leanDir ? [args.leanDir] : []),
    ];
    const codex = await dispatchAgent({
      ctx: args.ctx,
      deps: { runCodex: args.deps.runCodex },
      stage: args.mode === "convergence" ? "4" : "2.5",
      label: `F${args.mode === "convergence" ? "4 convergence" : "2.5 delta"} reviewer :: ${label}`,
      prompt,
      promptSources: dispatchSources,
      model: MODELS.codexKernel,
      reasoningEffort: effort,
      multiAgent: false,
    });
    if (args.mode === "convergence" && !args.deps.runClaude) {
      return { escalate: { kind: "missing-peer-reviewer", reason: `F4 requires both reviewers; Claude runner missing for ${label}` } };
    }
    let claudeRaw: string | null = null;
    if (args.mode === "convergence" && args.deps.runClaude) {
      claudeRaw = await dispatchClaudeAgent({
        ctx: args.ctx,
        deps: { runClaude: args.deps.runClaude },
        stage: "4",
        label: `F4 convergence claude reviewer :: ${label}`,
        promptSources: dispatchSources,
        input: { prompt, cwd: args.ctx.repoRoot, model: MODELS.claudeMain, allowedTools: ["Read", "Grep", "Glob"] },
      });
    }
    if (args.debugLogDir) {
      const log =
        `\n===== reviewer ${args.mode}/${claudeRaw ? "dual" : "codex"} :: ${effort} :: ${label} =====\n` +
        `--- codex stdout ---\n${codex.stdout}\n` +
        (claudeRaw ? `--- claude stdout ---\n${claudeRaw}\n` : "");
      await appendFile(path.join(args.debugLogDir, "_reviewer_calls.log"), log).catch(() => {});
    }
    try {
      const enforceExpected = (peer: ReviewerOutput, reviewer: "codex" | "claude"): ReviewerOutput => {
        const graded = gradeReviewerOutput(peer, expectedIds, idAliases);
        const forced = graded.rows
          .filter((row) => row.verdict === "drift")
          .map((row) => ({ obj_id: row.obj_id, verdict: "drift" as const, note: row.note }));
        for (const objId of expectedIds.filter((id) => deliveryObjIds.has(id))) {
          const row = graded.rows.find((candidate) => candidate.obj_id === objId);
          const nodeId = graphIdByObjId.get(objId);
          const evidenceHash = deliveryHashByObjId.get(objId);
          if (nodeId && evidenceHash) {
            deliveryReviewReceipts.push({
              node_id: nodeId,
              reviewer,
              verdict: row?.verdict === "equivalent" ? "matched" : "drift",
              evidence_hash: evidenceHash,
              ...(row?.note ? { note: row.note } : {}),
            });
          }
        }
        for (const objId of expectedIds.filter((id) => citedObjIds.has(id))) {
          const cited = citedByObjId.get(objId);
          const sourceRows = (peer.substrate_gates ?? []).filter((gate) => {
            if (gate.gate_class !== "cited") return false;
            const names = new Set([
              objId,
              cited?.nodeId,
              cited?.leanName,
              args.graph.nodes.find((node) => nodeIdToObjId(node.id) === objId)?.lean.decl_name ?? undefined,
            ].filter((name): name is string => Boolean(name)));
            const short = String(gate.name ?? "").split(".").at(-1) ?? "";
            return names.has(String(gate.name ?? "")) || [...names].some((name) => name.split(".").at(-1) === short);
          });
          const exact = cited
            ? sourceRows.filter((gate) =>
                gate.source?.cite_id === cited.citation.id && gate.source?.locator === cited.citation.locator)
            : [];
          const row = exact.length === 1 ? exact[0] : undefined;
          const status = row?.check_status ?? (cited ? "missing" : "missing-plan-citation");
          if (cited) {
            citedReviewReceipts.push({
              node_id: cited.nodeId,
              reviewer,
              check_status: status,
              cite_id: cited.citation.id,
              locator: cited.citation.locator,
              // Rebound to the post-verdict graph before returning; this provisional value is
              // never persisted and exists only to keep the receipt structurally complete.
              evidence_hash: citedEvidenceHash(citedPlan!, args.graph, cited.nodeId),
            });
          }
          const acceptable = status === "cited-verified" || status === "cited-verified-attested" || status === "cited-source-unverifiable";
          if (!cited || exact.length !== 1 || !acceptable) {
            const detail = !cited
              ? "plan/source metadata for cited target is missing"
              : exact.length !== 1
                ? `expected exactly one cited source-match row for ${cited.citation.id} @ ${cited.citation.locator}, found ${exact.length}`
                : `cited source-match verdict is ${status}`;
            forced.push({ obj_id: objId, verdict: "drift", note: `${reviewer}: ${detail}` });
          }
        }
        return forced.length > 0 ? mergeOutputs(peer, { statement_verdicts: forced }) : peer;
      };
      // Resolve prose-string verdict ids IMMEDIATELY after parse: every later step
      // (enforceExpected's merge, the batch/individual reduce) goes through mergeOutputs,
      // which has no expected-id list and would shred an unresolved "def:x: matched" into
      // an obj_id-less record — graded as a synthetic drift over a real matched.
      const parsePeer = (stdout: string): ReviewerOutput =>
        resolveVerdictIds(parseJsonObject(stdout), recognizedIds);
      let o = enforceExpected(parsePeer(codex.stdout), "codex");
      if (claudeRaw) o = mergeOutputs(o, enforceExpected(parsePeer(claudeRaw), "claude"));
      return o;
    } catch (err) {
      return {
        escalate: {
          kind: "unparsable-output",
          reason: `reviewer output failed to parse for ${label} (${err instanceof Error ? err.message : String(err)})` +
            (args.debugLogDir ? "; raw saved to _reviewer_calls.log" : ""),
        },
      };
    }
  };

  // Classify target rows by kind (symbols are always shallow). Chunk into groups, KEEPING only groups
  // of ≥2 — a singleton is cheaper as an individual high-effort call, so leftovers fall to wave 2.
  const targetItems = targetRows.map((r, i) => ({ row: r, block: targetBlocks[i] }));
  const deliveryItems = targetItems.filter((t) => deliveryObjIds.has(t.row.obj_id));
  const ordinaryItems = targetItems.filter((t) => !deliveryObjIds.has(t.row.obj_id));
  const theoremItems = ordinaryItems.filter((t) => t.row.kind === "theorem");
  const lemmaItems = ordinaryItems.filter((t) => t.row.kind === "lemma");
  const shallowItems = ordinaryItems.filter((t) => t.row.kind === "definition" || t.row.kind === "assumption");
  const groupsOf = <T>(arr: T[], size: number): T[][] => {
    const out: T[][] = [];
    for (let i = 0; i < arr.length; i += size) {
      const g = arr.slice(i, i + size);
      if (g.length >= 2) out.push(g);
    }
    return out;
  };
  const LEMMA_BATCH = 3;
  const SHALLOW_BATCH = 5;

  // ── WAVE 1 — batch pre-audit (lemmas high@≤3; defs/assumptions + symbols medium@≤5) ──
  const batchUnits: { label: string; prompt: string; effort: "high" | "medium"; dualReview: boolean; expectedIds: string[] }[] = [
    ...groupsOf(lemmaItems, LEMMA_BATCH).map((g) => ({
      label: `lemma-batch[${g.map((x) => x.row.obj_id).join(",")}]`, prompt: targetPrompt(g), effort: "high" as const, dualReview: false, expectedIds: g.map((x) => x.row.obj_id),
    })),
    ...groupsOf(shallowItems, SHALLOW_BATCH).map((g) => ({
      label: `batch[${g.map((x) => x.row.obj_id).join(",")}]`, prompt: targetPrompt(g), effort: "medium" as const, dualReview: true, expectedIds: g.map((x) => x.row.obj_id),
    })),
    ...groupsOf(symbolRows, SHALLOW_BATCH).map((g) => ({
      label: `sym-batch[${g.map((x) => x.id).join(",")}]`, prompt: symbolPrompt(g), effort: "medium" as const, dualReview: false, expectedIds: g.map((x) => x.id),
    })),
  ];
  const batchOut = (await mapLimit(batchUnits, REVIEW_CONCURRENCY, (u) => runUnit(u.label, u.prompt, u.effort, u.dualReview, u.expectedIds))).reduce(
    mergeOutputs,
    EMPTY,
  );
  // obj_ids the batch already verdicted (leading whitespace token; node ids keep their `:`).
  const knownReviewerIds = new Set([...targetObjIds, ...symbolRows.map((row) => row.id)]);
  const normId = (raw: unknown) => normalizeReviewerObjId(raw, knownReviewerIds);
  const covered = new Set<string>(
    [...toVerdictArray(batchOut.statement_verdicts), ...toVerdictArray(batchOut.assumption_verdicts)]
      .map((v) => normId(v.obj_id ?? v.id ?? v.object ?? v.target))
      .filter((x) => x.length > 0),
  );

  // ── WAVE 2 — individual HIGH-effort audits: every theorem, plus any lemma / def / assumption /
  // symbol the batch did not cover (singletons, drops, parse failures). The faithfulness floor. ──
  const indivUnits: { label: string; prompt: string; dualReview: boolean; expectedIds: string[] }[] = [
    ...deliveryItems.map((t) => ({ label: t.row.obj_id, prompt: targetPrompt([t]), dualReview: true, expectedIds: [t.row.obj_id] })),
    ...theoremItems.map((t) => ({ label: t.row.obj_id, prompt: targetPrompt([t]), dualReview: true, expectedIds: [t.row.obj_id] })),
    ...lemmaItems.filter((t) => !covered.has(t.row.obj_id)).map((t) => ({ label: t.row.obj_id, prompt: targetPrompt([t]), dualReview: false, expectedIds: [t.row.obj_id] })),
    ...shallowItems.filter((t) => !covered.has(t.row.obj_id)).map((t) => ({ label: t.row.obj_id, prompt: targetPrompt([t]), dualReview: true, expectedIds: [t.row.obj_id] })),
    ...symbolRows.filter((s) => !covered.has(s.id)).map((s) => ({ label: s.id, prompt: symbolPrompt([s]), dualReview: false, expectedIds: [s.id] })),
  ];
  const indivOuts = await mapLimit(indivUnits, REVIEW_CONCURRENCY, (u) => runUnit(u.label, u.prompt, "high", u.dualReview, u.expectedIds));

  // Fold batch + individual outputs into one. `mergeOutputs` keys by obj_id, so units accumulate
  // (no collisions); `escalate` resolves to the FIRST non-null across the frontier.
  const out = [batchOut, ...indivOuts].reduce(mergeOutputs, EMPTY);

  // Grade the (possibly schema-drifted) model output into verdict rows + blocking + escalate.
  // Every node has two legitimate names (graph `id` and `obj_id`); the reviewer may answer under
  // either. Map BOTH onto the canonical id in `targetObjIds`, else a verdict returned under the
  // other name is dropped and a synthetic `drift` is invented over a real `matched`.
  const allExpectedObjIds = [...targetObjIds, ...symbolRows.map((row) => row.id)];
  const graded = gradeReviewerOutput(out, allExpectedObjIds, idAliases);
  let graph = applyVerdictsToGraph(args.graph, graded.rows, args.hashes);
  // Persist symbol verdicts. `applyVerdictsToGraph` drops `sym:` rows (no backing node), so record
  // them on the graph's `symbolReview` map — this is what lets the NEXT delta pass skip a
  // matched-and-unchanged symbol. Only symbols actually reviewed THIS pass (present in
  // symbolHashById AND graded) update; symbols skipped this pass keep their prior entry.
  // Preserve the RAW reviewer verdict for symbols — critically `untagged`. `gradeReviewerOutput`
  // coerces every statement verdict to a CrosswalkVerdict (matched→`equivalent`, else `drift`), and
  // because `untagged` classifies as a PASS it collapses to `equivalent`. Persisting THAT would hide
  // the tagging gap: `symbolReview` reads `equivalent`, the tag-reroute (which keys on `untagged`)
  // never fires, and the scaffolder is never invoked. So key symbolReview off the raw model verdict.
  const rawSymVerdict = new Map<string, string>();
  const rawSymNote = new Map<string, string>();
  for (const v of toVerdictArray(out.statement_verdicts, allExpectedObjIds)) {
    const rec = v as Record<string, unknown>;
    const id = normId(rec.obj_id ?? rec.id ?? rec.object ?? rec.target);
    const vd = String(rec.verdict ?? "").trim();
    const note = String(rec.note ?? rec.detail ?? rec.reason ?? rec.message ?? "").trim();
    if (id.startsWith("sym:") && vd) {
      rawSymVerdict.set(id, vd);
      if (note) rawSymNote.set(id, note);
    }
  }
  const symUpdates: Record<string, { verdict: string; hash: string }> = {};
  for (const r of graded.rows) {
    if (!r.obj_id.startsWith("sym:")) continue;
    const hash = symbolHashById.get(r.obj_id);
    if (hash) symUpdates[r.obj_id] = { verdict: rawSymVerdict.get(r.obj_id) ?? r.verdict, hash };
  }
  if (Object.keys(symUpdates).length) {
    graph = { ...graph, symbolReview: { ...(graph.symbolReview ?? {}), ...symUpdates } };
  }
  return {
    graph,
    ok: graded.blocking.length === 0 && !graded.escalate,
    escalate: graded.escalate,
    blocking: graded.blocking,
    // Carry each drifted target's reviewer note so the loop can hand the scaffolder the SPECIFIC fix.
    // ALSO carry `untagged` symbol notes: the reviewer names the realizing decl ("hajekDenominators
    // defines the treated denominator formula, but the cluster is untagged"), which is exactly the
    // pointer the tag-reroute needs — without it the scaffolder gets a bare `sym:` id and cannot find
    // what to tag (the root cause of the tag-reroute failure loop).
    driftNotes: Object.fromEntries([
      ...graded.rows
        .filter(
          (r) =>
            r.verdict === "drift" &&
            typeof r.note === "string" &&
            r.note.trim().length > 0,
        )
        .map((r) => [r.obj_id, r.note as string]),
      ...[...rawSymNote.entries()].filter(([id]) => /untagged/i.test(rawSymVerdict.get(id) ?? "")),
    ]),
    substrateGates: graded.substrateGates,
    deliveryReviewReceipts: [...new Map(
      deliveryReviewReceipts.map((receipt) => [`${receipt.node_id}:${receipt.reviewer}`, receipt] as const),
    ).values()],
    citedReviewReceipts: [...new Map(
      citedReviewReceipts.map((receipt) => {
        const rebound = citedPlan
          ? { ...receipt, evidence_hash: citedEvidenceHash(citedPlan, graph, receipt.node_id) }
          : receipt;
        return [`${receipt.node_id}:${receipt.reviewer}`, rebound] as const;
      }),
    ).values()],
  };
}

export * from "./reviewer_verdicts.js";
