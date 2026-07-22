/**
 * Phase 3 — OpenQuestion bundle resolver.
 *
 * Reads an OpenQuestion node from the typed graph and walks its `radius=1`
 * neighborhood via `shared/graph.ts` queries to assemble the input bundle
 * Stage -1.2 consumes when invoked via `/causalsmith --from-question <oq_id>`.
 * Renders the Markdown block injected into the proposer prompt per spec §6.1.
 *
 * Readers do NOT acquire the graph lock (spec §15.2 readers section). Atomic
 * node writes + the atomic `rename`-based index swap mean a reader either sees
 * the pre-swap or post-swap state, never a partial one.
 */
import path from "node:path";
import { existsSync, readFileSync } from "node:fs";
import {
  bankedTheoremsForMethod,
  insightsForMethod,
  loadGraph,
  notesForMethod,
  type Graph,
} from "./graph.js";
import type {
  Assumption,
  BankedTheorem,
  Insight,
  Method,
  Note,
  OpenQuestion,
} from "./kb_types.js";

export const DEFAULT_INSIGHT_LIMIT = 10;
export const DEFAULT_NOTE_LIMIT = 5;
export const DEFAULT_BANKED_LIMIT = 10;

// ---------------------------------------------------------------------------
// Typed errors
// ---------------------------------------------------------------------------

export class OpenQuestionNotFound extends Error {
  constructor(public oq_id: string, public graphRoot: string) {
    super(`OpenQuestion not found: ${oq_id} (graphRoot=${graphRoot})`);
    this.name = "OpenQuestionNotFound";
  }
}

export class SeedMethodMissing extends Error {
  constructor(public oq_id: string, public method_id: string) {
    super(
      `OpenQuestion ${oq_id} references seed method ${method_id} which is not present in the graph.`,
    );
    this.name = "SeedMethodMissing";
  }
}

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

export interface AssumptionRow {
  assumption: Assumption | null;
  id: string;
  /** True when `assumption` is null because the id was unresolvable. */
  missing: boolean;
}

export interface SectionTruncation {
  shown: number;
  total: number;
}

export interface OpenQuestionBundle {
  oq: OpenQuestion;
  method: Method;
  assumptions: AssumptionRow[];
  precedentInsights: Insight[];
  precedentInsightsTruncation?: SectionTruncation;
  areaNotes: Note[];
  areaNotesTruncation?: SectionTruncation;
  bankedPrecedents: BankedTheorem[];
  bankedPrecedentsTruncation?: SectionTruncation;
}

export interface ResolveOpenQuestionOpts {
  /** Defaults to `<CausalSmith>/doc/study`. */
  graphRoot?: string;
  insightLimit?: number;
  noteLimit?: number;
  bankedLimit?: number;
}

// ---------------------------------------------------------------------------
// Loader
// ---------------------------------------------------------------------------

/**
 * Load an OpenQuestion and assemble its `radius=1` neighborhood.
 *
 * The seed Assumptions are read from the `oq.relies_on` / legacy
 * `seed_assumption_ids` field if present; if neither exists the bundle still
 * returns an empty assumption list (Stage -1 prompt section renders `_(none)_`).
 * A missing seed Method is fatal (we cannot do the per-method graph walk).
 */
export async function resolveOpenQuestion(
  oq_id: string,
  opts: ResolveOpenQuestionOpts = {},
): Promise<OpenQuestionBundle> {
  const graphRoot = opts.graphRoot ?? defaultGraphRoot();
  const oqPath = path.join(graphRoot, "nodes", "open_question", `${oq_id}.json`);
  if (!existsSync(oqPath)) {
    throw new OpenQuestionNotFound(oq_id, graphRoot);
  }
  const oq = JSON.parse(readFileSync(oqPath, "utf8")) as OpenQuestion;

  const graph = await loadGraph(graphRoot);

  const method_id = oq.seed_method_id;
  if (!method_id) {
    throw new SeedMethodMissing(oq_id, "<unset>");
  }
  const methodNode = graph.nodes.get(method_id);
  if (!methodNode || !("method_id" in methodNode)) {
    throw new SeedMethodMissing(oq_id, method_id);
  }
  const method = methodNode as Method;

  // Seed assumptions: tolerate two field shapes.
  const seedAssumptionIds = extractSeedAssumptionIds(oq);
  const assumptions: AssumptionRow[] = seedAssumptionIds.map((id) => {
    const node = graph.nodes.get(id);
    if (node && "assumption_id" in node) {
      return { assumption: node as Assumption, id, missing: false };
    }
    return { assumption: null, id, missing: true };
  });

  // Radius-1 walks.
  const insightLimit = opts.insightLimit ?? DEFAULT_INSIGHT_LIMIT;
  const noteLimit = opts.noteLimit ?? DEFAULT_NOTE_LIMIT;
  const bankedLimit = opts.bankedLimit ?? DEFAULT_BANKED_LIMIT;

  // Pull *all* matching items first so we can report `total` for truncation
  // footers; then slice down to the limit.
  const allInsights = insightsForMethod(graph, method_id, Number.MAX_SAFE_INTEGER);
  const allNotes = notesForMethod(graph, method_id, Number.MAX_SAFE_INTEGER);
  const allBanked = bankedTheoremsForMethod(graph, method_id, Number.MAX_SAFE_INTEGER);

  return {
    oq,
    method,
    assumptions,
    precedentInsights: allInsights.slice(0, insightLimit),
    precedentInsightsTruncation:
      allInsights.length > insightLimit
        ? { shown: insightLimit, total: allInsights.length }
        : undefined,
    areaNotes: allNotes.slice(0, noteLimit),
    areaNotesTruncation:
      allNotes.length > noteLimit ? { shown: noteLimit, total: allNotes.length } : undefined,
    bankedPrecedents: allBanked.slice(0, bankedLimit),
    bankedPrecedentsTruncation:
      allBanked.length > bankedLimit
        ? { shown: bankedLimit, total: allBanked.length }
        : undefined,
  };
}

// ---------------------------------------------------------------------------
// Renderer (spec §6.1)
// ---------------------------------------------------------------------------

/**
 * Render the bundle as the Markdown block spliced into Stage -1.2's prompt
 * under the `OPEN_QUESTION_CONTEXT` slot. Header text is part of the contract
 * with the prompt — do not rename.
 */
export function renderOpenQuestionContext(bundle: OpenQuestionBundle): string {
  const lines: string[] = [];

  const oqId = (bundle.oq as unknown as { open_question_id?: string }).open_question_id ?? "<unknown>";
  const motivation = renderOqMotivation(bundle.oq);

  lines.push("## Target OpenQuestion");
  lines.push(`oq_id: ${oqId}`);
  lines.push(motivation);
  lines.push("");

  lines.push("## Seed method");
  const methodDesc = bundle.method.description?.trim() ?? "";
  lines.push(`${bundle.method.name} (method_id: ${bundle.method.method_id})${methodDesc ? `: ${methodDesc}` : ""}`);
  lines.push("");

  lines.push("## Seed assumptions");
  if (bundle.assumptions.length === 0) {
    lines.push("_(none)_");
  } else {
    for (const row of bundle.assumptions) {
      if (row.missing || !row.assumption) {
        lines.push(`- ${row.id} _(unresolved — node missing from graph)_`);
        continue;
      }
      const desc = row.assumption.description?.trim() ?? "";
      lines.push(`- ${row.assumption.name} (${row.id})${desc ? `: ${desc}` : ""}`);
    }
  }
  lines.push("");

  lines.push("## Literature precedents (Insights instantiating this method)");
  if (bundle.precedentInsights.length === 0) {
    lines.push("_(none)_");
  } else {
    for (const ins of bundle.precedentInsights) {
      const reliesOn = (ins.relies_on ?? []).join(", ") || "—";
      const relaxes = (ins.relaxes ?? []).join(", ") || "—";
      const summary = ins.summary?.trim() ?? "";
      lines.push(`- ${ins.insight_id}: ${ins.title}${summary ? ` — ${summary}` : ""}`);
      lines.push(`  relies_on: [${reliesOn}], relaxes: [${relaxes}]`);
    }
    if (bundle.precedentInsightsTruncation) {
      lines.push(
        `_(showing top ${bundle.precedentInsightsTruncation.shown} of ${bundle.precedentInsightsTruncation.total}; older entries omitted)_`,
      );
    }
  }
  lines.push("");

  lines.push("## Area context (Notes discussing this method)");
  if (bundle.areaNotes.length === 0) {
    lines.push("_(none)_");
  } else {
    for (const n of bundle.areaNotes) {
      const excerpt = firstParagraphExcerpt(n.body, 240);
      lines.push(`- ${n.note_id} (kind: ${n.kind}): ${n.title}${excerpt ? ` — ${excerpt}` : ""}`);
    }
    if (bundle.areaNotesTruncation) {
      lines.push(
        `_(showing top ${bundle.areaNotesTruncation.shown} of ${bundle.areaNotesTruncation.total}; older entries omitted)_`,
      );
    }
  }
  lines.push("");

  lines.push("## Already banked under this method");
  if (bundle.bankedPrecedents.length === 0) {
    lines.push("_(none)_");
  } else {
    for (const bt of bundle.bankedPrecedents) {
      const inst = (bt.instantiates ?? []).join(", ") || "—";
      const uses = (bt.uses ?? []).join(", ") || "—";
      lines.push(`- ${bt.bt_id}: instantiates [${inst}], uses [${uses}]`);
    }
    if (bundle.bankedPrecedentsTruncation) {
      lines.push(
        `_(showing top ${bundle.bankedPrecedentsTruncation.shown} of ${bundle.bankedPrecedentsTruncation.total}; older entries omitted)_`,
      );
    }
  }

  return lines.join("\n");
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function renderOqMotivation(oq: OpenQuestion): string {
  // The OpenQuestion schema (study/types.ts) has `title` + `body`. The plan
  // also documents a `motivation` field on some hand-authored fixtures; if
  // present, prefer it. Otherwise fall back to `body`.
  const bag = oq as unknown as Record<string, unknown>;
  const motivation = bag.motivation;
  if (typeof motivation === "string" && motivation.trim().length > 0) return motivation.trim();
  const body = oq.body;
  if (typeof body === "string" && body.trim().length > 0) return body.trim();
  const title = oq.title;
  if (typeof title === "string" && title.trim().length > 0) return title.trim();
  return "_(no motivation provided)_";
}

function extractSeedAssumptionIds(oq: OpenQuestion): string[] {
  const bag = oq as unknown as Record<string, unknown>;
  const arr = bag.seed_assumption_ids ?? bag.relies_on;
  if (!Array.isArray(arr)) return [];
  return arr.filter((s): s is string => typeof s === "string");
}

function firstParagraphExcerpt(body: string | undefined, max: number): string {
  if (!body) return "";
  const trimmed = body.trim();
  if (trimmed.length === 0) return "";
  const firstBlankLine = trimmed.search(/\n\s*\n/);
  const first = firstBlankLine === -1 ? trimmed : trimmed.slice(0, firstBlankLine);
  if (first.length <= max) return first.replace(/\s+/g, " ").trim();
  return first.slice(0, max - 1).replace(/\s+/g, " ").trim() + "…";
}

function defaultGraphRoot(): string {
  // Resolve <CausalSmith>/doc/study by walking up from cwd looking for the
  // CausalSmith lakefile. Mirrors cli.ts#findRepoRoot — duplicated here so
  // the shared module has no upward dependency on cli.ts.
  let cur = path.resolve(process.cwd());
  while (true) {
    const lakefile = path.join(cur, "lakefile.toml");
    if (existsSync(lakefile)) {
      try {
        const content = readFileSync(lakefile, "utf8");
        if (/^\s*name\s*=\s*"CausalSmith"/m.test(content)) {
          return path.join(cur, "doc", "study");
        }
      } catch {
        // unreadable; keep walking
      }
    }
    const parent = path.dirname(cur);
    if (parent === cur) {
      throw new Error(
        `Could not locate CausalSmith package root from ${process.cwd()}. Pass {graphRoot} to resolveOpenQuestion explicitly.`,
      );
    }
    cur = parent;
  }
}

/** Re-export for callers that want to know graph loading succeeded. */
export type { Graph };
