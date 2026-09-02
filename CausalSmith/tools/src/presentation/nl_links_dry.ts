// Free-pass sweep for the P4 NL↔Lean crosslink sub-step.
//
// Everything the sub-step does BEFORE it spends a model call — selection, block
// extraction, Lean pieces and their reference closure, statement structuring,
// paper segmentation and its invariants, both prompt renderings, the cache read
// side, the artifact read side — is exercised here against a real bundle with a
// runCodex that THROWS if anything reaches it. A bundle shape the sub-step has
// never seen surfaces as a report line instead of a crash halfway through a paid
// run.
//
// It shares the stage's own primitives, so there is no second copy of the rules
// to drift out of step.

import { readFile, readdir, stat } from "node:fs/promises";
import { join } from "node:path";
import { z } from "zod";
import { presentationPrompt } from "./prompt_io.js";
import {
  assignSection,
  assignmentProblems,
  buildBlockInput,
  chunkBySize,
  extractBlockHtml,
  loadDeclIndex,
  selectsForNlLinks,
  verifyProblems,
  verifySection,
  MAX_PROMPT_BYTES,
  NL_LINKS_ARTIFACT,
  NL_LINKS_CACHE,
  NL_LINKS_POLICY,
  NL_LINKS_VERIFY_CACHE,
  type BlockInput,
  type VerifyInput,
} from "./nl_links.js";
import { segmentationProblems } from "./nl_segments.js";
import type { LeanSnippet } from "./types.js";

/** A runCodex that must never be reached. Passing it proves the pass is free. */
export const forbiddenCodex = {
  runCodex: async (): Promise<{ stdout: string; stderr: string }> => {
    throw new Error("nl-links dry run attempted a model call — the free pass is not free");
  },
};

export interface BundleReport {
  bundle: string;
  ok: boolean;
  blocks: number;
  skipped: { webOnly: number; synthesized: number; noSnippet: number; noLean: number; noBlock: number };
  /** Objects whose block IS in the HTML but could not be extracted — a defect. */
  extractionFailures: string[];
  /** Blocks whose Lean statement the parser declined: they ship segments only. */
  unstructured: string[];
  rows: { total: number; min: number; median: number; max: number };
  segments: { total: number; displays: number; min: number; median: number; max: number };
  /** Paid requests a cold run would make: assignment, then verification. */
  assignChunks: number;
  verifyChunks: number;
  promptBytesMax: number;
  caches: { assign: string; verify: string };
  artifact: string;
  anomalies: string[];
  errors: string[];
}

const median = (xs: number[]): number => {
  if (xs.length === 0) return 0;
  const s = [...xs].sort((a, b) => a - b);
  return s[Math.floor(s.length / 2)];
};

/** Bundle dirs under `root`: a directory with a meta.json. Sorted. */
export async function findBundles(root: string): Promise<string[]> {
  const out: string[] = [];
  let entries: string[];
  try {
    entries = (await readdir(root, { withFileTypes: true })).filter((e) => e.isDirectory()).map((e) => e.name);
  } catch {
    return [];
  }
  for (const name of entries.sort()) {
    if (await stat(join(root, name, "meta.json")).then(() => true, () => false)) out.push(join(root, name));
  }
  return out;
}

/** Run every free pass of the sub-step against one bundle directory. */
export async function dryRunBundle(dir: string): Promise<BundleReport> {
  const bundle = dir.split("/").filter(Boolean).pop() ?? dir;
  const report: BundleReport = {
    bundle,
    ok: true,
    blocks: 0,
    skipped: { webOnly: 0, synthesized: 0, noSnippet: 0, noLean: 0, noBlock: 0 },
    extractionFailures: [],
    unstructured: [],
    rows: { total: 0, min: 0, median: 0, max: 0 },
    segments: { total: 0, displays: 0, min: 0, median: 0, max: 0 },
    assignChunks: 0,
    verifyChunks: 0,
    promptBytesMax: 0,
    caches: { assign: "absent", verify: "absent" },
    artifact: "absent",
    anomalies: [],
    errors: [],
  };
  const fail = (msg: string): BundleReport => {
    report.ok = false;
    report.errors.push(msg);
    return report;
  };
  let crosswalk: { entries: Array<{ obj_id: string; env: string; status: string }> };
  let snippets: Record<string, LeanSnippet>;
  let html: string;
  try {
    crosswalk = JSON.parse(await readFile(join(dir, "presentation_crosswalk.json"), "utf8"));
    snippets = JSON.parse(await readFile(join(dir, "lean_snippets.json"), "utf8")).snippets;
    html = await readFile(join(dir, "paper_body.html"), "utf8");
  } catch (e) {
    return fail(`inputs unreadable: ${(e as Error).message}`);
  }
  let index;
  try {
    index = await loadDeclIndex(dir);
  } catch (e) {
    return fail((e as Error).message);
  }

  const rowCounts: number[] = [];
  const segCounts: number[] = [];
  const blocks: BlockInput[] = [];
  for (const entry of crosswalk.entries ?? []) {
    if (!selectsForNlLinks(entry)) {
      if (entry.status === "presentation-synthesized") report.skipped.synthesized++;
      else report.skipped.webOnly++;
      continue;
    }
    const snippet = snippets[entry.obj_id];
    if (!snippet) {
      report.skipped.noSnippet++;
      continue;
    }
    const blockHtml = extractBlockHtml(html, entry.obj_id);
    if (blockHtml === null || blockHtml.trim().length === 0) {
      // Distinguish "this object has no body block" (normal for a prose entry)
      // from "its block is there but unreadable" (a defect worth failing on).
      const present = new RegExp(
        `<div\\b[^>]*class="formal-block[^"]*"[^>]*data-objid="${entry.obj_id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}"`,
      ).test(html);
      if (present) {
        report.ok = false;
        report.extractionFailures.push(entry.obj_id);
      } else report.skipped.noBlock++;
      continue;
    }
    let input: BlockInput | null;
    try {
      input = buildBlockInput({ objId: entry.obj_id, blockHtml, snippet, index });
    } catch (e) {
      report.ok = false;
      report.errors.push(`${entry.obj_id}: ${(e as Error).message}`);
      continue;
    }
    if (!input) {
      report.skipped.noLean++;
      continue;
    }
    // The partition/atomicity invariants are asserted per block, not assumed.
    const segProblems = segmentationProblems(blockHtml, input.segments);
    if (segProblems.length > 0) {
      report.ok = false;
      report.errors.push(`${entry.obj_id}: ${segProblems.slice(0, 3).join("; ")}`);
    }
    report.blocks++;
    if (input.structured === null) report.unstructured.push(entry.obj_id);
    rowCounts.push(input.rows.length);
    segCounts.push(input.segments.length);
    report.rows.total += input.rows.length;
    report.segments.total += input.segments.length;
    report.segments.displays += input.segments.filter((s) => s.kind === "display").length;
    blocks.push(input);
  }
  report.rows = {
    total: report.rows.total,
    min: rowCounts.length ? Math.min(...rowCounts) : 0,
    median: median(rowCounts),
    max: rowCounts.length ? Math.max(...rowCounts) : 0,
  };
  report.segments = {
    ...report.segments,
    min: segCounts.length ? Math.min(...segCounts) : 0,
    median: median(segCounts),
    max: segCounts.length ? Math.max(...segCounts) : 0,
  };

  // Assignment side: how many paid requests a cold run makes, and how big.
  const askable = blocks.filter((b) => b.rows.length > 0 || b.segments.some((s) => s.kind === "display"));
  try {
    const chunks = chunkBySize(askable, assignSection);
    report.assignChunks = chunks.length;
    for (const chunk of chunks) {
      const payload = chunk.map(assignSection).join("\n\n");
      if (payload.length > MAX_PROMPT_BYTES) {
        report.ok = false;
        report.errors.push(
          `${chunk.map((c) => c.objId).join(", ")}: request material ${payload.length}B exceeds the ${MAX_PROMPT_BYTES}B ceiling`,
        );
        continue;
      }
      const prompt = await presentationPrompt("p4_nl_links", { objects_payload: payload });
      report.promptBytesMax = Math.max(report.promptBytesMax, Buffer.byteLength(prompt));
      if (/\{\{[a-z_]+\}\}/.test(prompt)) {
        report.ok = false;
        report.errors.push("assignment prompt has an unrendered placeholder");
      }
      // The totality validator must accept a well-formed total answer.
      for (const input of chunk) {
        const reply = {
          assignments: input.rows.map((r) => ({ row: r.id, unstated: true as const })),
          displayLinks: input.segments
            .filter((s) => s.kind === "display")
            .map((s) => ({ segment: s.id, presentationOnly: true as const })),
        };
        const problems = assignmentProblems(input, reply);
        if (problems.length > 0) {
          report.ok = false;
          report.errors.push(`${input.objId}: validator rejects a total answer: ${problems.slice(0, 3).join("; ")}`);
        }
      }
    }
  } catch (e) {
    report.ok = false;
    report.errors.push(`assignment pass failed: ${(e as Error).message}`);
  }

  // Verification side, over the same fabricated total answer.
  try {
    const verifyInputs: VerifyInput[] = askable.map((b) => ({
      objId: b.objId,
      block: b,
      assignments: b.rows.map((r) => ({ row: r.id, unstated: true as const })),
      displayLinks: b.segments
        .filter((s) => s.kind === "display")
        .map((s) => ({ segment: s.id, presentationOnly: true as const })),
    }));
    const chunks = chunkBySize(verifyInputs, verifySection);
    report.verifyChunks = chunks.length;
    for (const chunk of chunks) {
      const payload = chunk.map(verifySection).join("\n\n");
      const prompt = await presentationPrompt("p4_nl_links_verify", { claims_payload: payload });
      report.promptBytesMax = Math.max(report.promptBytesMax, Buffer.byteLength(prompt));
      if (/\{\{[a-z_]+\}\}/.test(prompt)) {
        report.ok = false;
        report.errors.push("verify prompt has an unrendered placeholder");
      }
      const verdicts = chunk.flatMap((v) => [
        ...v.assignments.map((a) => ({ obj_id: v.objId, claim: a.row, ok: true })),
        ...v.displayLinks.map((d) => ({ obj_id: v.objId, claim: d.segment, ok: true })),
      ]);
      const problems = verifyProblems(chunk, verdicts);
      if (problems.length > 0) {
        report.ok = false;
        report.errors.push(`verify validator rejects its own well-formed reply: ${problems.slice(0, 3).join("; ")}`);
      }
    }
  } catch (e) {
    report.ok = false;
    report.errors.push(`verify pass failed: ${(e as Error).message}`);
  }

  report.caches.assign = await inspectAssignCache(dir);
  report.caches.verify = await inspectVerifyCache(dir);
  report.artifact = await inspectArtifact(dir);
  for (const line of [report.caches.assign, report.caches.verify, report.artifact]) {
    if (line.startsWith("CORRUPT") || line.startsWith("INVALID")) report.anomalies.push(line);
  }
  return report;
}

const readJson = async (path: string): Promise<unknown | null | "corrupt"> => {
  let raw: string;
  try {
    raw = await readFile(path, "utf8");
  } catch {
    return null;
  }
  try {
    return JSON.parse(raw);
  } catch {
    return "corrupt";
  }
};

const AssignEntry = z.object({
  policy: z.literal(NL_LINKS_POLICY),
  key: z.string().min(1),
  complete: z.literal(true),
  assignments: z.array(z.object({ row: z.string() }).passthrough()),
  displayLinks: z.array(z.object({ segment: z.string() }).passthrough()),
});
const VerifyEntry = z.object({
  policy: z.literal(NL_LINKS_POLICY),
  key: z.string().min(1),
  complete: z.literal(true),
  verdicts: z.array(z.object({ obj_id: z.string(), claim: z.string(), ok: z.boolean() }).passthrough()),
});

async function inspectAssignCache(dir: string): Promise<string> {
  const parsed = await readJson(join(dir, NL_LINKS_CACHE));
  if (parsed === null) return "absent";
  if (parsed === "corrupt") return "CORRUPT (unparseable JSON; the stage warns and re-assigns)";
  const entries = Object.entries(parsed as Record<string, unknown>);
  const bad = entries.filter(([, v]) => !AssignEntry.safeParse(v).success).length;
  return `${entries.length} entries, ${bad} stale/pre-policy`;
}

async function inspectVerifyCache(dir: string): Promise<string> {
  const parsed = await readJson(join(dir, NL_LINKS_VERIFY_CACHE));
  if (parsed === null) return "absent";
  if (parsed === "corrupt") return "CORRUPT (unparseable JSON; the stage warns and re-reviews)";
  const entries = Object.entries(parsed as Record<string, unknown>);
  const bad = entries.filter(([, v]) => !VerifyEntry.safeParse(v).success).length;
  return `${entries.length} entries, ${bad} stale/pre-policy`;
}

/** An existing artifact: its generation, and how much it carries. */
async function inspectArtifact(dir: string): Promise<string> {
  const parsed = await readJson(join(dir, NL_LINKS_ARTIFACT));
  if (parsed === null) return "absent";
  if (parsed === "corrupt") return "CORRUPT (unparseable JSON)";
  const art = parsed as { policy?: string; blocks?: Record<string, unknown>; links?: Record<string, unknown[]> };
  if (art.policy !== NL_LINKS_POLICY) {
    const pairs = Object.values(art.links ?? {}).reduce((n, l) => n + (Array.isArray(l) ? l.length : 0), 0);
    return `policy ${art.policy ?? "?"} — superseded by ${NL_LINKS_POLICY} (${pairs} v2 pairs, dead)`;
  }
  const blocks = Object.entries(art.blocks ?? {});
  const assigned = blocks.reduce(
    (n, [, b]) => n + ((b as { assignments?: unknown[] }).assignments?.length ?? 0), 0);
  return `${blocks.length} blocks, ${assigned} row assignments`;
}
