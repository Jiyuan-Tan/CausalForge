// CausalSmith/tools/src/substrate/prompts.ts
//
// Prompt builders for the --study substrate-build mode. The static prompt text
// lives in editable `.txt` templates under `./prompts/` (mirroring the causalsmith
// pipeline's externalized prompts); these builders load a template once at
// module init and substitute `{{TOKEN}}` placeholders with the per-call context.
import { readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import type { CodexPrompt, RoundReport, ReviewVerdict } from "./types.js";

const PROMPT_DIR = path.join(path.dirname(fileURLToPath(import.meta.url)), "prompts");
const SCAFFOLDER_TEMPLATE = readFileSync(path.join(PROMPT_DIR, "scaffolder.txt"), "utf8");
const FILLER_TEMPLATE = readFileSync(path.join(PROMPT_DIR, "filler.txt"), "utf8");
const REVIEWER_TEMPLATE = readFileSync(path.join(PROMPT_DIR, "reviewer.txt"), "utf8");
const COORDINATOR_TEMPLATE = readFileSync(path.join(PROMPT_DIR, "coordinator.txt"), "utf8");

/** Replace every `{{KEY}}` in `tpl` with `vars[KEY]`. Each key is applied once,
 *  so a value that happens to contain another key's token is not re-expanded. */
function fillTemplate(tpl: string, vars: Record<string, string>): string {
  let out = tpl;
  for (const [k, v] of Object.entries(vars)) {
    out = out.split(`{{${k}}}`).join(v);
  }
  return out;
}

export function buildScaffolderPrompt(args: {
  slug: string; requirement: string; leanDir: string; modulePrefix: string;
  planMarkdown: string | null; lastReport: RoundReport | null;
  lastReview: ReviewVerdict | null; buildRounds: number; buildCap: number;
}): string {
  const reportBlock = args.lastReport
    ? `\n## Previous round report (round ${args.lastReport.round})\n` +
      `Build ok: ${args.lastReport.build.ok}; sorries remaining: ${args.lastReport.build.sorryCount}.\n` +
      `Build errors:\n${args.lastReport.build.errors.join("\n") || "(none)"}\n` +
      `Filler reports:\n${args.lastReport.fillers.map((f) => `- [${f.id}] ${f.ok ? "ok" : "FAILED"}: ${f.summary}`).join("\n")}\n`
    : "";
  const reviewBlock = args.lastReview
    ? `\n## Reviewer findings to address (the module FAILED review)\n${args.lastReview.findings}\n`
    : "";
  const planBlock = args.planMarkdown ? `\n## Your current plan\n${args.planMarkdown}\n` : "";
  return fillTemplate(SCAFFOLDER_TEMPLATE, {
    REQUIREMENT: args.requirement,
    LEAN_DIR: args.leanDir,
    MODULE_PREFIX: args.modulePrefix,
    ROUND: String(args.buildRounds + 1),
    BUILD_CAP: String(args.buildCap),
    PLAN_BLOCK: planBlock,
    REPORT_BLOCK: reportBlock,
    REVIEW_BLOCK: reviewBlock,
  });
}

export function buildFillerPrompt(args: { leanDir: string; modulePrefix: string; prompt: CodexPrompt }): string {
  return fillTemplate(FILLER_TEMPLATE, {
    LEAN_DIR: args.leanDir,
    MODULE_PREFIX: args.modulePrefix,
    TARGET_DECLS: args.prompt.target_decls.join(", ") || "(see instructions)",
    INSTRUCTIONS: args.prompt.prompt,
  });
}

export function buildReviewerPrompt(args: { requirement: string; leanDir: string; modulePrefix: string }): string {
  return fillTemplate(REVIEWER_TEMPLATE, {
    REQUIREMENT: args.requirement,
    LEAN_DIR: args.leanDir,
    MODULE_PREFIX: args.modulePrefix,
  });
}

export function buildCoordinatorPrompt(args: {
  requirement: string; leanDir: string; modulePrefix: string;
  leanFiles: string[]; stagingDir: string; lastFailureLog: string | null;
}): string {
  const failureBlock = args.lastFailureLog
    ? `\n## Previous attempt FAILED the integration gate — fix and retry\n` +
      "Your last manifest was applied then rolled back because a step below failed. " +
      "Read the log, find the cause (bad placement, missing/duplicate import, a dedup " +
      "rewire that broke a proof, a merge anchor that did not exist), and emit a corrected " +
      `manifest.\n\n\`\`\`\n${args.lastFailureLog}\n\`\`\`\n`
    : "";
  return fillTemplate(COORDINATOR_TEMPLATE, {
    REQUIREMENT: args.requirement,
    LEAN_DIR: args.leanDir,
    MODULE_PREFIX: args.modulePrefix,
    LEAN_FILES: args.leanFiles.map((f) => `- ${f}`).join("\n") || "(none)",
    STAGING_DIR: args.stagingDir,
    FAILURE_BLOCK: failureBlock,
  });
}
