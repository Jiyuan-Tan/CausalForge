// CausalSmith/tools/src/substrate/requirement.ts
import { existsSync } from "node:fs";
import { mkdir, readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { requirementPath } from "./paths.js";

export const REQUIREMENT_TEMPLATE = `# Substrate requirement: <slug>

## Goal
One sentence — the missing concept/result to build.

## Provides (API contract)
The declarations the module must expose, each as name + informal signature.

## Statement / milestones
The MAIN statement(s) or key milestone(s) to prove — in NL or near-Lean, with
hypotheses. Need NOT be exhaustive; the scaffolder may add supporting lemmas.

## Standard reference
Textbook/paper where this is standard — lets the reviewer check "standardness".

## Intended reuse
Which theorem(s)/setting will consume this, and the generality required.

## May assume / must derive
Hypotheses fair to take as given vs. facts that must be proven from primitives.

## Non-goals (optional)
What is explicitly out of scope — prevents scope creep.

## Known building blocks (optional)
Mathlib/Causalean lemmas to lean on.
`;

const REQUIRED_SECTIONS = [
  "Goal",
  "Provides",
  "Statement / milestones",
  "Standard reference",
  "Intended reuse",
  "May assume / must derive",
] as const;

export interface RequirementCheck { ok: boolean; missingSections: string[] }

/** A section is "present" if its `## <name>` heading exists AND has non-empty,
 *  non-placeholder body text before the next `## ` heading. Heading match is a
 *  prefix match (so "Provides (API contract)" matches required key "Provides"). */
export function validateRequirementText(text: string): RequirementCheck {
  const lines = text.split(/\r?\n/);
  const sections: { name: string; body: string }[] = [];
  let cur: { name: string; body: string } | null = null;
  for (const line of lines) {
    const m = line.match(/^##\s+(.*\S)\s*$/);
    if (m) {
      if (cur) sections.push(cur);
      cur = { name: m[1], body: "" };
    } else if (cur) {
      cur.body += line + "\n";
    }
  }
  if (cur) sections.push(cur);

  const missingSections: string[] = [];
  for (const req of REQUIRED_SECTIONS) {
    const found = sections.find((s) => s.name.startsWith(req));
    const body = found?.body.trim() ?? "";
    // Reject the untouched template hint lines as "empty".
    const placeholder = body.length === 0 || /^(One sentence|The declarations|The MAIN|Textbook\/paper|Which theorem|Hypotheses fair)/.test(body);
    if (placeholder) missingSections.push(req);
  }
  return { ok: missingSections.length === 0, missingSections };
}

export async function ensureRequirement(
  repoRoot: string,
  slug: string,
): Promise<{ status: "bootstrapped" | "invalid" | "ok"; text?: string; check?: RequirementCheck }> {
  const p = requirementPath(repoRoot, slug);
  if (!existsSync(p)) {
    await mkdir(path.dirname(p), { recursive: true });
    await writeFile(p, REQUIREMENT_TEMPLATE, "utf8");
    return { status: "bootstrapped" };
  }
  const text = await readFile(p, "utf8");
  const check = validateRequirementText(text);
  return check.ok ? { status: "ok", text, check } : { status: "invalid", text, check };
}
