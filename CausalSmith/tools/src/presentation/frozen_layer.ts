import type { CrosswalkEntry } from "./types.js";
import type { NoteBlock } from "./note_parser.js";
import { texSafeTitle } from "./tex_anchors.js";

export type EnvName = "theoremv" | "assumptionv" | "lemmav" | "definitionv";

// AUDIT-PRES: no src/bin caller in this checkout; retained as exported test/legacy helper.
export function envFor(
  objId: string,
  kind: string,
  overrides?: Record<string, "definitionv" | "assumptionv">,
): EnvName {
  if (objId.startsWith("T-")) return "theoremv";
  if (objId.startsWith("L-")) return "lemmav";
  // Presentation override (outline `env_overrides:`): a constructive object the
  // note filed as an assumption (a rule, tuning sequence, estimator) presents
  // as the Definition it mathematically is. Restricted to def/assumption swaps.
  const ov = overrides?.[objId];
  if (ov) return ov;
  return kind === "assumption" ? "assumptionv" : "definitionv";
}

/**
 * Mechanical first draft of every formal environment, statement text taken
 * verbatim from the note. P1's Opus touch-up may rewrite WORDING inside each
 * env body (Lean backticks → math prose) but the set of envs and their
 * obj_ids is fixed here, and after the P1 checkpoint the bodies are frozen
 * (hash-pinned) — see tex_anchors.lintAnchors.
 */
// AUDIT-PRES: no src/bin caller in this checkout; retained as exported test/legacy helper.
export function buildFrozenLayer(
  blocks: NoteBlock[],
  crosswalk: CrosswalkEntry[],
  envOverrides?: Record<string, "definitionv" | "assumptionv">,
): string {
  const byId = new Map(crosswalk.map((e) => [e.obj_id, e]));
  const out: string[] = [
    "% AUTO-GENERATED frozen formal layer — causalsmith P1. Edit wording only via P1 touch-up.",
  ];
  for (const b of blocks) {
    const cw = byId.get(b.obj_id);
    // Note blocks without a crosswalk row cannot be anchored; the linter
    // (tex_anchors) catches paper envs without crosswalk, not unused blocks.
    if (!cw) continue;
    const env = envFor(b.obj_id, cw.kind, envOverrides);
    const stmt = statementText(b);
    out.push(`\\begin{${env}}{${b.obj_id}}[${texSafeTitle(b.title)}]`, stmt.trim(), `\\end{${env}}`, "");
  }
  return out.join("\n");
}

function statementText(b: NoteBlock): string {
  const f = b.fields;
  const pick = (...names: string[]): string | undefined =>
    names.map((n) => f[n]).find((v) => v != null && v.trim() !== "");
  const body = b.body.trim();
  if (b.obj_id.startsWith("T-")) {
    // Current causalsmith T-blocks use `Statement.` / `Conclusion (typed).`; the
    // legacy dialect used `Conclusion`. Fall back to the raw body if neither.
    const concl = pick("Statement", "Conclusion (typed)", "Conclusion");
    const hyp = f["Load-bearing hypotheses"]
      ? `Under the stated assumptions:\n${f["Load-bearing hypotheses"]}\n`
      : "";
    return concl ? hyp + concl : body;
  }
  if (b.obj_id.startsWith("L-")) {
    const concl = pick("Conclusion", "Statement");
    const hyp = f["Hypotheses"] ? `Assume ${f["Hypotheses"]}.` : "";
    return concl ? [hyp, concl].filter(Boolean).join("\n") : body;
  }
  // P-block: legacy `Signature`/`Conditions` fields, else the typed body.
  const sig = [f["Signature"] ?? "", f["Conditions"] ?? ""].filter(Boolean).join("\n");
  return sig.trim() !== "" ? sig : body;
}
