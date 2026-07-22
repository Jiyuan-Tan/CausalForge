// Central model registry. The pipeline dispatches to two agent runners — OpenAI
// `codex` (discovery / proof filling) and Anthropic `claude` (review / judge) —
// and every concrete model id flows through this module so a user on a different
// model lineup can override them WITHOUT editing source.
//
// Each logical role has a committed default (the current lineup) and an env-var
// override. Set the env var to any id the corresponding CLI accepts:
//   - codex roles  → an OpenAI `codex` model id (e.g. "gpt-5.5")
//   - claude roles → a `claude` CLI --model value: an alias ("opus"/"sonnet"/
//     "haiku") or a pinned id ("claude-opus-4-8").
//
// Env overrides (all optional):
//   CAUSALEAN_MODEL_CODEX_KERNEL   hard D-stage math + proof filler (default gpt-5.6-sol)
//   CAUSALEAN_MODEL_CODEX_MECH     mechanical                       (default gpt-5.6-terra)
//   CAUSALEAN_MODEL_CODEX_PRESENT  presentation P0-P5               (default gpt-5.5)
//   CAUSALEAN_MODEL_CODEX_CONSULT  orchestrator D-stage              (default gpt-5.6-sol)
//                                  halt-consultation (manual,
//                                  referenced by causalsmith-d /
//                                  causalsmith-main skill prose)
//   CAUSALEAN_MODEL_CLAUDE_MAIN    main reviewer / producer  (default opus)
//   CAUSALEAN_MODEL_CLAUDE_MID     mid-tier                  (default sonnet)
//   CAUSALEAN_MODEL_CLAUDE_CHEAP   cheap / bulk              (default haiku)

/** A value accepted by the `claude` CLI `--model` flag: an alias
 *  (opus/sonnet/haiku) or a pinned model id. */
export type ClaudeModel = string;
/** A value accepted by `codex`'s `-c model=` config: an OpenAI model id. */
export type CodexModel = string;

function envModel(key: string, def: string): string {
  const v = process.env[key];
  return v && v.trim() ? v.trim() : def;
}

/** Concrete model ids by logical role, each overridable via its env var. */
export const MODELS = {
  /** codex, hard kernel-math / proof tier (D-stage math: proposal, D0-solve, D0.5 referees).
   *  ALSO the F-stage proof filler (moved off codexMechanical back to this tier). */
  codexKernel: envModel("CAUSALEAN_MODEL_CODEX_KERNEL", "gpt-5.6-sol"),
  /** codex, mechanical / clerical tier. */
  codexMechanical: envModel("CAUSALEAN_MODEL_CODEX_MECH", "gpt-5.6-terra"),
  /** codex, presentation authoring/review tier. Kept on 5.5 for stronger
   *  literature breadth and more readable long-form paper prose. */
  codexPresentation: envModel("CAUSALEAN_MODEL_CODEX_PRESENT", "gpt-5.5"),
  /** codex, orchestrator D-stage halt-consultation tier. The orchestrator (causalsmith-d /
   *  causalsmith-main skills) runs this MANUALLY per its codex recipe; no pipeline stage reads
   *  it. Kept on the stronger solving model (gpt-5.6-sol) for adjudication. */
  codexConsult: envModel("CAUSALEAN_MODEL_CODEX_CONSULT", "gpt-5.6-sol"),
  /** claude, main reviewer / producer tier. */
  claudeMain: envModel("CAUSALEAN_MODEL_CLAUDE_MAIN", "opus"),
  /** claude, mid tier. */
  claudeMid: envModel("CAUSALEAN_MODEL_CLAUDE_MID", "sonnet"),
  /** claude, cheap / bulk tier. */
  claudeCheap: envModel("CAUSALEAN_MODEL_CLAUDE_CHEAP", "haiku"),
} as const;
