// Match a presentation-synthesized definition to an existing Lean declaration of
// the run. The notation loop (P1) synthesizes a lean-less definition whenever a
// symbol has no `@realizes`-tagged home; but the run's Lean development often
// already contains the declaration (e.g. `centeredEstimator`), just untagged. It
// then surfaces only in the collapsed "Auxiliary Lean lemmas" group, unlinked to
// the printed definition. This matcher recovers the link so the printed
// definition opens the verified Lean instead of claiming "no standalone Lean
// declaration".
//
// Matching is DELIBERATELY conservative (see the run policy decision): a
// definition is linked ONLY when its concept key (prose of the title, falling
// back to the obj_id) equals a def-like declaration's name key EXACTLY after
// normalization, and that declaration is UNIQUE. This is a zero-false-link rule —
// a plural/singular or synonym gap leaves the definition presentation-synthesized
// (the honest state) rather than risk asserting a wrong Lean correspondence.

/** Def-like Lean kinds a synthesized DEFINITION may be homed by. Lemmas/theorems
 *  are proof helpers, never the formal object a definition introduces. */
const DEF_LIKE_KINDS = new Set(["def", "abbrev", "structure", "instance"]);

/** Minimum normalized-key length. Guards against trivial/ambiguous collisions
 *  (`mse`, `obs`) that a 2–3 char key would produce. */
const MIN_KEY_LEN = 6;

/** Normalize a title/obj_id/decl-name to its comparison key: drop LaTeX math and
 *  commands, then keep lowercase alphanumerics only. `Centered estimator
 *  \(\widehat\tau_{\mathrm{ctr}}\)` and `centeredEstimator` both key to
 *  `centeredestimator`. */
export function conceptKey(raw: string): string {
  const prose = raw
    .replace(/\$[^$]*\$/g, " ") // inline $...$
    .replace(/\\\([\s\S]*?\\\)/g, " ") // inline \(...\)
    .replace(/\\\[[\s\S]*?\\\]/g, " ") // display \[...\]
    .replace(/\\[a-zA-Z]+/g, " "); // residual LaTeX commands
  return prose.toLowerCase().replace(/[^a-z0-9]/g, "");
}

/** The short (unqualified) name of a possibly dotted Lean decl name. */
export function shortDeclName(name: string): string {
  const i = name.lastIndexOf(".");
  return i < 0 ? name : name.slice(i + 1);
}

export interface DeclLoc {
  file: string;
  line: number;
  kind?: string;
}

export interface SynthLeanMatch {
  decl: string;
  file: string;
  line: number;
  decl_kind: string;
}

/**
 * The unique def-like declaration that formalizes a synthesized definition, or
 * null when there is no exact, unambiguous name match. `title` is the env title
 * (prose + notation); `objId` is the fallback key source (e.g.
 * `def:centered-estimator`, with the `def:`/`ass:` prefix stripped).
 */
export function matchSynthDecl(
  title: string | null | undefined,
  objId: string,
  moduleDecls: Map<string, DeclLoc>,
): SynthLeanMatch | null {
  const candidateKeys = new Set<string>();
  if (title) candidateKeys.add(conceptKey(title));
  candidateKeys.add(conceptKey(objId.replace(/^[a-z]+:/, "")));
  const keys = [...candidateKeys].filter((k) => k.length >= MIN_KEY_LEN);
  if (keys.length === 0) return null;

  const hits: { name: string; loc: DeclLoc }[] = [];
  for (const [name, loc] of moduleDecls) {
    if (loc.kind && !DEF_LIKE_KINDS.has(loc.kind)) continue;
    if (keys.includes(conceptKey(shortDeclName(name)))) hits.push({ name, loc });
  }
  // Require a unique target: an ambiguous key (two decls share it) is not a
  // confident link.
  const uniqueByName = [...new Map(hits.map((h) => [shortDeclName(h.name), h])).values()];
  if (uniqueByName.length !== 1) return null;
  const { name, loc } = uniqueByName[0];
  return {
    decl: shortDeclName(name),
    file: loc.file,
    line: loc.line,
    decl_kind: loc.kind && DEF_LIKE_KINDS.has(loc.kind) ? loc.kind : "def",
  };
}
