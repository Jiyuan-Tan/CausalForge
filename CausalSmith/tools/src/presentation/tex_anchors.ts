import { createHash } from "node:crypto";

/**
 * Parser + linter for obj_id-anchored formal environments in paper tex.
 * The anchor chain's enforcement point: every formal environment must carry a
 * crosswalk obj_id, and after the P1 freeze its body must not drift.
 */

export interface AnchoredEnv {
  env: "theoremv" | "assumptionv" | "lemmav" | "definitionv" | "citedv" | "propositionv" | "remarkv";
  obj_id: string;
  title: string | null;
  body: string;
  order: number; // appearance order, used for paper numbering ("Theorem 2")
}

export interface LintProblem {
  gate: string;
  detail: string;
  /** The environment this problem is attributable to (for the readability revise loop). */
  objId?: string;
}

const ENV_BEGIN_RE =
  /\\begin\{(theoremv|assumptionv|lemmav|definitionv|citedv|propositionv|remarkv)\}\{([^}]+)\}/g;
const BARE_RE = /\\begin\{(theorem|assumption|lemma|definition|proposition|corollary)\}/g;

interface EnvMatch extends AnchoredEnv {
  scopeMarked: boolean;
  start: number;
  bodyStart: number;
  bodyEnd: number;
  end: number;
  raw: string;
}

function readOptionalTitle(tex: string, pos: number): { title: string | null; end: number } {
  if (tex[pos] !== "[") return { title: null, end: pos };
  let depth = 1;
  for (let i = pos + 1; i < tex.length; i++) {
    if (tex[i] === "\\") {
      i++; // why: escaped brackets in titles are display text, not delimiters.
    } else if (tex[i] === "[") {
      depth++;
    } else if (tex[i] === "]") {
      depth--;
      if (depth === 0) return { title: tex.slice(pos + 1, i), end: i + 1 };
    }
  }
  return { title: null, end: pos };
}

function scanAnchoredEnvs(tex: string): EnvMatch[] {
  const out: EnvMatch[] = [];
  let order = 0;
  ENV_BEGIN_RE.lastIndex = 0;
  let m: RegExpExecArray | null;
  while ((m = ENV_BEGIN_RE.exec(tex))) {
    const env = m[1] as AnchoredEnv["env"];
    const afterId = ENV_BEGIN_RE.lastIndex;
    const title = readOptionalTitle(tex, afterId);
    // A star after the optional title is presentation metadata: the environment macro places a
    // generated verification-footnote mark in the theorem heading. It is deliberately excluded
    // from the parsed/frozen body, just like the obj-id and title.
    const scopeMarked = tex[title.end] === "*";
    const bodyStart = title.end + (scopeMarked ? 1 : 0);
    const endTag = `\\end{${env}}`;
    const bodyEnd = tex.indexOf(endTag, bodyStart);
    if (bodyEnd < 0) continue;
    const end = bodyEnd + endTag.length;
    out.push({
      env,
      obj_id: m[2],
      title: title.title,
      body: tex.slice(bodyStart, bodyEnd),
      order: order++,
      scopeMarked,
      start: m.index,
      bodyStart,
      bodyEnd,
      end,
      raw: tex.slice(m.index, end),
    });
    ENV_BEGIN_RE.lastIndex = end;
  }
  return out;
}

function replaceAnchoredEnvs(tex: string, f: (e: EnvMatch) => string): string {
  const envs = scanAnchoredEnvs(tex);
  let out = tex;
  for (let i = envs.length - 1; i >= 0; i--) out = out.slice(0, envs[i].start) + f(envs[i]) + out.slice(envs[i].end);
  return out;
}

/** Append deterministic material immediately after selected anchored environments. */
export function appendAfterAnchoredEnvs(tex: string, suffixById: Map<string, string>): string {
  return replaceAnchoredEnvs(tex, (e) => {
    const suffix = suffixById.get(e.obj_id);
    return suffix ? `${e.raw}\n${suffix}` : e.raw;
  });
}

/** Ensure exactly the selected anchored environments carry the generated heading-footnote mark. */
export function normalizeAnchoredEnvScopeMarkers(tex: string, markedIds: Set<string>): string {
  return replaceAnchoredEnvs(tex, (e) => {
    const markerStart = e.bodyStart - e.start - (e.scopeMarked ? 1 : 0);
    const afterMarker = markerStart + (e.scopeMarked ? 1 : 0);
    return `${e.raw.slice(0, markerStart)}${markedIds.has(e.obj_id) ? "*" : ""}${e.raw.slice(afterMarker)}`;
  });
}

function stripAnchoredEnvBlocks(tex: string): string {
  return replaceAnchoredEnvs(tex, () => " ");
}

const PROSE_HEADING_RE = /\\(section|subsection|subsubsection)\*?\{([^}]*)\}/g;
const LIMITATION_HEADING_RE = /\b(?:limitations?|future work|future research|open questions?)\b/i;

/** Mask sections where explicit non-coverage statements are legitimate reader-facing content. */
function maskLimitationSections(tex: string): string {
  const headings: { start: number; level: number; title: string }[] = [];
  PROSE_HEADING_RE.lastIndex = 0;
  for (let m = PROSE_HEADING_RE.exec(tex); m; m = PROSE_HEADING_RE.exec(tex)) {
    headings.push({
      start: m.index,
      level: m[1] === "section" ? 1 : m[1] === "subsection" ? 2 : 3,
      title: m[2],
    });
  }
  const chars = tex.split(""); // preserve UTF-16 offsets reported by RegExp.index
  for (let i = 0; i < headings.length; i++) {
    const h = headings[i];
    if (!LIMITATION_HEADING_RE.test(h.title)) continue;
    const next = headings.slice(i + 1).find((x) => x.level <= h.level);
    const end = next?.start ?? tex.length;
    for (let j = h.start; j < end; j++) if (chars[j] !== "\n" && chars[j] !== "\r") chars[j] = " ";
  }
  return chars.join("");
}

const CONTRIBUTION_SUBJECT =
  "(?:this|the)\\s+(?:paper|work|article|study|analysis|result|theorem|lemma|bound|construction|method|approach|estimator|criterion|comparison|contribution|framework|rate|term|object|scope|target)|" +
  "our\\s+(?:paper|work|study|analysis|result|theorem|bound|construction|method|approach|estimator|contribution|framework)|we";
const NEGATIVE_CONTRIBUTION_RE = [
  new RegExp(`\\b(?:${CONTRIBUTION_SUBJECT})\\s+(?:do(?:es)?|is|are|has|have|can|could|will|would)\\s+not\\b`, "gi"),
  new RegExp(`\\b(?:${CONTRIBUTION_SUBJECT})\\s+(?:provide|offer|give|make|claim|establish|prove|derive|characterize|address|attempt|pursue)s?\\s+no\\b`, "gi"),
  /\b(?:this|it)\s+(?:is|was|are|were)\s+not\b/gi,
  /\b(?:the|these|our)\s+(?:results?|analysis|method|approach|construction|criterion|comparison|contribution|framework|rate|term|object|scope|target)\s+(?:is|are|was|were)\b[^.!?\n]{0,120},\s*not\b/gi,
  /\bno\s+(?:new\s+)?(?:estimator|test|procedure|algorithm|inference|standard errors?|finite-sample result|identification theorem|optimality claim)\s+(?:is|are|was|were)\s+(?:provided|proposed|proved|established|derived|developed|claimed)\b/gi,
  /\b(?:the|a|one)\s+(?:(?:key|main|important|central|major|primary)\s+)?(?:caveat|limitation|shortcoming|weakness|restriction)\s+(?:is|was|comes?\s+from|concerns?|lies?\s+in)\b/gi,
  /\b(?:the|these|our)\s+(?:results?|guarantees?|conclusions?|claims?|rates?|bounds?)\s+(?:hold|apply|are\s+(?:proved|shown|established|available))\s+only\b/gi,
  /\b(?:the|this|our)\s+(?:result|guarantee|claim|rate|bound|analysis|construction|method|estimator|schedule|design)\s+(?:is|was)\s+only\s+(?:proved|shown|established|derived|available)\b/gi,
  /\b(?:left|remains?|is|are|was|were)\s+(?:as\s+)?(?:an?\s+)?(?:open|unresolved)\s+(?:design\s+|research\s+)?(?:question|problem|issue|frontier)\b/gi,
  /\b(?:open|unresolved)\s+(?:design\s+|research\s+)?(?:question|problem|issue|frontier)\b/gi,
];

/**
 * Reader-facing contribution prose should lead with delivered results. Negative scope framing is
 * allowed only in explicitly labelled limitations/future-work sections. Frozen statements, proofs,
 * and generated verification disclosures are excluded because their negation can be mathematical or
 * mechanically required rather than editorial framing.
 */
export function lintNegativeContributionFraming(tex: string): LintProblem[] {
  let prose = maskLimitationSections(tex);
  prose = stripAnchoredEnvBlocks(prose)
    .replace(/\\begin\{proof\}(?:\[[^\]]*\])?[\s\S]*?\\end\{proof\}/g, " ")
    .replace(/% CAUSALSMITH-CITED-SCOPE-BEGIN[^\n]*[\s\S]*?% CAUSALSMITH-CITED-SCOPE-END[^\n]*/g, " ")
    .replace(/(?<!\\)%.*$/gm, " ");
  const hits = new Map<number, LintProblem>();
  for (const re of NEGATIVE_CONTRIBUTION_RE) {
    re.lastIndex = 0;
    for (let m = re.exec(prose); m; m = re.exec(prose)) {
      const left = Math.max(prose.lastIndexOf("\n", m.index), prose.lastIndexOf(". ", m.index)) + 1;
      const period = prose.indexOf(". ", m.index + m[0].length);
      const newline = prose.indexOf("\n", m.index + m[0].length);
      const candidates = [period < 0 ? prose.length : period + 1, newline < 0 ? prose.length : newline];
      const right = Math.min(...candidates.filter((x) => x >= m.index));
      const excerpt = prose.slice(left, right).replace(/\s+/g, " ").trim().slice(0, 320);
      const line = prose.slice(0, m.index).split("\n").length;
      hits.set(left, {
        gate: "negative-contribution-framing",
        detail: `line ${line}: "${excerpt}" — state the delivered contribution/scope affirmatively, or move genuine non-coverage to an explicitly titled Limitations/Future Work/Open Questions section`,
      });
    }
  }
  return [...hits.values()];
}

export function parseAnchoredEnvs(tex: string): AnchoredEnv[] {
  return scanAnchoredEnvs(tex).map(({ env, obj_id, title, body, order }) => ({ env, obj_id, title, body, order }));
}

function atSentenceStart(source: string, offset: number): boolean {
  const prior = source.slice(0, offset).trimEnd();
  return prior.length === 0 || /[.!?]\s*$/.test(prior);
}

/** One-time-safe canonicalization used before authored text is frozen or emitted. It removes a
 * manually asserted reference kind and upgrades every legacy `\ref` command to target-typed
 * cleveref. Running it repeatedly is idempotent; label ids and mathematical content are unchanged. */
export function normalizeCrefs(tex: string): string {
  let out = tex.replace(
    /\b(?:Appendix|Appendices|Chapters?|Sections?|Figures?|Tables?|Equations?|Theorems?|Lemmas?|Definitions?|Assumptions?|Propositions?|Remarks?|Cited results?)\s*~?\s*\\(?:Cref|cref|autoref|eqref|ref)\{([^}]+)\}/gi,
    (_whole, label: string, offset: number, source: string) =>
      `\\${atSentenceStart(source, offset) ? "Cref" : "cref"}{${label}}`,
  );
  out = out.replace(/\\(?:auto|eq)?ref\{([^}]+)\}/g, (_whole, label: string, offset: number, source: string) =>
    `\\${atSentenceStart(source, offset) ? "Cref" : "cref"}{${label}}`);
  return out;
}

/** @deprecated Use `normalizeCrefs`; retained for downstream callers during the migration. */
export const normalizeObjCrefs = normalizeCrefs;

/**
 * Repair + lint `\cref{obj:…}`/`\Cref{obj:…}` cross-references against the labels actually defined in the paper
 * (every anchored-env argument becomes a `\label{obj:<arg>}`). Drafting models sometimes drop a
 * kind prefix from an env id (e.g. `\cref{obj:oracle-regime-reduction}` for an env anchored at
 * `prop:oracle-regime-reduction`), which LaTeX renders as a silent `??`. This deterministically
 * rewrites such a ref to its unique prefixed label, and reports any `obj:` ref that still resolves
 * to no defined env (a dangling `??`) so the stage fails loud instead of shipping the broken link.
 *
 * Only the `obj:` label namespace is touched. The command is preserved; syntax canonicalization is
 * handled separately by `normalizeCrefs` before a body freezes.
 * `definedIds` is the set of env-argument ids present in the paper (use `parseAnchoredEnvs`).
 */
export function repairObjRefs(tex: string, definedIds: Set<string>): { tex: string; problems: LintProblem[] } {
  const problems: LintProblem[] = [];
  const out = tex.replace(/\\(Cref|cref|ref)\{([^}]+)\}/g, (whole, command: string, rawLabels: string) => {
    const labels = rawLabels.split(",").map((x) => x.trim());
    if (!labels.some((x) => x.startsWith("obj:"))) return whole;
    const repaired = labels.map((label) => {
      if (!label.startsWith("obj:")) return label;
      const id = label.slice(4);
      if (definedIds.has(id)) return label;
      // A unique env whose id is `<kind>:<id>` (the drafter dropped the kind prefix) → repair.
      const matches = [...definedIds].filter((d) => d.endsWith(`:${id}`));
      if (matches.length === 1) return `obj:${matches[0]}`;
      problems.push({
        gate: "undefined-ref",
        detail:
          matches.length === 0
            ? `\\${command}{obj:${id}} resolves to no defined environment (renders as "??"); point it at an existing env label`
            : `\\${command}{obj:${id}} is ambiguous — matches ${matches.map((d) => `obj:${d}`).join(", ")}; use the full label`,
      });
      return label;
    });
    return `\\${command}{${repaired.join(",")}}`;
  });
  return { tex: out, problems };
}

/**
 * Replace the body of the formal environment anchored at `objId` with `newBody`, preserving the
 * environment kind, obj-id, and optional title. Used by the P3 refine loop to write a statement
 * tightened toward Lean fidelity back into the frozen layer + paper. Returns the tex unchanged if
 * no such environment is found.
 */
export function replaceEnvBody(tex: string, objId: string, newBody: string): string {
  return replaceAnchoredEnvs(tex, (e) =>
    e.obj_id === objId ? `${tex.slice(e.start, e.bodyStart)}\n${newBody.trim()}\n${tex.slice(e.bodyEnd, e.end)}` : e.raw,
  );
}

/** Whitespace-insensitive: reflowing prose is not drift, changing tokens is. */
export function hashEnvBody(body: string): string {
  return createHash("sha256").update(body.replace(/\s+/g, " ").trim()).digest("hex");
}

/**
 * Reject inline/display math delimiters nested inside a display block. LaTeX may
 * compile some malformed variants, but Pandoc preserves the nested delimiters
 * and the site's KaTeX pass then exposes the raw TeX as a rendering error.
 */
export function lintNestedMathDelimiters(tex: string): LintProblem[] {
  const problems: LintProblem[] = [];
  // The negative lookbehind matters for cases/arrays: `\\[1.1em]` is a TeX row break with
  // vertical spacing, and its second backslash must not be mistaken for a nested `\[` opener.
  const displayRe = /(?<!\\)\\\[([\s\S]*?)(?<!\\)\\\]/g;
  let match: RegExpExecArray | null;
  while ((match = displayRe.exec(tex))) {
    const nested = /(?<!\\)\\\(|(?<!\\)\\\[/.test(match[1]);
    const paragraphArray = match[1].includes("\\begin{array}{p{");
    if (nested || paragraphArray) {
      const line = tex.slice(0, match.index).split("\n").length;
      problems.push({
        gate: paragraphArray ? "web-incompatible-math" : "nested-math-delimiter",
        detail: paragraphArray
          ? `display math beginning on line ${line} uses an array with paragraph columns; use a table/tabular environment so KaTeX does not expose raw TeX`
          : `display math beginning on line ${line} contains a nested \\(...\\) or \\[...\\] delimiter; move prose outside the display and keep only bare math inside`,
      });
    }
  }
  return problems;
}

/** Unicode math chars that note headers carry; pdflatex chokes on them raw. */
const TEX_CHAR: Record<string, string> = {
  "κ": "\\kappa ", "β": "\\beta ", "λ": "\\lambda ", "ρ": "\\rho ", "τ": "\\tau ",
  "η": "\\eta ", "μ": "\\mu ", "φ": "\\varphi ", "χ": "\\chi ", "Δ": "\\Delta ",
  "Ω": "\\Omega ", "𝒫": "\\mathcal{P}", "𝒳": "\\mathcal{X}", "≲": "\\lesssim ",
  "≤": "\\le ", "≥": "\\ge ", "≍": "\\asymp ", "∈": "\\in ", "−": "-", "⋆": "\\star ",
  "†": "\\dagger ", "★": "\\star ",
};

function mapTexChars(s: string): string {
  // combining circumflex: `τ̂` → \hat{\tau}
  s = s.replace(/(.)̂/gu, (_, c: string) => `\\hat{${TEX_CHAR[c]?.trim() ?? c}}`);
  // the `u` flag makes `.` match full code points (𝒫 is a surrogate pair)
  return s.replace(/./gsu, (c) => TEX_CHAR[c] ?? c);
}

/**
 * Note-block titles arrive with backtick Lean-ish notation, raw Unicode math,
 * and pipeline vocabulary; none of that may reach the PDF. Backtick spans
 * become math mode, Unicode is transliterated, "(P-form of A2)" → "(A2)",
 * ".tex NNN-NNN" anchors are dropped.
 */
export function texSafeTitle(title: string): string {
  let t = title
    .replace(/\(P-form of (A\d+)[^)]*\)/g, "($1)")
    .replace(/,?\s*\.tex[\s0-9–-]+/g, "")
    .replace(/–/g, "--")
    // Self-containedness: development-history adjectives describe the note's
    // revision process, not the mathematics — they may not reach the paper.
    .replace(/^(Corrected|Revised|Updated|Amended|Fixed|Final)\s+(\S)/i, (_, _adj, c: string) =>
      c.toUpperCase(),
    );
  t = t.replace(/`([^`]*)`/g, (_, span: string) => {
    const mapped = mapTexChars(span);
    // a span already carrying its own $…$ manages its math mode itself
    return span.includes("$") ? mapped : `$${mapped}$`;
  });
  return mapTexChars(t).replace(/\s+([,)\]])/g, "$1").trim();
}

/**
 * Replaces every anchored env block with its canonical frozen text (keyed by
 * obj_id). Drafting models occasionally paraphrase a body while "copying" it
 * into a section; the frozen layer is the trust anchor, so the mechanical
 * substitution — not the model's copy — is what reaches the paper. Blocks with
 * an obj_id missing from the canonical map are left as-is (the lint flags them).
 */
export function normalizeFrozenEnvs(tex: string, canonical: Map<string, string>): string {
  return replaceAnchoredEnvs(tex, (e) => canonical.get(e.obj_id) ?? e.raw);
}

/**
 * Drops \label{obj:...} from inside anchored env bodies. The env macro already
 * defines that label; drafting models sometimes add it anyway, which would be
 * a duplicate label in LaTeX and reads as frozen-drift to the linter.
 */
export function stripRedundantEnvLabels(tex: string): string {
  return replaceAnchoredEnvs(tex, (e) =>
    tex.slice(e.start, e.bodyStart) + e.body.replace(/[ \t]*\\label\{obj:[^}]*\}\n?/g, "") + tex.slice(e.bodyEnd, e.end),
  );
}

/**
 * Self-containedness gate. A named assumption/condition label invoked as
 * hypothesis shorthand (e.g. "Assumptions A1--A4", "Assumption~A5") must have a
 * defining environment — the label token must appear inside some
 * definitionv/assumptionv body or title. A label used only inside theorem
 * hypotheses with no definition anywhere is a defect the reader cannot resolve
 * (the A1–A5 / law-class miss). Ranges are expanded (A1--A4 → A1,A2,A3,A4) and
 * connectors (`--`, `,`, `and`, `to`) are followed. Returns one problem per
 * distinct undefined label.
 */
export function lintSelfContainment(tex: string): LintProblem[] {
  const defined = new Set<string>();
  for (const e of parseAnchoredEnvs(tex)) {
    if (e.env === "definitionv" || e.env === "assumptionv") {
      for (const t of `${e.title ?? ""} ${e.body}`.match(/\b[A-Z]\d+\b/g) ?? []) defined.add(t);
    }
  }
  const problems: LintProblem[] = [];
  const seen = new Set<string>();
  const clauseRe =
    /\bAssumptions?\b[~\s]*([A-Z]\d+(?:\s*(?:--|–|-|,|;|and|to|through|~|\s)+[A-Z]?\d+)*)/g;
  let m: RegExpExecArray | null;
  while ((m = clauseRe.exec(tex))) {
    const grp = m[1].replace(
      /([A-Z])(\d+)\s*(?:--|–|-|to|through)\s*([A-Z]?)(\d+)/g,
      (whole, L: string, a: string, L2: string, b: string) => {
        const lo = +a;
        const hi = +b;
        if ((L2 === "" || L2 === L) && hi >= lo && hi - lo < 50) {
          const xs: string[] = [];
          for (let i = lo; i <= hi; i++) xs.push(L + i);
          return xs.join(" ");
        }
        return whole;
      },
    );
    for (const lab of grp.match(/[A-Z]\d+/g) ?? []) {
      if (defined.has(lab) || seen.has(lab)) continue;
      seen.add(lab);
      problems.push({
        gate: "undefined-assumption",
        detail: `named assumption "${lab}" is referenced but has no defining environment (definitionv/assumptionv) — a reader cannot resolve it; give it a defining env or fold it into the law-class definition`,
      });
    }
  }
  return problems;
}

/**
 * Readability gate (the clarity check the equivalence gate cannot do: it verifies
 * statements MATCH the Lean, never that they READ as a paper). Two defect classes
 * in the displayed statement bodies, both reader-facing:
 *
 *  1. `lean-identifier` — a raw Lean declaration name leaking into displayed math.
 *     Lean decls are multi-word camelCase/PascalCase (≥3 segments) like
 *     `smoothedInverseWeightRegression`, `CrossFitNuisancesRandom`,
 *     `LowerClassWitnessClosure`. A statement must render these as mathematical
 *     notation (per the notation table), never the identifier. (Single-word names,
 *     all-caps acronyms like AIPW/DML, and `\command`s are NOT flagged.)
 *  2. `formalization-leak` — formalization-procedure / "Lean-side" phrasing in a
 *     statement body ("Assume the following Lean-side inputs", "checks have shown
 *     that…"). A statement states the mathematics, not how it was machine-checked.
 *
 * Catches the leak no matter which stage authored the env (P1 touch-up OR an
 * orchestrator re-freeze that bypassed the touch-up prompt). Runs before the P1
 * freeze so the producer must clean it.
 */
const LEAN_IDENT_RE = /(?<![\\A-Za-z0-9])[A-Za-z][a-z0-9]*(?:[A-Z][a-z0-9]+){2,}\b/g;
const FORMALIZATION_PHRASING: { re: RegExp; what: string }[] = [
  { re: /Lean[-\s]?side/i, what: `"Lean-side" formalization framing` },
  { re: /Lean[-\s]?verified input/i, what: `"Lean-verified inputs" framing` },
  { re: /\bchecks have shown\b/i, what: `proof-procedure phrasing ("checks have shown")` },
  { re: /analytic shape and scale checks/i, what: `proof-procedure phrasing ("…shape and scale checks…")` },
];
export function lintClarity(tex: string): LintProblem[] {
  const problems: LintProblem[] = [];
  for (const e of parseAnchoredEnvs(tex)) {
    const idents = new Set<string>();
    let m: RegExpExecArray | null;
    // BibTeX keys are opaque identifiers by design and often look like PascalCase Lean names
    // (`BochnakCosteRoy1998`). They are citation provenance, not displayed mathematical prose.
    const proseBody = e.body.replace(/\\cite[A-Za-z]*\s*(?:\[[^\]]*\]\s*){0,2}\{[^}]*\}/g, "");
    LEAN_IDENT_RE.lastIndex = 0;
    while ((m = LEAN_IDENT_RE.exec(proseBody))) idents.add(m[0]);
    for (const id of idents) {
      problems.push({
        gate: "lean-identifier",
        objId: e.obj_id,
        detail: `${e.obj_id}: Lean declaration name "${id}" appears in the displayed statement — render it as mathematical notation (per the notation table), never the raw identifier`,
      });
    }
    for (const p of FORMALIZATION_PHRASING) {
      if (p.re.test(e.body)) {
        problems.push({
          gate: "formalization-leak",
          objId: e.obj_id,
          detail: `${e.obj_id}: ${p.what} in the statement body — state the mathematical condition, not how it was formalized/checked`,
        });
      }
    }
  }
  return problems;
}

/**
 * Reference/structure readability gate (#3b numbering + #6 bare cross-references).
 *  - `assumption-numbering`: assumption A-labels (the "(A_k)" in titles) must be
 *    consecutive and agree with the printed Assumption order — never A1,A2,A4,…
 *    (a gap at A3) or "Assumption 3" labelled (A4). Renumber to one scheme.
 *  - `legacy-ref`: every reader-facing reference uses cleveref so its target,
 *    rather than surrounding prose, determines the printed kind.
 *  - `reference-kind`: a typed reference must name the environment it targets;
 *    e.g. `Section~\ref{obj:def:risk}` must not silently render as "Section 14".
 */
const PREP_REF_RE = /\b(of|in|from|see)\s*~?\s*\\ref\{obj:([^}]+)\}/g;
const TYPED_OBJ_REF_RE = /\b(Sections?|Theorems?|Lemmas?|Definitions?|Assumptions?|Propositions?|Remarks?|Cited results?)~\\ref\{obj:([^}]+)\}/gi;
const MANUALLY_TYPED_CREF_RE = /\b(Appendix|Appendices|Chapters?|Sections?|Figures?|Tables?|Equations?|Theorems?|Lemmas?|Definitions?|Assumptions?|Propositions?|Remarks?|Cited results?)\s*~?\s*\\(?:c|C)ref\{([^}]+)\}/gi;
const ENV_REFERENCE_KIND: Record<AnchoredEnv["env"], string> = {
  theoremv: "theorem",
  assumptionv: "assumption",
  lemmav: "lemma",
  definitionv: "definition",
  citedv: "cited result",
  propositionv: "proposition",
  remarkv: "remark",
};
/**
 * Notation-resolvability gate (deterministic; the Hölder-class incident). A
 * PARAMETERIZED named class — `\mathcal{X}` immediately followed by a super/sub
 * script or argument list (`\mathcal H^\beta(...)`, `\mathcal P_{\kappa,...}`) —
 * used in a STATEMENT (non-definition) body must be DEFINED somewhere anchored: a
 * `definitionv` whose title names it, or a "we say/denote/the class/let … X" /
 * "X := …" phrase. A bare ambient space (`\mathcal X`, no parameters) is NOT
 * checked. Flags a parameterized class used in a statement with no such anchor.
 */
// Which fonts name a CLASS for the deterministic detector. Calligraphic/script/
// fraktur are low false-positive (function classes, σ-fields, law families) — unlike
// `\mathbb` (standard sets ℝ, 𝔼, ℙ → `\mathbb E_{H_n}` is not an orphan) and `\mathrm`
// (operators, but also sub/superscript labels like `\varphi^{\mathrm{bd}}`), which the
// codex notation check handles with its standard-symbol exclusions and operator-vs-
// label judgment. Each font's letters are written both braced (`\mathcal{H}`) and
// bare/spaced (`\mathcal H`) in the same paper — the Hölder-ball incident: the
// braced-only regex missed every `\mathcal H^\beta`. Match both forms and canonicalise
// to `\<font>{X}` so the two spellings of one class collide (a def `\mathcal{P}`
// covers a use `\mathcal P`).
const CLASS_FONTS = "mathcal|mathscr|mathfrak";
const CLASS_FONT_RE = new RegExp(`\\\\(${CLASS_FONTS})\\s*(?:\\{([A-Z])\\}|([A-Z]))`, "g");
/** Canonical class symbols (`\mathcal{H}`, …) in a string; exported so the P1
 *  synthesis pass can match a cached Definition (by the class its title names) to
 *  a detected orphan. */
export function classSymbolsIn(s: string): string[] {
  const out: string[] = [];
  for (const m of s.matchAll(CLASS_FONT_RE)) out.push(`\\${m[1]}{${m[2] ?? m[3]}}`);
  return out;
}
const CLASS_FONT_SRC = `\\\\(?:${CLASS_FONTS})\\s*(?:\\{[A-Z]\\}|[A-Z])`;

export function orphanParameterizedClasses(tex: string): { symbol: string; usedIn: string[] }[] {
  const envs = parseAnchoredEnvs(tex);
  const defined = new Set<string>();
  for (const e of envs) {
    if (e.env === "definitionv") for (const c of classSymbolsIn(e.title ?? "")) defined.add(c);
    for (const m of e.body.matchAll(new RegExp(`(?:we say|denote|the class|let)\\b[^.]{0,50}?(${CLASS_FONT_SRC})`, "gi")))
      for (const c of classSymbolsIn(m[1])) defined.add(c);
    for (const m of e.body.matchAll(new RegExp(`(${CLASS_FONT_SRC})[\\s^_{}A-Za-z0-9\\\\,;()|-]{0,30}?:=`, "g")))
      for (const c of classSymbolsIn(m[1])) defined.add(c);
  }
  const used = new Map<string, Set<string>>();
  for (const e of envs) {
    if (e.env === "definitionv") continue;
    // PARAMETERIZED use only: the class is immediately followed by a super/sub
    // script or argument list (a bare ambient `\mathcal X` is not a named class).
    for (const m of e.body.matchAll(new RegExp(`(${CLASS_FONT_SRC})\\s*(\\^|_|\\()`, "g"))) {
      const sym = classSymbolsIn(m[1])[0];
      if (!sym || defined.has(sym)) continue;
      // Standard-normal notation is ordinary mathematics, not a paper-defined class.  Without
      // this exclusion, `Z\\sim\\mathcal N(0,1)` is routed into P1's synthesize-definition loop;
      // that adds a redundant definition of the normal law and can consume the whole repair cap.
      // Keep parameterized neighbourhoods such as `\\mathcal N_i` covered by the detector.
      if (sym === "\\mathcal{N}" && m[2] === "(") {
        const call = e.body.slice((m.index ?? 0) + m[0].length - 1);
        if (/^\(\s*0\s*,\s*1\s*\)/.test(call)) continue;
      }
      let s = used.get(sym);
      if (!s) used.set(sym, (s = new Set()));
      s.add(e.obj_id);
    }
  }
  return [...used].map(([symbol, ids]) => ({ symbol, usedIn: [...ids] }));
}

export function lintNotation(tex: string): LintProblem[] {
  return orphanParameterizedClasses(tex).map(({ symbol, usedIn }) => ({
    gate: "notation-undefined",
    detail: `the named class ${symbol} is used in ${usedIn.join("/")} but has no defining environment (no definitionv whose title names it, nor a "we say … ${symbol} … when" / "${symbol} := …" phrase) — give it an anchored definition and \\ref it from each use`,
  }));
}

interface NotationHome {
  symbol: string;
  home: string;
}

/** Parse the P1 notation table rows that assign a paper symbol to an anchored home. */
export function notationHomes(notation: string): NotationHome[] {
  const out: NotationHome[] = [];
  for (const line of notation.split("\n")) {
    if (!/^\s*\|/.test(line)) continue;
    const cells = line.split("|").slice(1, -1).map((x) => x.trim());
    if (cells.length < 4 || cells[0].toLowerCase() === "note symbol" || /^-+$/.test(cells[0])) continue;
    const home = cells[3].replace(/^`|`$/g, "").trim();
    if (!/^[A-Za-z0-9:_-]+$/.test(home) || home === "notation_gaps") continue;
    let symbol = cells[1]
      .replace(/^\\\(|\\\)$/g, "")
      .replace(/^\$|\$$/g, "")
      .trim();
    // A scalar declaration such as `K_-=2m+1` names `K_-`; the right side is its definition.
    // By contrast, a composite relation such as `Phi(theta)=Phi(eta)` is not a new atomic symbol
    // and its row's "home" describes the relation, not either already-defined operand.
    if (symbol.includes("=")) {
      const lhs = symbol.split("=")[0].trim();
      if (/[()]/.test(lhs)) continue;
      symbol = lhs;
    }
    // Bare ASCII parameters are too overloaded for a sound text-only home check (`d` may denote
    // both a weight family and, later, a polynomial degree). Structured tokens and TeX-named
    // parameters remain unambiguous enough to gate deterministically.
    if (!symbol || /^[A-Za-z]$/.test(symbol) || /(?:\\ldots|\\dots)/.test(symbol)) continue;
    out.push({ symbol, home });
  }
  return out;
}

function notationSearchText(tex: string): string {
  return tex
    .replace(/(?<!\\)%.*$/gm, "")
    .replace(/\\(?:Cref|cref|ref|label|pageref)\{[^}]*\}/g, "")
    // The first argument is metadata, not a displayed use (`sym:u_j` must not count as `u_j`).
    .replace(/\\leanref\{[^{}]*\}/g, "")
    .replace(/\\ensuremath\s*\{/g, "{")
    .replace(/\\\(|\\\)|\\\[|\\\]|\$/g, "")
    .replace(/\s+/g, "");
}

export function containsNotation(tex: string, symbol: string): boolean {
  const haystack = notationSearchText(tex);
  const needle = notationSearchText(symbol);
  if (!needle) return false;
  // Single-letter parameters must be tokens: `m` must not match the `m` in `\mathrm`.
  if (/^[A-Za-z]$/.test(needle)) {
    for (let at = haystack.indexOf(needle); at >= 0; at = haystack.indexOf(needle, at + 1)) {
      const before = haystack[at - 1] ?? "";
      const after = haystack[at + 1] ?? "";
      if (!/[A-Za-z0-9\\]/.test(before) && !/[A-Za-z0-9_^]/.test(after)) return true;
    }
    return false;
  }
  // A TeX control word ends before the next non-letter (`\delta` must not match a longer command).
  if (/^\\[A-Za-z]+$/.test(needle)) {
    for (let at = haystack.indexOf(needle); at >= 0; at = haystack.indexOf(needle, at + 1)) {
      if (!/[A-Za-z]/.test(haystack[at + needle.length] ?? "")) return true;
    }
    return false;
  }
  return haystack.includes(needle);
}

/**
 * A deliberately narrow semantic signature for decorated estimator notation.
 * Presentation reviewers often alternate between, for example,
 * `\widehat\tau_{\mathrm{sel}}` and
 * `\widehat\tau^{\mathrm{sel}}_{C_\epsilon,\epsilon}`.  Exact TeX matching
 * treats those as different symbols and used to synthesize the same reader
 * definition twice.  The base accent/letter plus a descriptive decorator
 * (`sel`, `ctr`, `hyb`, …) is stable; parameter decorators are not part of the
 * notation family.
 *
 * This intentionally returns null for undecorated quantities and for generic
 * subscripts such as `n`, `d`, or `epsilon`, keeping the heuristic out of the
 * general notation resolver.
 */
export function estimatorNotationFamilies(tex: string): string[] {
  const compact = notationSearchText(tex);
  const ignored = new Set(["n", "d", "c", "epsilon", "varepsilon"]);
  const matches = [...compact.matchAll(/\\widehat\{?(\\[A-Za-z]+|[A-Za-z])\}?/g)];
  const out = new Set<string>();
  for (const match of matches) {
    if (match.index == null) continue;
    const base = match[0].replace(/[{}]/g, "");
    const suffix = compact.slice(match.index + match[0].length);
    let at = 0;
    const decorators: string[] = [];
    // Only consume scripts attached to this occurrence. Scanning the whole
    // remaining statement merges a selector with the hybrid/centered
    // estimators used in its defining branches.
    while (suffix[at] === "_" || suffix[at] === "^") {
      at += 1;
      if (suffix[at] === "{") {
        const start = ++at;
        let depth = 1;
        while (at < suffix.length && depth > 0) {
          if (suffix[at] === "{") depth += 1;
          else if (suffix[at] === "}") depth -= 1;
          at += 1;
        }
        decorators.push(suffix.slice(start, Math.max(start, at - 1)));
      } else {
        const token = suffix.slice(at).match(/^(?:\\[A-Za-z]+|[A-Za-z0-9-]+)/)?.[0];
        if (!token) break;
        decorators.push(token);
        at += token.length;
      }
    }
    const tags: string[] = [];
    for (const decorator of decorators) {
      for (const m of decorator.matchAll(/\\(?:mathrm|text)\{([A-Za-z][A-Za-z0-9-]*)\}/g)) tags.push(m[1].toLowerCase());
      if (/^[A-Za-z][A-Za-z0-9-]*$/.test(decorator)) tags.push(decorator.toLowerCase());
    }
    const descriptive = [...new Set(tags.filter((tag) => tag.length >= 2 && !ignored.has(tag)))].sort();
    if (descriptive.length > 0) out.add(`${base}:${descriptive.join(",")}`);
  }
  return [...out];
}

export function estimatorNotationFamily(tex: string): string | null {
  return estimatorNotationFamilies(tex)[0] ?? null;
}

export function sameEstimatorNotationFamily(a: string, b: string): boolean {
  const fa = new Set(estimatorNotationFamilies(a));
  return estimatorNotationFamilies(b).some((family) => fa.has(family));
}

export function proseDefinesNotation(prose: string, symbol: string): boolean {
  const flat = prose.replace(/\s+/g, " ");
  for (let i = 0; i < flat.length; i++) {
    const tail = flat.slice(i);
    if (!containsNotation(tail, symbol)) break;
    // Locate approximately in the original prose; this deliberately accepts only explicit
    // introduction language, not a symbol merely appearing in a diagram or motivation sentence.
    const raw = notationSearchText(symbol);
    const compactAt = notationSearchText(tail).indexOf(raw);
    if (compactAt < 0) break;
    const context = tail.slice(Math.max(0, compactAt - 100), compactAt + symbol.length + 100);
    if (/\b(?:define|denote|let|write|fix|put|set|where)\b/i.test(context) || /:=|=/u.test(context)) return true;
    i += Math.max(1, compactAt + symbol.length);
  }
  return false;
}

/**
 * Hard reader-scope gate: a notation-table symbol may not occur in a formal environment before
 * the anchored environment recorded as its home, unless preceding prose explicitly introduces it.
 * This complements `lintNotation`, which detects orphan named classes but cannot see ordinary
 * vectors/functions such as `u_j` or distinguish a later definition from an earlier one.
 */
export function lintDefinitionOrder(tex: string, notation: string): LintProblem[] {
  const envs = scanAnchoredEnvs(tex);
  const byId = new Map(envs.map((e) => [e.obj_id, e]));
  const problems: LintProblem[] = [];
  const seen = new Set<string>();
  for (const { symbol, home } of notationHomes(notation)) {
    const homeEnv = byId.get(home);
    if (!homeEnv) continue; // Missing homes are owned by the existing resolvability review.
    const firstUse = envs.find((e) => e.order < homeEnv.order && containsNotation(`${e.title ?? ""} ${e.body}`, symbol));
    if (!firstUse) continue;
    const proseBeforeUse = stripAnchoredEnvBlocks(tex.slice(0, firstUse.start));
    if (proseDefinesNotation(proseBeforeUse, symbol)) continue;
    const key = `${symbol}|${home}|${firstUse.obj_id}`;
    if (seen.has(key)) continue;
    seen.add(key);
    problems.push({
      gate: "notation-defined-after-use",
      objId: firstUse.obj_id,
      detail: `${symbol} is first used in ${firstUse.obj_id} before its notation-table home ${home}; move/introduce its definition before that use`,
    });
  }
  return problems;
}

/** Presentation floor for theorem/lemma STATEMENTS — enforces the two `p1_touchup` formatting rules
 *  the executor sometimes ignores for hypothesis-heavy results, which then ship because the body is
 *  hash-frozen (P2/P3/P4 cannot reformat a frozen statement). A finding makes the P1 router RE-RENDER
 *  before the freeze. Flags: (1) a `\ref`'d assumption whose content is RESTATED inline
 *  ("…\cref{obj:ass:…}, explicitly/namely …") — a `\cref` is sufficient and P3 accepts it as faithful,
 *  so the inline copy is dead weight; (2) several hypothesis conditions run together inline with no
 *  `\begin{itemize}` list. */
export function lintHypothesisPresentation(tex: string): LintProblem[] {
  const problems: LintProblem[] = [];
  // condition markers: an assumption ref, or a prose hypothesis introducer.
  const COND = /\\(?:Cref|cref|ref)\{[^}]*obj:ass:|\b(?:Assume|Fix|satisfying|provided|such that|eventually in)\b/gi;
  for (const e of parseAnchoredEnvs(tex)) {
    if (e.env !== "theoremv" && e.env !== "lemmav") continue;
    if (/\\(?:Cref|cref|ref)\{[^}]*obj:ass:[^}]*\}[^.]{0,40}?\b(?:explicitly|namely|i\.e\.|that is|which (?:states|requires|reads))\b/i.test(e.body)) {
      problems.push({
        gate: "hypothesis-restated",
        objId: e.obj_id,
        detail: `${e.obj_id}: a referenced assumption is RESTATED inline (e.g. "…\\cref{obj:ass:…}, explicitly …") — reference it by \\cref only and delete the duplicated content; P3 accepts a \\cref'd assumption as faithful.`,
      });
    }
    const conds = (e.body.match(COND) ?? []).length;
    if (conds >= 4 && !/\\begin\{itemize\}/.test(e.body)) {
      problems.push({
        gate: "hypothesis-not-itemized",
        objId: e.obj_id,
        detail: `${e.obj_id}: ${conds} hypothesis conditions are run together inline with no list — set the hypotheses as a \\begin{itemize} (one \\item per condition) before the conclusion.`,
      });
    }
  }
  return problems;
}

export function lintReferences(tex: string): LintProblem[] {
  const problems: LintProblem[] = [];
  const envById = new Map(parseAnchoredEnvs(tex).map((e) => [e.obj_id, e.env] as const));
  // #3b — assumption A-labels must be consecutive; a GAP (A1,A2,A4,…) makes the
  // printed "Assumption k" disagree with its "(A_j)" label (the reader's "where is
  // Assumption 3?" confusion). A single label or a consecutive run is fine.
  const aLabels: number[] = [];
  for (const e of parseAnchoredEnvs(tex)) {
    if (e.env !== "assumptionv") continue;
    const m = (e.title ?? "").match(/\(A(\d+)\)/);
    if (m) aLabels.push(Number(m[1]));
  }
  for (let k = 1; k < aLabels.length; k++) {
    if (aLabels[k] !== aLabels[k - 1] + 1) {
      problems.push({
        gate: "assumption-numbering",
        detail: `assumption A-labels are non-consecutive (…A${aLabels[k - 1]}, A${aLabels[k]}…): the gap makes the printed "Assumption k" disagree with its "(A_j)" label; renumber the assumptions consecutively`,
      });
      break;
    }
  }
  const seen = new Set<string>();
  let r: RegExpExecArray | null;
  for (const legacy of tex.matchAll(/\\((?:auto|eq)?ref)\{([^}]+)\}/g)) {
    problems.push({
      gate: "legacy-ref",
      detail: `\\${legacy[1]}{${legacy[2]}} bypasses the manuscript's target-typed reference convention — use \\cref{${legacy[2]}} (or \\Cref at sentence start) so the target supplies its own kind`,
    });
  }
  MANUALLY_TYPED_CREF_RE.lastIndex = 0;
  while ((r = MANUALLY_TYPED_CREF_RE.exec(tex))) {
    problems.push({
      gate: "manual-cref-kind",
      detail: `"${r[1]}~\\cref{${r[2]}}" duplicates a manually chosen kind — write \\cref{${r[2]}} and let the target determine the label`,
    });
  }
  PREP_REF_RE.lastIndex = 0;
  while ((r = PREP_REF_RE.exec(tex))) {
    const key = `${r[1].toLowerCase()}|${r[2]}`;
    if (seen.has(key)) continue;
    seen.add(key);
    problems.push({
      gate: "bare-ref",
      detail: `"${r[1]} \\ref{obj:${r[2]}}" renders as "${r[1]} <number>" — write "${r[1]} \\cref{obj:${r[2]}}" so cleveref supplies the environment kind`,
    });
  }
  TYPED_OBJ_REF_RE.lastIndex = 0;
  while ((r = TYPED_OBJ_REF_RE.exec(tex))) {
    const targetEnv = envById.get(r[2]);
    if (!targetEnv) continue; // undefined references are handled by repairObjRefs.
    const actual = r[1].replace(/s$/i, "").toLowerCase();
    const expected = ENV_REFERENCE_KIND[targetEnv];
    if (actual === expected) continue;
    problems.push({
      gate: "reference-kind",
      detail: `"${r[1]}~\\ref{obj:${r[2]}}" targets a ${expected} environment — write "\\cref{obj:${r[2]}}" so the target supplies the correct kind`,
    });
  }
  return problems;
}

/**
 * Cross-reference faithfulness (P1 §4.6.3, deterministic). The graph's
 * `statement-uses` edges say exactly which other paper envs an env's statement
 * depends on. `allowed` maps each env's obj_id → the set of paper-env target
 * obj_ids it may / must `\cref`. A `\cref{obj:X}` to an X outside that set is a
 * dangling reference (`xref-dangling`, enforced); a declared target the body never
 * references is a missing one (`xref-missing`, ADVISORY — natural prose may name a
 * dependency instead of `\ref`-ing it, so the stage treats it as a warning, not a
 * halt). Envs absent from `allowed` are unconstrained (skipped).
 *
 * NOTE: presumes a RENDERED (touched-up) body — the mechanical layer (raw
 * `nl.statement`) carries no cross-references, so running this before the touch-up would
 * flag every dependency. The P1 loop runs it only after a render pass (§4.6).
 */
export function lintCrossRefs(tex: string, allowed: Map<string, Set<string>>): LintProblem[] {
  const problems: LintProblem[] = [];
  for (const e of parseAnchoredEnvs(tex)) {
    const want = allowed.get(e.obj_id);
    if (!want) continue;
    const refs = new Set<string>();
    for (const m of e.body.matchAll(/\\(?:Cref|cref|ref)\{([^}]+)\}/g)) {
      for (const label of m[1].split(",").map((x) => x.trim())) {
        if (label.startsWith("obj:")) refs.add(label.slice(4));
      }
    }
    for (const r of refs) {
      if (!want.has(r)) {
        problems.push({
          gate: "xref-dangling",
          objId: e.obj_id,
          detail: `${e.obj_id}: \\cref{obj:${r}} is not a statement-uses dependency of ${e.obj_id}`,
        });
      }
    }
    for (const t of want) {
      if (!refs.has(t)) {
        // A statement-uses dependency on an ASSUMPTION is a load-bearing hypothesis that MUST be
        // surfaced via \ref (so it is clickable AND so a reader can trace the env's full assumption
        // set) — emit the ENFORCED gate. A missing ref to a def/lemma/theorem may just be named in
        // prose, so it stays advisory (`xref-missing`). This is what makes a bundling definition such
        // as `def:law-class` actually list its constituent assumptions before the body is frozen.
        problems.push({
          gate: t.startsWith("ass:") ? "xref-missing-assumption" : "xref-missing",
          objId: e.obj_id,
          detail: `${e.obj_id}: depends on ${t} (statement-uses) but never references \\cref{obj:${t}}`,
        });
      }
    }
  }
  return problems;
}

export function lintAnchors(
  tex: string,
  knownObjIds: Set<string>,
  frozenHashes: Map<string, string> | null, // null before the P1 freeze
): LintProblem[] {
  const problems: LintProblem[] = [];
  BARE_RE.lastIndex = 0;
  let b: RegExpExecArray | null;
  while ((b = BARE_RE.exec(tex))) {
    problems.push({
      gate: "bare-env",
      detail: `unanchored \\begin{${b[1]}} — use ${b[1]}v with an obj_id`,
    });
  }
  for (const e of parseAnchoredEnvs(tex)) {
    if (!knownObjIds.has(e.obj_id)) {
      problems.push({ gate: "unknown-objid", detail: `${e.env}{${e.obj_id}} not in bank crosswalk` });
    }
    if (frozenHashes) {
      const h = frozenHashes.get(e.obj_id);
      if (h === undefined) {
        problems.push({ gate: "not-frozen", detail: `${e.obj_id} absent from frozen layer` });
      } else if (h !== hashEnvBody(e.body)) {
        problems.push({ gate: "frozen-drift", detail: `${e.obj_id} body differs from frozen layer` });
      }
    }
  }
  // Obj ids are plumbing: prose must reference statements via \cref{obj:<id>}
  // (the env macros define the labels), never as a bare id the reader can't
  // resolve against the printed numbering. Frozen env bodies are exempt (they
  // may cross-reference ids and cannot be edited anyway).
  const proseNoEnvs = stripAnchoredEnvBlocks(tex)
    .replace(/\\(?:Cref|cref|ref|label)\{[^}]*obj:[^}]*\}/g, " ")
    // Strip ALL LaTeX comments (inline too, not just full-line): proof steps carry
    // inline `% lean: <decl>` provenance tags, and an aux-lemma node whose id equals
    // its decl_name would otherwise false-positive on its own (invisible) comment tag.
    // An escaped `\%` is a literal percent, not a comment — leave it.
    .replace(/(?<!\\)%.*$/gm, " ");
  for (const id of knownObjIds) {
    const idRe = new RegExp(`(?<![\\w:-])${id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}(?![\\w-])`);
    if (idRe.test(proseNoEnvs)) {
      problems.push({
        gate: "objid-in-prose",
        detail: `${id} appears in prose — cross-reference it as \\cref{obj:${id}} instead`,
      });
    }
  }
  return problems;
}
