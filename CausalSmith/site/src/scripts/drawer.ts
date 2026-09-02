/** Docked Lean panel: click a formal block → show its verified Lean statement.
 *
 *  The panel is NON-MODAL. There is no scrim and the paper is never dimmed: the
 *  reading column shifts left to yield the right margin (see paper.css) and the
 *  reader can keep scrolling, selecting, commenting and clicking other blocks
 *  while it is open. Clicking a different block swaps the panel's content in
 *  place; Esc and ✕ close it.
 */

import { KATEX_MACROS } from "../lib/katexConfig.js";

// katex is OPTIONAL for the drawer: only the title's inline math needs it; the
// Lean statement (the drawer's substance) does not. Load it lazily so a failed
// katex fetch can't abort this module — a top-level `import katex` that 504s in
// dev would take initDrawer() down with it and leave every block un-clickable.
// Until (or unless) it resolves, title math degrades to escaped source text.
let katex: typeof import("katex").default | null = null;
const katexReady: Promise<void> = import("katex")
  .then((m) => {
    katex = m.default;
  })
  .catch(() => {
    /* drawer still works; title math stays raw */
  });

interface LeanRef {
  file: string;
  decl: string;
  decl_kind: string;
  line: number;
}
interface Entry {
  obj_id: string;
  env: string;
  paper_label: string;
  title: string | null;
  lean: LeanRef | null;
  fallback: string | null;
  uses: string[];
}
/** One binder row of a structured statement: a chip + its Lean source.
 *  `cited` = an assumed external result, stated but not proven here. */
interface HypRow {
  chip: "hyp" | "decl" | "cited";
  code: string;
  /** Stable row id assigned by enrichment; the renderer does not use it, but it
   *  is what the `xl` tokens are built from upstream. */
  id?: string;
  /** NL↔Lean crosslink tokens, space-separated. OPAQUE: nothing here parses
   *  their contents, so any stable id scheme works. */
  xl?: string;
  /** Verified to have no counterpart sentence in the paper. Not an error and
   *  not a warning — the reader is simply told the pairing is absent on
   *  purpose, so a row with no highlight does not read as a broken link. */
  unstated?: boolean;
}
/** One clause of a statement, split as far as the payload could split it.
 *
 *  A card is a LEAF when it carries `code` (the actual conclusion, marked `⊢`)
 *  and a BRANCH when it carries `sub` (an inner telescope or conjunction split
 *  one level further). `intro` is the verbatim prefix that could not be lifted
 *  into `hyps` — e.g. `∃ C ρ : ℝ, ∃ N : ℕ,` — and introduces binders rather
 *  than stating anything, so it never gets a `⊢`. */
interface ConclusionCard {
  hyps: HypRow[];
  /** See HypRow.id. A card's `xl`/`unstated` describe its OWN content row —
   *  the `intro` line when it branches, the `code` line when it is a leaf. */
  id?: string;
  intro?: string;
  /** Exactly one of `code` | `sub` is expected; see conclusionBodyHtml. */
  code?: string;
  sub?: ConclusionCard[];
  xl?: string;
  /** See HypRow.unstated — a conclusion clause can be unpaired too. */
  unstated?: boolean;
}
/** A statement split into shared hypotheses + one card per conclusion. */
interface StructuredView {
  sharedHyps: HypRow[];
  conclusions: ConclusionCard[];
}
/** One declaration's source, held once in the payload's shared side table
 *  (`declSources`) instead of being repeated in every drawer that cites it. */
interface DeclSource {
  file: string;
  line: number;
  statement: string;
  structured?: StructuredView;
  /** TRI-STATE. `true` = this decl's own proof is incomplete (the entry-level
   *  badge describes the anchor only, so a pulled-in helper must carry its own
   *  warning); `false` = checked and clean; ABSENT = unknown, which is what an
   *  index built before the field existed reports. Unknown is not clean, and
   *  must not be rendered as if it were. */
  usesSorry?: boolean;
}
/** A declaration the statement is built from, classified by its role.
 *
 *  The source may arrive EITHER by reference (`key` into `declSources`) or
 *  inline (`file`/`line`/`statement`/`structured`) — the inline fields are how
 *  pre-dedupe payloads carried it, and they remain the fallback. */
interface ComponentView {
  decl: string;
  /** Key into the payload's `declSources` table; absent on older payloads. */
  key?: string;
  file?: string;
  line?: number;
  /** "" is allowed when cls === "paper" (the code lives in the paper, not here). */
  statement?: string;
  /** `cited` = the anchor of a `citedv` crosswalk entry: a result this
   *  development ASSUMES rather than proves.
   *  `support` = retired. It encoded v2 pipeline provenance rather than
   *  anything a reader needs, and now renders as `lean_only`; accepted only so
   *  a pre-merge payload still shows its components. */
  cls: "anchor" | "env" | "paper" | "cited" | "support" | "lean_only";
  /** cls === "paper" | "cited": the crosswalk object this decl belongs to. */
  paperObjId?: string;
  paperLabel?: string;
  depth: number;
  structured?: StructuredView;
  /** An UPSTREAM declaration (Causalean / Mathlib) that a formula in this block
   *  states. It has no source in this bundle — no `key`, no `statement` — so the
   *  card is a name and a link out, never a code body. */
  external?: true;
  /** Fully-qualified name, resolved through /library/names.json for the
   *  explorer link when no `docUrl` is given. */
  fullName?: string;
  /** Where it lives, shown in the quiet "where" slot. */
  module?: string;
  /** Absolute documentation URL (the Mathlib family); wins over `fullName`. */
  docUrl?: string;
  /** NL↔Lean crosslink tokens for the card as a whole (space-separated). */
  xl?: string;
  /** Inline fallback for pre-dedupe payloads; see DeclSource.usesSorry. */
  usesSorry?: boolean;
}
/** Where a component's source actually came from, once resolved. */
interface ResolvedSource {
  file: string;
  line: number;
  statement: string;
  structured?: StructuredView;
  /** Tri-state, `undefined` = unknown; see DeclSource.usesSorry. */
  usesSorry: boolean | undefined;
}
/** Prefer the shared table when the view names a key that resolves; otherwise
 *  read the inline fields exactly as before. A key that does NOT resolve (a
 *  stale or partial table) degrades to the inline fields rather than blanking
 *  the card. */
function resolveSource(
  v: ComponentView,
  table: Record<string, DeclSource> | undefined,
): ResolvedSource {
  const src = v.key ? table?.[v.key] : undefined;
  if (src) {
    return {
      file: src.file ?? v.file ?? "",
      line: src.line ?? v.line ?? 0,
      statement: src.statement ?? v.statement ?? "",
      structured: src.structured ?? v.structured,
      // `?? ` and not `||`: a checked-clean `false` must survive, and only a
      // genuinely absent field on BOTH sides degrades to unknown.
      usesSorry: src.usesSorry ?? v.usesSorry,
    };
  }
  return {
    file: v.file ?? "",
    line: v.line ?? 0,
    statement: v.statement ?? "",
    structured: v.structured,
    usesSorry: v.usesSorry,
  };
}
interface Snippet {
  decl: string;
  file: string;
  line: number;
  statement: string;
  sorry_free: boolean;
  axioms: string[] | null;
  /** Composite objects: the Lean pieces that jointly formalize the statement. */
  components?: { label: string; statement: string }[];
  /** Structured render of `statement` (optional — older payloads omit it). */
  structured?: StructuredView;
  /** Classified component declarations (optional — older payloads omit it). */
  componentViews?: ComponentView[];
  /** Some declaration pulled into this entry's closure is not sorry-free. The
   *  entry's own `sorry_free` badge speaks for the ANCHOR only, so this is the
   *  only place the reader learns a helper is incomplete. */
  closureHasSorry?: boolean;
  /** How many closure declarations were dropped past the depth cutoff. */
  closureTruncated?: number;
  /** How many pulled-in declarations the index could say nothing about. */
  closureSorryUnknown?: number;
}
interface PaperData {
  github: string | null;
  /** Commit the bundle was audited at — provenance, shown as the pinned-commit label. */
  commit: string;
  /** Ref source links resolve against (see `sourceRef` in lib/config). */
  ref: string;
  leanSubdir: string;
  /** URL of the heavy per-statement payload (entries + Lean snippets). The
   *  multi-MB payload lives in a sibling static JSON, not the page HTML. */
  dataUrl?: string;
  /** Inline fallback for pages built before the dataUrl split. */
  entries?: Entry[];
  snippets?: Record<string, Snippet>;
  /** Shared decl-source table (see DeclSource); absent on pre-dedupe payloads. */
  declSources?: Record<string, DeclSource>;
  /** Per-paper Lean development page (null when the bundle has no index). */
  leanPage?: string | null;
  /** objId → anchor of the decl's card on the Lean development page. */
  leanAnchors?: Record<string, string>;
}

const esc = (s: string) =>
  s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");

/** Human kind label from a crosswalk env ("theoremv" → "Theorem"); "" if none —
 *  so the drawer head carries the same kind pill as a library decl card. */
function envKind(env: string): string {
  const stem = env.replace(/v$/, "");
  if (!stem || stem === env) return "";
  return stem.charAt(0).toUpperCase() + stem.slice(1);
}

/** Render a label that may carry inline math (`$…$` or `\(…\)`) — e.g. a title like
 *  "Law class \(\mathcal P_{\alpha,\gamma}\)". The drawer title was set via textContent, which left
 *  such math raw; KaTeX-render the math runs and escape the rest. */
function renderLabelMath(s: string): string {
  return s
    .split(/(\$[^$]+\$|\\\([\s\S]*?\\\))/g)
    .map((part) => {
      const m = part.match(/^\$([\s\S]+)\$$/) ?? part.match(/^\\\(([\s\S]*?)\\\)$/);
      if (!m) return esc(part);
      if (!katex) return esc(part); // katex not loaded (yet/at all) — show raw
      try {
        return katex.renderToString(m[1], { throwOnError: false, macros: { ...KATEX_MACROS } });
      } catch {
        return esc(part);
      }
    })
    .join("");
}

const LEAN_KEYWORDS = new Set([
  "theorem", "lemma", "def", "noncomputable", "abbrev", "structure", "class",
  "instance", "inductive", "deriving", "where", "fun", "let", "match", "with",
  "by", "do", "then", "else", "if", "open", "variable", "private", "protected",
  "Prop", "Type", "Sort",
]);

/** Library name map for cross-links into the explorer; lazily fetched. */
let libNames: Record<string, { a: string; n: string }> | null = null;
let libNamesLoading: Promise<void> | null = null;
function siteBase(): string {
  return location.pathname.replace(/\/papers\/.*$/, "").replace(/\/$/, "");
}
function ensureLibNames(): Promise<void> {
  if (libNames || libNamesLoading) return libNamesLoading ?? Promise.resolve();
  libNamesLoading = fetch(`${siteBase()}/library/names.json`)
    .then((r) => (r.ok ? r.json() : { names: {} }))
    .then((d) => {
      libNames = d.names ?? {};
    })
    .catch(() => {
      libNames = {};
    });
  return libNamesLoading;
}

/**
 * Lean statement highlighter — single-pass tokenizer (comments split out first,
 * then identifier-level replacement), so generated HTML is never re-scanned.
 * Identifiers found in the library name map link into the explorer.
 */
function highlightLean(src: string, decl: string): string {
  const segments = src.split(/(\/--[\s\S]*?-\/|\/-[\s\S]*?-\/|--[^\n]*)/g);
  let declMarked = false;
  const out = segments.map((seg, i) => {
    if (i % 2 === 1) return `<span class="comment">${esc(seg)}</span>`; // comment segment
    const re = /[A-Za-z_¡-￿][A-Za-z0-9_.'¡-￿]*/g;
    const parts: string[] = [];
    let last = 0;
    for (const m of seg.matchAll(re)) {
      parts.push(esc(seg.slice(last, m.index)));
      const tok = m[0];
      if (tok === "sorry" || tok === "sorryAx") {
        parts.push(`<span class="sorry-kw">${tok}</span>`);
      } else if (LEAN_KEYWORDS.has(tok)) {
        parts.push(`<span class="kw">${tok}</span>`);
      } else if (!declMarked && tok === decl) {
        parts.push(`<span class="ident">${esc(tok)}</span>`);
        declMarked = true;
      } else {
        // A token followed by `:` is a binder/field occurrence, not a reference
        // — don't link it to a same-named decl elsewhere.
        const isBinder = /^\s*:(?![:=])/.test(seg.slice(m.index! + tok.length));
        const hit = isBinder ? undefined : libNames?.[tok];
        if (hit) {
          parts.push(
            `<a class="lib-link" href="${siteBase()}/library/${hit.a}#${hit.n}" target="_blank" rel="noopener">${esc(tok)}</a>`,
          );
        } else {
          parts.push(esc(tok));
        }
      }
      last = m.index! + tok.length;
    }
    parts.push(esc(seg.slice(last)));
    return parts.join("");
  });
  return out.join("");
}

/* ── structured statement rendering ─────────────────────────────────────────
   Mirrors the library page's decl card (styles/library.css `.stmt-*`): binder
   rows carrying a chip over a `⊢` conclusion block, so a hypothesis's chip can
   never scroll out of view while reading its (possibly long) type. Every code
   run still goes through highlightLean, so library cross-links keep working. */

/** A structured view is usable only if it actually has a conclusion to show. */
function usableStructured(sv: StructuredView | undefined): sv is StructuredView {
  return !!sv && Array.isArray(sv.conclusions) && sv.conclusions.length > 0;
}

/** `data-xl="…"` when the payload carries crosslink tokens; inert otherwise.
 *  The value is passed through VERBATIM (escaped only for HTML): tokens are
 *  opaque ids, and nothing downstream inspects their contents. */
function xlAttr(r: { xl?: string }): string {
  return typeof r.xl === "string" && r.xl.trim() !== "" ? ` data-xl="${esc(r.xl)}"` : "";
}

/** The statement's own content lines — a hypothesis/side row, an `∃` intro, a
 *  `⊢` leaf. Component heads and `<summary>`s are carriers too, but they name a
 *  DECLARATION rather than a step of the statement, so a click that could mean
 *  either should land on the step. */
const STMT_ROW_SEL = ".ds-row, .ds-concl, .ds-intro";

/** Why a row can have no highlighted counterpart, said out loud. Without it an
 *  unpaired row is indistinguishable from a broken crosslink. */
const UNSTATED_TITLE =
  "this formal clause has no counterpart sentence in the paper — verified as unstated";
const unstatedMark = (r: { unstated?: boolean }): string =>
  r.unstated
    ? `<div class="ds-unstated" title="${esc(UNSTATED_TITLE)}">not stated in the paper</div>`
    : "";

/** A row whose chip needs to explain itself on hover. */
const CHIP_TITLE: Record<string, string> = {
  cited: "assumed external result — stated, not proven in this development",
};

type StatementRole = "theorem" | "assumption" | "definition";

interface StatementTerms {
  role: StatementRole;
  shared: string;
  clause: string;
  hypChip: string;
  declChip: string;
  sideChip: string;
}

const STATEMENT_TERMS: Record<StatementRole, StatementTerms> = {
  theorem: {
    role: "theorem",
    shared: "Hypotheses",
    clause: "Conclusion",
    hypChip: "hyp",
    declChip: "decl",
    sideChip: "side",
  },
  assumption: {
    role: "assumption",
    shared: "Parameters",
    clause: "Assumption clause",
    hypChip: "premise",
    declChip: "param",
    sideChip: "condition",
  },
  definition: {
    role: "definition",
    shared: "Parameters",
    clause: "Defining clause",
    hypChip: "premise",
    declChip: "param",
    sideChip: "condition",
  },
};

/** Reader-facing vocabulary follows the paper environment, not the parser's
 * theorem-shaped internal schema. A Prop-valued definition still decomposes
 * into inputs and logical clauses, but calling those clauses "conclusions"
 * makes an assumption read as though it were a theorem. */
function statementTerms(env?: string): StatementTerms {
  if (env === "assumptionv") return STATEMENT_TERMS.assumption;
  if (env === "definitionv") return STATEMENT_TERMS.definition;
  return STATEMENT_TERMS.theorem;
}

function hypRowHtml(r: HypRow, decl: string, terms: StatementTerms): string {
  // Whitelist rather than pass through: the chip name becomes a CSS class.
  const chip = r.chip === "hyp" || r.chip === "cited" ? r.chip : "decl";
  const title = CHIP_TITLE[chip] ? ` title="${esc(CHIP_TITLE[chip])}"` : "";
  const chipText =
    chip === "hyp"
      ? terms.hypChip
      : chip === "decl" && terms.role !== "theorem" && r.code.trimStart().startsWith("∀")
        ? "for each"
        : chip === "decl"
          ? terms.declChip
          : chip;
  return (
    `<div class="ds-row ds-row-${chip}"${xlAttr(r)}>` +
    `<span class="ds-chip ds-chip-${chip}"${title}>${chipText}</span>` +
    `<div class="ds-code">${highlightLean(r.code, decl)}</div>` +
    unstatedMark(r) +
    `</div>`
  );
}

function hypRowsHtml(rows: HypRow[] | undefined, decl: string, terms: StatementTerms): string {
  if (!rows || rows.length === 0) return "";
  return `<div class="ds-rows">${rows.map((r) => hypRowHtml(r, decl, terms)).join("")}</div>`;
}

/** A leaf conclusion: the `⊢`-marked block that actually states something. */
function conclusionHtml(c: ConclusionCard, decl: string): string {
  return (
    `<div class="ds-concl"${xlAttr(c)}>` +
    `<span class="ds-turnstile" aria-hidden="true">⊢</span>` +
    `<div class="ds-code">${highlightLean(c.code ?? "", decl)}</div>` +
    unstatedMark(c) +
    `</div>`
  );
}

/** A payload should carry exactly one of `code` | `sub`; a leaf is whichever
 *  is actually usable, with `code` winning if a malformed card carries both. */
const isLeaf = (c: ConclusionCard) => typeof c.code === "string" && c.code.trim() !== "";

/** Nesting the renderer will follow. The producer caps splits at 6; the extra
 *  headroom is only so a malformed (or cyclic) payload stops instead of
 *  recursing forever — deeper cards degrade to their own leaf code. */
const MAX_CONCL_DEPTH = 8;

/** The `∃ …` prefix line of a card. When the card BRANCHES this line is its own
 *  content row, so it — not the container around it — carries the card's token
 *  and unstated marker. */
function introHtml(c: ConclusionCard, decl: string, carries: boolean): string {
  return (
    `<div class="ds-intro"${carries ? xlAttr(c) : ""}>${highlightLean(c.intro!, decl)}</div>` +
    (carries ? unstatedMark(c) : "")
  );
}

/** One conclusion's contents, recursively: local hypothesis rows, then the
 *  binder-introducing `intro` prefix (never `⊢` — it states nothing), then
 *  either the leaf conclusion or the inset sub-cards it splits into. */
function conclusionBodyHtml(c: ConclusionCard, decl: string, depth: number, terms: StatementTerms): string {
  const parts: string[] = [hypRowsHtml(c.hyps, decl, terms)];
  const hasIntro = typeof c.intro === "string" && c.intro.trim() !== "";
  if (hasIntro) {
    // A leaf's own token belongs on its ⊢ line (below); only a BRANCH puts it
    // on the intro.
    parts.push(introHtml(c, decl, !isLeaf(c)));
  }
  const subs = Array.isArray(c.sub) ? c.sub : [];
  if (isLeaf(c) || subs.length === 0 || depth >= MAX_CONCL_DEPTH) {
    // Leaf, or a malformed card with neither branch — render whatever code it
    // has (possibly none) rather than throwing.
    if (isLeaf(c)) parts.push(conclusionHtml(c, decl));
  } else {
    parts.push(
      `<div class="ds-subs">` +
        subs
          .map(
            (s) =>
              // The sub CONTAINER never carries a token: `s`'s own token rides
              // on its content line inside (intro or ⊢ leaf).
              `<div class="ds-sub">${conclusionBodyHtml(s, decl, depth + 1, terms)}</div>`,
          )
          .join("") +
        `</div>`,
    );
  }
  return parts.join("");
}

/** A leaf that merely qualifies the binders an `intro` just introduced (e.g.
 *  `0 < a_epsilon` under `∃ a_epsilon …`). It asserts nothing on its own, so it
 *  must not be numbered as if it were one of the theorem's claims. */
const isSideCondition = (c: ConclusionCard) =>
  (c.hyps?.length ?? 0) === 0 && !c.intro && !(c.sub?.length ?? 0) && isLeaf(c);

/** A side condition, rendered as a quiet row rather than a `⊢` claim. */
function sideRowHtml(c: ConclusionCard, decl: string, terms: StatementTerms): string {
  return (
    `<div class="ds-row ds-row-side"${xlAttr(c)}>` +
    `<span class="ds-chip ds-chip-side">${terms.sideChip}</span>` +
    `<div class="ds-code">${highlightLean(c.code ?? "", decl)}</div>` +
    unstatedMark(c) +
    `</div>`
  );
}

/** The whole structured statement: shared hypotheses, then the conclusion(s). */
function structuredHtml(
  sv: StructuredView,
  decl: string,
  terms: StatementTerms = STATEMENT_TERMS.theorem,
): string {
  const parts: string[] = [];
  if (sv.sharedHyps && sv.sharedHyps.length > 0) {
    parts.push(
      `<div class="ds-sect"><div class="ds-label">${terms.shared}</div>${hypRowsHtml(sv.sharedHyps, decl, terms)}</div>`,
    );
  }
  const cs = sv.conclusions;
  const only = cs[0];
  const lone = cs.length === 1;
  if (
    terms.role === "theorem" &&
    lone &&
    (only.hyps?.length ?? 0) === 0 &&
    !only.intro &&
    isLeaf(only) &&
    !(only.sub?.length ?? 0)
  ) {
    // A single unconditional, unsplit clause needs no card header — it IS the
    // theorem's statement. Prop-valued assumptions/definitions keep an explicit
    // clause label so their body cannot be mistaken for another parameter row.
    parts.push(conclusionHtml(only, decl));
  } else if (
    lone &&
    (only.hyps?.length ?? 0) === 0 &&
    !only.intro &&
    isLeaf(only) &&
    !(only.sub?.length ?? 0)
  ) {
    parts.push(
      `<div class="ds-card"><div class="ds-label">${terms.clause}</div>` +
        conclusionHtml(only, decl) +
        `</div>`,
    );
  } else if (lone && only.intro && (only.sub?.length ?? 0) > 0) {
    // ∃-HEADED STATEMENT. The whole theorem is one `∃ …, …` clause, so numbering
    // it "Conclusion 1" names the existential rather than the claims — the paper
    // reads "there exist a_ε, ρ_ε, C_ε such that (i)…(iii)", and (i)…(iii) are
    // what the reader is looking for. So the ∃ frame is left UNLABELLED and the
    // numbering moves down one level onto the claims themselves.
    const subs = only.sub!;
    // Positivity-style qualifiers sit at the FRONT of the ∃ body; they bind the
    // introduced variables and are not claims.
    let lead = 0;
    while (lead < subs.length && isSideCondition(subs[lead])) lead++;
    // …but if EVERY sub looks like one, they are the claims (a conjunction of
    // plain facts). Demoting a real claim to a side condition is the worse
    // error, so in that case nothing is lifted out and all of them get numbered.
    if (lead === subs.length) lead = 0;
    parts.push(
      // The frame is a container, so it carries nothing; the ∃ line inside it is
      // the frame's own content row and takes its token.
      `<div class="ds-lift">` +
        hypRowsHtml(only.hyps, decl, terms) +
        introHtml(only, decl, true) +
        (lead > 0
          ? `<div class="ds-rows ds-sides">${subs.slice(0, lead).map((s) => sideRowHtml(s, decl, terms)).join("")}</div>`
          : "") +
        `</div>`,
    );
    subs.slice(lead).forEach((c, i) => {
      // Each claim is a full card, rendered exactly as a top-level one would be
      // — anything nested BELOW it stays unlabelled, as before.
      parts.push(
        `<div class="ds-card"><div class="ds-label">${terms.clause} ${i + 1}</div>` +
          conclusionBodyHtml(c, decl, 1, terms) +
          `</div>`,
      );
    });
  } else {
    cs.forEach((c, i) => {
      // Only TOP-LEVEL cards are numbered; nested cards are subdivisions of one
      // conclusion, so they carry no header.
      parts.push(
        `<div class="ds-card"><div class="ds-label">${terms.clause} ${i + 1}</div>` +
          conclusionBodyHtml(c, decl, 0, terms) +
          `</div>`,
      );
    });
  }
  return `<div class="ds-structured">${parts.join("")}</div>`;
}

/** Structured when the payload provides it, else the raw statement block. */
function stmtHtml(sv: StructuredView | undefined, src: string, decl: string, env?: string): string {
  return usableStructured(sv)
    ? structuredHtml(sv, decl, statementTerms(env))
    : `<pre>${highlightLean(src, decl)}</pre>`;
}

/** A pulled-in declaration whose own proof is incomplete. The entry-level
 *  "✓ sorry-free" badge covers the ANCHOR only, so without this a reader would
 *  read a verified badge over a helper that is not. */
const SORRY_CHIP = '<span class="cv-tag cv-tag-sorry">⚠ uses sorry</span>';
/** An index built before `usesSorry` existed reports nothing at all. Silence is
 *  NOT a clean bill of health, so it gets its own quiet, non-alarming chip
 *  rather than being folded into either verdict. */
const UNKNOWN_CHIP = '<span class="cv-tag cv-tag-unknown">verification unknown</span>';

/** The verification chip for one component: red when it is known to use sorry,
 *  grey when nothing is known, nothing at all when it is known to be clean. */
const verifChip = (usesSorry: boolean | undefined): string =>
  usesSorry === true ? SORRY_CHIP : usesSorry === undefined ? UNKNOWN_CHIP : "";

/** A component card's header: decl name, where it lives (dropped when the
 *  payload knows no location), the tag naming the component's role, and its
 *  verification chip. */
function cvHead(
  decl: string,
  src: ResolvedSource,
  tag: string,
  tagCls: string,
  /** The component's crosslink token rides on this HEAD LINE, never on the card
   *  container around it — see the carrier rule in bindXl. */
  xl = "",
): string {
  const where = src.file ? `<span class="cv-file">${esc(src.file)}:${src.line}</span>` : "";
  return (
    `<div class="cv-head"${xl}><code class="cv-decl">${esc(decl)}</code>${where}` +
    `<span class="cv-tag ${tagCls}">${tag}</span>${verifChip(src.usesSorry)}</div>`
  );
}

/** A payload string is about to become an `href`, so vouch for it first:
 *  anything that is not plain http(s) is dropped rather than rendered. */
const safeHttpUrl = (u: string | undefined): string | null =>
  typeof u === "string" && /^https?:\/\//i.test(u) ? u : null;

/** An UPSTREAM declaration (Causalean / Mathlib) that a formula in this block
 *  states. The bundle carries no source for it, so the card is a name, a quiet
 *  tag and a way to go read it — never a code body, never a fold, and never a
 *  sorry chip, since nothing here was scanned to earn one.
 *
 *  The link is `docUrl` when the payload gives one (the Mathlib family), else
 *  the explorer entry for `fullName` from the lazily-loaded name map that
 *  already backs the in-code lib-links. When the map has no entry the card
 *  renders name-and-tag only: no link beats a dead link. */
function externalCard(v: ComponentView): string {
  const doc = safeHttpUrl(v.docUrl);
  const hit = !doc && v.fullName ? libNames?.[v.fullName] : undefined;
  const link = doc
    ? `<a class="cv-ext-link" href="${esc(doc)}" target="_blank" rel="noopener">docs ↗</a>`
    : hit
      ? `<a class="cv-ext-link" href="${esc(`${siteBase()}/library/${hit.a}#${hit.n}`)}" target="_blank" rel="noopener">library ↗</a>`
      : "";
  const where = v.module ? `<span class="cv-file">${esc(v.module)}</span>` : "";
  return (
    `<div class="cv-card cv-card-external">` +
    // the head is the content LINE, so it carries the token
    `<div class="cv-head"${xlAttr(v)}><code class="cv-decl">${esc(v.decl)}</code>${where}` +
    `<span class="cv-tag cv-tag-external">library declaration</span>${link}</div>` +
    `</div>`
  );
}

const lineCount = (s: string) => s.split("\n").length;
const plural = (n: number) => (n === 1 ? "" : "s");

export function initDrawer(): void {
  const dataEl = document.getElementById("paper-data");
  if (!dataEl) return;
  const data: PaperData = JSON.parse(dataEl.textContent ?? "{}");
  // The per-statement payload is fetched once, lazily: warmed on idle so a
  // click rarely waits, but never on the page's critical path.
  type Payload = {
    entries: Entry[];
    snippets: Record<string, Snippet>;
    /** Absent on pre-dedupe payloads — components then carry their own source. */
    declSources?: Record<string, DeclSource>;
  };
  type Heavy = {
    byId: Map<string, Entry>;
    snippets: Record<string, Snippet>;
    declSources: Record<string, DeclSource>;
  };
  let heavyP: Promise<Heavy> | null = null;
  const loadHeavy = (): Promise<Heavy> =>
    (heavyP ??= (data.entries && data.snippets
      ? Promise.resolve<Payload>({
          entries: data.entries,
          snippets: data.snippets,
          declSources: data.declSources,
        })
      : fetch(data.dataUrl!).then((r) => {
          if (!r.ok) throw new Error(`paper-data fetch failed: ${r.status}`);
          return r.json() as Promise<Payload>;
        })
    )
      .then((d) => ({
        byId: new Map(d.entries.map((e) => [e.obj_id, e])),
        snippets: d.snippets,
        declSources: d.declSources ?? {},
      }))
      // A transient failure must not be cached for the page's lifetime: clear
      // the memo so the next click (or idle retry) fetches again.
      .catch((err: unknown) => {
        heavyP = null;
        throw err;
      }));
  // Warm the multi-MB payload only on reader INTENT (hovering/focusing any
  // formal block) — an unconditional idle warm charges every visitor ~3.4MB
  // they may never use, while intent still beats the click by enough to hide
  // the fetch latency on same-origin gzip.
  const warm = () => void loadHeavy().catch(() => {});
  document.addEventListener("pointerover", intentWarm, { passive: true });
  document.addEventListener("focusin", intentWarm);
  function intentWarm(ev: Event): void {
    if (!(ev.target instanceof Element) || !ev.target.closest("[data-objid]")) return;
    document.removeEventListener("pointerover", intentWarm);
    document.removeEventListener("focusin", intentWarm);
    warm();
  }
  const drawer = document.getElementById("drawer")!;
  const titleEl = document.getElementById("drawer-title")!;
  const subEl = document.getElementById("drawer-sub")!;
  const bodyEl = document.getElementById("drawer-body")!;
  let openBlock: Element | null = null;
  // Non-modal: the panel is a dialog that deliberately does NOT trap focus or
  // inert the page — `aria-modal="false"` is exactly that contract, and keeps
  // the ✕/Esc affordances a dialog role implies (a `complementary` landmark
  // would announce as permanent page furniture, which this is not).
  drawer.setAttribute("role", "dialog");
  drawer.setAttribute("aria-modal", "false");
  if (!drawer.hasAttribute("aria-label")) drawer.setAttribute("aria-label", "Lean statement");
  drawer.tabIndex = -1;

  /** Listeners bound into the paper body for the open statement's crosslinks. */
  let xlCtl: AbortController | null = null;
  const clearXl = () => {
    xlCtl?.abort();
    xlCtl = null;
    for (const el of document.querySelectorAll(".xl-hot, .xl-jump")) {
      el.classList.remove("xl-hot", "xl-jump");
    }
  };

  const close = () => {
    document.body.classList.remove("drawer-visible");
    drawer.setAttribute("aria-hidden", "true");
    clearXl();
    // Restore focus to the block that opened the drawer (keyboard flow).
    if (openBlock instanceof HTMLElement) openBlock.focus();
    openBlock?.classList.remove("drawer-open");
    openBlock = null;
  };

  const blockFor = (objId: string): Element | null => {
    try {
      return document.querySelector(`[data-objid="${CSS.escape(objId)}"]`);
    } catch {
      return document.querySelector(`[data-objid="${objId}"]`);
    }
  };

  const flashBlock = (objId: string) => {
    const target = blockFor(objId);
    if (!target) return;
    target.scrollIntoView?.({ behavior: "smooth", block: "center" });
    target.classList.add("flash");
    setTimeout(() => target.classList.remove("flash"), 1600);
  };

  const leanPageLink = (objId: string): string => {
    if (!data.leanPage) return "";
    const anchor = data.leanAnchors?.[objId];
    const href = anchor ? `${data.leanPage}#${encodeURIComponent(anchor)}` : data.leanPage;
    return ` · <a href="${href}">view in Lean development</a>`;
  };

  /* ── component-view sections ─────────────────────────────────────────────
     Ordered so the statement itself reads first, then what it is built from:
     the anchor decl, the environment decls it names, the paper objects it
     points back at, and finally the Lean-only scaffolding. */
  /** The panel body below the metadata line, in the three sections a reader
   *  actually distinguishes: what the paper states, what it assumes, and what
   *  exists only in Lean. `anchorHtml` is the entry's own statement, which
   *  opens the first section. */
  const componentsHtml = (
    views: ComponentView[],
    byId: Map<string, Entry>,
    declSources: Record<string, DeclSource>,
    truncated: number,
    anchorHtml: string,
  ): string => {
    // An external view has no source in this bundle, so it never flows into the
    // source-bearing branches — it renders as a name-and-link card instead.
    const isExternal = (v: ComponentView) => v.external === true;
    const of = (cls: ComponentView["cls"]) =>
      views.filter((v) => v.cls === cls && !isExternal(v));
    const out: string[] = [];

    // ── 1. Stated in the paper ────────────────────────────────────────────
    // The statement itself, the definitions it names (which say WHERE in this
    // statement they appear), and the objects stated at another block. One
    // header: from the reader's side these are all "the paper says this".
    const stated: string[] = [anchorHtml];

    // env cards and upstream-library cards sit together, in payload order.
    for (const v of views.filter((v) => isExternal(v) || v.cls === "env")) {
      if (isExternal(v)) {
        stated.push(externalCard(v));
        continue;
      }
      const src = resolveSource(v, declSources);
      stated.push(
        `<div class="cv-card cv-card-env">${cvHead(v.decl, src, "↔ formula in this statement", "cv-tag-env", xlAttr(v))}` +
          stmtHtml(src.structured, src.statement, v.decl) +
          `</div>`,
      );
    }

    // Objects the paper states at ANOTHER block. Same section: still "stated in
    // the paper", just not here — which is what the chip's jump says.
    const papers = of("paper");
    if (papers.length > 0) {
      const chips = papers
        .map((v) => {
          const label = v.paperLabel ?? v.paperObjId ?? "";
          const text = `${esc(v.decl)} → ${esc(label)}`;
          const id = v.paperObjId;
          const warn = verifChip(resolveSource(v, declSources).usesSorry);
          // Only offer navigation we can actually honour: a block in this page,
          // or an entry whose panel we can swap in. Otherwise it is plain text.
          if (id && (blockFor(id) || byId.has(id))) {
            return `<button type="button" class="cv-paper-chip"${xlAttr(v)} data-paper-obj="${esc(id)}">${text} <span class="cv-paper-go">↑ view in paper</span></button>${warn}`;
          }
          return `<span class="cv-paper-flat"${xlAttr(v)}>${text}</span>${warn}`;
        })
        .join("");
      stated.push(`<div class="cv-chips">${chips}</div>`);
    }
    out.push(
      `<div class="cv-sect cv-sect-stated"><div class="cv-label">Stated in the paper</div>${stated.join("")}</div>`,
    );

    // ── 2. Cited assumptions ──────────────────────────────────────────────
    // The load-bearing things the development does NOT establish, so they must
    // be impossible to miss and impossible to mistake for results.
    const cited = of("cited");
    if (cited.length > 0) {
      const cards = cited
        .map((v) => {
          const src = resolveSource(v, declSources);
          const id = v.paperObjId;
          const where = src.file ? `<span class="cv-file">${esc(src.file)}:${src.line}</span>` : "";
          // A citedv entry carries no paper number, so its `paperLabel` is the
          // raw crosswalk id ("Object lem:zeng-one-arm-minimax-lower"). That is
          // machinery, not a name — never show it. The decl name plus a fixed
          // descriptor (and the entry's own title when it has one) is what the
          // reader can actually place.
          const title = id ? byId.get(id)?.title : null;
          const desc = `cited result${title ? ` — ${esc(title)}` : ""}`;
          const openable = !!id && byId.has(id);
          const inner =
            `<code class="cv-decl">${esc(v.decl)}</code>` +
            `<span class="cv-cited-desc">${desc}</span>${where}` +
            `<span class="cv-tag cv-tag-cited">cited — assumed</span>${verifChip(src.usesSorry)}` +
            // It has no block in the paper to scroll to; the affordance opens
            // the assumption's own panel, so it must not promise otherwise.
            (openable ? `<span class="cv-open-go">view assumed statement</span>` : "");
          // The token rides on the head LINE, not the card container.
          const head = openable
            ? `<button type="button" class="cv-head cv-head-open"${xlAttr(v)} data-open-obj="${esc(id!)}">${inner}</button>`
            : `<div class="cv-head"${xlAttr(v)}>${inner}</div>`;
          // Inlined UNFOLDED on purpose: an assumption the reader cannot see is
          // an assumption the reader cannot check.
          return `<div class="cv-card cv-card-cited">${head}${stmtHtml(src.structured, src.statement, v.decl)}</div>`;
        })
        .join("");
      out.push(
        `<div class="cv-sect cv-sect-cited"><div class="cv-label">Cited assumptions — assumed, not proven here</div>${cards}</div>`,
      );
    }

    // ── 3. Lean only ──────────────────────────────────────────────────────
    // `support` was v2 pipeline provenance, not something a reader needs told
    // apart — it folds in here. Kept as an accepted value rather than dropped
    // from the union so a payload built before the merge still renders its
    // components instead of silently losing them.
    const leanOnly = views
      .filter((v) => v.cls === "lean_only" || v.cls === "support")
      .map((v, i) => ({ v, i }))
      .sort((a, b) => a.v.depth - b.v.depth || a.i - b.i)
      .map(({ v }) => {
        const src = resolveSource(v, declSources);
        const n = lineCount(src.statement);
        return (
          // <details> is a container; the <summary> is its content line.
          `<details class="lean-fold cv-lean-only"><summary${xlAttr(v)}>${esc(v.decl)} ` +
          `<span class="fold-count">(${n} line${plural(n)})</span>${verifChip(src.usesSorry)}</summary>` +
          `<pre>${highlightLean(src.statement, v.decl)}</pre></details>`
        );
      })
      .join("");
    // The closure is depth-capped, so say so rather than letting the list read
    // as the complete set of what the statement rests on. It closes the Lean-only
    // section, which is the list it qualifies.
    let note = "";
    if (truncated > 0) {
      const page = data.leanPage
        ? `<a href="${data.leanPage}">the Lean development page</a>`
        : "the Lean development page";
      note = `<p class="cv-truncated">closure truncated — ${truncated} more declaration${plural(truncated)} at depth &gt;4 (see ${page})</p>`;
    }
    if (leanOnly || note) {
      out.push(
        `<div class="cv-sect cv-sect-lean-only"><div class="cv-label">Lean only — not stated in the paper</div>${leanOnly}${note}</div>`,
      );
    }
    return out.join("");
  };

  const open = async (objId: string, block: Element) => {
    let heavy: Heavy;
    try {
      heavy = await loadHeavy();
    } catch {
      // Surface the failure instead of a silently dead click; retried next click.
      titleEl.textContent = "Lean details unavailable";
      subEl.textContent = "could not load statement data — check the connection and click again";
      bodyEl.innerHTML = "";
      document.body.classList.add("drawer-visible");
      drawer.setAttribute("aria-hidden", "false");
      drawer.focus();
      return;
    }
    const { byId, snippets, declSources } = heavy;
    const e = byId.get(objId);
    if (!e) return;
    openBlock?.classList.remove("drawer-open");
    clearXl();
    openBlock = block;
    block.classList.add("drawer-open");
    const kind = envKind(e.env);
    const setTitle = () => {
      titleEl.innerHTML =
        (kind ? `<span class="drawer-kind">${kind}</span> ` : "") +
        renderLabelMath(`${e.paper_label}${e.title ? ` (${e.title})` : ""}`);
    };
    setTitle();
    // If a very fast click beat katex loading, re-render the title once it lands.
    if (!katex) void katexReady.then(() => openBlock === block && setTitle());

    const snip = snippets[objId];

    /** Wire up whatever the freshly-painted body offers. */
    const bindBody = () => {
      for (const a of bodyEl.querySelectorAll("a[data-jump]")) {
        a.addEventListener("click", (ev) => {
          ev.preventDefault();
          // Non-modal panel: jumping to a used object scrolls + flashes it and
          // LEAVES the panel open, so the reader keeps the statement in view.
          flashBlock((a as HTMLElement).dataset.jump!);
        });
      }
      for (const b of bodyEl.querySelectorAll("button[data-paper-obj]")) {
        b.addEventListener("click", () => {
          const pid = (b as HTMLElement).dataset.paperObj!;
          if (blockFor(pid)) flashBlock(pid);
          else void open(pid, block);
        });
      }
      // A cited assumption has no block in the paper to jump to — its own panel
      // is the only place its statement lives.
      for (const b of bodyEl.querySelectorAll("[data-open-obj]")) {
        b.addEventListener("click", () => {
          void open((b as HTMLElement).dataset.openObj!, block);
        });
      }
      bindXl();
    };

    /** Two-way NL↔Lean highlight between the panel's rows/cards and the
     *  `[data-xl]` spans in the open block.
     *
     *  `data-xl` is a SPACE-SEPARATED token list, exactly the way `class` is:
     *  an element may translate several binders, and a binder may be translated
     *  by several phrases. So hovering an element lights the UNION — every
     *  element sharing ANY of its tokens — and pinning pins that full token set,
     *  not just the token that happened to match.
     *
     *  The word match is done over the collected element list rather than by
     *  running a `[data-xl~="<token>"]` selector per token: the semantics are
     *  identical (both split on ASCII whitespace), it is one pass instead of one
     *  query per token, and tokens contain `#` — so there is no CSS.escape round
     *  trip that a slip could break. Entirely inert until tokens exist. */
    const bindXl = () => {
      const within = (root: ParentNode | null) =>
        root ? [...root.querySelectorAll<HTMLElement>("[data-xl]")] : [];
      const panelEls = within(bodyEl);
      const paperEls = within(block);
      // the block itself may carry the attribute, not only its descendants
      if (block instanceof HTMLElement && block.hasAttribute("data-xl")) paperEls.push(block);
      const els = [...panelEls, ...paperEls];
      if (els.length === 0) return;
      xlCtl?.abort();
      xlCtl = new AbortController();
      const opts = { signal: xlCtl.signal };
      const toks = (el: HTMLElement) => (el.dataset.xl ?? "").split(/\s+/).filter(Boolean);
      let pinned: HTMLElement | null = null;
      /** on/off for every element whose token list intersects `tokens`. */
      const setHot = (tokens: string[], on: boolean) => {
        for (const el of els) {
          if (toks(el).some((t) => tokens.includes(t))) el.classList.toggle("xl-hot", on);
        }
      };
      // The jump marker belongs to the pin that created it: unpinning, or
      // pinning something else, must take it away with the highlight.
      const clearAll = () => els.forEach((el) => el.classList.remove("xl-hot", "xl-jump"));

      // DELEGATED, not per-element. Two reasons, both of which broke the Lean
      // side in production:
      //  • What the pointer actually enters is a CHILD of the carrier (the
      //    `.ds-code` box filling the row), not the annotated element itself.
      //  • Carriers NEST — a `.ds-sub` card and the `.ds-concl` leaf inside it
      //    routinely carry the same token — so the inner one's mouseleave fired
      //    while the pointer was still inside the outer one, which never
      //    re-enters, and the highlight died until you left the row entirely.
      // Resolving the NEAREST annotated ancestor of whatever the pointer is
      // over makes both cases fall out: the innermost carrier wins, and moving
      // between nested carriers is just a recompute.
      // CARRIER INVARIANT: `data-xl` is emitted ONLY on content LINES — a
      // hypothesis row, a side row, an `∃` intro line, a `⊢` leaf, a component
      // head or summary — and never on a card/sub/frame container. Without that
      // rule, a click in a card's padding resolved up to the enclosing card and
      // fired ITS token, lighting a far broader stretch of prose than the row
      // the reader aimed at. With it, a click hits a precise row or nothing.
      const carrierOf = (t: EventTarget | null): HTMLElement | null => {
        if (!(t instanceof Element)) return null;
        const el = t.closest<HTMLElement>("[data-xl]");
        return el && els.includes(el) ? el : null;
      };

      let hovered: HTMLElement | null = null;
      const onOver = (ev: Event) => {
        if (pinned) return;
        const el = carrierOf(ev.target);
        if (el === hovered) return;
        if (hovered) setHot(toks(hovered), false);
        hovered = el;
        if (el) setHot(toks(el), true);
      };
      const onOut = (ev: Event) => {
        if (pinned || !hovered) return;
        // Moving deeper inside the SAME carrier is not a leave; a move to a
        // different carrier is handled by the mouseover that follows.
        const to = carrierOf((ev as MouseEvent).relatedTarget);
        if (to === hovered) return;
        setHot(toks(hovered), false);
        hovered = null;
      };
      const onClick = (ev: Event) => {
        const el = carrierOf(ev.target);
        if (!el) return;
        const same = pinned === el;
        clearAll();
        hovered = null;
        pinned = same ? null : el;
        if (!pinned) return; // unpinning is not a navigation — scroll nothing
        setHot(toks(el), true);
        // Pinning also JUMPS to the counterpart, so the pair can be read
        // together even when one half is off screen.
        const t = toks(el);
        const inPanel = bodyEl.contains(el);
        const candidates = (inPanel ? paperEls : panelEls).filter((o) =>
          toks(o).some((x) => t.includes(x)),
        );
        // PAPER → PANEL, target choice. A prose span usually carries several
        // tokens: the statement rows it translates, plus a display-segment
        // token that ALSO sits on a component card head. The head renders above
        // every row, so picking the first match in DOM order always landed the
        // reader on the card header instead of the row they clicked. Statement
        // rows therefore win; a head is the correct fallback only when no row
        // shares a token (a display→decl link on a definition that has no rows
        // of its own), where the declaration card really is the destination.
        // Panel → paper needs none of this: every paper target is a span.
        const target =
          (inPanel ? undefined : candidates.find((o) => o.matches(STMT_ROW_SEL))) ??
          candidates[0];
        if (!target) return;
        let behavior: ScrollBehavior = "smooth";
        try {
          if (window.matchMedia?.("(prefers-reduced-motion: reduce)")?.matches) behavior = "auto";
        } catch {
          /* no matchMedia — keep the default */
        }
        // Mark where the jump landed. Every token partner shares the `.xl-hot`
        // wash, so without this the reader cannot tell which row the panel just
        // scrolled to — and neither can a test.
        target.classList.add("xl-jump");
        setTimeout(() => target.classList.remove("xl-jump"), 900);
        if (inPanel) {
          // Paper target: centre it in the page.
          target.scrollIntoView?.({ behavior, block: "center", inline: "nearest" });
          return;
        }
        // Panel target: centre it inside the panel body's OWN scroller. This is
        // done by hand rather than with scrollIntoView({block:"center"}) because
        // that also scrolls the page to bring the nested container into view,
        // yanking the article out from under the reader — the reason "nearest"
        // was used before. Rect maths (not offsetTop) so no assumption is made
        // about which ancestor happens to be positioned.
        const r = target.getBoundingClientRect();
        const c = bodyEl.getBoundingClientRect();
        const max = Math.max(0, bodyEl.scrollHeight - bodyEl.clientHeight);
        const wanted = bodyEl.scrollTop + (r.top - c.top) - bodyEl.clientHeight / 2 + r.height / 2;
        const top = Math.min(max, Math.max(0, wanted));
        if (typeof bodyEl.scrollTo === "function") bodyEl.scrollTo({ top, behavior });
        else bodyEl.scrollTop = top;
      };

      for (const root of [bodyEl, block]) {
        if (!root) continue;
        root.addEventListener("mouseover", onOver, opts);
        root.addEventListener("mouseout", onOut, opts);
        root.addEventListener("click", onClick, opts);
      }
    };

    /** Repaint the body, preserving which <details> the reader had opened. */
    const paint = (render: () => string) => {
      const wasOpen = [...bodyEl.querySelectorAll("details")].map((d) => d.open);
      bodyEl.innerHTML = render();
      [...bodyEl.querySelectorAll("details")].forEach((d, i) => {
        if (wasOpen[i] !== undefined) d.open = wasOpen[i];
      });
      bindBody();
    };

    const badge = (s: Snippet) =>
      s.sorry_free
        ? '<span class="badge-ok">✓ sorry-free (source scan)</span>'
        : '<span class="badge-warn">⚠ contains sorry</span>';
    // The badge above scans the ANCHOR. A sorry anywhere in the pulled-in
    // closure is a separate fact and must be said separately, right beside it —
    // otherwise a green badge silently vouches for a helper it never checked.
    const closureBadge = (s: Snippet) => {
      const parts: string[] = [];
      if (s.closureHasSorry) {
        parts.push('<span class="badge-warn">⚠ a pulled-in helper uses sorry</span>');
      }
      // Unknown is its own verdict, and quieter than the sorry warning: it says
      // the index could not answer, not that something is wrong.
      const n = s.closureSorryUnknown ?? 0;
      if (n > 0) {
        parts.push(
          `<span class="badge-unknown">verification status of ${n} pulled-in helper${plural(n)} unknown</span>`,
        );
      }
      return parts.map((p) => ` ${p}`).join("");
    };
    const axiomsOf = (s: Snippet) =>
      s.axioms === null
        ? ""
        : ` · axioms: ${s.axioms.length === 0 ? '<span class="badge-ok">standard</span>' : esc(s.axioms.join(", "))}`;
    const ghLinkOf = (lean: LeanRef) =>
      data.github
        ? `<a href="https://github.com/${data.github}/blob/${data.ref}/${data.leanSubdir}/${lean.file}#L${lean.line}" target="_blank" rel="noopener">full file ↗ GitHub @ ${data.ref.slice(0, 7)}</a>`
        : `pinned commit ${data.commit.slice(0, 7)}`;
    const usesHtml = () =>
      e.uses.length > 0
        ? `<div class="drawer-uses">uses: ${e.uses
            .map((u) => {
              const ue = byId.get(u);
              return `<a data-jump="${esc(u)}">${esc(ue ? `${ue.paper_label} (${u})` : u)}</a>`;
            })
            .join(" · ")}</div>`
        : "";

    if (snip?.componentViews?.length) {
      // Classified components: statement first, then what it is built from.
      const views = snip.componentViews;
      const anchors = views.filter((v) => v.cls === "anchor");
      subEl.innerHTML = e.lean
        ? `↔ <span class="ident">${esc(e.lean.decl)}</span> · ${esc(e.lean.file)}:${e.lean.line}`
        : `formalized by ${views.length} Lean component${plural(views.length)} · ${esc(snip.file)}`;
      const render = () => {
        const stmt = anchors.length
          ? anchors
              .map((v) => {
                const src = resolveSource(v, declSources);
                // The anchor IS the entry's own statement. Prefer the per-entry
                // structured view: crosslink tokens (xl) are attached to it,
                // never to the shared declSources copy — rendering the shared
                // copy here silently dropped every statement-level highlight.
                return (
                  `<div class="cv-card cv-card-anchor">` +
                  cvHead(v.decl, src, "anchor decl", "cv-tag-anchor", xlAttr(v)) +
                  stmtHtml(snip.structured ?? src.structured, src.statement, v.decl, e.env) +
                  `</div>`
                );
              })
              .join("")
          : stmtHtml(snip.structured, snip.statement, e.lean?.decl ?? snip.decl, e.env);
        const meta = `${badge(snip)}${closureBadge(snip)}${axiomsOf(snip)}${e.lean ? ` · ${ghLinkOf(e.lean)}` : ""}${leanPageLink(objId)}`;
        // `stmt` opens the "Stated in the paper" section rather than standing
        // apart from it — see componentsHtml.
        return `<div class="drawer-meta">${meta}</div>${componentsHtml(views, byId, declSources, snip.closureTruncated ?? 0, stmt)}${usesHtml()}`;
      };
      paint(render);
      void ensureLibNames().then(() => openBlock === block && paint(render));
    } else if (snip?.components?.length) {
      // Legacy composite object: several Lean pieces jointly formalize it.
      subEl.innerHTML = `formalized by ${snip.components.length} Lean component${plural(snip.components.length)} · ${esc(snip.file)}`;
      const render = () => {
        // long Lean blocks fold by default; click a component header to expand
        const blocks = snip
          .components!.map((c) => {
            const n = lineCount(c.statement);
            return `<details class="lean-fold"><summary>${esc(c.label)} <span class="fold-count">(${n} line${plural(n)})</span></summary><pre>${highlightLean(c.statement, c.label)}</pre></details>`;
          })
          .join("");
        return `<div class="drawer-meta">${badge(snip)}${leanPageLink(objId)}</div>${blocks}`;
      };
      paint(render);
      void ensureLibNames().then(() => openBlock === block && paint(render));
    } else if (e.lean && snip) {
      const lean = e.lean;
      subEl.innerHTML = `↔ <span class="ident">${esc(lean.decl)}</span> · ${esc(lean.file)}:${lean.line}`;
      const render = () => {
        const nLines = lineCount(snip.statement);
        // structured when available; otherwise short statements show inline and
        // long ones fold (click to expand), exactly as before.
        const stmt = usableStructured(snip.structured)
          ? structuredHtml(snip.structured, lean.decl, statementTerms(e.env))
          : nLines <= 14
            ? `<pre>${highlightLean(snip.statement, lean.decl)}</pre>`
            : `<details class="lean-fold"><summary>Lean statement <span class="fold-count">(${nLines} lines)</span></summary><pre>${highlightLean(snip.statement, lean.decl)}</pre></details>`;
        return `<div class="drawer-meta">${badge(snip)}${closureBadge(snip)}${axiomsOf(snip)} · ${ghLinkOf(lean)}${leanPageLink(objId)}</div>${stmt}${usesHtml()}`;
      };
      paint(render);
      // upgrade the snippet with library cross-links once the name map arrives
      void ensureLibNames().then(() => openBlock === block && paint(render));
    } else {
      subEl.textContent = "no standalone Lean declaration";
      paint(() => `<p class="drawer-fallback">${esc(e.fallback ?? "")}</p>`);
    }
    document.body.classList.add("drawer-visible");
    drawer.setAttribute("aria-hidden", "false");
    drawer.focus();
  };

  for (const block of document.querySelectorAll("[data-objid]")) {
    const objId = (block as HTMLElement).dataset.objid!;
    if (block instanceof HTMLElement) {
      block.setAttribute("role", "button");
      if (!block.hasAttribute("tabindex")) block.tabIndex = 0;
    }
    block.addEventListener("click", (ev) => {
      // A click on a link INSIDE the block (e.g. an objref cross-reference)
      // must navigate only — not also slide the drawer open.
      if (ev.target instanceof Element && ev.target.closest("a")) return;
      // A click that ends a text selection (e.g. selecting a passage to leave
      // a margin comment on) must not open the drawer.
      const sel = window.getSelection();
      if (sel && !sel.isCollapsed) return;
      // A click on an annotated span inside the block whose panel is ALREADY
      // open is a pin/unpin gesture on the crosslink (the span's own handler
      // has just run), so it must not also re-open — a repaint would rebuild
      // the panel and throw the pin away. Only for the LIVE block: on a closed
      // panel, or one showing a different block, an annotated span opens the
      // panel exactly like any other part of the paper.
      if (openBlock === block && ev.target instanceof Element) {
        const xl = ev.target.closest("[data-xl]");
        if (xl && block.contains(xl)) return;
      }
      void open(objId, block);
    });
    block.addEventListener("keydown", (ev) => {
      const e = ev as KeyboardEvent;
      if (e.target instanceof Element && e.target.closest("a")) return;
      if (e.key === "Enter" || e.key === " ") {
        e.preventDefault();
        void open(objId, block);
      }
    });
  }
  document.getElementById("drawer-close")?.addEventListener("click", close);
  document.addEventListener("keydown", (ev) => {
    if (ev.key === "Escape") close();
  });
}
