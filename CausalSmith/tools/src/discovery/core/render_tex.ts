// Deterministic core → .tex renderer (D0_CORE_REDESIGN.md §12 / §5).
//
// The typed core is the single source of truth; the .tex is a PURE FUNCTION of it
// — no LLM. Shared by D-1.2 (proposal core: prose fields + to-prove statements)
// and D0 (solved core: + proof_tex). Prose fields are authored LaTeX and emitted
// verbatim; formal fields (condition / statement / proof_tex) are emitted verbatim
// from the typed core, never paraphrased. Each formal node gets a \label{<id>} so
// authored prose may \ref / \coreref it.
import type { Core, CoreAssumption, CoreDefinition, CoreStatement } from "./schema.js";
import { repairSerializedLatex } from "./latex_serialization.js";

/** Escape deterministic plain-text metadata such as qids/specs. Authored core
 * fields are handled separately because they may intentionally contain LaTeX. */
function escapeTexText(value: string): string {
  return value.replace(/[\\{}%$#_&~^]/g, (ch) => ({
    "\\": "\\textbackslash{}",
    "{": "\\{",
    "}": "\\}",
    "%": "\\%",
    "$": "\\$",
    "#": "\\#",
    "_": "\\_",
    "&": "\\&",
    "~": "\\textasciitilde{}",
    "^": "\\textasciicircum{}",
  })[ch]!);
}

/** Metadata identifiers commonly use underscores, but an escaped underscore is
 * not a useful line-break point to TeX. Preserve the exact rendered text while
 * allowing long qid/specialization headings to wrap at identifier boundaries. */
function escapeBreakableTexMetadata(value: string): string {
  return escapeTexText(value).replaceAll("\\_", "\\_\\allowbreak{}");
}

/** Long legacy formal DSL strings are rendered as monospace rather than guessed
 * LaTeX. Insert invisible discretionary breaks at their structural punctuation;
 * otherwise a single escaped `\\texttt` token can exceed the full text width. */
function escapeBreakableFormalText(value: string): string {
  return escapeTexText(value)
    .replaceAll("\\textbackslash{}", "\\textbackslash{}\\allowbreak{}")
    .replaceAll("\\_", "\\_\\allowbreak{}")
    .replaceAll("\\}", "\\}\\allowbreak{}")
    .replace(/([=,;:+/])/g, "$1\\allowbreak{}")
    .replace(/-(?![}\]])/g, "-\\allowbreak{}");
}

/** Minimal fail-safe normalization for authored LaTeX. The authoring prompts own
 * semantic LaTeX; the renderer only repairs two recurrent serialization hazards:
 * literal `\\n` separators emitted by JSON workers and raw sub/superscript marks
 * in text mode. `_` and `^` are BOTH math-mode-only characters, so they are
 * escaped together — escaping one but not the other still aborts the compile
 * ("Missing $ inserted") on the first `x^{...}` a producer leaves undelimited.
 * Inside $...$, \\(...\\), or \\[...\\] both remain live sub/superscripts. */
function normalizeAuthoredLatex(value: string): string {
  // `\\texttt` returns to text rules even when nested inside `\\(...\\)`.
  // Raw underscores in flat code identifiers therefore still abort TeX; make
  // those literal identifiers safe before the outer math-mode scan.
  const text = repairSerializedLatex(value).replace(
    /\\texttt\{([^{}]*)\}/g,
    (_whole, body: string) => `\\texttt{${body.replace(/(?<!\\)_/g, "\\_")}}`,
  );
  let out = "";
  let math = false;
  for (let i = 0; i < text.length; i++) {
    const pair = text.slice(i, i + 2);
    if (pair === "\\(" || pair === "\\[") {
      math = true;
      out += pair;
      i += 1;
      continue;
    }
    if (pair === "\\)" || pair === "\\]") {
      math = false;
      out += pair;
      i += 1;
      continue;
    }
    if (text[i] === "$" && (i === 0 || text[i - 1] !== "\\")) {
      math = !math;
      out += text[i];
      continue;
    }
    if ((text[i] === "_" || text[i] === "^") && !math && (i === 0 || text[i - 1] !== "\\")) {
      out += text[i] === "_" ? "\\_" : "\\textasciicircum{}";
      continue;
    }
    out += text[i];
  }
  return fitLongAuthoredMath(repairTaggedAlignedDisplays(out));
}

/** `aligned` is a subsidiary math environment, so amsmath rejects a `\tag`
 * placed inside it even when the author wrapped it in `\[...\]`. Preserve the
 * authored label while moving it to the owning `equation` environment. */
function repairTaggedAlignedDisplays(value: string): string {
  return value.replace(
    /\\\[\s*\\begin\{aligned\}((?:(?!\\end\{aligned\})[\s\S])*?)\\tag\{([^{}]+)\}([\s\S]*?)\\end\{aligned\}\s*\\\]/g,
    (_whole, before: string, tag: string, after: string) =>
      `\\begin{equation}\n\\begin{aligned}${before}${after}\\end{aligned}\n\\tag{${tag}}\n\\end{equation}`,
  );
}

/** TeX will not line-break an oversized display, and long inline formulas can
 * become indivisible boxes. Move only genuinely long inline formulas onto their
 * own fitted line and scale only genuinely long untagged displays. The content
 * remains authored LaTeX; this changes layout, not notation or semantics. */
function fitLongAuthoredMath(value: string): string {
  const fit = (body: string): string =>
    `\\makebox[\\linewidth][c]{\\resizebox{0.98\\linewidth}{!}{\\(\\displaystyle ${body.trim()}\\)}}`;
  let out = value.replace(/\\\[([\s\S]*?)\\\]/g, (whole, body: string) => {
    const compact = body.replace(/\s+/g, " ").trim();
    if (compact.length < 110 || /\\tag\b/.test(body)) return whole;
    return `\\[\n${fit(body)}\n\\]`;
  });
  out = out.replace(/\\\(([^\n]*?)\\\)/g, (whole, body: string) => {
    const compact = body.replace(/\s+/g, " ").trim();
    if (compact.length < 100) return whole;
    return `\\par\\noindent ${fit(body)}\\par\\noindent`;
  });
  return out;
}

/** Schema-aware formal-field adapter. New producers emit explicitly delimited
 * LaTeX and pass through. Legacy cores used a plain formal DSL (e.g. `theta=n^-1`
 * or `P_Z=product...`); render that faithfully as escaped monospace text instead
 * of guessing at mathematical semantics or placing it in an invalid math context. */
function renderFormalField(value: string): string {
  const serializationRepaired = repairSerializedLatex(value);
  const normalized = normalizeAuthoredLatex(serializationRepaired);
  const explicitlyAuthored = /(?:\\\(|\\\[|\\begin\{(?:equation|align|gather|multline|math|displaymath)\*?\}|(?<!\\)\$)/.test(normalized);
  return explicitlyAuthored ? normalized : `\\texttt{${escapeBreakableFormalText(serializationRepaired)}}`;
}

/** Bibliography citations are authored prose with occasional LaTeX such as
 * `\\emph{...}`. Preserve those commands while escaping raw alignment/comment
 * characters common in publication names. */
function normalizeBibliographyLatex(value: string): string {
  return normalizeAuthoredLatex(value)
    .replace(/(?<!\\)&/g, "\\&")
    .replace(/(?<!\\)%/g, "\\%")
    .replace(/(?<!\\)#/g, "\\#");
}

const STMT_ENV: Record<string, string> = {
  theorem: "theorem",
  lemma: "lemma",
  proposition: "proposition",
  openendedquestion: "openendedquestion",
  conjecture: "conjecture",
};

function preamble(): string {
  return [
    "\\documentclass{article}",
    "\\usepackage[margin=0.8in]{geometry}",
    // Keep this compatibility preamble broad: authored core fields are emitted
    // verbatim and may use standard commands chosen by an LLM. Package order is
    // intentional (natbib before hyperref; cleveref after hyperref).
    "\\usepackage{amsmath,amssymb,amsthm,mathtools}",
    "\\usepackage{mathrsfs,bm,bbm}",
    "\\usepackage{graphicx,booktabs,array,multirow,tabularx,longtable}",
    "\\usepackage{enumitem}",
    "\\usepackage{xcolor}",
    "\\usepackage{algorithm,algpseudocode}",
    "\\usepackage{subcaption,tikz}",
    "\\usepackage{siunitx,cancel,accents}",
    "\\usepackage{microtype}",
    "\\usepackage[numbers,sort&compress]{natbib}",
    "\\usepackage[colorlinks=true,linkcolor=blue,citecolor=blue,urlcolor=blue]{hyperref}",
    "\\usepackage{cleveref}",
    "\\setlength{\\emergencystretch}{2em}",
    "\\newtheorem{assumption}{Assumption}",
    "\\newtheorem{definition}{Definition}",
    "\\newtheorem{theorem}{Theorem}",
    "\\newtheorem{lemma}{Lemma}",
    "\\newtheorem{proposition}{Proposition}",
    "\\newtheorem{openendedquestion}{Open-ended Question}",
    "\\newtheorem{conjecture}{Conjecture}",
    "\\newcommand{\\coreref}[1]{\\ref{#1}}",
  ].join("\n");
}

function renderSymbols(core: Core): string {
  const items = core.symbols.map((s) => {
    const domainOrSignature = s.space ?? s.sig;
    const bits = [s.type, domainOrSignature, s.role]
      .filter(Boolean)
      .map((x) => renderFormalField(x!))
      .join("; ");
    const def = s.def
      ? `\n  \\par\\smallskip\\noindent\\emph{Definition.} ${renderFormalField(s.def)}`
      : "";
    return `  \\item ${renderFormalField(s.name)} --- ${bits}${def}`;
  });
  const lines = [
    `Target (estimand / structural parameter): ${renderFormalField(core.target_estimand)}.`,
    // This shared field also carries Stat estimators/rates, Panel regression
    // formulas, and route-feasibility diagnostics. Calling every value an
    // identifying functional is a substantive false claim for those lanes.
    core.estimand_functional ? `Primary functional / estimator / diagnostic: ${renderFormalField(core.estimand_functional)}.` : "",
    "\\begin{itemize}",
    ...items,
    "\\end{itemize}",
  ].filter(Boolean);
  return lines.join("\n");
}

function renderAssumption(a: CoreAssumption): string {
  const tag = a.standard
    ? `\\par\\smallskip\\noindent\\emph{Standard} (${a.standard.name}, \\cite{${a.standard.cite}}).`
    : a.novel
      ? `\\par\\smallskip\\noindent\\emph{Novel.} ${normalizeAuthoredLatex(a.novel.justification)}`
      : "";
  return [`\\begin{assumption}[${a.id}]\\label{${a.id}}`, renderFormalField(a.condition), tag, "\\end{assumption}"]
    .filter(Boolean)
    .join("\n");
}

function renderDefinition(d: CoreDefinition): string {
  const body = [
    `\\par\\smallskip\\noindent\\emph{Defined object.} ${renderFormalField(d.name)}`,
    `\\par\\smallskip\\noindent\\emph{Construction.} ${renderFormalField(d.construction)}`,
  ];
  if (d.by_member_properties !== undefined) {
    body.push(
      `\\par\\smallskip\\noindent\\emph{Member properties.} ${d.by_member_properties.map(renderFormalField).join("; ")}.`,
    );
  } else if (d.inputs && d.inputs.length > 0) {
    body.push(`\\par\\smallskip\\noindent\\emph{Inputs.} ${d.inputs.map(renderFormalField).join("; ")}.`);
  }
  return [`\\begin{definition}[${d.id}]\\label{${d.id}}`, ...body, "\\end{definition}"].join("\n");
}

function renderStatement(s: CoreStatement): string {
  const env = STMT_ENV[s.kind] ?? "theorem";
  const lines = [`\\begin{${env}}[${s.id}]\\label{${s.id}}`, renderFormalField(s.statement), `\\end{${env}}`];
  if (s.proof_tex && s.proof_tex.trim()) {
    const proof = normalizeAuthoredLatex(s.proof_tex.trim());
    const shouldWrapProof = s.status === "proved";
    const renderedProof = !shouldWrapProof || /\\begin\{proof\}/.test(proof)
      ? proof
      : `\\begin{proof}\n${proof}\n\\end{proof}`;
    // why: plain proof_tex after theorem text needs a LaTeX proof environment.
    lines.push(renderedProof);
  }
  const notes: string[] = [];
  if (s.justification) notes.push(`\\textit{Justification.} ${normalizeAuthoredLatex(s.justification)}`);
  if (s.gap) notes.push(`\\textit{Gap.} ${normalizeAuthoredLatex(s.gap)}`);
  if (s.consumer) notes.push(`\\textit{Consumer.} ${normalizeAuthoredLatex(s.consumer)}`);
  if (notes.length > 0) lines.push(`\\par\\smallskip\\noindent ${notes.join(" ")}`);
  return lines.join("\n");
}

/** Render a complete, readable .tex from the typed core. Pure; no LLM, no I/O. */
export function renderCoreTex(core: Core): string {
  const parts: string[] = [preamble(), "\\begin{document}", "\\sloppy"];
  parts.push(`\\section*{${escapeBreakableTexMetadata(core.qid)}}`);
  if (core.specialization) {
    parts.push(`\\noindent\\textit{Specialization:} ${escapeBreakableTexMetadata(core.specialization)}\\par`);
  }

  if (core.tldr) parts.push(`\\paragraph{TL;DR.} ${normalizeAuthoredLatex(core.tldr)}`);
  if (core.project_justification) {
    const p = core.project_justification;
    parts.push(
      "\\section{Project justification}",
      `\\paragraph{Gap.} ${normalizeAuthoredLatex(p.gap)}`,
      `\\paragraph{Niche.} ${normalizeAuthoredLatex(p.niche)}`,
      `\\paragraph{Fill.} ${normalizeAuthoredLatex(p.fill)}`,
    );
  }
  if (core.related_work) parts.push("\\section{Related work}", normalizeAuthoredLatex(core.related_work));

  parts.push("\\section{Setup}", renderSymbols(core));
  parts.push("\\section{Assumptions}", ...core.assumptions.map(renderAssumption));
  if (core.definitions.length > 0) {
    parts.push("\\section{Definitions}", ...core.definitions.map(renderDefinition));
  }
  parts.push("\\section{Main results}", ...core.statements.map(renderStatement));

  if (core.interpretation) parts.push("\\section{Interpretation}", normalizeAuthoredLatex(core.interpretation));
  if (core.technical_internal_limitation) {
    parts.push(
      "\\section*{Technical internal limitation (diagnostic only)}",
      normalizeAuthoredLatex(core.technical_internal_limitation),
    );
  }
  if (core.honest_scope) parts.push("\\section{Honest scope}", normalizeAuthoredLatex(core.honest_scope));
  if (core.bibliography.length > 0) {
    const entries = core.bibliography.map((b) => `  \\bibitem{${b.key}} ${normalizeBibliographyLatex(b.citation ?? b.key)}`);
    parts.push("\\begin{thebibliography}{99}", ...entries, "\\end{thebibliography}");
  }
  parts.push("\\end{document}");
  return parts.join("\n\n");
}
