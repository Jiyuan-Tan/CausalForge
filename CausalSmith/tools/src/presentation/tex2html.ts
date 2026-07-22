import { spawn } from "node:child_process";
import { parseAnchoredEnvs } from "./tex_anchors.js";
import { paperLabels } from "./emit.js";
import { citedKeys, type BibEntry } from "./citations.js";

type ObjLabelPart = { id: string; kind: string; number: string };

function objLabelParts(rawLabels: string, labels: ReadonlyMap<string, string>): ObjLabelPart[] | null {
  const ids = rawLabels.split(",").map((x) => x.trim());
  if (ids.length === 0 || ids.some((x) => !labels.has(x.startsWith("obj:") ? x.slice(4) : x))) return null;
  return ids.map((raw) => {
    const id = raw.startsWith("obj:") ? raw.slice(4) : raw;
    const label = labels.get(id) ?? id;
    const m = label.match(/^(.*)\s+(\S+)$/);
    return { id, kind: m?.[1] ?? "result", number: m?.[2] ?? label };
  });
}

/** PDF-like labels needed by the static HTML renderer. Formal objects use the same independent
 * per-kind counters as `paperLabels`; structural labels cover every environment the manuscript
 * prompts may cross-reference with cleveref. */
export function paperReferenceLabels(tex: string): Map<string, string> {
  const out = paperLabels(parseAnchoredEnvs(tex));
  const appendixAt = tex.indexOf("\\appendix");
  let ordinarySections = 0;
  let appendixSections = 0;
  for (const m of tex.matchAll(/\\section(?!\*)\s*\{/g)) {
    const at = m.index ?? 0;
    const title = readBalancedBraceGroup(tex, tex.indexOf("{", at));
    if (!title) continue;
    const label = tex.slice(title.end).match(/^\s*\\label\{([^}]+)\}/)?.[1];
    if (appendixAt >= 0 && at > appendixAt) {
      appendixSections += 1;
      if (label) out.set(label, `Section ${String.fromCharCode(64 + appendixSections)}`);
    } else {
      ordinarySections += 1;
      if (label) out.set(label, `Section ${ordinarySections}`);
    }
  }
  let tables = 0;
  for (const m of tex.matchAll(/\\begin\{table\*?\}[\s\S]*?\\end\{table\*?\}/g)) {
    tables += 1;
    const label = m[0].match(/\\label\{([^}]+)\}/)?.[1];
    if (label) out.set(label, `Table ${tables}`);
  }
  let figures = 0;
  for (const m of tex.matchAll(/\\begin\{figure\*?\}[\s\S]*?\\end\{figure\*?\}/g)) {
    figures += 1;
    const label = m[0].match(/\\label\{([^}]+)\}/)?.[1];
    if (label) out.set(label, `Figure ${figures}`);
  }
  let equations = 0;
  for (const m of tex.matchAll(/\\begin\{(?:equation|align)\*?\}[\s\S]*?\\end\{(?:equation|align)\*?\}/g)) {
    for (const label of m[0].matchAll(/\\label\{([^}]+)\}/g)) {
      equations += 1;
      out.set(label[1], `Equation ${equations}`);
    }
  }
  return out;
}

function joinNatural(parts: string[]): string {
  if (parts.length <= 1) return parts[0] ?? "";
  if (parts.length === 2) return `${parts[0]} and ${parts[1]}`;
  return `${parts.slice(0, -1).join(", ")}, and ${parts[parts.length - 1]}`;
}

function crefWords(parts: ObjLabelPart[], capitalize: boolean, link: (p: ObjLabelPart) => string): string {
  const sameKind = parts.every((p) => p.kind === parts[0]?.kind);
  if (sameKind) {
    let kind = parts[0]?.kind ?? "result";
    if (parts.length > 1) kind += kind.endsWith("s") ? "" : "s";
    kind = capitalize ? kind[0].toUpperCase() + kind.slice(1) : kind.toLowerCase();
    return `${kind} ${joinNatural(parts.map(link))}`;
  }
  return joinNatural(parts.map((p) => {
    const kind = capitalize ? p.kind[0].toUpperCase() + p.kind.slice(1) : p.kind.toLowerCase();
    return `${kind} ${link(p)}`;
  }));
}

/** Resolve cleveref references for page metadata, where hyperlinks are unavailable. */
export function resolveObjCrefsPlain(tex: string, labels: ReadonlyMap<string, string>): string {
  let out = tex.replace(/\\(Cref|cref)\{([^}]+)\}/g, (whole, command: string, raw: string) => {
    const parts = objLabelParts(raw, labels);
    return parts ? crefWords(parts, command === "Cref", (p) => p.number) : whole;
  });
  // Legacy bundles remain readable while the pipeline gate requires new prose to use cleveref.
  out = out.replace(/\\ref\{([^}]+)\}/g, (_whole, raw: string) => {
    const id = raw.startsWith("obj:") ? raw.slice(4) : raw;
    return labels.get(id)?.split(" ").pop() ?? id;
  });
  return out;
}

/**
 * tex → HTML fragment for the website, done at P4 (never at site build).
 * pandoc 2.9 silently drops unknown environments, so we split the document
 * ourselves: anchored envs (and proofs/abstract) are extracted, their bodies
 * converted separately, and re-wrapped in `data-objid` divs the drawer can
 * target. Citations are pre-rendered from the verified pool (the PDF uses
 * natbib; the web fragment inlines author-year text).
 */
export async function tex2html(
  paperTex: string,
  bib: BibEntry[],
  /** Object ids with an actual Lean declaration or composite Lean snippet.
   * When supplied, presentation-only blocks remain anchored but are not drawers. */
  drawerObjIds?: ReadonlySet<string>,
): Promise<string> {
  const cited = citedKeys(paperTex);
  const body = paperTex.match(/\\begin\{document\}([\s\S]*)\\end\{document\}/)?.[1] ?? paperTex;
  let tex = body
    .replace(/\\maketitle/g, "")
    .replace(/\\bibliographystyle\{[^}]*\}/g, "")
    .replace(/\\bibliography\{[^}]*\}/g, "")
    .replace(/\\appendix/g, "");
  // Proof provenance is stored as ordinary LaTeX comments (% lean: ...), sometimes on the same
  // line as a display closer. Pandoc can carry that text into its MathJax payload, where `%`
  // comments out the closing delimiter and KaTeX warns or renders malformed math. Remove unescaped
  // comments before any block is stashed; escaped percentages (\\%) remain reader-visible.
  tex = stripLatexComments(tex);
  tex = renderCites(tex, bib);

  // A symbol `\leanref` whose display is inline math, nested inside a larger `\(…\)`/`\[…\]` display,
  // would become a math-span INSIDE a math-span (the page's KaTeX pass then emits raw markup). The PDF
  // tolerates it via `\ensuremath`; the web cannot, so unwrap the link there — the symbol renders as
  // part of the surrounding equation, and the clickable link survives at standalone prose mentions and
  // in the formal-layer panel.
  tex = unwrapNestedSymbolLeanrefs(tex);

  // \leanref{obj-id}{display} → a drawer-opening span (the drawer binds every [data-objid]).
  // Tokenized pre-conversion (pandoc would mangle a raw <span>), patched back after pandoc.
  const lr = renderLeanrefs(tex);
  tex = lr.tex;

  // cleveref object references → the target env's kind + printed number, linked to its block.
  // Pandoc cannot resolve these (no aux file), so swap in tokens pre-conversion and patch HTML.
  const refLabels = paperReferenceLabels(body);
  const refTokens: { token: string; html: string }[] = [];
  tex = tex.replace(/\\(Cref|cref)\{([^}]+)\}/g, (whole, command: string, raw: string) => {
    const parts = objLabelParts(raw, refLabels);
    if (!parts) return whole;
    const token = `PSMITHREF${refTokens.length}X`;
    refTokens.push({
      token,
      html: crefWords(parts, command === "Cref", (p) =>
        raw.split(",").map((x) => x.trim()).find((x) => (x.startsWith("obj:") ? x.slice(4) : x) === p.id)?.startsWith("obj:")
          ? `<a class="objref" href="#obj-${esc(p.id)}">${esc(p.number)}</a>`
          : esc(p.number)),
    });
    return token;
  });
  // Legacy \ref remains renderable for accepted bundles created before the cleveref migration.
  tex = tex.replace(/\\ref\{([^}]+)\}/g, (_, rawLabel: string) => {
    const isObj = rawLabel.startsWith("obj:");
    const id = isObj ? rawLabel.slice(4) : rawLabel;
    const label = refLabels.get(id);
    const num = label?.split(" ").pop() ?? id;
    const token = `PSMITHREF${refTokens.length}X`;
    refTokens.push({
      token,
      html: isObj ? `<a class="objref" href="#obj-${esc(id)}">${esc(num)}</a>` : esc(num),
    });
    return token;
  });

  const placeholders: { token: string; html: () => Promise<string> }[] = [];
  let n = 0;
  const stash = (texOf: string, wrap: (inner: string) => string): string => {
    const token = `PSMITHBLOCK${n++}MARKER`;
    placeholders.push({ token, html: async () => wrap(await pandoc(texOf)) });
    return `\n\n${token}\n\n`;
  };

  // Generated cited-dependency footnotes are custom LaTeX macros defined in the PDF preamble,
  // which is intentionally absent from the pandoc fragment. Extract them explicitly so the web
  // paper preserves the same trust-boundary disclosure instead of dropping an unknown command.
  tex = replaceVerificationFootnotes(tex, (inner) =>
    stash(inner, (h) => `<aside class="verification-footnote">${h}</aside>`),
  );

  // abstract
  tex = tex.replace(/\\begin\{abstract\}([\s\S]*?)\\end\{abstract\}/g, (_, inner: string) =>
    stash(inner, (h) => `<div class="abstract"><h2>Abstract</h2>${h}</div>`),
  );
  // anchored formal environments
  const labels = refLabels;
  tex = replaceFormalEnvs(tex, ({ env, objId, title, inner }) => {
      const label = labels.get(objId) ?? env;
      const head = `<span class="env-label">${esc(label)} <span class="obj-tag">[${esc(objId)}]</span>${title ? ` (${titleHtml(title)})` : ""}.</span>`;
      const kind = env.replace(/v$/, "");
      const drawerEnabled = drawerObjIds?.has(objId) ?? true;
      const drawerAttrs = drawerEnabled
        ? ` data-objid="${esc(objId)}" tabindex="0"`
        : ` data-presentation-only="true"`;
      return stash(
        inner,
        (h) =>
          `<div class="formal-block kind-${kind}" id="obj-${esc(objId)}"${drawerAttrs}>${head}${h}${drawerEnabled ? `<span class="lean-hint">⊢ Lean</span>` : ""}</div>`,
      );
    });
  // proofs
  tex = tex.replace(/\\begin\{proof\}(?:\[([^\]]*)\])?([\s\S]*?)\\end\{proof\}/g, (_, title: string | undefined, inner: string) =>
    stash(inner, (h) => `<div class="proof"><span class="env-label">${esc(title ?? "Proof")}.</span>${h}<span class="qed">∎</span></div>`),
  );

  let html = await pandoc(tex);
  for (const p of placeholders) {
    const rendered = await p.html();
    html = html.replace(new RegExp(`<p>\\s*${p.token}\\s*</p>`), () => rendered);
  }
  for (const r of refTokens) html = html.replaceAll(r.token, r.html);
  for (const r of lr.tokens) html = html.replaceAll(r.token, r.html);
  html += references(bib.filter((e) => cited.has(e.key))); // why: P4 verifies cited keys only, so uncited stale entries must not publish.
  return html;
}

function stripLatexComments(tex: string): string {
  return tex
    .split("\n")
    .map((line) => {
      for (let i = 0; i < line.length; i++) {
        if (line[i] !== "%") continue;
        let slashes = 0;
        for (let j = i - 1; j >= 0 && line[j] === "\\"; j--) slashes++;
        if (slashes % 2 === 0) return line.slice(0, i);
      }
      return line;
    })
    .join("\n");
}

const FORMAL_BEGIN_RE =
  /\\begin\{(theoremv|assumptionv|lemmav|definitionv|citedv|propositionv|remarkv)\}\{([^}]+)\}/g;

function readOptionalFormalTitle(tex: string, pos: number): { title: string | undefined; end: number } {
  if (tex[pos] !== "[") return { title: undefined, end: pos };
  let depth = 1;
  for (let i = pos + 1; i < tex.length; i++) {
    if (tex[i] === "\\") {
      i++;
    } else if (tex[i] === "[") {
      depth++;
    } else if (tex[i] === "]") {
      depth--;
      if (depth === 0) return { title: tex.slice(pos + 1, i), end: i + 1 };
    }
  }
  return { title: undefined, end: pos };
}

function replaceFormalEnvs(
  tex: string,
  f: (e: { env: string; objId: string; title: string | undefined; inner: string }) => string,
): string {
  let out = "";
  let last = 0;
  FORMAL_BEGIN_RE.lastIndex = 0;
  let m: RegExpExecArray | null;
  while ((m = FORMAL_BEGIN_RE.exec(tex))) {
    const env = m[1];
    const objId = m[2];
    const title = readOptionalFormalTitle(tex, FORMAL_BEGIN_RE.lastIndex);
    // A star immediately after the optional title asks the PDF macro to put a generated scope-note
    // mark in the environment heading. It is header metadata, not mathematical body text.
    const bodyStart = title.end + (tex[title.end] === "*" ? 1 : 0); // why: titles may contain nested bracketed math, so `[^\]]*` corrupts the body.
    const endTag = `\\end{${env}}`;
    const bodyEnd = tex.indexOf(endTag, bodyStart);
    if (bodyEnd < 0) continue;
    const end = bodyEnd + endTag.length;
    out += tex.slice(last, m.index) + f({ env, objId, title: title.title, inner: tex.slice(bodyStart, bodyEnd) });
    last = end;
    FORMAL_BEGIN_RE.lastIndex = end;
  }
  return out + tex.slice(last);
}

/** Inline display text → HTML, converting `$...$` / `\(...\)` math to the page's KaTeX spans
 *  (mirrors `titleHtml`), escaping the rest. Used for `\leanref` display text. */
function inlineMathHtml(s: string): string {
  return s
    .split(/(\$[^$]+\$|\\\([\s\S]*?\\\))/g)
    .map((part) => {
      const m = part.match(/^\$([^$]+)\$$/) ?? part.match(/^\\\(([\s\S]*?)\\\)$/);
      return m ? `<span class="math inline">\\(${esc(m[1])}\\)</span>` : esc(part);
    })
    .join("");
}

/** Read one TeX braced argument, including nested groups and literal escaped braces. */
function readBalancedBraceGroup(tex: string, open: number): { content: string; end: number } | null {
  if (tex[open] !== "{") return null;
  let depth = 1;
  for (let i = open + 1; i < tex.length; i++) {
    // `\{` and `\}` are literal glyphs, not grouping delimiters.
    if (tex[i] === "\\") {
      i++;
      continue;
    }
    if (tex[i] === "{") depth++;
    else if (tex[i] === "}" && --depth === 0) return { content: tex.slice(open + 1, i), end: i + 1 };
  }
  return null;
}

function replaceVerificationFootnotes(tex: string, render: (inner: string) => string): string {
  // Longest first: the legacy macro name is a prefix of the split `...footnotetext` macro.
  const needles = ["\\verificationfootnotetext", "\\verificationfootnote"];
  let out = "";
  let cursor = 0;
  while (true) {
    const candidates = needles
      .map((needle) => ({ needle, idx: tex.indexOf(needle, cursor) }))
      .filter(({ idx }) => idx >= 0)
      .sort((a, b) => a.idx - b.idx || b.needle.length - a.needle.length);
    if (candidates.length === 0) break;
    const { needle, idx } = candidates[0];
    const group = readBalancedBraceGroup(tex, idx + needle.length);
    if (!group) break;
    out += tex.slice(cursor, idx) + render(group.content);
    cursor = group.end;
  }
  return out + tex.slice(cursor);
}

/**
 * Replace every `\leanref{obj-id}{display}` with a token (patched to a drawer-opening
 * `<span class="leanref" data-objid="obj-id">display</span>` after pandoc), and collect the
 * referenced obj-ids. Parses the two arguments with a balanced-brace scan so the display may
 * contain nested braces / inline math. Malformed occurrences are passed through untouched.
 */
export function renderLeanrefs(tex: string): {
  tex: string;
  ids: string[];
  tokens: { token: string; html: string }[];
} {
  const ids: string[] = [];
  const tokens: { token: string; html: string }[] = [];
  const MARK = "\\leanref{";
  let out = "";
  let i = 0;
  for (;;) {
    const idx = tex.indexOf(MARK, i);
    if (idx < 0) {
      out += tex.slice(i);
      break;
    }
    out += tex.slice(i, idx);
    const idGroup = readBalancedBraceGroup(tex, idx + "\\leanref".length);
    if (!idGroup) {
      out += tex.slice(idx);
      break;
    }
    const dispGroup = readBalancedBraceGroup(tex, idGroup.end);
    if (!dispGroup) {
      // malformed (no second arg) — emit verbatim, continue past the marker
      out += tex.slice(idx, idGroup.end);
      i = idGroup.end;
      continue;
    }
    const id = idGroup.content;
    const disp = dispGroup.content;
    const token = `PSMITHLEANREF${tokens.length}X`;
    // Symbol displays are `\ensuremath{…}` (math-safe for the PDF); render that run as inline math.
    const dispWeb = disp.replace(/^\\ensuremath\{([\s\S]*)\}$/, "\\($1\\)");
    tokens.push({
      token,
      html: `<span class="leanref" data-objid="${esc(id)}">${inlineMathHtml(dispWeb)}</span>`,
    });
    ids.push(id);
    out += token;
    i = dispGroup.end;
  }
  return { tex: out, ids, tokens };
}

/** The obj-ids referenced by `\leanref` in a paper — for P4 validation that each resolves. */
export function extractLeanrefIds(tex: string): string[] {
  return renderLeanrefs(tex).ids;
}

/** Strip symbol `\leanref{sym:…}{…}` wrappers from a fragment, leaving the bare math display (used for
 *  fragments INSIDE a math display, where a clickable link cannot survive). Balanced-brace parse. */
function stripSymbolLeanrefs(s: string): string {
  const OPEN = "\\leanref{sym:";
  let out = "";
  let i = 0;
  for (;;) {
    const idx = s.indexOf(OPEN, i);
    if (idx < 0) {
      out += s.slice(i);
      break;
    }
    out += s.slice(i, idx);
    const idGroup = readBalancedBraceGroup(s, idx + "\\leanref".length);
    if (!idGroup) {
      out += s.slice(idx);
      break;
    }
    const dispGroup = readBalancedBraceGroup(s, idGroup.end);
    if (!dispGroup) {
      out += s.slice(idx, idGroup.end);
      i = idGroup.end;
      continue;
    }
    const disp = dispGroup.content;
    const m =
      disp.match(/^\\ensuremath\{([\s\S]*)\}$/) ?? disp.match(/^\$([\s\S]+)\$$/) ?? disp.match(/^\\\(([\s\S]*?)\\\)$/);
    out += m ? m[1] : disp;
    i = dispGroup.end;
  }
  return out;
}

/** Unwrap symbol `\leanref`s nested inside a `\(…\)`/`\[…\]` math display (web-only — see tex2html). */
function unwrapNestedSymbolLeanrefs(tex: string): string {
  return tex
    .replace(/\\\(([\s\S]*?)\\\)/g, (_, inner: string) => `\\(${stripSymbolLeanrefs(inner)}\\)`)
    .replace(/\\\[([\s\S]*?)\\\]/g, (_, inner: string) => `\\[${stripSymbolLeanrefs(inner)}\\]`);
}

function pandoc(tex: string): Promise<string> {
  return new Promise((resolve, reject) => {
    const child = spawn("pandoc", ["--from", "latex", "--to", "html", "--mathjax"], {
      stdio: ["pipe", "pipe", "pipe"],
    });
    let out = "";
    let err = "";
    child.stdout.on("data", (d) => (out += d));
    child.stderr.on("data", (d) => (err += d));
    child.on("error", reject);
    child.on("close", (code) =>
      code === 0 ? resolve(out.trim()) : reject(new Error(`pandoc exited ${code}: ${err.slice(0, 2000)}`)),
    );
    child.stdin.end(tex);
  });
}

function esc(s: string): string {
  return s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");
}

/** Env titles may carry inline math, with EITHER `$…$` or `\(…\)` delimiters (e.g.
 *  `Law class \(\mathcal P_{\alpha,\gamma}\)`): emit the same pandoc-style math spans as body text so
 *  the page's KaTeX pass renders them. (Handling only `$…$` left `\(…\)` titles raw on the page.) */
function titleHtml(title: string): string {
  return title
    .split(/(\$[^$]+\$|\\\([\s\S]*?\\\))/g)
    .map((part) => {
      const m = part.match(/^\$([\s\S]+)\$$/) ?? part.match(/^\\\(([\s\S]*?)\\\)$/);
      return m ? `<span class="math inline">\\(${esc(m[1])}\\)</span>` : esc(part);
    })
    .join("");
}

function firstFamily(author: string): string {
  const first = author.split(/\s+and\s+/)[0];
  return first.includes(",") ? first.split(",")[0].trim() : first.trim().split(/\s+/).pop() ?? first;
}

function renderCites(tex: string, bib: BibEntry[]): string {
  const byKey = new Map(bib.map((e) => [e.key, e]));
  const name = (k: string) => {
    const e = byKey.get(k.trim());
    if (!e) return k;
    const fam = firstFamily(e.fields.author ?? "");
    const etal = (e.fields.author ?? "").includes(" and ") ? " et al." : "";
    return { fam: fam + etal, year: e.fields.year ?? "" };
  };
  return tex
    .replace(/\\citet\*?(?:\[[^\]]*\])*\{([^}]+)\}/g, (_, keys: string) =>
      keys
        .split(",")
        .map((k) => {
          const v = name(k);
          return typeof v === "string" ? v : `${v.fam} (${v.year})`;
        })
        .join("; "),
    )
    .replace(/\\citep\*?(?:\[[^\]]*\])*\{([^}]+)\}/g, (_, keys: string) => {
      const inner = keys
        .split(",")
        .map((k) => {
          const v = name(k);
          return typeof v === "string" ? v : `${v.fam}, ${v.year}`;
        })
        .join("; ");
      return `(${inner})`;
    });
}

function references(bib: BibEntry[]): string {
  if (bib.length === 0) return "";
  const items = bib
    .map((e) => {
      const f = e.fields;
      const link = f.doi
        ? ` <a href="https://doi.org/${esc(f.doi)}">doi</a>`
        : f.eprint
          ? ` <a href="https://arxiv.org/abs/${esc(f.eprint)}">arXiv</a>`
          : "";
      const venue = f.journal ?? f.booktitle ?? f.publisher ?? "";
      return `<li id="ref-${esc(e.key)}">${esc(f.author ?? "")} (${esc(f.year ?? "")}). ${esc(f.title ?? "")}. <em>${esc(venue)}</em>.${link}</li>`;
    })
    .join("\n");
  return `\n<section class="references"><h2>References</h2><ul>\n${items}\n</ul></section>`;
}
