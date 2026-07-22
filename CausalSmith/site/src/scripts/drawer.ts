/** Slide-over drawer: click a formal block → show its verified Lean statement. */

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
interface Snippet {
  decl: string;
  file: string;
  line: number;
  statement: string;
  sorry_free: boolean;
  axioms: string[] | null;
  /** Composite objects: the Lean pieces that jointly formalize the statement. */
  components?: { label: string; statement: string }[];
}
interface PaperData {
  github: string | null;
  commit: string;
  leanSubdir: string;
  entries: Entry[];
  snippets: Record<string, Snippet>;
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
        return katex.renderToString(m[1], { throwOnError: false });
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

export function initDrawer(): void {
  const dataEl = document.getElementById("paper-data");
  if (!dataEl) return;
  const data: PaperData = JSON.parse(dataEl.textContent ?? "{}");
  const byId = new Map(data.entries.map((e) => [e.obj_id, e]));
  const drawer = document.getElementById("drawer")!;
  const scrim = document.getElementById("drawer-scrim")!;
  const titleEl = document.getElementById("drawer-title")!;
  const subEl = document.getElementById("drawer-sub")!;
  const bodyEl = document.getElementById("drawer-body")!;
  let openBlock: Element | null = null;

  const close = () => {
    document.body.classList.remove("drawer-visible");
    drawer.setAttribute("aria-hidden", "true");
    openBlock?.classList.remove("drawer-open");
    openBlock = null;
  };

  const flashBlock = (objId: string) => {
    const target = document.querySelector(`[data-objid="${objId}"]`);
    if (!target) return;
    target.scrollIntoView({ behavior: "smooth", block: "center" });
    target.classList.add("flash");
    setTimeout(() => target.classList.remove("flash"), 1600);
  };

  const leanPageLink = (objId: string): string => {
    if (!data.leanPage) return "";
    const anchor = data.leanAnchors?.[objId];
    const href = anchor ? `${data.leanPage}#${encodeURIComponent(anchor)}` : data.leanPage;
    return ` · <a href="${href}">view in Lean development</a>`;
  };

  const open = (objId: string, block: Element) => {
    const e = byId.get(objId);
    if (!e) return;
    openBlock?.classList.remove("drawer-open");
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

    const snip = data.snippets[objId];
    if (snip?.components?.length) {
      // composite object: several Lean pieces jointly formalize the statement
      subEl.innerHTML = `formalized by ${snip.components.length} Lean component${snip.components.length === 1 ? "" : "s"} · ${esc(snip.file)}`;
      const badge = snip.sorry_free
        ? '<span class="badge-ok">✓ sorry-free (source scan)</span>'
        : '<span class="badge-warn">⚠ contains sorry</span>';
      // long Lean blocks fold by default; click a component header to expand
      const blocks = snip.components
        .map((c) => {
          const n = c.statement.split("\n").length;
          return `<details class="lean-fold"><summary>${esc(c.label)} <span class="fold-count">(${n} line${n === 1 ? "" : "s"})</span></summary><pre>${highlightLean(c.statement, c.label)}</pre></details>`;
        })
        .join("");
      bodyEl.innerHTML = `<div class="drawer-meta">${badge}${leanPageLink(objId)}</div>${blocks}`;
      void ensureLibNames().then(() => {
        if (openBlock !== block) return;
        const pres = bodyEl.querySelectorAll("pre");
        snip.components!.forEach((c, i) => {
          if (pres[i]) pres[i].innerHTML = highlightLean(c.statement, c.label);
        });
      });
    } else if (e.lean && snip) {
      const ghLink = data.github
        ? `<a href="https://github.com/${data.github}/blob/${data.commit}/${data.leanSubdir}/${e.lean.file}#L${e.lean.line}" target="_blank" rel="noopener">full file ↗ GitHub @ ${data.commit.slice(0, 7)}</a>`
        : `pinned commit ${data.commit.slice(0, 7)}`;
      subEl.innerHTML = `↔ <span class="ident">${esc(e.lean.decl)}</span> · ${esc(e.lean.file)}:${e.lean.line}`;
      const badge = snip.sorry_free
        ? '<span class="badge-ok">✓ sorry-free (source scan)</span>'
        : '<span class="badge-warn">⚠ contains sorry</span>';
      const axioms =
        snip.axioms === null
          ? ""
          : ` · axioms: ${snip.axioms.length === 0 ? '<span class="badge-ok">standard</span>' : esc(snip.axioms.join(", "))}`;
      const uses =
        e.uses.length > 0
          ? `<div class="drawer-uses">uses: ${e.uses
              .map((u) => {
                const ue = byId.get(u);
                return `<a data-jump="${esc(u)}">${esc(ue ? `${ue.paper_label} (${u})` : u)}</a>`;
              })
              .join(" · ")}</div>`
          : "";
      const nLines = snip.statement.split("\n").length;
      // short statements show inline; long ones fold (click to expand)
      const stmtHtml =
        nLines <= 14
          ? `<pre>${highlightLean(snip.statement, e.lean.decl)}</pre>`
          : `<details class="lean-fold"><summary>Lean statement <span class="fold-count">(${nLines} lines)</span></summary><pre>${highlightLean(snip.statement, e.lean.decl)}</pre></details>`;
      bodyEl.innerHTML = `
        <div class="drawer-meta">${badge}${axioms} · ${ghLink}${leanPageLink(objId)}</div>
        ${stmtHtml}
        ${uses}`;
      // upgrade the snippet with library cross-links once the name map arrives
      void ensureLibNames().then(() => {
        const pre = bodyEl.querySelector("pre");
        if (pre && openBlock === block) pre.innerHTML = highlightLean(snip.statement, e.lean.decl);
      });
    } else {
      subEl.textContent = "no standalone Lean declaration";
      bodyEl.innerHTML = `<p class="drawer-fallback">${esc(e.fallback ?? "")}</p>`;
    }
    for (const a of bodyEl.querySelectorAll("a[data-jump]")) {
      a.addEventListener("click", (ev) => {
        ev.preventDefault();
        close();
        flashBlock((a as HTMLElement).dataset.jump!);
      });
    }
    document.body.classList.add("drawer-visible");
    drawer.setAttribute("aria-hidden", "false");
  };

  for (const block of document.querySelectorAll("[data-objid]")) {
    const objId = (block as HTMLElement).dataset.objid!;
    block.addEventListener("click", () => open(objId, block));
    block.addEventListener("keydown", (ev) => {
      if ((ev as KeyboardEvent).key === "Enter") open(objId, block);
    });
  }
  scrim.addEventListener("click", close);
  document.getElementById("drawer-close")?.addEventListener("click", close);
  document.addEventListener("keydown", (ev) => {
    if (ev.key === "Escape") close();
  });
}
