import { lintNegativeContributionFraming, type LintProblem } from "./tex_anchors.js";

/**
 * P6 slides — parser and mechanical lint for `slides.md`, the authored seminar-deck
 * source (see internal/plans/2026-08-27-p6-slides-proposal.md).
 *
 * Format contract (kept deliberately tiny so a single model call can honor it and an
 * operator can hand-edit the file):
 *   - `---` on its own line separates slides;
 *   - the first slide opens with `# <talk title>`, every later slide with `## <slide title>`;
 *   - `@formal <obj_id>` on its own line marks where the frozen formal-layer body is
 *     injected verbatim at render time — the model NEVER writes displayed math itself;
 *   - `@informal <obj_id>: <one-line headline>` is a labeled plain-language restatement,
 *     rendered with an "informal" chip linking to the audited paper environment;
 *   - `@figure <kebab-name>: <caption>` shows `slides_assets/<name>.svg` — a SCHEMATIC
 *     illustration (DAG, regime diagram, pipeline sketch; never a data plot), rendered
 *     with an "illustrative" label; the stage authors a missing asset with one codex
 *     call, and existing assets (incl. hand-drawn) are never overwritten;
 *   - everything else is ordinary markdown prose/bullets (inline `\(…\)`/`$…$` allowed).
 *
 * The site has a mirroring renderer in `site/src/lib/slides.ts` — keep the two in sync.
 */

export type SlideBlock =
  | { kind: "prose"; md: string }
  | { kind: "formal"; objId: string }
  | { kind: "informal"; objId: string; text: string }
  | { kind: "figure"; name: string; caption: string };

export interface Slide {
  title: string;
  blocks: SlideBlock[];
}

export interface SlidesDoc {
  talkTitle: string;
  slides: Slide[];
}

/** Minimal view of a formal-layer source block that the lint needs. */
export interface FormalBlockRef {
  obj_id: string;
  kind: string;
}

const FORMAL_RE = /^@formal\s+(\S+)\s*$/;
const INFORMAL_RE = /^@informal\s+(\S+)\s*:\s*(.*)$/;
const FIGURE_RE = /^@figure\s+([A-Za-z0-9_-]+)\s*:\s*(.*)$/;

/** Split `slides.md` into slides and typed blocks. Throws on structural defects the
 *  renderer could not survive (no title, a slide with no `##` heading). */
export function parseSlidesMd(md: string): SlidesDoc {
  const chunks = md
    .split(/\n---[ \t]*\n/)
    .map((c) => c.trim())
    .filter((c) => c.length > 0);
  if (chunks.length === 0) throw new Error("slides.md is empty");
  const first = chunks[0];
  const titleMatch = /^#\s+(.+)$/m.exec(first);
  if (!titleMatch || !first.trimStart().startsWith("# ")) {
    throw new Error("slides.md must open with a `# <talk title>` title slide");
  }
  const talkTitle = titleMatch[1].trim();
  const slides: Slide[] = [];
  for (const [i, chunk] of chunks.entries()) {
    const lines = chunk.split("\n");
    let title: string;
    if (i === 0) {
      title = talkTitle;
      lines.shift();
    } else {
      const m = /^##\s+(.+)$/.exec(lines[0] ?? "");
      if (!m) throw new Error(`slide ${i + 1} does not open with a \`## <title>\` heading`);
      title = m[1].trim();
      lines.shift();
    }
    const blocks: SlideBlock[] = [];
    let prose: string[] = [];
    const flush = () => {
      const md = prose.join("\n").trim();
      if (md) blocks.push({ kind: "prose", md });
      prose = [];
    };
    for (const line of lines) {
      const f = FORMAL_RE.exec(line);
      const inf = INFORMAL_RE.exec(line);
      const fig = FIGURE_RE.exec(line);
      if (f) {
        flush();
        blocks.push({ kind: "formal", objId: normalizeObjId(f[1]) });
      } else if (inf) {
        flush();
        blocks.push({ kind: "informal", objId: normalizeObjId(inf[1]), text: inf[2].trim() });
      } else if (fig) {
        flush();
        blocks.push({ kind: "figure", name: fig[1], caption: fig[2].trim() });
      } else {
        prose.push(line);
      }
    }
    flush();
    slides.push({ title, blocks });
  }
  return { talkTitle, slides };
}

/** Models sometimes emit the paper-body form `obj:thm:x`; the formal layer keys on `thm:x`. */
function normalizeObjId(raw: string): string {
  return raw.replace(/^obj:/, "");
}

/**
 * Mechanical quality gate (no model calls). Checks:
 *   - every directive resolves to a formal-layer block;
 *   - every theorem block appears on some slide (formal or informal) — the deck may
 *     not silently drop a main result;
 *   - no model-authored displayed math (`$$`, `\[`, `\begin{align…}`) — displayed math
 *     enters only through `@formal` injection;
 *   - `@informal` headlines are non-empty;
 *   - deck shape: 8–18 slides for a 15–20 minute talk;
 *   - affirmative contribution framing (reused P4 lint) over the prose.
 */
export function lintSlides(doc: SlidesDoc, formalBlocks: FormalBlockRef[]): LintProblem[] {
  const problems: LintProblem[] = [];
  const known = new Set(formalBlocks.map((b) => b.obj_id));
  const referenced = new Set<string>();
  let proseAll = "";
  let figures = 0;
  const displayedMath = (s: string): boolean =>
    /\$\$|\\\[|\\begin\{(align|equation|gather|multline)/.test(s);
  for (const [i, slide] of doc.slides.entries()) {
    const where = `slide ${i + 1} ("${slide.title}")`;
    // The prompt permits an open-directions/limitations slide when the paper
    // states them; its prose is exempt from the negative-framing lint (which
    // would otherwise always trip on "open question/problem" phrasing).
    const limitationsSlide = /\b(limitations?|open (directions?|questions?|problems?)|future work)\b/i.test(
      slide.title,
    );
    for (const block of slide.blocks) {
      if (block.kind === "prose") {
        if (!limitationsSlide) proseAll += block.md + "\n";
        if (displayedMath(block.md)) {
          problems.push({
            gate: "slides-displayed-math",
            detail: `${where}: displayed math in authored prose — formal content must enter via @formal <obj_id>`,
          });
        }
        if (/^@(formal|informal|figure)\b/m.test(block.md)) {
          problems.push({
            gate: "slides-directive-malformed",
            detail: `${where}: a line starts with @formal/@informal/@figure but does not parse (expected \`@formal <obj_id>\`, \`@informal <obj_id>: <headline>\`, or \`@figure <kebab-name>: <caption>\`)`,
          });
        }
      } else if (block.kind === "figure") {
        figures += 1;
        if (displayedMath(block.caption)) {
          problems.push({
            gate: "slides-displayed-math",
            detail: `${where}: displayed math in the @figure caption — use inline \\(…\\) only`,
          });
        }
        if (!/^[a-z][a-z0-9-]*$/.test(block.name)) {
          problems.push({
            gate: "slides-figure-name",
            detail: `${where}: figure name "${block.name}" must be lowercase kebab-case (it becomes slides_assets/<name>.svg)`,
          });
        }
        if (!block.caption) {
          problems.push({
            gate: "slides-figure-caption",
            detail: `${where}: @figure ${block.name} has an empty caption`,
          });
        }
      } else {
        referenced.add(block.objId);
        if (!known.has(block.objId)) {
          problems.push({
            gate: "slides-unknown-obj",
            detail: `${where}: @${block.kind} references "${block.objId}", which is not a formal-layer block`,
            objId: block.objId,
          });
        }
        if (block.kind === "informal") {
          proseAll += block.text + "\n";
          if (displayedMath(block.text)) {
            problems.push({
              gate: "slides-displayed-math",
              detail: `${where}: displayed math in an @informal headline — use inline \\(…\\) only`,
            });
          }
          // A long multi-clause headline defeats the labeled-restatement register
          // and smuggles extra claims past the checkpoint read.
          if (block.text.length > 280 || /[.!?]\s+[A-Z(\\]/.test(block.text)) {
            problems.push({
              gate: "slides-informal-headline",
              detail: `${where}: @informal ${block.objId} headline must be ONE short sentence (got ${block.text.length} chars)`,
              objId: block.objId,
            });
          }
          if (!block.text) {
            problems.push({
              gate: "slides-empty-informal",
              detail: `${where}: @informal ${block.objId} has an empty headline`,
              objId: block.objId,
            });
          }
        }
      }
    }
  }
  for (const b of formalBlocks) {
    if (b.kind !== "theorem" || referenced.has(b.obj_id)) continue;
    // Variant subsumption: a restricted/predecessor theorem whose EXTENSION is on a
    // slide (a covered obj_id of the form `<this>-<suffix>`, e.g. `…-all-d`) needs no
    // slide of its own. The reverse is never waived — the strongest form must appear.
    const subsumed = [...referenced].some((r) => r.startsWith(`${b.obj_id}-`));
    if (subsumed) continue;
    problems.push({
      gate: "slides-missing-theorem",
      detail: `theorem "${b.obj_id}" appears on no slide — cover every main theorem via @formal or @informal`,
      objId: b.obj_id,
    });
  }
  if (figures > 3) {
    problems.push({
      gate: "slides-figure-count",
      detail: `deck declares ${figures} figures; at most 3 — schematics must earn their slide`,
    });
  }
  if (doc.slides.length < 8 || doc.slides.length > 18) {
    problems.push({
      gate: "slides-deck-shape",
      detail: `deck has ${doc.slides.length} slides; a 15–20 minute talk needs 8–18`,
    });
  }
  problems.push(...lintNegativeContributionFraming(proseAll));
  return problems;
}
