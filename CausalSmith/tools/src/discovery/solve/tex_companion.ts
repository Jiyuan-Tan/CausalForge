// Phase 3 of the 2026-07-30 migration: TeX-out-of-JSON at the D0 solve boundary.
//
// Model-authored LaTeX inside JSON strings kept producing escaping corruption
// (under-escaped `\theta` → control chars; whole-string over-escapes; math-mode
// breaks), and every defense was a heuristic dictionary that grew per incident.
// The proof-archive channel (`proof_archive/objects/<sha>.tex`) has NEVER had an
// escaping incident — raw file bytes are never JSON-decoded. This module extends
// that pattern to solver output: the solver writes ONE companion file next to
// its JSON (`solve_<unit>.json` → `solve_<unit>.tex`) containing raw TeX blocks
// delimited by `%%% FIELD <local-ref>` header lines, and the JSON carries
// `{"tex_ref": "<local-ref>"}` in place of the inline string. Ingest slices the
// companion, resolves every ref to its raw bytes (fail-loud on missing or
// duplicate refs), and content-addresses each block into the proof archive.
// From the stores inward the pipeline handles resolved strings exactly as
// today — this migration is about the MODEL boundary, where the corruption
// happens, not the internal stores. Inline strings remain valid indefinitely;
// the normalizer/seal-guard stay as the backstop for them.
//
// Block grammar: a header line matching /^%%% FIELD <ref>$/ starts a block; the
// block's content is every byte after the header line's newline up to (not
// including) the newline that precedes the next header (or EOF). That single
// separating newline is the DELIMITER, not content — so any TeX byte sequence,
// including ones containing lines that merely resemble headers mid-line,
// round-trips byte-identically as long as the solver terminates each block with
// a newline.

import path from "node:path";

/** Directory holding every solve companion, one level under the discovery dir —
 *  keeps raw TeX out of the qid folder's top level. */
export const COMPANION_DIR = "solve_tex";

/** `solve_<unit>.json` → its companion `solve_tex/solve_<unit>.tex`. */
export function companionPathFor(outPath: string): string {
  const dir = path.dirname(outPath);
  const base = path.basename(outPath).replace(/\.json$/, "");
  return path.join(dir, COMPANION_DIR, `${base}.tex`);
}

const HEADER = /^%%% FIELD[ \t]+(\S+)[ \t]*$/;

/** Slice a companion file into `<local-ref> → raw TeX bytes`. Duplicate refs and
 *  content before the first header fail loud — a silently mis-sliced companion
 *  would attach the wrong mathematics to a field.
 *
 *  Whitespace normalization (the ONLY bytes not preserved, all deliberate and
 *  all TeX-equivalent — they exist to make the downstream JSON-channel repair
 *  heuristics provably unable to fire on companion content, which never passed
 *  through JSON decoding and therefore must never be "repaired"):
 *  - CRLF line endings are accepted and normalized to LF (audit P23F3 — a
 *    Windows worker's companion must not fail ingestion wholesale);
 *  - horizontal tabs become two spaces (audit P23F4 — defuses the
 *    tab-before-letter → `\t…` heuristic);
 *  - a content line starting with the bare sequences `e`/`otin` (then
 *    whitespace, `\`, or `}`/`]`/`,`) gains one leading space (audit R3P23F1 —
 *    defuses the newline-before-`e`/`otin` → `\ne`/`\notin` heuristic; TeX
 *    ignores leading whitespace on a line, so the mathematics is unchanged).
 *
 *  ACCEPTED LIMITATION (audit R4P23F1, minor): the defusal space is
 *  context-blind, and inside a whitespace-PRESERVING environment (`verbatim`)
 *  a leading space is rendered. A D0 proof carrying a verbatim block whose
 *  line starts with a bare `e `/`otin ` trigger would gain one cosmetic space
 *  there; context-aware TeX parsing in the slicer is not worth that case. */
export function sliceTexCompanion(text: string, source: string): Map<string, string> {
  const blocks = new Map<string, string>();
  const NEWLINE_HEURISTIC_TRIGGER = /^(?:e|otin)(?:\\|\s|[}\],]|$)/;
  const lines = text
    .replace(/\t/g, "  ")
    .replace(/\r\n?/g, "\n")
    .split("\n")
    .map((line) => (NEWLINE_HEURISTIC_TRIGGER.test(line) ? ` ${line}` : line));
  let ref: string | null = null;
  let buf: string[] = [];
  const flush = (): void => {
    if (ref === null) return;
    if (blocks.has(ref)) {
      throw new Error(`TeX companion ${source}: duplicate block ref '${ref}' — refusing an ambiguous slice`);
    }
    // The newline terminating the block is the delimiter, not content: a block
    // ending at EOF leaves one trailing "" element (from the final "\n"), which
    // the pre-header case does not (split consumed that newline with the header
    // line). Strip exactly one so both cases mean "content, then terminator".
    if (buf.length > 0 && buf[buf.length - 1] === "") buf.pop();
    blocks.set(ref, buf.join("\n"));
  };
  for (const line of lines) {
    const m = HEADER.exec(line);
    if (m) {
      flush();
      ref = m[1];
      buf = [];
      continue;
    }
    if (ref === null) {
      if (line.trim().length > 0) {
        throw new Error(`TeX companion ${source}: content before the first '%%% FIELD <ref>' header`);
      }
      continue;
    }
    buf.push(line);
  }
  flush();
  return blocks;
}

/** Is a parsed-JSON value a companion reference (`{"tex_ref": "<ref>"}`)? */
export function isTexRef(value: unknown): value is { tex_ref: string } {
  return (
    value !== null &&
    typeof value === "object" &&
    !Array.isArray(value) &&
    Object.keys(value).length === 1 &&
    typeof (value as { tex_ref?: unknown }).tex_ref === "string"
  );
}

/** Resolve every `{"tex_ref": ...}` in a parsed solve payload to its raw block
 *  bytes, in place. A ref with no block fails loud — including the case where
 *  the JSON carries refs but no companion file exists at all (the caller passes
 *  an empty map then). Returns the refs used, so the caller can archive the
 *  blocks and report unused ones. */
export function resolveTexRefs(
  body: unknown,
  blocks: Map<string, string>,
  source: string,
): Set<string> {
  const used = new Set<string>();
  const resolve = (ref: string): string => {
    const block = blocks.get(ref);
    if (block === undefined) {
      throw new Error(
        `solve output references tex_ref '${ref}' but the companion ${source} has no such block` +
          (blocks.size === 0 ? " (no companion file / empty companion)" : ""),
      );
    }
    used.add(ref);
    return block;
  };
  const walk = (node: unknown): void => {
    if (Array.isArray(node)) {
      node.forEach((item, i) => {
        if (isTexRef(item)) node[i] = resolve(item.tex_ref);
        else walk(item);
      });
      return;
    }
    if (node !== null && typeof node === "object") {
      for (const [key, value] of Object.entries(node as Record<string, unknown>)) {
        if (isTexRef(value)) (node as Record<string, unknown>)[key] = resolve(value.tex_ref);
        else walk(value);
      }
    }
  };
  walk(body);
  return used;
}
