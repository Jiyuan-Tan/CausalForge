/**
 * Wire format for paper-page comments stored in GitHub Discussions.
 *
 * One Discussion per paper (title = paper id, in a dedicated category); each
 * margin comment is a Discussion comment whose body opens with an invisible
 * HTML-comment metadata header followed by the human-readable markdown text.
 * On github.com the header does not render, so the thread stays readable
 * there; the paper page parses it to place, tag, and lifecycle the comment.
 *
 * Bodies without a header (someone commenting directly on GitHub) are still
 * valid: they parse as untagged, unanchored comments and render at page level.
 */

import type { Anchor } from "./anchor.js";

export const SCHEMA_MARKER = "causalsmith:comment";
export const SCHEMA_VERSION = 1;

export type CommentTag = "none" | "verified" | "problem";

export interface CommentMeta {
  v: number;
  paper: string;
  tag: CommentTag;
  /** Absent for page-level comments (including plain GitHub replies). */
  anchor?: Anchor;
  /** Paper bundle commit shown at post time — display only ("on the version
   * of …"); re-anchoring is content-based and never keys on this. */
  revision?: string;
}

export interface PaperComment {
  meta: CommentMeta;
  /** The human-readable markdown the commenter wrote. */
  text: string;
}

const HEADER_RE = new RegExp(
  // <!-- causalsmith:comment v1\n{...}\n-->
  `^<!--\\s*${SCHEMA_MARKER}\\s+v(\\d+)\\n([\\s\\S]*?)\\n-->\\s*\\n?`,
);

export function serializeComment(c: PaperComment): string {
  const meta: CommentMeta = { ...c.meta, v: SCHEMA_VERSION };
  return `<!-- ${SCHEMA_MARKER} v${SCHEMA_VERSION}\n${JSON.stringify(meta)}\n-->\n\n${c.text.trim()}\n`;
}

function isValidTag(t: unknown): t is CommentTag {
  return t === "none" || t === "verified" || t === "problem";
}

function isValidAnchor(a: unknown): a is Anchor {
  if (typeof a !== "object" || a === null) return false;
  const x = a as Record<string, unknown>;
  return (
    typeof x.exact === "string" &&
    x.exact.length > 0 &&
    typeof x.prefix === "string" &&
    typeof x.suffix === "string" &&
    typeof x.count === "number" &&
    Number.isInteger(x.count) &&
    x.count >= 1
  );
}

/**
 * Parse a Discussion comment body. Never throws: a missing or malformed
 * header degrades to an untagged page-level comment carrying the whole body
 * as text, so hand-written GitHub replies always render.
 */
export function parseComment(body: string, paper: string): PaperComment {
  const fallback: PaperComment = {
    meta: { v: SCHEMA_VERSION, paper, tag: "none" },
    text: body.trim(),
  };
  const m = body.match(HEADER_RE);
  if (!m) return fallback;
  let raw: unknown;
  try {
    raw = JSON.parse(m[2]);
  } catch {
    return fallback;
  }
  if (typeof raw !== "object" || raw === null) return fallback;
  const j = raw as Record<string, unknown>;
  if (!isValidTag(j.tag)) return fallback;
  const meta: CommentMeta = { v: Number(m[1]), paper, tag: j.tag };
  if (isValidAnchor(j.anchor)) meta.anchor = j.anchor;
  if (typeof j.revision === "string" && j.revision) meta.revision = j.revision;
  return { meta, text: body.slice(m[0].length).trim() };
}
