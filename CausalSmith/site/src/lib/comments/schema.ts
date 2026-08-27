/**
 * Shared vocabulary for paper-page comments.
 *
 * Comments are stored by the worker as structured JSON, one record per (paper,
 * author) — see `comments-worker/README.md`. Nothing needs serializing on the
 * client, so all that survives here is the tag vocabulary the composer, the
 * renderer, and the worker have to agree on.
 *
 * This file used to define a metadata header embedded in a GitHub Discussion
 * comment's markdown body, back when a Discussion was the storage. That format
 * is gone along with the storage; a comment is now a record, not a document.
 */

/** 💬 plain, ✅ the reader checked this, ⚠️ the reader thinks it is wrong. */
export type CommentTag = "none" | "verified" | "problem";
