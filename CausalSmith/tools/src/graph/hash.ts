import { createHash } from "node:crypto";

/** sha1 of a statement with runs of whitespace collapsed, so reformatting
 *  (indent / line-wrap changes) does not register as a content change. */
export function statementHash(statement: string): string {
  const normalized = statement.replace(/\s+/g, " ").trim();
  return createHash("sha1").update(normalized).digest("hex");
}
