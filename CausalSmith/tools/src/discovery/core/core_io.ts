// Canonical read path for core/proto JSON artifacts.
//
// Every reader of a core-shaped artifact must go through the same three-layer
// escape defense: pre-parse raw-byte normalization (repairs under-escaped TeX
// while the bytes still disambiguate), post-parse LaTeX repair (covers control
// characters that arrived pre-encoded as valid `\u00XX` escapes — including
// legacy artifacts persisted before the defense existed), and the decoded
// control-character backstop (fail-loud with the artifact path, never silent
// corruption). Reading through bare `JSON.parse` lets a legacy corrupted field
// flow into live state without repair or a loud failure (audit finding H).
import { readFile } from "node:fs/promises";
import { CoreSchema, type Core } from "./schema.js";
import {
  assertNoDecodedControlChars,
  normalizeRawModelJson,
  repairCoreLatexSerialization,
  repairLatexStringsDeep,
} from "./latex_serialization.js";

/** Read + schema-parse + repair + control-check a core/proto artifact. Throws
 * with the artifact path on unrecoverable corruption. Repairs are in-memory
 * only; persisting the canonical form stays the writer's responsibility. */
/** Schema-free variant of the three-layer defense for model-authored JSON that
 * must keep ALL its keys (raw proto cores with ideation metadata, stdout
 * handoffs, solve round files, legacy proposal arrays). Same layers as
 * `readTypedCore` minus the CoreSchema strip: pre-parse raw-byte normalization,
 * post-parse LaTeX repair, decoded control-character backstop (fail-loud,
 * naming `source`). */
export function parseRepairedModelJson(text: string, source: string): unknown {
  const value = JSON.parse(normalizeRawModelJson(text)) as unknown;
  repairLatexStringsDeep(value);
  assertNoDecodedControlChars(value, source);
  return value;
}

/** `parseRepairedModelJson` over a file, using the path as the failure source. */
export async function readRepairedModelJson(filePath: string): Promise<unknown> {
  return parseRepairedModelJson(await readFile(filePath, "utf8"), filePath);
}

export async function readTypedCore(filePath: string): Promise<Core> {
  const core = CoreSchema.parse(JSON.parse(normalizeRawModelJson(await readFile(filePath, "utf8")))) as Core;
  repairCoreLatexSerialization(core);
  assertNoDecodedControlChars(core, `core artifact ${filePath}`);
  return core;
}
