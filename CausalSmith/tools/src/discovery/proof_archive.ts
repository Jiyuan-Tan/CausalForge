// Cold, append-only archive for D0 proof bytes.
//
// D0 proofs are expensive artifacts, and several legitimate operations displace them
// from hot state: a re-solve overwrites a record, an OEQ resolution deletes its source
// record, a proposal-revision reset rebuilds the cursor, `clearRoundOutputs` deletes the
// round's raw solve payloads. The invariant this module supports:
//
//   Never silently lose proof bytes — but never let historical proofs re-enter solver
//   context automatically.
//
// So: archiving is a SIDE EFFECT of displacement (callers copy bytes here at the moment
// they would otherwise vanish), never a disposition decision, and nothing in ordinary
// D0 context assembly reads this directory. Restoring an archived proof is an explicit
// orchestrator act: read `index.jsonl`, pick a hash, read `objects/<hash>.tex`. There is
// deliberately no restore command — the archive is plain files.
//
// Layout, under `<discoveryDir>/proof_archive/`:
//   objects/<sha256>.tex   — proof bodies, content-addressed and deduplicated
//   index.jsonl            — one metadata line per archived (node, bytes) pair

import { createHash } from "node:crypto";
import { existsSync } from "node:fs";
import { appendFile, mkdir, readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { normalizeRawModelJson, repairLatexStringsDeep } from "./core/latex_serialization.js";

export interface ProofArchiveEntry {
  /** sha256 (hex) of the proof bytes; names the body file under objects/. */
  hash: string;
  node_id: string;
  /** Why the bytes left hot state, e.g. "displaced/round-3", "round-cleared". */
  reason: string;
  chars: number;
  archived_at: string;
  /** The proof's validity basis at archive time (statement/defs/assumptions), when the
   *  caller had one. What a future restore must be checked against. */
  snapshot?: unknown;
}

export interface ProofToArchive {
  nodeId: string;
  proofTex: string;
  reason: string;
  snapshot?: unknown;
}

export function proofArchiveDir(discoveryDir: string): string {
  return path.join(discoveryDir, "proof_archive");
}
function indexPath(discoveryDir: string): string {
  return path.join(proofArchiveDir(discoveryDir), "index.jsonl");
}

export async function readProofArchiveIndex(discoveryDir: string): Promise<ProofArchiveEntry[]> {
  const p = indexPath(discoveryDir);
  if (!existsSync(p)) return [];
  const entries: ProofArchiveEntry[] = [];
  const text = await readFile(p, "utf8");
  text.split("\n").forEach((line, i) => {
    if (line.trim().length === 0) return;
    try {
      const entry = JSON.parse(line) as ProofArchiveEntry;
      // Legacy index rows can carry decoded control-escape corruption from
      // before the escape defense; repair on read so proof reuse gets the
      // intended TeX (corpus-verified: tab+"exttt" snapshots in live archives).
      repairLatexStringsDeep(entry);
      entries.push(entry);
    } catch (err) {
      // A torn index row loses only METADATA — the body object is still on disk — but
      // silently skipping it would make dedup re-archive and the row's provenance vanish.
      throw new Error(
        `proof archive index is corrupt at ${p}:${i + 1}: ` +
          `${err instanceof Error ? err.message : String(err)}. ` +
          `The body objects are unaffected; repair or delete the torn line.`,
      );
    }
  });
  return entries;
}

/** Proof bytes a raw round file (a `solve_*.json` unit output or a legacy
 *  `proposed_proofs.json`) can hold. Withheld payloads (collisions, unmatched ids,
 *  duplicate re-proofs) exist ONLY in these files, so whoever deletes or overwrites one
 *  must archive these first. Tolerant of shape drift on purpose: it walks the fields it
 *  knows and ignores the rest. A torn file is returned wholesale (reason suffixed
 *  `-unparsed`) — it still holds paid-for bytes. */
export function proofBytesInRoundFile(fileName: string, raw: string, reason = "round-cleared"): ProofToArchive[] {
  let parsed: unknown;
  try {
    // Round files are agent-raw (solve units) or pre-defense legacy: normalize
    // under-escaped TeX before parse and repair decoded control escapes after,
    // so paid-for proofs archive per-node instead of as one `-unparsed` blob.
    parsed = JSON.parse(normalizeRawModelJson(raw));
    repairLatexStringsDeep(parsed);
  } catch {
    return [{ nodeId: `file:${fileName}`, proofTex: raw, reason: `${reason}-unparsed` }];
  }
  const out: ProofToArchive[] = [];
  const push = (nodeId: unknown, proofTex: unknown): void => {
    if (typeof nodeId === "string" && typeof proofTex === "string" && proofTex.trim().length > 0) {
      out.push({ nodeId, proofTex, reason });
    }
  };
  // legacy proposed_proofs.json: a bare array of {id, proof_tex}
  const o = (Array.isArray(parsed) ? { proofs: parsed } : parsed) as Record<string, unknown>;
  if (o === null || typeof o !== "object") return out;
  for (const p of Array.isArray(o.proofs) ? o.proofs : []) push((p as { id?: unknown })?.id, (p as { proof_tex?: unknown })?.proof_tex);
  for (const l of Array.isArray(o.added_lemmas) ? o.added_lemmas : []) push((l as { id?: unknown })?.id, (l as { proof_tex?: unknown })?.proof_tex);
  for (const r of Array.isArray(o.resolved_oeqs) ? o.resolved_oeqs : []) {
    const theorem = (r as { theorem?: { id?: unknown; proof_tex?: unknown } })?.theorem;
    push(theorem?.id, theorem?.proof_tex);
  }
  for (const ob of Array.isArray(o.open_obligations) ? o.open_obligations : []) {
    push((ob as { node_id?: unknown })?.node_id, (ob as { partial_result?: unknown })?.partial_result);
  }
  return out;
}

// Appends are serialized in-process: parallel solve units may sweep stale outputs
// concurrently, and an unserialized read-index/append-index pair would defeat dedup
// and write duplicate metadata rows. (Cross-process races are out of scope — different
// qids use different run directories and the orchestrator is single-threaded.)
let archiveQueue: Promise<unknown> = Promise.resolve();

/** Append proof bytes to the archive. Deduplicates on (node, bytes) — the FIRST record
 *  for a byte-identical (node, proof) pair wins; a later same-byte displacement is
 *  suppressed (the bytes are already durably recoverable; only its reason/snapshot row
 *  is not repeated). Empty bodies are skipped (no bytes to preserve). Returns the
 *  entries actually written. */
export function archiveProofs(
  discoveryDir: string,
  proofs: ProofToArchive[],
): Promise<ProofArchiveEntry[]> {
  const run = archiveQueue.then(() => archiveProofsSerial(discoveryDir, proofs));
  archiveQueue = run.catch(() => undefined);
  return run;
}

async function archiveProofsSerial(
  discoveryDir: string,
  proofs: ProofToArchive[],
): Promise<ProofArchiveEntry[]> {
  const candidates = proofs.filter((p) => p.proofTex.trim().length > 0);
  if (candidates.length === 0) return [];

  const seen = new Set(
    (await readProofArchiveIndex(discoveryDir)).map((e) => `${e.hash} ${e.node_id}`),
  );
  const objectsDir = path.join(proofArchiveDir(discoveryDir), "objects");
  const written: ProofArchiveEntry[] = [];
  const lines: string[] = [];
  for (const p of candidates) {
    const hash = createHash("sha256").update(p.proofTex, "utf8").digest("hex");
    const key = `${hash} ${p.nodeId}`;
    if (seen.has(key)) continue;
    seen.add(key);
    if (written.length === 0) await mkdir(objectsDir, { recursive: true });
    const objectPath = path.join(objectsDir, `${hash}.tex`);
    if (!existsSync(objectPath)) await writeFile(objectPath, p.proofTex, "utf8");
    const entry: ProofArchiveEntry = {
      hash,
      node_id: p.nodeId,
      reason: p.reason,
      chars: p.proofTex.length,
      archived_at: new Date().toISOString(),
      ...(p.snapshot !== undefined ? { snapshot: p.snapshot } : {}),
    };
    written.push(entry);
    lines.push(JSON.stringify(entry));
  }
  if (lines.length > 0) await appendFile(indexPath(discoveryDir), lines.join("\n") + "\n", "utf8");
  return written;
}
