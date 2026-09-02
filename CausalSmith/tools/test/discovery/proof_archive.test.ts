// The cold proof archive: append-only, content-addressed, never read by dispatch.
//
// Contract under test: every byte handed to `archiveProofs` is durably recoverable
// (objects/<hash>.tex + index.jsonl), identical (node, bytes) pairs are stored once,
// and empty bodies are not archived (there are no bytes to preserve).

import { describe, it, expect } from "vitest";
import { mkdtemp, mkdir, readFile, rm, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import { createHash } from "node:crypto";
import os from "node:os";
import path from "node:path";
import {
  archiveProofs,
  proofArchiveDir,
  proofBytesInRoundFile,
  readProofArchiveIndex,
} from "../../src/discovery/proof_archive.js";

async function tmpDiscoveryDir(): Promise<string> {
  return mkdtemp(path.join(os.tmpdir(), "proof-archive-"));
}

describe("proof archive", () => {
  it("stores bytes content-addressed and records index metadata", async () => {
    const dir = await tmpDiscoveryDir();
    try {
      const written = await archiveProofs(dir, [
        { nodeId: "thm:main", proofTex: "A long canonical argument.", reason: "displaced/round-3" },
      ]);
      expect(written).toHaveLength(1);

      const index = await readProofArchiveIndex(dir);
      expect(index).toHaveLength(1);
      expect(index[0].node_id).toBe("thm:main");
      expect(index[0].reason).toBe("displaced/round-3");
      expect(index[0].chars).toBe("A long canonical argument.".length);

      const body = await readFile(
        path.join(proofArchiveDir(dir), "objects", `${index[0].hash}.tex`),
        "utf8",
      );
      expect(body).toBe("A long canonical argument.");
    } finally { await rm(dir, { recursive: true, force: true }); }
  });

  it("dedupes identical (node, bytes) pairs across calls", async () => {
    const dir = await tmpDiscoveryDir();
    try {
      await archiveProofs(dir, [{ nodeId: "lem:x", proofTex: "P.", reason: "displaced/round-1" }]);
      const second = await archiveProofs(dir, [
        { nodeId: "lem:x", proofTex: "P.", reason: "round-cleared" }, // same bytes → skip
        { nodeId: "lem:y", proofTex: "P.", reason: "round-cleared" }, // same bytes, other node → keep
      ]);
      expect(second).toHaveLength(1);
      const index = await readProofArchiveIndex(dir);
      expect(index.map((e) => e.node_id).sort()).toEqual(["lem:x", "lem:y"]);
    } finally { await rm(dir, { recursive: true, force: true }); }
  });

  it("rejects a corrupt pre-existing hash object instead of indexing its pathname", async () => {
    const dir = await tmpDiscoveryDir();
    try {
      const proofTex = "The intended complete proof.";
      const hash = createHash("sha256").update(proofTex, "utf8").digest("hex");
      const objects = path.join(proofArchiveDir(dir), "objects");
      await mkdir(objects, { recursive: true });
      await writeFile(path.join(objects, `${hash}.tex`), "torn", "utf8");

      await expect(archiveProofs(dir, [
        { nodeId: "lem:x", proofTex, reason: "round-cleared" },
      ])).rejects.toThrow(/archive object is corrupt/);
      expect(existsSync(path.join(proofArchiveDir(dir), "index.jsonl"))).toBe(false);
    } finally { await rm(dir, { recursive: true, force: true }); }
  });

  it("repairs a missing object before an existing index row may dedupe hot bytes", async () => {
    const dir = await tmpDiscoveryDir();
    try {
      const proof = { nodeId: "lem:x", proofTex: "Recoverable hot proof.", reason: "round-cleared" };
      const [entry] = await archiveProofs(dir, [proof]);
      const objectPath = path.join(proofArchiveDir(dir), "objects", `${entry.hash}.tex`);
      await rm(objectPath, { force: true });

      expect(await archiveProofs(dir, [proof])).toHaveLength(0);
      expect(await readFile(objectPath, "utf8")).toBe(proof.proofTex);
    } finally { await rm(dir, { recursive: true, force: true }); }
  });

  it("rejects a corrupt object even when an existing index row would dedupe it", async () => {
    const dir = await tmpDiscoveryDir();
    try {
      const proof = { nodeId: "lem:x", proofTex: "Recoverable hot proof.", reason: "round-cleared" };
      const [entry] = await archiveProofs(dir, [proof]);
      const objectPath = path.join(proofArchiveDir(dir), "objects", `${entry.hash}.tex`);
      await writeFile(objectPath, "torn", "utf8");

      await expect(archiveProofs(dir, [proof])).rejects.toThrow(/archive object is corrupt/);
    } finally { await rm(dir, { recursive: true, force: true }); }
  });

  it("proofBytesInRoundFile parses an under-escaped TeX round file per-node instead of blob-fallback", () => {
    // `\alpha`/`\forall` are invalid JSON escapes: bare JSON.parse throws, and the
    // old code archived the whole file as one `-unparsed` blob, losing per-node
    // recoverability for paid-for proofs.
    const raw = String.raw`[{"id":"thm:a","proof_tex":"\alpha \forall x bound"}]`;
    const got = proofBytesInRoundFile("solve_test.json", raw, "round-cleared");
    expect(got).toEqual([
      { nodeId: "thm:a", proofTex: String.raw`\alpha \forall x bound`, reason: "round-cleared" },
    ]);
  });

  it("skips empty and whitespace-only bodies", async () => {
    const dir = await tmpDiscoveryDir();
    try {
      const written = await archiveProofs(dir, [
        { nodeId: "thm:a", proofTex: "", reason: "dropped/round-2" },
        { nodeId: "thm:b", proofTex: "   \n", reason: "dropped/round-2" },
      ]);
      expect(written).toHaveLength(0);
      expect(existsSync(proofArchiveDir(dir))).toBe(false);
    } finally { await rm(dir, { recursive: true, force: true }); }
  });
});
