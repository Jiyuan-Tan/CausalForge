import { describe, it, expect, beforeEach, afterEach } from "vitest";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { loadRerankerMeta, rerankerAvailable } from "../src/formalization/reranker_tier.js";

let root: string;
beforeEach(() => {
  root = fs.mkdtempSync(path.join(os.tmpdir(), "rrmeta_"));
  fs.mkdirSync(path.join(root, "doc"), { recursive: true });
});
afterEach(() => fs.rmSync(root, { recursive: true, force: true }));

const writeMeta = (o: unknown) =>
  fs.writeFileSync(path.join(root, "doc", "retrieval_reranker.meta.json"), JSON.stringify(o));

describe("loadRerankerMeta", () => {
  it("returns null when the sidecar is absent", () => {
    expect(loadRerankerMeta(root)).toBeNull();
  });

  it("parses model/base/passage/pool, defaulting passage+pool", () => {
    writeMeta({ model: "doc/retrieval_reranker_ft", base: "BAAI/bge-reranker-base" });
    const m = loadRerankerMeta(root)!;
    expect(m.model).toBe("doc/retrieval_reranker_ft");
    expect(m.passage).toBe("nbr");
    expect(m.pool).toBe(50);
  });

  it("returns null when model is missing (an unusable sidecar)", () => {
    writeMeta({ base: "x", passage: "nbr" });
    expect(loadRerankerMeta(root)).toBeNull();
  });
});

describe("rerankerAvailable", () => {
  it("is false without a meta", () => {
    expect(rerankerAvailable(root)).toBe(false);
  });

  it("is false when the meta points at a missing model directory", () => {
    writeMeta({ model: "doc/retrieval_reranker_ft" });
    expect(rerankerAvailable(root)).toBe(false);
  });

  it("is true when both the meta and the model dir exist", () => {
    fs.mkdirSync(path.join(root, "doc", "retrieval_reranker_ft"));
    writeMeta({ model: "doc/retrieval_reranker_ft" });
    expect(rerankerAvailable(root)).toBe(true);
  });
});
