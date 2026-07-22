import { mkdtemp, mkdir, readFile, writeFile, rm } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterAll, beforeAll, describe, expect, it } from "vitest";
import {
  buildProtoCoreReviewBlock,
  neg1ReviewArtifactPath,
  sourceReceiptValidationError,
} from "../../src/discovery/stages/neg0_5.js";
import { protoCoreJsonPath } from "../../src/discovery/stages/neg1_2_author.js";
import type { PipelineContext } from "../../src/types.js";

const QID = "stat_ate_overlap_decay";
const SPEC = "v1";

let repoRoot: string;
let goldenProto: string;

function makeCtx(root: string): PipelineContext {
  return { repoRoot: root, qid: QID, specialization: SPEC, dryRun: false, resume: false };
}

beforeAll(async () => {
  repoRoot = await mkdtemp(path.join(os.tmpdir(), "neg1dualrev-"));
  goldenProto = await readFile(
    new URL("../fixtures/stat_ate_overlap_decay_proto_core.json", import.meta.url),
    "utf8",
  );
});

describe("sourceReceiptValidationError", () => {
  it("rejects a source-dependent flag without a primary-version receipt", () => {
    expect(sourceReceiptValidationError({
      novelty_flags: [{ code: "N-mischar" }],
      soundness_flags: [{ code: "C-assumption-nonstandard" }],
      source_verification_receipts: [],
    })).toMatch(/N-mischar.*C-assumption-nonstandard/);
  });

  it("accepts source-dependent flags when complete receipts cover their codes", () => {
    expect(sourceReceiptValidationError({
      novelty_flags: [{ code: "N-mischar" }],
      soundness_flags: [],
      source_verification_receipts: [{
        bibkey: "Primary2025",
        source_url: "https://example.org/proceedings.pdf",
        version: "conference proceedings",
        locator: "p. 12, Eq. (4)",
        verified_claim: "The lower envelope is (1-rho) mu.",
        supports_flag_codes: ["N-mischar"],
      }],
    })).toBeNull();
  });
});

afterAll(async () => {
  await rm(repoRoot, { recursive: true, force: true });
});

describe("buildProtoCoreReviewBlock (D-0.5 single-artifact: inline the core)", () => {
  it("returns '' when no proto_core exists (legacy monolithic .tex path is untouched)", async () => {
    const ctx = makeCtx(repoRoot);
    expect(await buildProtoCoreReviewBlock(ctx)).toBe("");
  });

  it("inlines the proposal core once it exists (no adapter — the core rubric is self-contained)", async () => {
    const ctx = makeCtx(repoRoot);
    const cp = protoCoreJsonPath(ctx);
    await mkdir(path.dirname(cp), { recursive: true });
    await writeFile(cp, goldenProto, "utf8");

    const block = await buildProtoCoreReviewBlock(ctx);
    expect(block).toContain("PROPOSAL CORE"); // the core is inlined under its header
    expect(block).toContain("ass:tail"); // a real assumption node id
    expect(block).toContain("thm:lower"); // a real statement node id
  });

  it("routes every reviewer-facing path to the core once it exists", async () => {
    const ctx = makeCtx(repoRoot);
    const cp = protoCoreJsonPath(ctx);
    const legacyTex = path.join(repoRoot, "stale-proposal.tex");
    await mkdir(path.dirname(cp), { recursive: true });
    await writeFile(cp, goldenProto, "utf8");
    await writeFile(legacyTex, "stale reciprocal-endpoint proposal", "utf8");

    expect(neg1ReviewArtifactPath(ctx, legacyTex)).toBe(cp);
  });

  it("repairs an under-escaped / legacy-corrupted proto core instead of failing or inlining garbage", async () => {
    const ctx = makeCtx(repoRoot);
    const cp = protoCoreJsonPath(ctx);
    await mkdir(path.dirname(cp), { recursive: true });
    // Agent-raw file: `\alpha` is an invalid JSON escape (old code threw the
    // misleading torn-file error) and `\texttt` is a VALID escape that bare
    // JSON.parse silently decodes to tab + "exttt" (the 2026-07-21 incident).
    const corrupted = goldenProto.replace(
      /"tldr":\s*"/,
      String.raw`"tldr": "\alpha rate; \texttt{clipped} estimator -- `,
    );
    expect(corrupted).not.toBe(goldenProto);
    await writeFile(cp, corrupted, "utf8");

    const block = await buildProtoCoreReviewBlock(ctx);
    expect(block).toContain(String.raw`\\alpha`); // canonical JSON spelling of the TeX
    expect(block).toContain(String.raw`\\texttt{clipped}`);
    expect(block).not.toMatch(/\t/); // no decoded control chars reach the reviewer
  });
});
