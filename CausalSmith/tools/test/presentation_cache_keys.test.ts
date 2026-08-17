import { describe, it, expect } from "vitest";
import { equivalenceAuditKey, proofAuditCacheKey, proofAuditSemanticNotation } from "../src/presentation/audit.js";
import { sectionCacheKey, proofRenderCacheKey, frontMatterCacheKey } from "../src/presentation/stages/p2_draft.js";
import { hashEnvBody } from "../src/presentation/tex_anchors.js";
import { PRESENTATION_PROSE_POLICY_VERSION } from "../src/presentation/prompt_io.js";

// BYTE-STABILITY PINS. Every persisted cache on every existing run dir is keyed by
// these formulas; an accidental change to any component order, separator, or version
// token silently colds ALL run-dir caches (P1 alone is ~30 codex audits). A failing
// pin means either an unintended formula change (fix the code) or an INTENTIONAL
// invalidation (update the pinned hex here and say why in the commit).
describe("cache key formulas are byte-stable", () => {
  it("equivalenceAuditKey (equivalence_cache.json)", () => {
    expect(
      equivalenceAuditKey({
        envBody: "BODY", mapping: "F.lean:decl:3", leanStatement: "STMT",
        refDefs: "DEFS", citedDependencies: "CITED",
      }),
    ).toBe("f6741bb319146cf7c9706aede0c027954ab7cbba67d2e06bedccb90d8e84998a");
  });

  it("sectionCacheKey (sections/_cache_keys.json)", () => {
    expect(sectionCacheKey("Intro", ["a", "b"], "brief", "k1, k2", ["e1", "e2"], "rev"))
      .toBe("4ba8e5cf357b8d4555d398488131f309eb953bf7ae96c373a5eb79e437199668");
  });

  it("proofRenderCacheKey (proofs/_cache_keys.json)", () => {
    // Hex updated 2026-08-16: `informalDerivation` added as a render input (the D-stage
    // derivation now reaches the proof prompt) — an INTENTIONAL whole-proof-cache
    // invalidation so existing thin proofs re-render with the derivation as context.
    expect(
      proofRenderCacheKey({
        modelKey: "m", objId: "T-1", envTex: "ENV", leanPath: "/p/F.lean", leanDecl: "d",
        exactDecl: "DECL", helperContext: [{ obj_id: "L-1", tex: "H" }], notation: "N",
        revisionBrief: "R", citedDependencies: "C", informalDerivation: "I",
      }),
    ).toBe("815026c7518308bfe534e8dff916b6f7f57bfb0e6ffac5f01d4f04bc1cf36d15");
  });

  it("frontMatterCacheKey (sections/_cache_keys.json `_front`)", () => {
    expect(frontMatterCacheKey("mk", "body", "fb", "brief", "keys"))
      .toBe("427acaaefb490a8e85a5c8143f715e9593b9fe46a30667d1d1ee93cc2ad3be27");
  });

  // proofAuditCacheKey embeds PRESENTATION_PROSE_POLICY_VERSION, whose bumps are
  // INTENTIONAL whole-cache invalidations — so pin the composition, not raw hex.
  it("proofAuditCacheKey (proof_audit_cache.json) — layout pin", () => {
    const parts = { proofTex: "P", leanPointer: "L", leanProofCacheSource: "S", notationTable: "| a | b | c | d |" };
    expect(proofAuditCacheKey(parts)).toBe(
      hashEnvBody(`${PRESENTATION_PROSE_POLICY_VERSION}|P|L|S|${proofAuditSemanticNotation(parts.notationTable)}`),
    );
  });
});
