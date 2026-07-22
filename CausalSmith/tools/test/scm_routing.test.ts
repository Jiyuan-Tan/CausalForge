import { describe, it, expect } from "vitest";
import { clusterFor } from "../src/discovery/cluster_setup.js";
import { substrateForQid, canonicalLeanSubdir, formalizationKind } from "../src/paths.js";
import { clusterFromLeanSubdir } from "../src/pipeline_support.js";

// Regression guard for the scm cluster wiring (docs/superpowers/plans/2026-07-03-scm-cluster.md, Task B7).
describe("scm cluster routing", () => {
  const ctx = { qid: "scm_smoke_test" } as any;

  it("routes scm_ qid to the scm cluster via prefix (empty state)", () => {
    expect(clusterFor(ctx, {} as any)).toBe("scm");
  });

  it("honors an explicit proposed_from.cluster === scm", () => {
    expect(clusterFor({ qid: "anything" } as any, { proposed_from: { cluster: "scm" } } as any)).toBe("scm");
  });

  it("maps scm_ qid to the SCM substrate dir", () => {
    expect(substrateForQid("scm_smoke_test")).toBe("SCM");
    expect(canonicalLeanSubdir("scm_smoke_test").startsWith("CausalSmith/SCM/")).toBe(true);
  });

  it("classifies cluster-prefixed qids as research; the retired q_ grammar is not research", () => {
    expect(formalizationKind("panel_event_study_weights")).toBe("research");
    expect(formalizationKind("stat_ate_overlap_decay")).toBe("research");
    // The q_ / q<digit>_ panel-question grammar is retired (superseded by panel_*):
    // such ids no longer carry a research prefix and fall through to study.
    expect(formalizationKind("q1_minimal_basis")).toBe("study");
    expect(formalizationKind("q_freeform_panel")).toBe("study");
  });

  it("reverse-maps a CausalSmith/SCM/... lean subdir back to scm", () => {
    expect(clusterFromLeanSubdir("CausalSmith/SCM/Foo")).toBe("scm");
  });
});
