import { describe, it, expect, vi, afterEach } from "vitest";
import { solvedStatus } from "../../src/discovery/core/status.js";

afterEach(() => vi.restoreAllMocks());

describe("solvedStatus", () => {
  it("preserves cited — an imported result is not something this paper proved", () => {
    expect(solvedStatus({ status: "cited", proof_tex: "P" })).toBe("cited");
  });

  it("marks a to-prove node with a real proof as proved", () => {
    expect(solvedStatus({ status: "to-prove", proof_tex: "P" })).toBe("proved");
  });

  it("preserves cited even with an empty proof, without warning", () => {
    const warn = vi.spyOn(console, "warn").mockImplementation(() => {});
    expect(solvedStatus({ status: "cited", proof_tex: "" })).toBe("cited");
    expect(warn).not.toHaveBeenCalled();
  });

  it("WARNS when asked to mark a node proved over an empty proof", () => {
    // Behaviour is preserved rather than changed, but an unearned `proved` reaching a
    // rendered paper must not do so silently.
    const warn = vi.spyOn(console, "warn").mockImplementation(() => {});
    expect(solvedStatus({ id: "lem:hollow", status: "to-prove", proof_tex: "   " })).toBe("proved");
    expect(warn).toHaveBeenCalledTimes(1);
    expect(warn.mock.calls[0][0]).toContain("lem:hollow");
    expect(warn.mock.calls[0][0]).toMatch(/EMPTY proof/);
  });

  it("stays silent when the proof field is absent rather than empty", () => {
    // Callers that pass only a status are not making a claim about the proof body.
    const warn = vi.spyOn(console, "warn").mockImplementation(() => {});
    expect(solvedStatus({ status: "to-prove" })).toBe("proved");
    expect(warn).not.toHaveBeenCalled();
  });
});
