import { describe, expect, it } from "vitest";
import { parseCausalSmithCommand } from "../bin/causalsmith.js";

describe("causalsmith umbrella CLI", () => {
  it.each(["research", "present", "study"] as const)("routes %s", (mode) => {
    expect(parseCausalSmithCommand([mode, "target"]))
      .toEqual({ mode, args: ["target"] });
  });

  it("rejects a missing or unknown mode", () => {
    expect(() => parseCausalSmithCommand([])).toThrow(/research\|present\|study/);
    expect(() => parseCausalSmithCommand(["causalsmith"])).toThrow(/research\|present\|study/);
  });
});
