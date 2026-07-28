import { describe, expect, it } from "vitest";
import { topologicallyOrderSymbols } from "../../src/discovery/core/symbol_order.js";

describe("topologicallyOrderSymbols", () => {
  it("moves appended prerequisites before stable existing consumers", () => {
    const symbols = [
      { name: "base", type: "scalar" },
      { name: "short-M", type: "class", refs: ["indexed-M", "base"] },
      { name: "short-N", type: "scalar", refs: ["indexed-N", "short-M"] },
      { name: "unrelated", type: "scalar" },
      { name: "indexed-M", type: "class", refs: ["base"] },
      { name: "indexed-N", type: "scalar", refs: ["indexed-M"] },
    ];
    const ordered = topologicallyOrderSymbols(symbols);
    expect(ordered.map((symbol) => symbol.name)).toEqual([
      "base", "unrelated", "indexed-M", "short-M", "indexed-N", "short-N",
    ]);
    expect(new Set(ordered)).toEqual(new Set(symbols));
  });

  it("leaves cycles unchanged for the gate to diagnose", () => {
    const cyclic = [
      { name: "a", type: "scalar", refs: ["b"] },
      { name: "b", type: "scalar", refs: ["a"] },
    ];
    expect(topologicallyOrderSymbols(cyclic)).toBe(cyclic);
  });
});
