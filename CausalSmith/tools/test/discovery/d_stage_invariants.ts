// Test-side wrapper over the RUNTIME invariant checks.
//
// The detection logic lives in `src/discovery/core/coherence.ts` (warn tier) and runs inside
// `commitRound` on every real round. This file only adapts it to vitest, so a soak
// scenario and a live run can never disagree about what "broken" means — a second copy
// of these rules would be the same two-copies-that-drift pattern behind several of the
// faults they exist to catch.

import { expect } from "vitest";
import {
  checkRoundInvariants,
  formatRoundViolation,
  type RoundViolation,
  type RoundInvariantInput,
} from "../../src/discovery/core/coherence.js";

/** Violations of one specific invariant, for a focused assertion. */
export function violationsOf(input: RoundInvariantInput, code: RoundViolation["code"]): RoundViolation[] {
  return checkRoundInvariants(input).filter((v) => v.code === code);
}

/** Assert one invariant holds, reporting the offending ids on failure. */
export function assertInvariant(
  input: RoundInvariantInput,
  code: RoundViolation["code"],
  where: string,
): void {
  const found = violationsOf(input, code);
  expect(found.map(formatRoundViolation), `${where}: ${code}`).toEqual([]);
}

/** Assert a round left NO invariant violated — the check a soak scenario runs after every round. */
export function assertRoundInvariants(input: RoundInvariantInput, where: string): void {
  const found = checkRoundInvariants(input);
  expect(found.map(formatRoundViolation), `${where}: round invariants violated`).toEqual([]);
}
