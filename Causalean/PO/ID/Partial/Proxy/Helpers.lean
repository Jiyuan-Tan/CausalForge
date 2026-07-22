/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Proximal partial-identification — shared helpers (facade)

Re-exports the helpers used across `WBased.lean`, `ZBased.lean`, and
`TwoProxy.lean`. The actual lemmas live in:

* `Helpers/Common.lean`   — marginalisation identity + Y(a) clamp lemmas
* `Helpers/BridgeW.lean`  — W-only bridge-substitution identity
* `Helpers/BridgeWZ.lean` — two-proxy bridge-substitution identity
* `Helpers/CondExpQ.lean` — q-collapse on the on-arm σ_AX (TwoProxy)
-/

import Causalean.PO.ID.Partial.Proxy.Helpers.Common
import Causalean.PO.ID.Partial.Proxy.Helpers.BridgeW
import Causalean.PO.ID.Partial.Proxy.Helpers.BridgeWZ
import Causalean.PO.ID.Partial.Proxy.Helpers.CondExpQ

/-!
This file gathers the shared algebra and conditioning facts used by proximal
partial-identification bounds, covering marginalization, bridge substitution,
and proxy-collapse arguments. It re-exports the common marginalization and
clamp lemmas, the W-only bridge identity `condIntYofA_eq_h_arm`, the two-proxy
bridge identity `condIntYofA_eq_hq_armSwap_twoProxy`, and the treatment-bridge
collapse `condExp_q_eq_stratumOddsRatio_arm_AX`.
-/
