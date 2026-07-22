/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Proximal partial identification — umbrella

Re-exports all files in `Causalean/PO/ID/Partial/Proxy/`. Formalises
the partial-identification bounds of Ghassami-Shpitser-Tchetgen Tchetgen
(arXiv 2304.04374), Sections 2-3:

* `WBased`   — outcome-confounding-proxy bounds (Theorem 1, Corollary 1).
* `ZBased`   — treatment-confounding-proxy bounds (Theorem 2, Corollary 2).
* `TwoProxy` — two-conditionally-independent-invalid-proxies bounds (Theorem 3).
* `IntervalForm` — `Set.Icc` interval restatements of all five sandwich bounds.
-/

import Causalean.PO.ID.Partial.Proxy.Setup
import Causalean.PO.ID.Partial.Proxy.Assumptions
import Causalean.PO.ID.Partial.Proxy.Helpers
import Causalean.PO.ID.Partial.Proxy.WBased
import Causalean.PO.ID.Partial.Proxy.ZBased
import Causalean.PO.ID.Partial.Proxy.TwoProxy
import Causalean.PO.ID.Partial.Proxy.IntervalForm

/-!
This file is the umbrella module for proximal partial-identification bounds,
bringing together the setup, assumptions, shared helpers, one-proxy bounds,
two-proxy bounds, and interval statements. It re-exports the system setup and
assumption bundles, the helper facade, the W-proxy, Z-proxy, and two-proxy
bound theorems, and the `Set.Icc` interval restatements used by the public
partial-identification API.
-/
