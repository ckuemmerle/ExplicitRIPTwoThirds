/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.LDLResidual

/-!
# The nonzero pivots of exact LDLᵀ elimination

Source: [KM, proof of Theorem 1, footnote 4].
-/

@[expose] public section

open scoped Matrix

/-- The indices `k`, in increasing order, whose pivot `d_k = (ldlResidual G k)(k, k)` is
nonzero. Zero pivots are omitted, corresponding to deletion of their zero rows in
[KM, footnote 4]. For positive semidefinite `G`, these pivots are positive and their number
is `rank G`; see `ExplicitRIP.ldl_factorization`. -/
def ExplicitRIP.ldlPivots {v : ℕ} (G : Matrix (Fin v) (Fin v) ℚ) : List (Fin v) :=
  (List.finRange v).filter fun k => ExplicitRIP.ldlResidual G k k k ≠ 0
