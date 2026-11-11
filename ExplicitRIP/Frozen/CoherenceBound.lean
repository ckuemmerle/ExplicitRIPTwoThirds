/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.RIPConstant
public import ExplicitRIP.Frozen.Defs.Coherence
import ExplicitRIP.Provider.CoherenceBound

/-!
# [KM, (2)]: the coherence bound

Source: [KM, Section 1, (2)].
-/

public section

open scoped Matrix

/-- If the columns of `Φ` have unit norm and `k ≥ 1`, then `δ_k ≤ (k - 1) μ`, as in [KM, (2)]. -/
theorem ExplicitRIP.ripConstant_le_coherence :
    ∀ {𝕜 : Type} [RCLike 𝕜] {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
      (Φ : Matrix m n 𝕜), (∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) → ∀ k : ℕ, 1 ≤ k →
        ExplicitRIP.ripConstant Φ k ≤ ((k : ℝ) - 1) * ExplicitRIP.coherence Φ :=
by exact ExplicitRIP.Provider.ripConstant_le_coherence
