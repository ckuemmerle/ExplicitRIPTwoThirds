/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.RIPConstant
import ExplicitRIP.Provider.RIPConstantCharacterization

/-!
# The equivalent definitions of the restricted isometry constant

Source: [KM, Section 1, the definition of δ_k before (1)].
-/

public section

open scoped Matrix

/-- The restricted isometry constant `δ_k(Φ)`, defined by the principal-Gram norm formula, is
the smallest `δ ≥ 0` such that `(1 - δ) ‖z‖² ≤ ‖Φ z‖² ≤ (1 + δ) ‖z‖²` whenever
`|supp z| ≤ k`. These are the equivalent definitions before [KM, (1)]. -/
theorem ExplicitRIP.ripConstant_isLeast :
    ∀ {𝕜 : Type} [RCLike 𝕜] {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
      (Φ : Matrix m n 𝕜) (k : ℕ),
      IsLeast {δ : ℝ | 0 ≤ δ ∧ ∀ z : n → 𝕜, (Function.support z).ncard ≤ k →
          (1 - δ) * ∑ j, ‖z j‖ ^ 2 ≤ ∑ i, ‖(Φ *ᵥ z) i‖ ^ 2 ∧
            ∑ i, ‖(Φ *ᵥ z) i‖ ^ 2 ≤ (1 + δ) * ∑ j, ‖z j‖ ^ 2}
        (ExplicitRIP.ripConstant Φ k) :=
by exact ExplicitRIP.Provider.ripConstant_isLeast
