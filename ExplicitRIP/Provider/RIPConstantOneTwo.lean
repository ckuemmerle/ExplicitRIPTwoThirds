/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.RIPConstant
public import ExplicitRIP.Frozen.Defs.Coherence
import ExplicitRIP.Analysis.RIPOneTwo.Characterization

/-!
# The first two restricted isometry constants

Source: [KM, Section 2.2, the claim about δ₁ and δ₂].

For unit-norm columns, `δ_1 = 0` and `δ_2 = μ`, where `μ` is the coherence.
-/

public section

open scoped Matrix

theorem ExplicitRIP.Provider.ripConstant_one_two :
    ∀ {𝕜 : Type} [RCLike 𝕜] {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
      (Φ : Matrix m n 𝕜), (∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) →
        ExplicitRIP.ripConstant Φ 1 = 0 ∧ ExplicitRIP.ripConstant Φ 2 = ExplicitRIP.coherence Φ :=
by
  intro 𝕜 _ m n _ _ _ Φ hΦ
  exact ExplicitRIP.RIPOneTwo.ripConstant_one_two Φ hΦ
