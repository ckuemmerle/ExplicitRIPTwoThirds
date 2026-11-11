/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.RIPConstant
public import ExplicitRIP.Frozen.Defs.Coherence
import ExplicitRIP.Provider.RIPConstantOneTwo

/-!
# The first two restricted isometry constants

Source: [KM, Section 2.2, the claim about δ₁ and δ₂].
-/

public section

open scoped Matrix

/-- Unit-norm columns have restricted isometry constant `δ_1 = 0`, and their coherence equals
`δ_2`, as stated in [KM, Section 2.2]. -/
theorem ExplicitRIP.ripConstant_one_two :
    ∀ {𝕜 : Type} [RCLike 𝕜] {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
      (Φ : Matrix m n 𝕜), (∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) →
        ExplicitRIP.ripConstant Φ 1 = 0 ∧ ExplicitRIP.ripConstant Φ 2 = ExplicitRIP.coherence Φ :=
by exact ExplicitRIP.Provider.ripConstant_one_two
