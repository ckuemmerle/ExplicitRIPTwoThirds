/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.FlatConstant
import ExplicitRIP.Provider.FlatConstantCharacterization

/-!
# The least flat-RIP constant

Source: [KM, (4) and the definition of θ_k in Lemma 2].
-/

public section

open scoped Matrix

/-- For every real or complex matrix `Φ`, `θ_k(Φ)`, defined as a maximum of normalized
rectangular sums, is the smallest `θ ≥ 0` for which [KM, (4)] holds for all disjoint
`I, J ⊆ [n]` with `|I|, |J| ≤ k`. This characterizes the parameter of [KM, Lemma 2]. -/
theorem ExplicitRIP.flatConstant_isLeast :
    ∀ {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] (Φ : Matrix m n 𝕜) (k : ℕ),
      IsLeast {θ : ℝ | 0 ≤ θ ∧ ∀ I J : Finset n, Disjoint I J → I.card ≤ k → J.card ≤ k →
          ‖∑ i ∈ I, ∑ j ∈ J, (Φᴴ * Φ) i j‖ ≤ θ * Real.sqrt ((I.card : ℝ) * J.card)}
        (ExplicitRIP.flatConstant Φ k) :=
by exact ExplicitRIP.Provider.flatConstant_isLeast
