/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# The flat-RIP constant

Source: [KM, (4) and Lemma 2].
-/

@[expose] public section

open scoped Matrix

/-- The flat-RIP constant `θ_k(Φ)` of [KM, (4) and Lemma 2]: the largest normalized rectangular
sum `|⟨∑_{i ∈ I} φ_i, ∑_{j ∈ J} φ_j⟩| / √(|I| |J|)` over disjoint nonempty column sets
`I, J` with `|I|, |J| ≤ k`, where `⟨φ_i, φ_j⟩ = (Φ^* Φ)_{ij}`. It is `0` when there are no
such sets. The frozen statement `ExplicitRIP.flatConstant_isLeast` characterizes it as the
smallest `θ ≥ 0` satisfying [KM, (4)]. -/
noncomputable def ExplicitRIP.flatConstant {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m]
    [Fintype n] (Φ : Matrix m n 𝕜) (k : ℕ) : ℝ :=
  ⨆ IJ : {IJ : Finset n × Finset n // IJ.1.Nonempty ∧ IJ.2.Nonempty ∧ Disjoint IJ.1 IJ.2 ∧
      IJ.1.card ≤ k ∧ IJ.2.card ≤ k},
    ‖∑ i ∈ IJ.1.1, ∑ j ∈ IJ.1.2, (Φᴴ * Φ) i j‖ / Real.sqrt ((IJ.1.1.card : ℝ) * IJ.1.2.card)
