/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.FlatConstant

/-!
# The least flat-RIP constant

Source: [KM, (4) and the definition of θ_k in Lemma 2].

The finite supremum of normalized rectangular sums is nonnegative, satisfies the flat-RIP
bounds, and is bounded by every nonnegative admissible parameter. It is therefore the smallest
`θ ≥ 0` satisfying [KM, (4)] on disjoint sets of size at most `k`.
-/

public section

open scoped Matrix

/-- The normalized maximum is the least nonnegative flat-RIP parameter. -/
theorem ExplicitRIP.Provider.flatConstant_isLeast :
    ∀ {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] (Φ : Matrix m n 𝕜) (k : ℕ),
      IsLeast {θ : ℝ | 0 ≤ θ ∧ ∀ I J : Finset n, Disjoint I J → I.card ≤ k → J.card ≤ k →
          ‖∑ i ∈ I, ∑ j ∈ J, (Φᴴ * Φ) i j‖ ≤ θ * Real.sqrt ((I.card : ℝ) * J.card)}
        (ExplicitRIP.flatConstant Φ k) := by
  intro 𝕜 _ m n _ _ Φ k
  classical
  let pairs := {IJ : Finset n × Finset n // IJ.1.Nonempty ∧ IJ.2.Nonempty ∧
    Disjoint IJ.1 IJ.2 ∧ IJ.1.card ≤ k ∧ IJ.2.card ≤ k}
  let normalized : pairs → ℝ := fun IJ =>
    ‖∑ i ∈ IJ.1.1, ∑ j ∈ IJ.1.2, (Φᴴ * Φ) i j‖ /
      Real.sqrt ((IJ.1.1.card : ℝ) * IJ.1.2.card)
  rw [show ExplicitRIP.flatConstant Φ k = ⨆ IJ, normalized IJ from rfl]
  have sqrt_pos (I J : Finset n) (hI : I.Nonempty) (hJ : J.Nonempty) :
      0 < Real.sqrt ((I.card : ℝ) * J.card) :=
    Real.sqrt_pos.mpr (mul_pos (Nat.cast_pos.mpr hI.card_pos) (Nat.cast_pos.mpr hJ.card_pos))
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact Real.iSup_nonneg fun IJ => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  · intro I J hIJ hIk hJk
    obtain rfl | hI := I.eq_empty_or_nonempty
    · simp only [Finset.sum_empty, norm_zero, Finset.card_empty, Nat.cast_zero,
        zero_mul, Real.sqrt_zero, mul_zero, le_refl]
    obtain rfl | hJ := J.eq_empty_or_nonempty
    · simp only [Finset.sum_empty, Finset.sum_const_zero, norm_zero, Finset.card_empty,
        Nat.cast_zero, mul_zero, Real.sqrt_zero, le_refl]
    exact (div_le_iff₀ (sqrt_pos I J hI hJ)).mp
      (le_ciSup (Finite.bddAbove_range normalized)
        (⟨(I, J), hI, hJ, hIJ, hIk, hJk⟩ : pairs))
  · intro θ hθ
    apply Real.iSup_le ?_ hθ.1
    intro IJ
    exact (div_le_iff₀ (sqrt_pos IJ.1.1 IJ.1.2 IJ.2.1 IJ.2.2.1)).mpr
      (hθ.2 IJ.1.1 IJ.1.2 IJ.2.2.2.1 IJ.2.2.2.2.1 IJ.2.2.2.2.2)
