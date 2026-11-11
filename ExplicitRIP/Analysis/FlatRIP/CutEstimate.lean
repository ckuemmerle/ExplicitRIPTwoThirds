/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.FlatRIP.Counting

/-!
# The rectangle estimate from balanced cuts

A zero-diagonal kernel on a support of size at most `2k` has every rectangle
bounded by twice its disjoint-rectangle parameter at size `k`.
-/

public section

namespace ExplicitRIP.Flat

open Finset

variable {α : Type*} [DecidableEq α]

theorem sum_sqrt_cut_card_le (S I J : Finset α) (hI : I ⊆ S) (hJ : J ⊆ S)
    (hs : 2 ≤ S.card) :
    (∑ P ∈ S.powersetCard (S.card / 2),
      Real.sqrt (((I.filter (· ∈ P)).card : ℝ) * (J.filter (· ∉ P)).card)) ≤
        2 * ((S.card - 2).choose (S.card / 2 - 1) : ℝ) *
          Real.sqrt ((I.card : ℝ) * J.card) := by
  have hp : 0 < S.card / 2 := by omega
  obtain ⟨_, ha, hb⟩ := balanced_choose_bounds S.card hs
  have ha' : ((S.card - 1).choose (S.card / 2 - 1) : ℝ) ≤
      2 * ((S.card - 2).choose (S.card / 2 - 1) : ℝ) := by exact_mod_cast ha
  have hb' : ((S.card - 1).choose (S.card / 2) : ℝ) ≤
      2 * ((S.card - 2).choose (S.card / 2 - 1) : ℝ) := by exact_mod_cast hb
  let c : ℝ := (S.card - 2).choose (S.card / 2 - 1)
  have hc : 0 ≤ c := Nat.cast_nonneg _
  calc
    _ = ∑ P ∈ S.powersetCard (S.card / 2),
        Real.sqrt ((I.filter (· ∈ P)).card : ℝ) *
          Real.sqrt ((J.filter (· ∉ P)).card : ℝ) := by
      apply sum_congr rfl
      intro P _
      exact Real.sqrt_mul (Nat.cast_nonneg _) _
    _ ≤ Real.sqrt (∑ P ∈ S.powersetCard (S.card / 2),
        ((I.filter (· ∈ P)).card : ℝ)) *
        Real.sqrt (∑ P ∈ S.powersetCard (S.card / 2),
        ((J.filter (· ∉ P)).card : ℝ)) :=
      Real.sum_sqrt_mul_sqrt_le _ (fun _ => Nat.cast_nonneg _) (fun _ => Nat.cast_nonneg _)
    _ = Real.sqrt ((I.card : ℝ) * (S.card - 1).choose (S.card / 2 - 1)) *
        Real.sqrt ((J.card : ℝ) * (S.card - 1).choose (S.card / 2)) := by
      rw [sum_card_cut_left S I _ hp hI, sum_card_cut_right S J _ hJ]
    _ ≤ Real.sqrt ((I.card : ℝ) * (2 * c)) *
        Real.sqrt ((J.card : ℝ) * (2 * c)) := by
      apply mul_le_mul
      · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ha' (Nat.cast_nonneg _))
      · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hb' (Nat.cast_nonneg _))
      · exact Real.sqrt_nonneg _
      · exact Real.sqrt_nonneg _
    _ = 2 * c * Real.sqrt ((I.card : ℝ) * J.card) := by
      rw [← Real.sqrt_mul (by positivity)]
      rw [show ((I.card : ℝ) * (2 * c)) * ((J.card : ℝ) * (2 * c)) =
        (2 * c) ^ 2 * ((I.card : ℝ) * J.card) by ring]
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

omit [DecidableEq α] in
theorem rectangle_bound_of_disjoint_bound (M : α → α → ℂ) (hdiag : ∀ i, M i i = 0)
    (S : Finset α) (k : ℕ) (hSk : S.card ≤ 2 * k) (θ : ℝ) (hθ : 0 ≤ θ)
    (hflat : ∀ A B : Finset α, A ⊆ S → B ⊆ S → Disjoint A B →
      A.card ≤ k → B.card ≤ k →
      ‖∑ i ∈ A, ∑ j ∈ B, M i j‖ ≤ θ * Real.sqrt ((A.card : ℝ) * B.card))
    (I J : Finset α) (hI : I ⊆ S) (hJ : J ⊆ S) :
    ‖∑ i ∈ I, ∑ j ∈ J, M i j‖ ≤ 2 * θ * Real.sqrt ((I.card : ℝ) * J.card) := by
  classical
  by_cases hs : 2 ≤ S.card
  · have hp : 0 < S.card / 2 := by omega
    let c := (S.card - 2).choose (S.card / 2 - 1)
    have hc : (0 : ℝ) < c := by exact_mod_cast (balanced_choose_bounds S.card hs).1
    have hcut (P : Finset α) (hP : P ∈ S.powersetCard (S.card / 2)) :
        ‖∑ i ∈ I.filter (· ∈ P), ∑ j ∈ J.filter (· ∉ P), M i j‖ ≤
          θ * Real.sqrt (((I.filter (· ∈ P)).card : ℝ) * (J.filter (· ∉ P)).card) := by
      obtain ⟨hPS, hPc⟩ := mem_powersetCard.mp hP
      apply hflat
      · exact (filter_subset _ _).trans hI
      · exact (filter_subset _ _).trans hJ
      · apply disjoint_left.mpr
        intro i hi hj
        exact (mem_filter.mp hj).2 (mem_filter.mp hi).2
      · have hsub : I.filter (· ∈ P) ⊆ P := fun i hi => (mem_filter.mp hi).2
        exact (card_le_card hsub).trans (by omega)
      · have hsub : J.filter (· ∉ P) ⊆ S \ P := by
          intro j hj
          exact mem_sdiff.mpr ⟨hJ (mem_filter.mp hj).1, (mem_filter.mp hj).2⟩
        have hcard := card_sdiff_of_subset hPS
        exact (card_le_card hsub).trans (by omega)
    have hsum : (c : ℝ) * ‖∑ i ∈ I, ∑ j ∈ J, M i j‖ ≤
        (c : ℝ) * (2 * θ * Real.sqrt ((I.card : ℝ) * J.card)) := by
      calc
        _ = ‖∑ P ∈ S.powersetCard (S.card / 2),
            ∑ i ∈ I.filter (· ∈ P), ∑ j ∈ J.filter (· ∉ P), M i j‖ := by
          rw [sum_cut_rectangles M hdiag S I J hI hJ _ hp, norm_mul, Complex.norm_natCast]
        _ ≤ ∑ P ∈ S.powersetCard (S.card / 2),
            ‖∑ i ∈ I.filter (· ∈ P), ∑ j ∈ J.filter (· ∉ P), M i j‖ :=
          norm_sum_le _ _
        _ ≤ ∑ P ∈ S.powersetCard (S.card / 2),
            θ * Real.sqrt (((I.filter (· ∈ P)).card : ℝ) * (J.filter (· ∉ P)).card) :=
          sum_le_sum hcut
        _ = θ * (∑ P ∈ S.powersetCard (S.card / 2),
            Real.sqrt (((I.filter (· ∈ P)).card : ℝ) * (J.filter (· ∉ P)).card)) :=
          (mul_sum _ _ _).symm
        _ ≤ θ * (2 * (c : ℝ) * Real.sqrt ((I.card : ℝ) * J.card)) :=
          mul_le_mul_of_nonneg_left (sum_sqrt_cut_card_le S I J hI hJ hs) hθ
        _ = _ := by ring
    exact le_of_mul_le_mul_left hsum hc
  · have hz : (∑ i ∈ I, ∑ j ∈ J, M i j) = 0 := by
      apply sum_eq_zero
      intro i hi
      apply sum_eq_zero
      intro j hj
      have hij := card_le_one.mp (show S.card ≤ 1 by omega) i (hI hi) j (hJ hj)
      rw [hij, hdiag]
    rw [hz, norm_zero]
    positivity

end ExplicitRIP.Flat
