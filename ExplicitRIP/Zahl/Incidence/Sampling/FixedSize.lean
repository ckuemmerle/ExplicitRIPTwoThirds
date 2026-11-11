/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Incidence.Sampling.Counts

/-! # Exact inclusion probabilities for fixed-size subsets -/

public section

namespace ExplicitRIP.Zahl.Sampling

open scoped BigOperators

open Classical in
lemma expect_subset_powersetCard {α : Type*} [DecidableEq α] (L W : Finset α) (hWL : W ⊆ L)
    (m : ℕ) (hm : m ≤ L.card) :
    Finset.expect (L.powersetCard m) (fun T => if W ⊆ T then (1 : ℝ) else 0) =
      (Nat.choose m W.card : ℝ) / (Nat.choose L.card W.card : ℝ) := by
  rw [Finset.expect_eq_sum_div_card, Finset.sum_boole, Finset.card_powersetCard]
  by_cases hw : W.card ≤ m
  · rw [powersetCard_containing_count L W m hWL hw]
    have h₁ : (Nat.choose L.card m : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hm).ne'
    have h₂ : (Nat.choose L.card W.card : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (Finset.card_le_card hWL)).ne'
    apply (div_eq_div_iff h₁ h₂).mpr
    have hc := (Nat.choose_mul (n := L.card) hw).symm
    have hc' : (L.card - W.card).choose (m - W.card) * L.card.choose W.card =
        m.choose W.card * L.card.choose m := by simpa only [mul_comm] using hc
    exact_mod_cast hc'
  · have he : (L.powersetCard m).filter (fun T => W ⊆ T) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro T hT
      obtain ⟨hT, hWT⟩ := Finset.mem_filter.mp hT
      exact hw ((Finset.card_le_card hWT).trans (Finset.mem_powersetCard.mp hT).2.le)
    rw [he, Finset.card_empty, Nat.cast_zero, zero_div,
      Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hw), Nat.cast_zero, zero_div]

open Classical in
lemma expect_mem_powersetCard {α : Type*} [DecidableEq α] (L : Finset α) (m : ℕ) (hm : m ≤ L.card)
    (a : α) (ha : a ∈ L) :
    Finset.expect (L.powersetCard m) (fun T => if a ∈ T then (1 : ℝ) else 0) =
      (m : ℝ) / (L.card : ℝ) := by
  simpa only [Finset.singleton_subset_iff, Finset.card_singleton, Nat.choose_one_right] using
    expect_subset_powersetCard L {a} (Finset.singleton_subset_iff.mpr ha) m hm

open Classical in
lemma expect_pair_mem_powersetCard {α : Type*} [DecidableEq α]
    (L : Finset α) (m : ℕ) (hm : m ≤ L.card)
    (a b : α) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) :
    Finset.expect (L.powersetCard m) (fun T => if a ∈ T ∧ b ∈ T then (1 : ℝ) else 0) =
      (Nat.choose m 2 : ℝ) / (Nat.choose L.card 2 : ℝ) := by
  have hsub : {a, b} ⊆ L := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨ha, hb⟩
  simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff,
    Finset.card_pair hab] using expect_subset_powersetCard L {a, b} hsub m hm

lemma choose_two_ratio_le_sq (m n : ℕ) (hm : m ≤ n) :
    (Nat.choose m 2 : ℝ) / (Nat.choose n 2 : ℝ) ≤ ((m : ℝ) / (n : ℝ)) ^ 2 := by
  by_cases hn : n ≤ 1
  · rw [Nat.choose_eq_zero_of_lt (by omega : n < 2), Nat.cast_zero, div_zero]
    exact sq_nonneg _
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    linarith
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [Nat.cast_choose_two, Nat.cast_choose_two]
  have heq : ((m : ℝ) * ((m : ℝ) - 1) / 2) /
      ((n : ℝ) * ((n : ℝ) - 1) / 2) =
      (m : ℝ) * ((m : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1)) :=
    div_div_div_cancel_right₀ (by norm_num) _ _
  rw [heq, div_pow]
  apply (div_le_div_iff₀ (mul_pos hn0 hn1) (sq_pos_of_pos hn0)).mpr
  nlinarith [mul_nonneg (mul_nonneg hm0 hn0.le) (sub_nonneg.mpr hmn)]

end ExplicitRIP.Zahl.Sampling
