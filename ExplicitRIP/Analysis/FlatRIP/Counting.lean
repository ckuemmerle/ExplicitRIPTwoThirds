/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# Counting balanced cuts

Finite subset counts used to extend the cut argument to every support size.
-/

public section

namespace ExplicitRIP.Flat

open Finset

variable {α : Type*} [DecidableEq α]

theorem card_cuts_mem (S : Finset α) (p : ℕ) (hp : 0 < p) {i : α} (hi : i ∈ S) :
    ((S.powersetCard p).filter (fun P => i ∈ P)).card =
      (S.card - 1).choose (p - 1) := by
  simpa only [singleton_subset_iff, card_singleton] using
    card_filter_powersetCard_subset {i} S p (singleton_subset_iff.mpr hi) hp

theorem cuts_not_mem (S : Finset α) (p : ℕ) (j : α) :
    (S.powersetCard p).filter (fun P => j ∉ P) = (S.erase j).powersetCard p := by
  ext P
  simp only [mem_filter, mem_powersetCard]
  constructor
  · rintro ⟨⟨hPS, hP⟩, hj⟩
    exact ⟨subset_erase.mpr ⟨hPS, hj⟩, hP⟩
  · rintro ⟨hPS, hP⟩
    obtain ⟨hPS, hj⟩ := subset_erase.mp hPS
    exact ⟨⟨hPS, hP⟩, hj⟩

theorem card_cuts_not_mem (S : Finset α) (p : ℕ) {j : α} (hj : j ∈ S) :
    ((S.powersetCard p).filter (fun P => j ∉ P)).card = (S.card - 1).choose p := by
  rw [cuts_not_mem, card_powersetCard, card_erase_of_mem hj]

theorem card_cuts_cross (S : Finset α) (p : ℕ) (hp : 0 < p)
    {i j : α} (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) :
    ((S.powersetCard p).filter (fun P => i ∈ P ∧ j ∉ P)).card =
      (S.card - 2).choose (p - 1) := by
  have hf : (S.powersetCard p).filter (fun P => i ∈ P ∧ j ∉ P) =
      ((S.powersetCard p).filter (fun P => j ∉ P)).filter (fun P => i ∈ P) := by
    ext P
    simp only [mem_filter]
    tauto
  rw [hf, cuts_not_mem, card_cuts_mem _ p hp (mem_erase.mpr ⟨hij, hi⟩),
    card_erase_of_mem hj, Nat.sub_sub]

theorem balanced_choose_bounds (s : ℕ) (hs : 2 ≤ s) :
    0 < (s - 2).choose (s / 2 - 1) ∧
      (s - 1).choose (s / 2 - 1) ≤ 2 * (s - 2).choose (s / 2 - 1) ∧
      (s - 1).choose (s / 2) ≤ 2 * (s - 2).choose (s / 2 - 1) := by
  have hm : (s - 2) / 2 = s / 2 - 1 := by omega
  have hmax (r : ℕ) : (s - 2).choose r ≤ (s - 2).choose (s / 2 - 1) := by
    simpa only [hm] using Nat.choose_le_middle r (s - 2)
  have hp : 0 < s / 2 := by omega
  refine ⟨Nat.choose_pos (by omega), ?_, ?_⟩
  · by_cases h : s / 2 - 1 = 0
    · simp only [h, Nat.choose_zero_right]
      omega
    · have hpas := Nat.choose_succ_left (s - 2) (s / 2 - 1) (by omega)
      have hs' : s - 2 + 1 = s - 1 := by omega
      rw [hs'] at hpas
      rw [hpas]
      exact (Nat.add_le_add (hmax _) (hmax _)).trans_eq (by omega)
  · have hpas := Nat.choose_succ_left (s - 2) (s / 2) hp
    have hs' : s - 2 + 1 = s - 1 := by omega
    rw [hs'] at hpas
    rw [hpas]
    exact (Nat.add_le_add (hmax _) (hmax _)).trans_eq (by omega)

theorem sum_card_cut_left (S I : Finset α) (p : ℕ) (hp : 0 < p) (hI : I ⊆ S) :
    (∑ P ∈ S.powersetCard p, ((I.filter (· ∈ P)).card : ℝ)) =
      (I.card : ℝ) * (S.card - 1).choose (p - 1) := by
  calc
    _ = ∑ P ∈ S.powersetCard p, ∑ i ∈ I, if i ∈ P then (1 : ℝ) else 0 := by
      simp only [sum_boole]
    _ = ∑ i ∈ I, ∑ P ∈ S.powersetCard p, if i ∈ P then (1 : ℝ) else 0 :=
      sum_comm
    _ = ∑ _i ∈ I, ((S.card - 1).choose (p - 1) : ℝ) := by
      apply sum_congr rfl
      intro i hi
      rw [sum_boole, card_cuts_mem S p hp (hI hi)]
    _ = _ := by simp only [sum_const, nsmul_eq_mul]

theorem sum_card_cut_right (S J : Finset α) (p : ℕ) (hJ : J ⊆ S) :
    (∑ P ∈ S.powersetCard p, ((J.filter (· ∉ P)).card : ℝ)) =
      (J.card : ℝ) * (S.card - 1).choose p := by
  calc
    _ = ∑ P ∈ S.powersetCard p, ∑ j ∈ J, if j ∉ P then (1 : ℝ) else 0 := by
      simp only [sum_boole]
    _ = ∑ j ∈ J, ∑ P ∈ S.powersetCard p, if j ∉ P then (1 : ℝ) else 0 :=
      sum_comm
    _ = ∑ _j ∈ J, ((S.card - 1).choose p : ℝ) := by
      apply sum_congr rfl
      intro j hj
      rw [sum_boole, card_cuts_not_mem S p (hJ hj)]
    _ = _ := by simp only [sum_const, nsmul_eq_mul]

theorem sum_cut_rectangles (M : α → α → ℂ) (hdiag : ∀ i, M i i = 0)
    (S I J : Finset α) (hI : I ⊆ S) (hJ : J ⊆ S) (p : ℕ) (hp : 0 < p) :
    (∑ P ∈ S.powersetCard p,
      ∑ i ∈ I.filter (· ∈ P), ∑ j ∈ J.filter (· ∉ P), M i j) =
      ((S.card - 2).choose (p - 1) : ℂ) * (∑ i ∈ I, ∑ j ∈ J, M i j) := by
  calc
    _ = ∑ P ∈ S.powersetCard p, ∑ i ∈ I, ∑ j ∈ J,
        if i ∈ P ∧ j ∉ P then M i j else 0 := by
      apply sum_congr rfl
      intro P _
      rw [sum_filter]
      apply sum_congr rfl
      intro i _
      by_cases hi : i ∈ P
      · simp only [hi, ite_true, true_and, sum_filter]
      · simp only [hi, ite_false, false_and, sum_const_zero]
    _ = ∑ i ∈ I, ∑ j ∈ J, ∑ P ∈ S.powersetCard p,
        if i ∈ P ∧ j ∉ P then M i j else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
    _ = ∑ i ∈ I, ∑ j ∈ J, ((S.card - 2).choose (p - 1) : ℂ) * M i j := by
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      by_cases hij : i = j
      · subst j
        simp only [hdiag, ite_self, sum_const_zero, mul_zero]
      · rw [← sum_filter, sum_const, card_cuts_cross S p hp (hI hi) (hJ hj) hij,
          nsmul_eq_mul]
    _ = _ := by simp only [mul_sum]

end ExplicitRIP.Flat
