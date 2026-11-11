/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# Finite-sum estimates for the unsigned barrier

Row-energy bounds and fixed-support averaging control the full Gram-error energy.

Source: [KM, proof of Theorem 4, (12)].
-/

public section

open scoped BigOperators
open Finset

namespace ExplicitRIP.Absbar

variable {ι : Type*} [Fintype ι]

/-- A bound on every `r`-term energy controls the full energy by the full mass. -/
theorem sum_sq_le_of_support_bound (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (D : ℝ) (hD : 0 ≤ D) (r : ℕ) (hr : 0 < r)
    (hsub : ∀ S : Finset ι, S.card ≤ r → ∑ i ∈ S, f i ^ 2 ≤ D ^ 2) :
    (∑ i, f i ^ 2) ≤ D ^ 2 + D / Real.sqrt r * ∑ i, f i := by
  classical
  let c := D / Real.sqrt r
  let S := univ.filter (fun i => c < f i)
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hc : 0 ≤ c := div_nonneg hD (Real.sqrt_nonneg _)
  have hc2 : (r : ℝ) * c ^ 2 = D ^ 2 := by
    dsimp [c]
    rw [div_pow, Real.sq_sqrt hrR.le]
    exact mul_div_cancel₀ _ (ne_of_gt hrR)
  have hcard : S.card < r := by
    by_contra! hcard
    obtain ⟨T, hTS, hT⟩ := exists_subset_card_eq hcard
    have hTne : T.Nonempty := card_pos.mp (hT ▸ hr)
    have hlt : (r : ℝ) * c ^ 2 < ∑ i ∈ T, f i ^ 2 := by
      calc
        (r : ℝ) * c ^ 2 = ∑ _i ∈ T, c ^ 2 := by simp [hT]
        _ < ∑ i ∈ T, f i ^ 2 := by
          apply sum_lt_sum_of_nonempty hTne
          intro i hi
          have hci : c < f i := (mem_filter.mp (hTS hi)).2
          nlinarith only [hc, hci]
    rw [hc2] at hlt
    exact (not_lt_of_ge (hsub T hT.le)) hlt
  have hpoint (i : ι) : f i ^ 2 ≤ (if i ∈ S then f i ^ 2 else 0) + c * f i := by
    by_cases hi : i ∈ S
    · rw [ite_eq_left hi]
      exact le_add_of_nonneg_right (mul_nonneg hc (hf i))
    · have hfi : f i ≤ c := by
        simpa only [S, mem_filter, mem_univ, true_and, not_lt] using hi
      rw [ite_eq_right hi, zero_add]
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hfi (hf i)
  calc
    (∑ i, f i ^ 2) ≤ ∑ i, ((if i ∈ S then f i ^ 2 else 0) + c * f i) :=
      sum_le_sum fun i _ => hpoint i
    _ = (∑ i ∈ S, f i ^ 2) + c * ∑ i, f i := by
      rw [sum_add_distrib, ← mul_sum]
      congr 1
      simp [S, sum_filter]
    _ ≤ D ^ 2 + c * ∑ i, f i := add_le_add (hsub S hcard.le) le_rfl

theorem card_supports_containing_pair [DecidableEq ι]
    (k : ℕ) (hk : 2 ≤ k) (i j : ι) (hij : i ≠ j) :
    ((univ.powersetCard k).filter (fun S : Finset ι => i ∈ S ∧ j ∈ S)).card =
      (Fintype.card ι - 2).choose (k - 2) := by
  have hpair : ({i, j} : Finset ι).card = 2 := by simp [hij]
  have h := card_filter_powersetCard_subset ({i, j} : Finset ι) univ k
    (subset_univ _) (hpair ▸ hk)
  simpa only [insert_subset_iff, singleton_subset_iff, hpair, card_univ] using h

/-- Each ordered pair of distinct indices occurs in the same number of supports. -/
theorem sum_support_masses (H : ι → ι → ℝ) (hdiag : ∀ i, H i i = 0)
    (k : ℕ) (hk : 2 ≤ k) :
    (∑ S ∈ univ.powersetCard k, ∑ i ∈ S, ∑ j ∈ S, H i j) =
      ((Fintype.card ι - 2).choose (k - 2) : ℝ) * (∑ i, ∑ j, H i j) := by
  classical
  calc
    _ = ∑ S ∈ univ.powersetCard k, ∑ i, ∑ j,
        if i ∈ S ∧ j ∈ S then H i j else 0 := by
      apply sum_congr rfl
      intro S _
      calc
        _ = ∑ i, if i ∈ S then ∑ j ∈ S, H i j else 0 := by
          rw [← sum_filter]
          simp only [filter_mem_eq_inter, univ_inter]
        _ = _ := by
          apply sum_congr rfl
          intro i _
          by_cases hi : i ∈ S
          · simp only [hi, true_and, ite_true, ← sum_filter,
              filter_mem_eq_inter, univ_inter]
          · simp only [hi, false_and, ite_false, sum_const_zero]
    _ = ∑ i, ∑ j, ∑ S ∈ univ.powersetCard k,
        if i ∈ S ∧ j ∈ S then H i j else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
    _ = ∑ i, ∑ j, ((Fintype.card ι - 2).choose (k - 2) : ℝ) * H i j := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      by_cases hij : i = j
      · subst j
        simp only [hdiag, ite_self, sum_const_zero, mul_zero]
      · rw [← sum_filter, sum_const, card_supports_containing_pair k hk i j hij,
          nsmul_eq_mul]
    _ = _ := by simp only [mul_sum]

/-- The binomial normalization in averaging ordered pairs over `k`-sets. -/
theorem choose_pair_identity (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    (n.choose k : ℝ) * k * ((k : ℝ) - 1) =
      ((n - 2).choose (k - 2) : ℝ) * n * ((n : ℝ) - 1) := by
  have h₁ := Nat.add_one_mul_choose_eq (n - 1) (k - 1)
  have h₂ := Nat.add_one_mul_choose_eq (n - 2) (k - 2)
  have hn : 2 ≤ n := hk.trans hkn
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n),
    Nat.sub_add_cancel (by omega : 1 ≤ k)] at h₁
  rw [show n - 2 + 1 = n - 1 by omega, show k - 2 + 1 = k - 1 by omega] at h₂
  have h₁R : (n : ℝ) * ((n - 1).choose (k - 1) : ℝ) = (n.choose k : ℝ) * k := by
    exact_mod_cast h₁
  have h₂R : ((n : ℝ) - 1) * ((n - 2).choose (k - 2) : ℝ) =
      ((n - 1).choose (k - 1) : ℝ) * ((k : ℝ) - 1) := by
    have h₂' : ((n - 1 : ℕ) : ℝ) * ((n - 2).choose (k - 2) : ℝ) =
        ((n - 1).choose (k - 1) : ℝ) * ((k - 1 : ℕ) : ℝ) := by exact_mod_cast h₂
    simpa only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 1 ≤ k),
      Nat.cast_one] using h₂'
  rw [← h₁R, mul_assoc, ← h₂R]
  ring

/-- An upper bound for each support mass bounds the total off-diagonal mass. -/
theorem total_mass_le (H : ι → ι → ℝ) (hdiag : ∀ i, H i i = 0)
    (D : ℝ) (k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ Fintype.card ι)
    (hlocal : ∀ S : Finset ι, S.card = k →
      (∑ i ∈ S, ∑ j ∈ S, H i j) ≤ (k : ℝ) * D) :
    (∑ i, ∑ j, H i j) ≤
      (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) / ((k : ℝ) - 1) * D := by
  classical
  have hsum := sum_le_sum (s := univ.powersetCard k) (fun S hS =>
    hlocal S (mem_powersetCard.mp hS).2)
  rw [sum_support_masses H hdiag k hk] at hsum
  simp only [sum_const, card_powersetCard, card_univ, nsmul_eq_mul] at hsum
  have hchoose : (0 : ℝ) < ((Fintype.card ι - 2).choose (k - 2) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : k - 2 ≤ Fintype.card ι - 2)
  have hkr : (0 : ℝ) < (k : ℝ) - 1 := by
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  apply (mul_le_mul_iff_right₀ hkr).mp
  apply (mul_le_mul_iff_left₀ hchoose).mp
  have h := mul_le_mul_of_nonneg_right hsum hkr.le
  have hid := choose_pair_identity (Fintype.card ι) k hk hkn
  calc
    _ = (((Fintype.card ι - 2).choose (k - 2) : ℝ) * (∑ i, ∑ j, H i j)) *
        ((k : ℝ) - 1) := by ring
    _ ≤ ((Fintype.card ι).choose k : ℝ) * ((k : ℝ) * D) * ((k : ℝ) - 1) := h
    _ = (((Fintype.card ι - 2).choose (k - 2) : ℝ) *
        (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1)) * D := by
      calc
        _ = (((Fintype.card ι).choose k : ℝ) * k * ((k : ℝ) - 1)) * D := by ring
        _ = _ := by rw [hid]
    _ = _ := by field_simp

end ExplicitRIP.Absbar
