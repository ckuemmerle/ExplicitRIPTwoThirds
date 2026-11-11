/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Sampling.Moments

/-!
# Simultaneous witness sampling

The second moment bounds each witness failure probability by `1/32`.
Linearity then controls a single cost combining sample size and failure count,
without an independence assumption between different witness sets.
-/

public section

namespace ExplicitRIP.GuthZahl

namespace Sampling.DegreeReduction

theorem bernoulliWeight_nonneg {α : Type*} (S T : Finset α) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) : 0 ≤ bernoulliWeight q S T :=
  mul_nonneg (pow_nonneg hq _) (pow_nonneg (sub_nonneg.mpr hq1) _)

open Classical in
/-- The mass of samples hitting fewer than half the required witnesses. -/
theorem witness_failure_mass_le {α : Type*} (S W : Finset α) (A q : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hμ : 128 ≤ q * A)
    (hW : W ⊆ S) (hAW : A ≤ (W.card : ℝ)) :
    (∑ T ∈ S.powerset, bernoulliWeight q S T *
      (if ((T ∩ W).card : ℝ) < q * A / 2 then 1 else 0)) ≤ 1 / 32 := by
  let μ : ℝ := q * W.card
  have hμA : q * A ≤ μ := mul_le_mul_of_nonneg_left hAW hq
  have hμ128 : 128 ≤ μ := hμ.trans hμA
  have hμpos : 0 < μ := by linarith only [hμ128]
  have hpoint (T : Finset α) :
      32 * μ * (if ((T ∩ W).card : ℝ) < q * A / 2 then 1 else 0) ≤
        (((T ∩ W).card : ℝ) - μ) ^ 2 := by
    split_ifs with hT
    · have hx : ((T ∩ W).card : ℝ) ≤ μ / 2 := by linarith only [hT, hμA]
      have hs : (μ / 2) ^ 2 ≤ (μ - ((T ∩ W).card : ℝ)) ^ 2 := by
        exact pow_le_pow_left₀ (le_of_lt (half_pos hμpos))
          (by linarith only [hx]) 2
      nlinarith only [hs, hμ128, sq_nonneg (μ - 128)]
    · simp only [mul_zero]
      exact sq_nonneg _
  have hsum := Finset.sum_le_sum (fun T (_ : T ∈ S.powerset) =>
    mul_le_mul_of_nonneg_left (hpoint T) (bernoulliWeight_nonneg S T q hq hq1))
  have hfactor :
      (∑ T ∈ S.powerset, bernoulliWeight q S T *
        (32 * μ * (if ((T ∩ W).card : ℝ) < q * A / 2 then 1 else 0))) =
      32 * μ * (∑ T ∈ S.powerset, bernoulliWeight q S T *
        (if ((T ∩ W).card : ℝ) < q * A / 2 then 1 else 0)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T _
    ring
  rw [hfactor, bernoulli_second_moment q S W hW] at hsum
  have hvar : q * (1 - q) * W.card ≤ μ := by
    change q * (1 - q) * W.card ≤ q * W.card
    nlinarith only [mul_nonneg hq (Nat.cast_nonneg W.card),
      mul_nonneg (sq_nonneg q) (Nat.cast_nonneg W.card)]
  have h := hsum.trans hvar
  apply (mul_le_mul_iff_of_pos_left (show 0 < 32 * μ by positivity)).mp
  linarith only [h]

end Sampling.DegreeReduction

open Classical in
/-- Chebyshev + linearity + Markov + a union bound. Witness sets for different indices may
overlap arbitrarily. -/
theorem sample_hits_many_witness_sets {α : Type*}
    (S : Finset α) (W : α → Finset α) (A q : ℝ)
    (hA : 0 < A) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hμ : 128 ≤ q * A)
    (hW : ∀ l ∈ S, W l ⊆ S ∧ A ≤ ((W l).card : ℝ)) :
    ∃ T : Finset α, T ⊆ S ∧ (T.card : ℝ) ≤ 4 * q * S.card ∧
      4 * (S.filter (fun l => ((T ∩ W l).card : ℝ) < q * A / 2)).card ≤ S.card := by
  by_cases hS : S = ∅
  · subst S
    exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
  have hqpos : 0 < q := (mul_pos_iff_of_pos_right hA).mp (by
    linarith only [hμ] : 0 < q * A)
  have hcard : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
  let bad (T : Finset α) := S.filter (fun l => ((T ∩ W l).card : ℝ) < q * A / 2)
  have hbad : (∑ T ∈ S.powerset, bernoulliWeight q S T * (bad T).card) ≤
      (S.card : ℝ) / 32 := by
    have hcount (T : Finset α) : ((bad T).card : ℝ) =
        ∑ l ∈ S, if ((T ∩ W l).card : ℝ) < q * A / 2 then 1 else 0 := by
      simp only [bad, ← Finset.sum_boole]
    simp_rw [hcount, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ l ∈ S, (1 / 32 : ℝ) := Finset.sum_le_sum fun l hl =>
        Sampling.DegreeReduction.witness_failure_mass_le S (W l) A q hq hq1 hμ
          (hW l hl).1 (hW l hl).2
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  have hsize : (∑ T ∈ S.powerset, bernoulliWeight q S T * (T.card : ℝ)) =
      q * S.card := by
    convert bernoulli_first_moment q S S (Finset.Subset.refl _) using 1
    apply Finset.sum_congr rfl
    intro T hT
    rw [Finset.inter_eq_left.mpr (Finset.mem_powerset.mp hT)]
  let cost (T : Finset α) : ℝ := T.card + 16 * q * (bad T).card
  have hcost : (∑ T ∈ S.powerset, bernoulliWeight q S T * cost T) <
      ∑ T ∈ S.powerset, bernoulliWeight q S T * (4 * q * S.card) := by
    have heq : (∑ T ∈ S.powerset, bernoulliWeight q S T * cost T) =
        q * S.card + 16 * q *
          (∑ T ∈ S.powerset, bernoulliWeight q S T * (bad T).card) := by
      simp only [cost, mul_add, Finset.sum_add_distrib]
      rw [hsize, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro T _
      ring
    rw [heq, ← Finset.sum_mul, bernoulliWeight_sum, one_mul]
    have hb := mul_le_mul_of_nonneg_left hbad (show 0 ≤ 16 * q by positivity)
    nlinarith only [hb, mul_pos hqpos hcard]
  obtain ⟨T, hT, hcostT⟩ := Finset.exists_lt_of_sum_lt hcost
  have hcostT' : cost T < 4 * q * S.card := lt_of_mul_lt_mul_left hcostT
    (Sampling.DegreeReduction.bernoulliWeight_nonneg S T q hq hq1)
  refine ⟨T, Finset.mem_powerset.mp hT, ?_, ?_⟩
  · have hb : 0 ≤ 16 * q * (bad T).card := by positivity
    dsimp only [cost] at hcostT'
    linarith only [hcostT', hb]
  · have hc : 4 * ((bad T).card : ℝ) ≤ S.card := by
      have hTcard : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
      dsimp only [cost] at hcostT'
      apply (mul_le_mul_iff_of_pos_left hqpos).mp
      linarith only [hcostT', hTcard]
    exact_mod_cast hc

end ExplicitRIP.GuthZahl

end
