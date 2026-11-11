/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Defs
import ExplicitRIP.Zahl.Basic.Lie

/-!
# Elementary estimates and finite counts for Zahl's theorem

Real power estimates, direction-pencil fibers, the empty rich-pencil count above the ambient
cardinality and the quadratic finite-mean inequality. -/

public section

namespace ExplicitRIP.Zahl

theorem div_le_three_halves_scale (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    (n : ℝ) / (k : ℝ) ≤
      (n : ℝ) ^ (3 / 2 : ℝ) * (k : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hratio : (1 : ℝ) ≤ (n : ℝ) / (k : ℝ) := by
    apply (le_div_iff₀ hk').2
    simpa only [one_mul] using (Nat.cast_le.mpr hkn : (k : ℝ) ≤ n)
  calc
    (n : ℝ) / (k : ℝ) = ((n : ℝ) / (k : ℝ)) ^ (1 : ℝ) :=
      (Real.rpow_one _).symm
    _ ≤ ((n : ℝ) / (k : ℝ)) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hratio (by norm_num)
    _ = (n : ℝ) ^ (3 / 2 : ℝ) * (k : ℝ) ^ (-(3 / 2 : ℝ)) := by
      rw [Real.div_rpow (Nat.cast_nonneg n) (Nat.cast_nonneg k),
        Real.rpow_neg (Nat.cast_nonneg k), div_eq_mul_inv]

theorem half_le_three_halves (n : ℕ) :
    (n : ℝ) / 2 ≤ (n : ℝ) ^ (3 / 2 : ℝ) := by
  by_cases hn : n = 0
  · subst n
    norm_num
  have hn' : (1 : ℝ) ≤ n := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  calc
    (n : ℝ) / 2 ≤ n := div_le_self (Nat.cast_nonneg n) (by norm_num)
    _ = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (n : ℝ) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn' (by norm_num)

section

variable {F : Type*} [Field F]

theorem directionPencil_injective (h2 : (2 : F) ≠ 0) :
    Function.Injective (directionPencil : (F × F × F) → Set (Sphere F)) := by
  intro v w hvw
  have hv : parametersSphere (⟨0, v.1, v.2.1, v.2.2⟩ : HLine F) ∈
      directionPencil v := by
    simp only [directionPencil, Set.mem_ofPred_eq,
      sphereParameters_parametersSphere h2, and_self]
  rw [hvw] at hv
  simp only [directionPencil, Set.mem_ofPred_eq,
    sphereParameters_parametersSphere h2] at hv
  exact Prod.ext hv.1 (Prod.ext hv.2.1 hv.2.2)

-- The statement includes a finite enumeration of the field.
set_option linter.unusedFintypeInType false in
theorem parallelRichCount_mul_le_card [Fintype F]
    (S : Finset (Sphere F)) (k : ℕ) :
    k * parallelRichCount S k ≤ S.card := by
  classical
  let V : Finset (F × F × F) :=
    {v : F × F × F | k ≤ (S.filter (· ∈ directionPencil v)).card}.toFinset
  have hV : parallelRichCount S k = V.card :=
    Set.ncard_eq_toFinset_card' _
  have hfiber (T : Sphere F) (v : F × F × F) :
      T ∈ directionPencil v ↔
        ((sphereParameters T).b, (sphereParameters T).c, (sphereParameters T).d) = v := by
    simp only [directionPencil, Set.mem_ofPred_eq, Prod.ext_iff]
  calc
    k * parallelRichCount S k = ∑ _v ∈ V, k := by
      rw [hV, Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ v ∈ V, (S.filter (· ∈ directionPencil v)).card := by
      apply Finset.sum_le_sum
      intro v hv
      simpa only [V, Set.mem_toFinset, Set.mem_ofPred_eq] using hv
    _ = (S.filter (fun T =>
        ((sphereParameters T).b, (sphereParameters T).c, (sphereParameters T).d) ∈ V)).card := by
      simp_rw [hfiber]
      exact Finset.sum_card_fiberwise_eq_card_filter S V _
    _ ≤ S.card := Finset.card_filter_le _ _

theorem richPencilCount_eq_zero_of_card_lt [Fintype F]
    (S : Finset (Sphere F)) (k : ℕ) (hk : S.card < k) :
    ExplicitRIP.richPencilCount S k = 0 := by
  classical
  unfold ExplicitRIP.richPencilCount
  have hempty :
      {P : Set (Sphere F) | ExplicitRIP.IsContactPencil P ∧
        k ≤ (S.filter (· ∈ P)).card} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro P hP
    exact (not_le_of_gt hk) (hP.2.trans (Finset.card_filter_le _ _))
  rw [hempty, Set.ncard_empty]

end

open Classical in
theorem finiteMean_chebyshev {α : Type*}
    (Ω : Finset α) (f : α → ℝ) (μ d : ℝ) (hd : 0 < d) :
    d ^ 2 * finiteMean Ω (fun x => if d ≤ |f x - μ| then 1 else 0) ≤
      finiteMean Ω (fun x => (f x - μ) ^ 2) := by
  unfold finiteMean
  rw [Finset.mul_expect]
  apply Finset.expect_le_expect
  intro x _hx
  split_ifs with hx
  · simpa only [mul_one, sq_abs] using
      (sq_le_sq₀ hd.le (abs_nonneg (f x - μ))).2 hx
  · simpa only [mul_zero] using sq_nonneg (f x - μ)

end ExplicitRIP.Zahl
