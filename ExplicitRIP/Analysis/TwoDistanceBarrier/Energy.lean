/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.TwoDistanceBarrier.RankEnergy

/-!
# A large star in the shifted Gram matrix

A low-rank matrix with a large constant diagonal cannot have small energy in
every column. For two-distance frames this forces a star of coherence entries
whose total squared magnitude is at least one.

Source: [KM, proof of Proposition 10].
-/

public section

open scoped Matrix BigOperators

namespace ExplicitRIP.TwoDistanceBarrier

variable {J : Type*} [Fintype J]

/-- A sufficiently redundant two-distance Gram matrix contains a star of energy at least one. -/
theorem exists_large_star (m : ℕ) (Φ : Matrix (Fin m) J ℝ) (η μ : ℝ)
    (hdiag : ∀ i, (Φᵀ * Φ) i i = 1) (hμ : 0 ≤ μ) (hημ : |η| ≤ μ)
    (hη : |η| ≤ 1 / 2)
    (hvalues : ∀ i j, i ≠ j → (Φᵀ * Φ) i j = η ∨ |(Φᵀ * Φ) i j| = μ)
    (hsize : 100 * ((m : ℝ) + 1) ≤ Fintype.card J) :
    ∃ v : J, ∃ T : Finset J, v ∉ T ∧
      (∀ i ∈ T, |(Φᵀ * Φ) i v| = μ) ∧ 1 ≤ (T.card : ℝ) * μ ^ 2 := by
  classical
  let G := Φᵀ * Φ
  let H := G - Matrix.of (fun _ _ => η)
  let T := fun v : J => Finset.univ.filter fun i => i ≠ v ∧ |G i v| = μ
  have hH : H.IsHermitian := by
    change (G - Matrix.of (fun _ _ => η)).IsHermitian
    apply Matrix.IsHermitian.sub
    · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.isHermitian_conjTranspose_mul_self Φ
    · change (Matrix.of (fun _ _ => η))ᴴ = Matrix.of (fun _ _ => η)
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
  have htrace : H.trace = (Fintype.card J : ℝ) * (1 - η) := by
    simp only [Matrix.trace, Matrix.diag, H, G, Matrix.sub_apply, Matrix.of_apply,
      hdiag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  by_contra! hnot
  have hsmall (v : J) : (T v).card * μ ^ 2 < 1 := by
    have hv : v ∉ T v := by simp only [T, Finset.mem_filter, Finset.mem_univ,
      true_and, ne_eq, not_true_eq_false, false_and, not_false_eq_true]
    exact hnot v (T v) hv (fun i hi => (Finset.mem_filter.mp hi).2.2)
  have hentry (v i : J) : H i v ^ 2 ≤
      (if i = v then (1 - η) ^ 2 else 0) + (if i ∈ T v then 4 * μ ^ 2 else 0) := by
    by_cases hiv : i = v
    · subst i
      have hv : v ∉ T v := by simp [T]
      simp only [H, G, Matrix.sub_apply, Matrix.of_apply, hdiag, ite_true,
        ite_eq_right hv, add_zero, le_refl]
    · rw [ite_eq_right hiv, zero_add]
      by_cases hiT : i ∈ T v
      · rw [ite_eq_left hiT]
        have hiμ := (Finset.mem_filter.mp hiT).2.2
        have hab : |G i v - η| ≤ 2 * μ := by
          calc
            _ ≤ |G i v| + |η| := abs_sub _ _
            _ ≤ μ + μ := add_le_add (le_of_eq hiμ) hημ
            _ = 2 * μ := by ring
        have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num) hμ)).mpr hab
        simpa only [H, Matrix.sub_apply, Matrix.of_apply, sq_abs, mul_pow,
          show (2 : ℝ) ^ 2 = 4 by norm_num] using hs
      · rw [ite_eq_right hiT]
        have hiμ : |G i v| ≠ μ := by
          intro h
          exact hiT (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiv, h⟩)
        have he : G i v = η := (hvalues i v hiv).resolve_right hiμ
        simp only [H, Matrix.sub_apply, Matrix.of_apply, he, sub_self, zero_pow
          (by decide : 2 ≠ 0), le_refl]
  have hcol (v : J) : ∑ i, H i v ^ 2 ≤ (1 - η) ^ 2 + 4 := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hentry v i)
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.univ_inter, Finset.sum_const, nsmul_eq_mul] at h
    have hT := hsmall v
    nlinarith only [h, hT]
  have henergy : ∑ i, ∑ j, H i j ^ 2 ≤
      (Fintype.card J : ℝ) * ((1 - η) ^ 2 + 4) := by
    rw [Finset.sum_comm]
    exact (Finset.sum_le_sum (fun v _ => hcol v)).trans_eq (by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul])
  have hspec := trace_sq_le_rank_mul_energy H hH
  have hrank : (H.rank : ℝ) ≤ (m : ℝ) + 1 := by
    exact_mod_cast shifted_gram_rank_le m Φ η
  have htotal : ((Fintype.card J : ℝ) * (1 - η)) ^ 2 ≤
      ((m : ℝ) + 1) * ((Fintype.card J : ℝ) * ((1 - η) ^ 2 + 4)) := by
    rw [← htrace]
    exact hspec.trans (mul_le_mul hrank henergy
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
      (by positivity))
  have hn : (0 : ℝ) < Fintype.card J := lt_of_lt_of_le (by positivity) hsize
  have hcancel : (Fintype.card J : ℝ) * (1 - η) ^ 2 ≤
      ((m : ℝ) + 1) * ((1 - η) ^ 2 + 4) := by
    apply (mul_le_mul_iff_right₀ hn).mp
    convert htotal using 1 <;> ring
  have ha : (1 / 4 : ℝ) ≤ (1 - η) ^ 2 ∧ (1 - η) ^ 2 ≤ 9 / 4 := by
    have h := abs_le.mp hη
    have hlo : (1 / 2 : ℝ) ≤ 1 - η := by linarith only [h.2]
    have hhi : 1 - η ≤ (3 / 2 : ℝ) := by linarith only [h.1]
    constructor
    · have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hlo 2
      norm_num at hs ⊢
      exact hs
    · have hs := pow_le_pow_left₀ (by linarith only [hlo] : 0 ≤ 1 - η) hhi 2
      norm_num at hs ⊢
      exact hs
  have hlower : 25 * ((m : ℝ) + 1) ≤ (Fintype.card J : ℝ) * (1 - η) ^ 2 := by
    calc
      _ = (100 * ((m : ℝ) + 1)) * (1 / 4) := by ring
      _ ≤ (Fintype.card J : ℝ) * (1 - η) ^ 2 :=
        mul_le_mul hsize ha.1 (by norm_num) (le_of_lt hn)
  have hupper : ((m : ℝ) + 1) * ((1 - η) ^ 2 + 4) ≤
      ((m : ℝ) + 1) * (9 / 4 + 4) :=
    mul_le_mul_of_nonneg_left (by linarith only [ha.2]) (by positivity)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith only [hlower, hcancel, hupper, hm]

end ExplicitRIP.TwoDistanceBarrier
