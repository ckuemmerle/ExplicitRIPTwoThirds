/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.HermitianForms.Defs.HostGram

/-!
# Uniform bounds for the host parameters

The row count and adjacent and nonadjacent Gram magnitudes in [KM, (13)] satisfy elementary bounds
sufficient for the construction barrier and the quantitative RIP estimate [KM, (16)].
-/

@[expose] public section

open scoped Matrix BigOperators

namespace ExplicitRIP.Actbar

/-- The number of rows of the host frame. -/
def rowCount (p : ℕ) : ℕ := (p - 1) * (p ^ 2 + 1)

/-- Magnitude of an adjacent off-diagonal Gram entry. -/
noncomputable def largeEntry (p : ℕ) : ℝ :=
  ((p : ℝ) ^ 2 - p + 1) / (((p : ℝ) - 1) * ((p : ℝ) ^ 2 + 1))

/-- The nonadjacent off-diagonal Gram entry. -/
noncomputable def smallEntry (p : ℕ) : ℝ := 1 / ((p : ℝ) ^ 2 + 1)

theorem rowCount_cast {p : ℕ} (hp : 1 ≤ p) :
    (rowCount p : ℝ) = ((p : ℝ) - 1) * ((p : ℝ) ^ 2 + 1) := by
  simp only [rowCount, Nat.cast_mul, Nat.cast_sub hp, Nat.cast_one, Nat.cast_add,
    Nat.cast_pow]

theorem rowCount_pos {p : ℕ} (hp : 2 ≤ p) : 0 < rowCount p := by
  exact Nat.mul_pos (by omega) (by positivity)

theorem cube_le_two_rowCount {p : ℕ} (hp : 2 ≤ p) :
    (p : ℝ) ^ 3 ≤ 2 * (rowCount p : ℝ) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  rw [rowCount_cast (by omega)]
  nlinarith only [mul_nonneg (sq_nonneg (p : ℝ)) (sub_nonneg.mpr hp'), hp']

theorem largeEntry_nonneg {p : ℕ} (hp : 2 ≤ p) : 0 ≤ largeEntry p := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  apply div_nonneg
  · nlinarith only [sq_nonneg ((p : ℝ) - 1)]
  · exact mul_nonneg (by linarith) (by positivity)

theorem one_le_two_mul_largeEntry {p : ℕ} (hp : 2 ≤ p) :
    1 ≤ 2 * (p : ℝ) * largeEntry p := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hd : 0 < ((p : ℝ) - 1) * ((p : ℝ) ^ 2 + 1) :=
    mul_pos (by linarith) (by positivity)
  rw [largeEntry, ← mul_div_assoc, le_div_iff₀ hd]
  nlinarith only [mul_nonneg (sq_nonneg (p : ℝ)) (sub_nonneg.mpr hp'), hp']

theorem one_le_four_mul_sq_largeEntry {p : ℕ} (hp : 2 ≤ p) :
    1 ≤ 4 * (p : ℝ) ^ 2 * largeEntry p ^ 2 := by
  have h := one_le_two_mul_largeEntry hp
  have hs := sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ 2 * (p : ℝ) * largeEntry p)
    |>.2 h
  nlinarith only [hs]

theorem host_card_le (p : ℕ) [Fact p.Prime]
    (Γ : Finset (ZMod p × ZMod p × ZMod p × ZMod p)) : Γ.card ≤ p ^ 4 := by
  have h := Finset.card_le_univ Γ
  simpa only [Fintype.card_prod, ZMod.card, pow_succ, pow_zero, mul_one, one_mul, mul_assoc] using h

theorem small_energy_le_one {p n : ℕ} (hn : n ≤ p ^ 4) :
    (n : ℝ) * smallEntry p ^ 2 ≤ 1 := by
  have hn' : (n : ℝ) ≤ (p : ℝ) ^ 4 := by exact_mod_cast hn
  have hd : 0 < (p : ℝ) ^ 2 + 1 := by positivity
  rw [smallEntry, div_pow, one_pow, ← mul_div_assoc, div_le_iff₀ (sq_pos_of_pos hd)]
  nlinarith only [hn', sq_nonneg (p : ℝ)]

theorem sq_le_four_rowCount_rpow {p : ℕ} (hp : 2 ≤ p) :
    (p : ℝ) ^ 2 ≤ 4 * (rowCount p : ℝ) ^ (2 / 3 : ℝ) := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ rowCount p := Nat.cast_nonneg _
  have hc : ((p : ℝ) / 2) ^ 3 ≤ (rowCount p : ℝ) := by
    have h := cube_le_two_rowCount hp
    nlinarith only [h, hm0]
  have h := Real.rpow_le_rpow (pow_nonneg (div_nonneg hp0 (by norm_num)) 3) hc
    (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have heq : (((p : ℝ) / 2) ^ 3 : ℝ) ^ (2 / 3 : ℝ) = ((p : ℝ) / 2) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hp0 (by norm_num))]
    norm_num
  rw [heq] at h
  nlinarith only [h]

open Classical in
theorem hostGram_offdiag (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
    (v w : ZMod p × ZMod p × ZMod p × ZMod p) (hvw : v ≠ w) :
    hermitianHostGram ℝ p v w =
      if (hermitianGraph p).Adj v w then -largeEntry p else smallEntry p := by
  classical
  by_cases hadj : (hermitianGraph p).Adj v w
  · simp [hermitianHostGram, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply_ne hvw, SimpleGraph.adjMatrix_apply, largeEntry, hadj]
  · simp [hermitianHostGram, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply_ne hvw, SimpleGraph.adjMatrix_apply, smallEntry, hadj]

/-- The dimension ratio cannot vanish while the prime parameter stays bounded. -/
theorem selected_ratio_le_two_mul (p : ℕ) [Fact p.Prime]
    (Γ : Finset (ZMod p × ZMod p × ZMod p × ZMod p)) :
    (Γ.card : ℝ) / rowCount p ≤ 2 * (p : ℝ) := by
  have hp := (Fact.out : p.Prime).two_le
  have hm : (0 : ℝ) < rowCount p := Nat.cast_pos.mpr (rowCount_pos hp)
  have hn : (Γ.card : ℝ) ≤ (p : ℝ) ^ 4 := by exact_mod_cast host_card_le p Γ
  have hc := mul_le_mul_of_nonneg_left (cube_le_two_rowCount hp) (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
  apply (div_le_iff₀ hm).2
  nlinarith only [hn, hc]

end ExplicitRIP.Actbar
