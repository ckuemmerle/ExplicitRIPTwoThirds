/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.LevDR.OperatorBound

/-!
# Proof of [KM, (5)]: the logarithmic discrete Rayleigh comparison

Source: [KM, Section 2.1, (5)].

Finite Abel summation and a complex coordinate decomposition give an absolute multiplier of `32`
in the comparison `‖M‖_{2→2} ≤ 32 log(2k) ‖M‖_DR` for complex matrices indexed by a finite set
of size `k`.
-/

public section

open scoped Matrix

namespace ExplicitRIP.Lev

theorem one_add_log_le_two_log_two_mul {n : ℕ} (hn : 1 ≤ n) :
    1 + Real.log (n : ℝ) ≤ 2 * Real.log (2 * (n : ℝ)) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have htwo : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hn0)]
  linarith only [htwo, hlog]

end ExplicitRIP.Lev

/-- The operator norm is bounded by an absolute multiple of the discrete Rayleigh norm
and the logarithm of twice the dimension. -/
theorem ExplicitRIP.Provider.lev_dr_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ),
      ExplicitRIP.opNorm M ≤ C * Real.log (2 * Fintype.card ι) * ExplicitRIP.drNorm M := by
  refine ⟨32, by norm_num, ?_⟩
  intro ι _ _ M
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let := hι
      have hM : M = 0 := Subsingleton.elim _ _
      simp only [hM, ExplicitRIP.opNorm, map_zero, norm_zero,
        Fintype.card_of_isEmpty, Nat.cast_zero, mul_zero, Real.log_zero, zero_mul, le_refl]
  | inr hι =>
      let := hι
      have hn : 1 ≤ Fintype.card ι := Nat.succ_le_of_lt Fintype.card_pos
      calc
        _ ≤ 16 * ExplicitRIP.drNorm M * (1 + Real.log (Fintype.card ι : ℝ)) :=
          ExplicitRIP.Lev.op_norm_le_dr_norm M
        _ ≤ 16 * ExplicitRIP.drNorm M * (2 * Real.log (2 * Fintype.card ι)) :=
          mul_le_mul_of_nonneg_left
            (ExplicitRIP.Lev.one_add_log_le_two_log_two_mul hn)
            (mul_nonneg (by norm_num) (ExplicitRIP.Lev.dr_norm_nonneg M))
        _ = 32 * Real.log (2 * Fintype.card ι) * ExplicitRIP.drNorm M := by ring
