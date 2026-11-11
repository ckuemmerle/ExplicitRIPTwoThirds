/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Boundary.Descent.Polynomial

/-!
# Uniqueness of a quadric through a skew triple

In coordinates adapted to three skew lines, nine quadratic coefficients are
fixed and the remaining equation is a scalar multiple of the determinant.
-/

public section

namespace ExplicitRIP.GuthZahl.Boundary.Descent

variable {K : Type*} [Field K]

/-- Three affine parameter values suffice to homogenize a quadratic identity. -/
theorem determinantFour_span_eq_zero (h2 : (2 : K) ≠ 0) (a b : Fin 4 → K)
    (h : ∀ t : K, determinantFour (a + t • b) = 0) (s t : K) :
    determinantFour (s • a + t • b) = 0 := by
  have h0 := h 0
  have hp := h 1
  have hm := h (-1)
  apply (mul_eq_zero.mp (show 2 * determinantFour (s • a + t • b) = 0 from ?_)).resolve_left h2
  simp only [determinantFour, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    zero_mul, one_mul, neg_one_mul, add_zero] at h0 hp hm ⊢
  linear_combination 2 * (s ^ 2 - t ^ 2) * h0 +
    (t ^ 2 + s * t) * hp + (t ^ 2 - s * t) * hm

theorem determinantFour_of_nine_zero (a b c d : Fin 4 → K)
    (ha : determinantFour a = 0) (hb : determinantFour b = 0)
    (hc : determinantFour c = 0) (hd : determinantFour d = 0)
    (hab : determinantFour (a + b) = 0) (hcd : determinantFour (c + d) = 0)
    (hac : determinantFour (a + c) = 0) (hbd : determinantFour (b + d) = 0)
    (hall : determinantFour (a + b + c + d) = 0) (x : Fin 4 → K) :
    determinantFour (x 0 • a + x 1 • b + x 2 • c + x 3 • d) =
      determinantFour (a + d) * determinantFour x := by
  simp only [determinantFour, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  linear_combination
    (x 0 ^ 2 - x 0 * x 3 - x 0 * x 1 - x 0 * x 2 + 2 * x 1 * x 2) * ha +
    (x 1 ^ 2 - x 0 * x 1 - x 1 * x 3 + x 1 * x 2) * hb +
    (x 2 ^ 2 - x 0 * x 2 - x 2 * x 3 + x 1 * x 2) * hc +
    (x 3 ^ 2 - x 0 * x 3 - x 1 * x 3 - x 2 * x 3 + 2 * x 1 * x 2) * hd +
    (x 0 * x 1 - x 1 * x 2) * hab + (x 2 * x 3 - x 1 * x 2) * hcd +
    (x 0 * x 2 - x 1 * x 2) * hac + (x 1 * x 3 - x 1 * x 2) * hbd +
    x 1 * x 2 * hall

/-- Coordinates preserving the two coordinate planes and their diagonal preserve the
determinant up to a nonzero scalar. -/
theorem determinantFour_comp_eq_scalar (T : Zahl.SplitQuadric K)
    (hleft : ∀ a b : K, determinantFour (T ![a, b, 0, 0]) = 0)
    (hright : ∀ a b : K, determinantFour (T ![0, 0, a, b]) = 0)
    (hdiag : ∀ a b : K, determinantFour (T ![a, b, a, b]) = 0) :
    ∃ c : K, c ≠ 0 ∧ ∀ v, determinantFour (T v) = c * determinantFour v := by
  let a := T ![1, 0, 0, 0]
  let b := T ![0, 1, 0, 0]
  let c := T ![0, 0, 1, 0]
  let d := T ![0, 0, 0, 1]
  have hab : a + b = T ![1, 1, 0, 0] := by
    rw [← map_add]; congr 1; ext i; fin_cases i <;> simp
  have hcd : c + d = T ![0, 0, 1, 1] := by
    rw [← map_add]; congr 1; ext i; fin_cases i <;> simp
  have hac : a + c = T ![1, 0, 1, 0] := by
    rw [← map_add]; congr 1; ext i; fin_cases i <;> simp
  have hbd : b + d = T ![0, 1, 0, 1] := by
    rw [← map_add]; congr 1; ext i; fin_cases i <;> simp
  have hall : a + b + c + d = T ![1, 1, 1, 1] := by
    rw [← map_add, ← map_add, ← map_add]
    congr 1; ext i; fin_cases i <;> simp
  have hrep (v : Fin 4 → K) : T v = v 0 • a + v 1 • b + v 2 • c + v 3 • d := by
    rw [← map_smul, ← map_smul, ← map_smul, ← map_smul,
      ← map_add, ← map_add, ← map_add]
    congr 1; ext i; fin_cases i <;> simp
  have heq (v : Fin 4 → K) :
      determinantFour (T v) = determinantFour (a + d) * determinantFour v := by
    rw [hrep]
    exact determinantFour_of_nine_zero a b c d
      (hleft 1 0) (hleft 0 1) (hright 1 0) (hright 0 1)
      (hab ▸ hleft 1 1) (hcd ▸ hright 1 1) (hac ▸ hdiag 1 0)
      (hbd ▸ hdiag 0 1) (hall ▸ hdiag 1 1) v
  refine ⟨determinantFour (a + d), ?_, heq⟩
  intro hz
  have h := heq (T.symm ![1, 0, 0, 1])
  rw [T.apply_symm_apply, hz, zero_mul] at h
  norm_num [determinantFour] at h

end ExplicitRIP.GuthZahl.Boundary.Descent

end
