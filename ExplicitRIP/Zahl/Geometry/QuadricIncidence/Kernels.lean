/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Geometry.Rulings.Kernels

/-!
# Common kernels of a singular matrix pencil

Two singular two-by-two matrices whose mixed determinant vanishes have a
common left or right kernel. The first matrix is assumed nonzero.
-/

public section

namespace ExplicitRIP.Zahl.Geometry.QuadricIncidence

variable {K : Type*} [Field K]

/-- Elimination at a nonzero upper-left entry of the first matrix. -/
theorem singular_pair_dichotomy (a b c d e f g h : K) (ha : a ≠ 0)
    (hA : a * d - b * c = 0) (hB : e * h - f * g = 0)
    (hAB : a * h + e * d - b * g - f * c = 0) :
    (a * g - c * e = 0 ∧ a * h - c * f = 0) ∨
      (a * f - b * e = 0 ∧ a * h - b * g = 0) := by
  have hprod : (a * g - c * e) * (a * f - b * e) = 0 := by
    linear_combination -a ^ 2 * hB + a * e * hAB - e ^ 2 * hA
  rcases mul_eq_zero.mp hprod with hleft | hright
  · left
    refine ⟨hleft, (mul_eq_zero.mp ?_).resolve_left ha⟩
    change a * (a * h - c * f) = 0
    linear_combination a * hAB - e * hA + b * hleft
  · right
    refine ⟨hright, (mul_eq_zero.mp ?_).resolve_left ha⟩
    change a * (a * h - b * g) = 0
    linear_combination a * hAB - e * hA + c * hright

/-- A singular matrix pencil has a nonzero kernel on one fixed side. -/
theorem exists_common_rulingSpace (A B : Fin 4 → K) (hA0 : A ≠ 0)
    (hA : A 0 * A 3 - A 1 * A 2 = 0)
    (hB : B 0 * B 3 - B 1 * B 2 = 0)
    (hAB : A 0 * B 3 + B 0 * A 3 - A 1 * B 2 - B 1 * A 2 = 0) :
    ∃ side : Bool, ∃ c : Fin 2 → K, c ≠ 0 ∧
      A ∈ Rulings.rulingSpace side c ∧ B ∈ Rulings.rulingSpace side c := by
  by_cases h0 : A 0 = 0
  · by_cases h1 : A 1 = 0
    · by_cases h2 : A 2 = 0
      · have h3 : A 3 ≠ 0 := by
          intro h3
          apply hA0
          ext i
          fin_cases i <;> assumption
        have hb0 : B 0 = 0 := by
          apply (mul_eq_zero.mp ?_).resolve_right h3
          simpa only [h0, h1, h2, zero_mul, mul_zero, zero_add, sub_zero] using hAB
        have hb12 : B 1 * B 2 = 0 := by
          simpa only [hb0, zero_mul, zero_sub, neg_eq_zero] using hB
        rcases mul_eq_zero.mp hb12 with hb1 | hb2
        · refine ⟨false, ![1, 0], ?_, ?_, ?_⟩
          · intro h; exact one_ne_zero (congrFun h 0)
          · rw [Rulings.mem_leftSpace_iff]
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, zero_mul,
              add_zero, h0, h1, and_self]
          · rw [Rulings.mem_leftSpace_iff]
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, zero_mul,
              add_zero, hb0, hb1, and_self]
        · refine ⟨true, ![1, 0], ?_, ?_, ?_⟩
          · intro h; exact one_ne_zero (congrFun h 0)
          · rw [Rulings.mem_rightSpace_iff]
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero,
              add_zero, h0, h2, and_self]
          · rw [Rulings.mem_rightSpace_iff]
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero,
              add_zero, hb0, hb2, and_self]
      · have hmix : B 0 * A 3 - B 1 * A 2 = 0 := by
          simpa only [h0, h1, zero_mul, zero_add, sub_zero] using hAB
        by_cases hb0 : B 0 = 0
        · have hb1 : B 1 = 0 := by
            apply (mul_eq_zero.mp ?_).resolve_right h2
            simpa only [hb0, zero_mul, zero_sub, neg_eq_zero] using hmix
          refine ⟨false, ![1, 0], ?_, ?_, ?_⟩
          · intro h; exact one_ne_zero (congrFun h 0)
          · rw [Rulings.mem_leftSpace_iff]
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, zero_mul,
              add_zero, h0, h1, and_self]
          · rw [Rulings.mem_leftSpace_iff]
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, zero_mul,
              add_zero, hb0, hb1, and_self]
        · have hlast : B 2 * (-A 3) + B 3 * A 2 = 0 := by
            apply (mul_eq_zero.mp ?_).resolve_left hb0
            change B 0 * (B 2 * (-A 3) + B 3 * A 2) = 0
            linear_combination A 2 * hB - B 2 * hmix
          refine ⟨true, ![-A 3, A 2], ?_, ?_, ?_⟩
          · intro h; exact h2 (congrFun h 1)
          · rw [Rulings.mem_rightSpace_iff]
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
            constructor
            · rw [h0, h1, zero_mul, zero_mul, add_zero]
            · ring
          · rw [Rulings.mem_rightSpace_iff]
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
            exact ⟨by linear_combination -hmix, hlast⟩
    · have ha2 : A 2 = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_left h1
        simpa only [h0, zero_mul, zero_sub, neg_eq_zero] using hA
      have hmix : B 0 * A 3 - A 1 * B 2 = 0 := by
        simpa only [h0, ha2, zero_mul, mul_zero, zero_add, sub_zero] using hAB
      by_cases hb0 : B 0 = 0
      · have hb2 : B 2 = 0 := by
          apply (mul_eq_zero.mp ?_).resolve_left h1
          simpa only [hb0, zero_mul, zero_sub, neg_eq_zero] using hmix
        refine ⟨true, ![1, 0], ?_, ?_, ?_⟩
        · intro h; exact one_ne_zero (congrFun h 0)
        · rw [Rulings.mem_rightSpace_iff]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero,
            add_zero, h0, ha2, and_self]
        · rw [Rulings.mem_rightSpace_iff]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero,
            add_zero, hb0, hb2, and_self]
      · have hlast : (-A 3) * B 1 + A 1 * B 3 = 0 := by
          apply (mul_eq_zero.mp ?_).resolve_left hb0
          change B 0 * ((-A 3) * B 1 + A 1 * B 3) = 0
          linear_combination A 1 * hB - B 1 * hmix
        refine ⟨false, ![-A 3, A 1], ?_, ?_, ?_⟩
        · intro h; exact h1 (congrFun h 1)
        · rw [Rulings.mem_leftSpace_iff]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          constructor
          · rw [h0, ha2, mul_zero, mul_zero, add_zero]
          · ring
        · rw [Rulings.mem_leftSpace_iff]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          exact ⟨by linear_combination -hmix, hlast⟩
  · obtain hleft | hright := singular_pair_dichotomy
      (A 0) (A 1) (A 2) (A 3) (B 0) (B 1) (B 2) (B 3) h0 hA hB hAB
    · refine ⟨false, ![-A 2, A 0], ?_, ?_, ?_⟩
      · intro h; exact h0 (congrFun h 1)
      · rw [Rulings.mem_leftSpace_iff]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        exact ⟨by ring, by linear_combination hA⟩
      · rw [Rulings.mem_leftSpace_iff]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        exact ⟨by linear_combination hleft.1, by linear_combination hleft.2⟩
    · refine ⟨true, ![-A 1, A 0], ?_, ?_, ?_⟩
      · intro h; exact h0 (congrFun h 1)
      · rw [Rulings.mem_rightSpace_iff]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        exact ⟨by ring, by linear_combination hA⟩
      · rw [Rulings.mem_rightSpace_iff]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        exact ⟨by linear_combination hright.1, by linear_combination hright.2⟩

/-- Any nonzero left or right kernel forces the determinant to vanish. -/
theorem det_eq_zero_of_mem_rulingSpace (side : Bool) (a : Fin 2 → K)
    (ha : a ≠ 0) (v : Fin 4 → K) (hv : v ∈ Rulings.rulingSpace side a) :
    v 0 * v 3 - v 1 * v 2 = 0 := by
  cases side
  · rw [Rulings.mem_leftSpace_iff] at hv
    by_cases h0 : a 0 = 0
    · apply (mul_eq_zero.mp ?_).resolve_left (Rulings.coord_one_ne_zero a ha h0)
      change a 1 * (v 0 * v 3 - v 1 * v 2) = 0
      linear_combination v 0 * hv.2 - v 1 * hv.1
    · apply (mul_eq_zero.mp ?_).resolve_left h0
      change a 0 * (v 0 * v 3 - v 1 * v 2) = 0
      linear_combination v 3 * hv.1 - v 2 * hv.2
  · rw [Rulings.mem_rightSpace_iff] at hv
    by_cases h0 : a 0 = 0
    · apply (mul_eq_zero.mp ?_).resolve_left (Rulings.coord_one_ne_zero a ha h0)
      change a 1 * (v 0 * v 3 - v 1 * v 2) = 0
      linear_combination v 0 * hv.2 - v 2 * hv.1
    · apply (mul_eq_zero.mp ?_).resolve_left h0
      change a 0 * (v 0 * v 3 - v 1 * v 2) = 0
      linear_combination v 3 * hv.1 - v 1 * hv.2

end ExplicitRIP.Zahl.Geometry.QuadricIncidence
