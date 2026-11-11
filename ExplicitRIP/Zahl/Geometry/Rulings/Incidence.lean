/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Geometry.Rulings.Kernels

/-!
# Intersections of the two families of ruling subspaces

Fixed kernels on the same side determine equal spaces whenever their spaces
share a nonzero matrix. Opposite kernel spaces share an explicit outer product,
and a left kernel space cannot be contained in a right kernel space.
-/

@[expose] public section

namespace ExplicitRIP.Zahl.Rulings

variable {K : Type*} [Field K]

/-- Transposition in the four-coordinate presentation of a two by two matrix. -/
def transposeVector (v : Fin 4 → K) : Fin 4 → K := ![v 0, v 2, v 1, v 3]

omit [Field K] in
theorem transposeVector_involutive : Function.Involutive (transposeVector (K := K)) := by
  intro v
  ext i
  fin_cases i <;> rfl

theorem transposeVector_ne_zero {v : Fin 4 → K} (hv : v ≠ 0) : transposeVector v ≠ 0 := by
  intro h
  have hzero : transposeVector (0 : Fin 4 → K) = 0 := by
    ext i; fin_cases i <;> rfl
  exact hv (transposeVector_involutive.injective (h.trans hzero.symm))

theorem transposeVector_mem_leftSpace_iff (a : Fin 2 → K) (v : Fin 4 → K) :
    transposeVector v ∈ rulingSpace false a ↔ v ∈ rulingSpace true a := by
  simp [mem_leftSpace_iff, mem_rightSpace_iff, transposeVector, mul_comm]

theorem det_mul_eq_zero (a b : Fin 2 → K) (x y : K)
    (ha : a 0 * x + a 1 * y = 0) (hb : b 0 * x + b 1 * y = 0) :
    (a 0 * b 1 - a 1 * b 0) * x = 0 ∧ (a 0 * b 1 - a 1 * b 0) * y = 0 := by
  constructor
  · linear_combination b 1 * ha - a 1 * hb
  · linear_combination a 0 * hb - b 0 * ha

theorem dot_eq_zero_of_det_eq_zero (a b : Fin 2 → K) (ha : a ≠ 0)
    (hdet : a 0 * b 1 - a 1 * b 0 = 0) (x y : K)
    (h : a 0 * x + a 1 * y = 0) : b 0 * x + b 1 * y = 0 := by
  by_cases h₀ : a 0 = 0
  · have h₁ := coord_one_ne_zero a ha h₀
    apply (mul_eq_zero.mp (show a 1 * (b 0 * x + b 1 * y) = 0 from ?_)).resolve_left h₁
    linear_combination b 1 * h - x * hdet
  · apply (mul_eq_zero.mp (show a 0 * (b 0 * x + b 1 * y) = 0 from ?_)).resolve_left h₀
    linear_combination b 0 * h + y * hdet

theorem leftSpace_eq_of_nonzero_mem (a b : Fin 2 → K) (ha : a ≠ 0) (hb : b ≠ 0)
    (v : Fin 4 → K) (hv : v ≠ 0)
    (hva : v ∈ rulingSpace false a) (hvb : v ∈ rulingSpace false b) :
    rulingSpace false a = rulingSpace false b := by
  rw [mem_leftSpace_iff] at hva hvb
  have hdet : a 0 * b 1 - a 1 * b 0 = 0 := by
    by_contra hd
    have h₀ := det_mul_eq_zero a b (v 0) (v 2) hva.1 hvb.1
    have h₁ := det_mul_eq_zero a b (v 1) (v 3) hva.2 hvb.2
    apply hv
    ext i
    fin_cases i
    · exact (mul_eq_zero.mp h₀.1).resolve_left hd
    · exact (mul_eq_zero.mp h₁.1).resolve_left hd
    · exact (mul_eq_zero.mp h₀.2).resolve_left hd
    · exact (mul_eq_zero.mp h₁.2).resolve_left hd
  apply Submodule.eq_of_le_of_finrank_eq
  · intro w hw
    rw [mem_leftSpace_iff] at hw ⊢
    exact ⟨dot_eq_zero_of_det_eq_zero a b ha hdet _ _ hw.1,
      dot_eq_zero_of_det_eq_zero a b ha hdet _ _ hw.2⟩
  · rw [finrank_rulingSpace false a ha, finrank_rulingSpace false b hb]

theorem rulingSpace_eq_of_nonzero_mem (side : Bool) (a b : Fin 2 → K)
    (ha : a ≠ 0) (hb : b ≠ 0) (v : Fin 4 → K) (hv : v ≠ 0)
    (hva : v ∈ rulingSpace side a) (hvb : v ∈ rulingSpace side b) :
    rulingSpace side a = rulingSpace side b := by
  cases side
  · exact leftSpace_eq_of_nonzero_mem a b ha hb v hv hva hvb
  · have he := leftSpace_eq_of_nonzero_mem a b ha hb (transposeVector v)
      (transposeVector_ne_zero hv)
      ((transposeVector_mem_leftSpace_iff a v).mpr hva)
      ((transposeVector_mem_leftSpace_iff b v).mpr hvb)
    ext w
    rw [← transposeVector_mem_leftSpace_iff, ← transposeVector_mem_leftSpace_iff, he]

theorem not_leftSpace_le_rightSpace (a b : Fin 2 → K) (ha : a ≠ 0) (hb : b ≠ 0) :
    ¬ rulingSpace false a ≤ rulingSpace true b := by
  intro hle
  have h₀ : (![a 1, 0, -a 0, 0] : Fin 4 → K) ∈ rulingSpace true b := by
    apply hle
    rw [mem_leftSpace_iff]
    change (a 0 * a 1 + a 1 * (-a 0) = 0) ∧ (a 0 * 0 + a 1 * 0 = 0)
    constructor <;> ring
  have h₁ : (![0, a 1, 0, -a 0] : Fin 4 → K) ∈ rulingSpace true b := by
    apply hle
    rw [mem_leftSpace_iff]
    change (a 0 * 0 + a 1 * 0 = 0) ∧ (a 0 * a 1 + a 1 * (-a 0) = 0)
    constructor <;> ring
  rw [mem_rightSpace_iff] at h₀ h₁
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    zero_mul, add_zero, zero_add] at h₀ h₁
  apply hb
  ext i
  fin_cases i
  · by_cases ha₀ : a 0 = 0
    · exact (mul_eq_zero.mp h₀.1).resolve_left (coord_one_ne_zero a ha ha₀)
    · exact (mul_eq_zero.mp h₀.2).resolve_left (neg_ne_zero.mpr ha₀)
  · by_cases ha₀ : a 0 = 0
    · exact (mul_eq_zero.mp h₁.1).resolve_left (coord_one_ne_zero a ha ha₀)
    · exact (mul_eq_zero.mp h₁.2).resolve_left (neg_ne_zero.mpr ha₀)

/-- The outer product of the vectors perpendicular to the two kernel vectors. -/
def perpendicularProduct (a b : Fin 2 → K) : Fin 4 → K :=
  ![a 1 * b 1, -(a 1 * b 0), -(a 0 * b 1), a 0 * b 0]

theorem perpendicularProduct_ne_zero (a b : Fin 2 → K) (ha : a ≠ 0) (hb : b ≠ 0) :
    perpendicularProduct a b ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hb
  simp only [Pi.zero_apply] at hi hj
  intro h
  fin_cases i <;> fin_cases j
  · exact mul_ne_zero hi hj (congrFun h 3)
  · apply mul_ne_zero hi hj
    have hz := congrFun h 2
    simpa [perpendicularProduct] using hz
  · apply mul_ne_zero hi hj
    have hz := congrFun h 1
    simpa [perpendicularProduct] using hz
  · exact mul_ne_zero hi hj (congrFun h 0)

theorem perpendicularProduct_mem_leftSpace (a b : Fin 2 → K) :
    perpendicularProduct a b ∈ rulingSpace false a := by
  rw [mem_leftSpace_iff]
  simp only [perpendicularProduct, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  constructor <;> ring

theorem perpendicularProduct_mem_rightSpace (a b : Fin 2 → K) :
    perpendicularProduct a b ∈ rulingSpace true b := by
  rw [mem_rightSpace_iff]
  simp only [perpendicularProduct, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  constructor <;> ring

theorem exists_nonzero_mem_opposite (side : Bool) (a b : Fin 2 → K)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ v : Fin 4 → K, v ≠ 0 ∧ v ∈ rulingSpace side a ∧ v ∈ rulingSpace (!side) b := by
  cases side
  · exact ⟨perpendicularProduct a b, perpendicularProduct_ne_zero a b ha hb,
      perpendicularProduct_mem_leftSpace a b, perpendicularProduct_mem_rightSpace a b⟩
  · exact ⟨perpendicularProduct b a, perpendicularProduct_ne_zero b a hb ha,
      perpendicularProduct_mem_rightSpace b a, perpendicularProduct_mem_leftSpace b a⟩

end ExplicitRIP.Zahl.Rulings
