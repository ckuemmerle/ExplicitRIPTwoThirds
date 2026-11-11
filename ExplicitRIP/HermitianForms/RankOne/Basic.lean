/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.HermitianForms.Defs.RankOneSet
public import ExplicitRIP.Algebra.ZModNonsquare

/-!
# Rank-one Hermitian matrices in coordinates

The elementary rank and determinant calculation identifies nonzero rank-one Hermitian matrices
with `ac = b₁² + b₂²`. Under the sphere map these are the nonzero isotropic vectors for the
quadratic form of [KM, Section 4.1].
-/

@[expose] public section

namespace ExplicitRIP.Rank1

open scoped Matrix

theorem matrix_rank_eq_zero_iff {F : Type*} [Field F]
    (M : Matrix (Fin 2) (Fin 2) F) : M.rank = 0 ↔ M = 0 := by
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
  constructor
  · intro h
    apply Matrix.toLin'.injective
    simpa only [Matrix.toLin'_apply', Matrix.mulVecLin_zero] using h
  · rintro rfl
    exact Matrix.mulVecLin_zero

theorem matrix_rank_eq_two_iff {F : Type*} [Field F]
    (M : Matrix (Fin 2) (Fin 2) F) : M.rank = 2 ↔ M.det ≠ 0 := by
  change M.rank = Fintype.card (Fin 2) ↔ M.det ≠ 0
  rw [← Matrix.mulVec_surjective_iff_rank_eq_card,
    Matrix.mulVec_surjective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

theorem matrix_rank_eq_one_iff {F : Type*} [Field F]
    (M : Matrix (Fin 2) (Fin 2) F) : M.rank = 1 ↔ M ≠ 0 ∧ M.det = 0 := by
  have hr := M.rank_le_width
  have hzero := matrix_rank_eq_zero_iff M
  have htwo := matrix_rank_eq_two_iff M
  constructor
  · intro h
    constructor
    · intro hM
      have hz := hzero.mpr hM
      omega
    · by_contra hd
      have ht := htwo.mpr hd
      omega
  · rintro ⟨hM, hd⟩
    have hz : M.rank ≠ 0 := fun h => hM (hzero.mp h)
    have ht : M.rank ≠ 2 := fun h => htwo.mp h hd
    omega

variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

theorem hermitian_det (K : ZMod p × ZMod p × ZMod p × ZMod p) :
    (hermitianMatrix p K).det =
      (⟨K.1 * K.2.2.2 - (K.2.1 ^ 2 + K.2.2.1 ^ 2), 0⟩ :
        QuadraticAlgebra (ZMod p) (-1) 0) := by
  rw [hermitianMatrix, Matrix.det_fin_two]
  ext <;> simp <;> ring

theorem hermitian_eq_zero_iff (K : ZMod p × ZMod p × ZMod p × ZMod p) :
    hermitianMatrix p K = 0 ↔
      K.1 = 0 ∧ K.2.1 = 0 ∧ K.2.2.1 = 0 ∧ K.2.2.2 = 0 := by
  constructor
  · intro h
    have he (i j : Fin 2) : hermitianMatrix p K i j = 0 :=
      congrFun (congrFun h i) j
    exact ⟨congrArg QuadraticAlgebra.re (he 0 0),
      congrArg QuadraticAlgebra.re (he 0 1),
      congrArg QuadraticAlgebra.im (he 0 1),
      congrArg QuadraticAlgebra.re (he 1 1)⟩
  · rintro ⟨ha, hb, hc, hd⟩
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      apply QuadraticAlgebra.ext <;> simp [hermitianMatrix, ha, hb, hc, hd]

theorem sum_sq_eq_zero_iff (b c : ZMod p) : b ^ 2 + c ^ 2 = 0 ↔ b = 0 ∧ c = 0 := by
  have h := QuadraticAlgebra.norm_eq_zero_iff_eq_zero
    (z := (⟨b, c⟩ : QuadraticAlgebra (ZMod p) (-1) 0))
  simpa [QuadraticAlgebra.norm_def, QuadraticAlgebra.ext_iff, pow_two] using h

theorem rank_one_iff_coordinates (K : ZMod p × ZMod p × ZMod p × ZMod p) :
    (hermitianMatrix p K).rank = 1 ↔
      (K.1 ≠ 0 ∧ K.2.2.2 = (K.2.1 ^ 2 + K.2.2.1 ^ 2) / K.1) ∨
        (K.1 = 0 ∧ K.2.1 = 0 ∧ K.2.2.1 = 0 ∧ K.2.2.2 ≠ 0) := by
  rw [matrix_rank_eq_one_iff, hermitian_det]
  simp only [ne_eq, hermitian_eq_zero_iff, QuadraticAlgebra.ext_iff, QuadraticAlgebra.re_zero,
    QuadraticAlgebra.im_zero, and_true, sub_eq_zero]
  by_cases ha : K.1 = 0
  · simp only [ha, zero_mul, not_true_eq_false, false_and,
      true_and, false_or, eq_comm (a := (0 : ZMod p))]
    rw [sum_sq_eq_zero_iff]
    tauto
  · simp only [ha, false_and, or_false, true_and, not_false_eq_true]
    rw [eq_div_iff ha, mul_comm K.2.2.2]

theorem mem_rankOneSet_iff (K : ZMod p × ZMod p × ZMod p × ZMod p) :
    K ∈ rankOneSet p ↔
      (K.1 ≠ 0 ∧ K.2.2.2 = (K.2.1 ^ 2 + K.2.2.1 ^ 2) / K.1) ∨
        (K.1 = 0 ∧ K.2.1 = 0 ∧ K.2.2.1 = 0 ∧ K.2.2.2 ≠ 0) := by
  classical
  simpa only [rankOneSet, Finset.mem_filter, Finset.mem_univ, true_and]
    using rank_one_iff_coordinates p K

theorem neg_mem_rankOneSet (K : ZMod p × ZMod p × ZMod p × ZMod p)
    (hK : K ∈ rankOneSet p) : -K ∈ rankOneSet p := by
  rw [mem_rankOneSet_iff] at hK ⊢
  rcases hK with ⟨ha, hd⟩ | ⟨ha, hb, hc, hd⟩
  · left
    exact ⟨by simpa using ha, by simpa [neg_sq, div_neg] using congrArg Neg.neg hd⟩
  · right
    simpa using And.intro ha (And.intro hb (And.intro hc hd))

end ExplicitRIP.Rank1
