/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# Real tight frames from scaled projections

A real symmetric matrix with `G * G = c • G`, `c > 0`, and trace `c * m`
has an `m`-row Gram factor whose rows are orthogonal with squared norm `c`.
-/

public section

open Matrix
open scoped BigOperators Matrix

namespace ExplicitRIP.HostFrame

/-- The eigenvalues of a symmetric scaled projection are zero or its scale. -/
theorem eigenvalues_eq_zero_or_scale {V : Type*} [Fintype V] [DecidableEq V]
    {G : Matrix V V ℝ} (hG : G.IsHermitian) {c : ℝ} (hsq : G * G = c • G)
    (i : V) : hG.eigenvalues i = 0 ∨ hG.eigenvalues i = c := by
  have hd := congrArg (Unitary.conjStarAlgAut ℝ (Matrix V V ℝ)
    (star hG.eigenvectorUnitary)) hsq
  simp only [map_mul, map_smul, hG.conjStarAlgAut_star_eigenvectorUnitary,
    RCLike.ofReal_real_eq_id, Function.id_comp] at hd
  have hi := congrArg (fun M : Matrix V V ℝ => M i i) hd
  simp only [diagonal_mul_diagonal, diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul] at hi
  have hz : hG.eigenvalues i * (hG.eigenvalues i - c) = 0 := by nlinarith only [hi]
  rcases mul_eq_zero.mp hz with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- Counting the nonzero eigenvalues by the trace gives the prescribed row count. -/
theorem card_nonzero_eigenvalues {V : Type*} [Fintype V] [DecidableEq V]
    {G : Matrix V V ℝ} (hG : G.IsHermitian) {c : ℝ} (hc : c ≠ 0)
    (hsq : G * G = c • G) (m : ℕ) (htrace : G.trace = c * m) :
    Fintype.card {i // hG.eigenvalues i ≠ 0} = m := by
  classical
  have he : ∀ i : {i // hG.eigenvalues i ≠ 0}, hG.eigenvalues i = c := by
    intro i
    exact (eigenvalues_eq_zero_or_scale hG hsq i).resolve_left i.property
  have hz : ∀ i : {i // ¬ hG.eigenvalues i ≠ 0}, hG.eigenvalues i = 0 := by
    intro i
    exact not_ne_iff.mp i.property
  rw [hG.trace_eq_sum_eigenvalues,
    ← Fintype.sum_subtype_add_sum_subtype (fun i => hG.eigenvalues i ≠ 0)] at htrace
  simp only [RCLike.ofReal_real_eq_id, id_eq, he, hz, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_zero, add_zero] at htrace
  have hcard : (Fintype.card {i // hG.eigenvalues i ≠ 0} : ℝ) = m := by
    apply (mul_right_cancel₀ hc)
    simpa only [mul_comm] using htrace
  exact_mod_cast hcard

/-- A symmetric scaled projection has a real tight-frame Gram factor. -/
theorem exists_tight_frame_of_scaled_projection {V : Type*} [Fintype V]
    (G : Matrix V V ℝ) (hG : G.IsHermitian) (c : ℝ) (hc : 0 < c)
    (hsq : G * G = c • G) (m : ℕ) (htrace : G.trace = c * m) :
    ∃ B : Matrix (Fin m) V ℝ, Bᵀ * B = G ∧ B * Bᵀ = c • (1 : Matrix (Fin m) (Fin m) ℝ) := by
  classical
  let U : Matrix V V ℝ := hG.eigenvectorUnitary
  let C : Matrix {i // hG.eigenvalues i ≠ 0} V ℝ := fun i j => Real.sqrt c * U j i
  have hroot : Real.sqrt c * Real.sqrt c = c := by
    simpa only [pow_two] using Real.sq_sqrt hc.le
  have he : ∀ i : {i // hG.eigenvalues i ≠ 0}, hG.eigenvalues i = c := by
    intro i
    exact (eigenvalues_eq_zero_or_scale hG hsq i).resolve_left i.property
  have hz : ∀ i : {i // ¬ hG.eigenvalues i ≠ 0}, hG.eigenvalues i = 0 := by
    intro i
    exact not_ne_iff.mp i.property
  have hU : Uᵀ * U = 1 := by
    simpa only [U, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hG.eigenvectorUnitary
  have hspec : G = U * diagonal hG.eigenvalues * Uᵀ := by
    simpa only [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id,
      Function.id_comp, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hG.spectral_theorem
  have hCC : C * Cᵀ =
      c • (1 : Matrix {i // hG.eigenvalues i ≠ 0} {i // hG.eigenvalues i ≠ 0} ℝ) := by
    ext i j
    have hu := congrArg (fun M : Matrix V V ℝ => M i j) hU
    simp only [mul_apply, transpose_apply] at hu
    calc
      (C * Cᵀ) i j = c * ∑ k, U k i * U k j := by
        rw [Matrix.mul_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        change (Real.sqrt c * U k i) * (Real.sqrt c * U k j) = c * (U k i * U k j)
        calc
          _ = (Real.sqrt c * Real.sqrt c) * (U k i * U k j) := by ring
          _ = _ := by rw [hroot]
      _ = c * (1 : Matrix V V ℝ) i j := by rw [hu]
      _ = (c • (1 : Matrix {i // hG.eigenvalues i ≠ 0} {i // hG.eigenvalues i ≠ 0} ℝ)) i j := by
        simp only [Matrix.smul_apply, smul_eq_mul, one_apply, Subtype.val_inj]
  have hCtC : Cᵀ * C = G := by
    apply Eq.trans _ hspec.symm
    ext i j
    change (∑ k : {i // hG.eigenvalues i ≠ 0}, C k i * C k j) =
      (U * diagonal hG.eigenvalues * Uᵀ) i j
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (fun k => hG.eigenvalues k ≠ 0) (fun k => U i k * hG.eigenvalues k * U j k)
    simp only [he, hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero] at hsplit
    rw [← hsplit]
    apply Finset.sum_congr rfl
    intro k _
    change (Real.sqrt c * U i k) * (Real.sqrt c * U j k) = U i k * c * U j k
    calc
      _ = (Real.sqrt c * Real.sqrt c) * (U i k * U j k) := by ring
      _ = _ := by rw [hroot]; ring
  have hcard : Fintype.card {i // hG.eigenvalues i ≠ 0} = m :=
    card_nonzero_eigenvalues hG hc.ne' hsq m htrace
  let e : Fin m ≃ {i // hG.eigenvalues i ≠ 0} := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨C.submatrix e id, ?_, ?_⟩
  · simpa only [transpose_submatrix, submatrix_mul_equiv, submatrix_id_id] using hCtC
  · rw [transpose_submatrix, ← submatrix_mul C Cᵀ e id e Function.bijective_id, hCC]
    change c • ((1 : Matrix _ _ ℝ).submatrix e e) = c • (1 : Matrix (Fin m) (Fin m) ℝ)
    rw [Matrix.submatrix_one_equiv]

end ExplicitRIP.HostFrame
