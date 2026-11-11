/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.CommonLines.Substitution

/-!
# Counting affine graphs on a plane curve

A generic vertical slice separates any finite family of different affine
graphs and leaves a nonzero plane polynomial nonzero. Univariate root counting
then bounds the family by the total degree of the plane polynomial.
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl.CommonLines

open scoped BigOperators

theorem exists_mvPolynomial_eval_ne_zero {K σ : Type*} [CommRing K] [IsDomain K]
    [Infinite K] (p : MvPolynomial σ K) (hp : p ≠ 0) :
    ∃ x, MvPolynomial.eval x p ≠ 0 := by
  by_contra! h
  apply hp
  apply MvPolynomial.funext
  intro x
  simpa only [map_zero] using h x

/-- Specialize the first coordinate of a plane polynomial. -/
noncomputable def planeSlice {K : Type*} [CommSemiring K]
    (p : MvPolynomial (Fin 2) K) (t : K) : Polynomial K :=
  p.eval₂ Polynomial.C ![Polynomial.C t, Polynomial.X]

theorem eval_planeSlice {K : Type*} [CommSemiring K]
    (p : MvPolynomial (Fin 2) K) (t y : K) :
    (planeSlice p t).eval y = MvPolynomial.eval ![t, y] p := by
  rw [planeSlice, MvPolynomial.polynomial_eval_eval₂]
  congr 1
  · ext c
    simp
  · ext i
    fin_cases i <;> simp

theorem natDegree_planeSlice_le {K : Type*} [CommSemiring K]
    (p : MvPolynomial (Fin 2) K) (t : K) :
    (planeSlice p t).natDegree ≤ p.totalDegree := by
  apply natDegree_eval₂_le
  intro i
  fin_cases i
  · change (Polynomial.C t).natDegree ≤ 1
    simp only [Polynomial.natDegree_C, Nat.zero_le]
  · exact Polynomial.natDegree_X_le

theorem card_le_totalDegree_of_graphs {K ι : Type*} [Field K] [Infinite K] [Fintype ι]
    (a b : ι → K) (hab : Function.Injective (fun i => (a i, b i)))
    (R : MvPolynomial (Fin 2) K) (hR : R ≠ 0)
    (hvanish : ∀ i t, MvPolynomial.eval ![t, a i + t * b i] R = 0) :
    Fintype.card ι ≤ R.totalDegree := by
  classical
  let I := {ij : ι × ι // ij.1 ≠ ij.2}
  let H : I → MvPolynomial (Fin 2) K := fun ij =>
    (MvPolynomial.C (a ij.val.1) + MvPolynomial.X 0 * MvPolynomial.C (b ij.val.1)) -
    (MvPolynomial.C (a ij.val.2) + MvPolynomial.X 0 * MvPolynomial.C (b ij.val.2))
  have hH : ∀ ij, H ij ≠ 0 := by
    intro ij h
    have h₀ := congrArg (MvPolynomial.eval (0 : Fin 2 → K)) h
    have h₁ := congrArg (MvPolynomial.eval (1 : Fin 2 → K)) h
    simp only [H, map_sub, map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      Pi.zero_apply, zero_mul, add_zero, map_zero, sub_eq_zero] at h₀
    simp only [H, map_sub, map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      Pi.one_apply, one_mul, map_zero, sub_eq_zero, h₀, add_right_inj] at h₁
    exact ij.property (hab (Prod.ext h₀ h₁))
  have hprod : R * ∏ ij, H ij ≠ 0 :=
    mul_ne_zero hR (Finset.prod_ne_zero_iff.mpr fun ij _ => hH ij)
  obtain ⟨x, hx⟩ := exists_mvPolynomial_eval_ne_zero _ hprod
  have hxmul : MvPolynomial.eval x R * MvPolynomial.eval x (∏ ij, H ij) ≠ 0 := by
    simpa only [map_mul] using hx
  have hxR : MvPolynomial.eval x R ≠ 0 := (mul_ne_zero_iff.mp hxmul).1
  have hxH : ∀ ij, MvPolynomial.eval x (H ij) ≠ 0 := by
    have hh := (mul_ne_zero_iff.mp hxmul).2
    rw [map_prod] at hh
    exact fun ij => (Finset.prod_ne_zero_iff.mp hh) ij (Finset.mem_univ _)
  have hxy : ![x 0, x 1] = x := by ext i; fin_cases i <;> rfl
  have hslice : planeSlice R (x 0) ≠ 0 := by
    intro h
    apply hxR
    have he := congrArg (Polynomial.eval (x 1)) h
    simpa only [eval_planeSlice, Polynomial.eval_zero, hxy] using he
  have hinj : Function.Injective (fun i => a i + x 0 * b i) := by
    intro i j hij
    by_contra hne
    apply hxH ⟨(i, j), hne⟩
    simpa only [H, map_sub, map_add, map_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X, sub_eq_zero] using hij
  by_contra hcard
  apply hslice
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hinj
  · intro i
    rw [eval_planeSlice]
    exact hvanish i (x 0)
  · exact (natDegree_planeSlice_le R (x 0)).trans_lt (Nat.lt_of_not_ge hcard)

end ExplicitRIP.GuthZahl.CommonLines
end
