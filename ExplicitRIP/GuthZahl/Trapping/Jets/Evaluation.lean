/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Trapping.Defs
import ExplicitRIP.GuthZahl.Basic.Restriction

/-!
# Line substitution and directional differentiation

Substituting `x + t v` into the coefficient variables, with constant direction
variables `v`, carries the literal direction derivative to ordinary polynomial
differentiation. These identities do not divide by any factorial.
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl

theorem derivative_restrictLine_eq_sum {K : Type*} [Field K]
    (f : Poly K) (x v : Point K) :
    Polynomial.derivative (restrictLine f x v) =
      ∑ i : Fin 3, Polynomial.C (v i) * restrictLine (MvPolynomial.pderiv i f) x v := by
  classical
  let R : Poly K →+* Polynomial K := MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X)
  change Polynomial.derivative (R f) =
    ∑ i : Fin 3, Polynomial.C (v i) * R (MvPolynomial.pderiv i f)
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [MvPolynomial.eval₂Hom_C, Polynomial.derivative_C, MvPolynomial.derivation_C,
      MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_zero, mul_zero, Finset.sum_const_zero, R]
  | add f g hf hg =>
    simp only [map_add, hf, hg, mul_add, Finset.sum_add_distrib]
  | mul_X f n hf =>
    simp only [map_mul, Polynomial.derivative_mul, hf, MvPolynomial.pderiv_mul, map_add,
      mul_add, Finset.sum_add_distrib]
    rw [Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      ring
    · have hX : Polynomial.derivative (R (MvPolynomial.X n)) = Polynomial.C (v n) := by
        simp only [R, MvPolynomial.eval₂Hom_X', Polynomial.derivative_add,
          Polynomial.derivative_C, Polynomial.derivative_C_mul_X, zero_add]
      rw [hX]
      symm
      calc
        _ = Polynomial.C (v n) * (R f * R (MvPolynomial.pderiv n (MvPolynomial.X n))) := by
          apply Finset.sum_eq_single n
          · intro i _ hin
            rw [MvPolynomial.pderiv_X_of_ne hin.symm, map_zero, mul_zero, mul_zero]
          · intro hn
            exact (hn (Finset.mem_univ n)).elim
        _ = R f * Polynomial.C (v n) := by
          rw [MvPolynomial.pderiv_X_self, map_one, mul_one]
          exact mul_comm _ _

/-- Substitute a line in the coefficient variables and fix the direction variables. -/
noncomputable def restrictDirection {K : Type*} [Field K]
    (H : DirectionPoly K) (x v : Point K) : Polynomial K :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.eval₂Hom Polynomial.C
      (fun i => Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X))
    (fun i => Polynomial.C (v i)) H

theorem restrictDirection_eq_sum {K : Type*} [Field K]
    (H : DirectionPoly K) (x v : Point K) :
    restrictDirection H x v =
      ∑ a ∈ H.support,
        Polynomial.C (∏ i : Fin 3, v i ^ a i) * restrictLine (H.coeff a) x v := by
  classical
  unfold restrictDirection
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq']
  apply Finset.sum_congr rfl
  intro a _
  simp only [map_prod, map_pow, restrictLine]
  exact mul_comm _ _

theorem restrictDirection_directionDeriv {K : Type*} [Field K]
    (H : DirectionPoly K) (x v : Point K) :
    restrictDirection (directionDeriv H) x v =
      Polynomial.derivative (restrictDirection H x v) := by
  classical
  rw [restrictDirection_eq_sum H, Polynomial.derivative_sum]
  simp only [Polynomial.derivative_C_mul, derivative_restrictLine_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold directionDeriv restrictDirection
  simp only [map_sum, map_mul, MvPolynomial.eval₂Hom_X',
    MvPolynomial.eval₂Hom_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  rw [Finsupp.prod_pow]
  simp only [map_prod, map_pow, restrictLine]
  ring

theorem eval_zero_restrictDirection {K : Type*} [Field K]
    (H : DirectionPoly K) (x v : Point K) :
    Polynomial.eval 0 (restrictDirection H x v) = evalDirection H x v := by
  classical
  rw [restrictDirection_eq_sum, evalDirection, ← MvPolynomial.eval₂_eq_eval_map,
    MvPolynomial.eval₂_eq']
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_C_mul, eval_restrictLine,
    zero_smul, add_zero]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

theorem restrictDirection_directionJet {K : Type*} [Field K]
    (f : Poly K) (x v : Point K) (j : ℕ) :
    restrictDirection (directionJet f j) x v =
      Polynomial.derivative^[j] (restrictLine f x v) := by
  classical
  induction j with
  | zero =>
    simp only [restrictDirection, directionJet, MvPolynomial.eval₂Hom_C,
      MvPolynomial.coe_eval₂Hom, restrictLine, Function.iterate_zero, id_eq]
  | succ j ih =>
    rw [directionJet, restrictDirection_directionDeriv, ih,
      Function.iterate_succ_apply']

end ExplicitRIP.GuthZahl

end
