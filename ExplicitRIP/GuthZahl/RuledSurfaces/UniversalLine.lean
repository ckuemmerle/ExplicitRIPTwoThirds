/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.RuledSurfaces.Restriction
public import ExplicitRIP.GuthZahl.RuledSurfaces.ConstructiblePoints
public import ExplicitRIP.GuthZahl.RuledSurfaces.LineChart

/-!
# Polynomial equations for line parameters

Substituting polynomial base and direction coordinates into a surface equation
produces a univariate polynomial with polynomial coefficients. Evaluating these
coefficients recovers the ordinary line restriction.
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K] {σ : Type*}

/-- Universal restriction with polynomial base and direction coordinates. -/
noncomputable def universalRestriction (f : Poly K)
    (a v : Fin 3 → MvPolynomial σ K) : Polynomial (MvPolynomial σ K) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun i => Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) f

/-- Specializing polynomial line parameters gives the ordinary restriction. -/
theorem map_universalRestriction (f : Poly K) (a v : Fin 3 → MvPolynomial σ K)
    (z : σ → K) :
    Polynomial.map (MvPolynomial.eval z) (universalRestriction f a v) =
      restrictLine f (fun i => MvPolynomial.eval z (a i))
        (fun i => MvPolynomial.eval z (v i)) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [universalRestriction, restrictLine_C]
  | add f g hf hg =>
    simpa only [universalRestriction, map_add, Polynomial.map_add, restrictLine_add] using
      congrArg₂ (· + ·) hf hg
  | mul_X f i hf =>
    simp only [universalRestriction, map_mul, Polynomial.map_mul, Polynomial.map_add,
      MvPolynomial.eval₂Hom_X', Polynomial.map_C, Polynomial.map_X,
      restrictLine_mul, restrictLine_X] at *
    rw [hf]

/-- Each coefficient of the restriction is polynomial in its line parameters. -/
theorem eval_coeff_universalRestriction (f : Poly K)
    (a v : Fin 3 → MvPolynomial σ K) (z : σ → K) (n : ℕ) :
    MvPolynomial.eval z ((universalRestriction f a v).coeff n) =
      (restrictLine f (fun i => MvPolynomial.eval z (a i))
        (fun i => MvPolynomial.eval z (v i))).coeff n := by
  rw [← map_universalRestriction f a v z, Polynomial.coeff_map]

/-- Substituting polynomial coordinates and evaluating is ordinary evaluation at those
coordinates. -/
theorem eval_substitute_coordinates (f : Poly K) (a : Fin 3 → MvPolynomial σ K)
    (z : σ → K) :
    MvPolynomial.eval z (MvPolynomial.eval₂Hom MvPolynomial.C a f) =
      MvPolynomial.eval (fun i => MvPolynomial.eval z (a i)) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.eval₂Hom_C, MvPolynomial.eval_C]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf => simp only [map_mul, MvPolynomial.eval₂Hom_X', MvPolynomial.eval_X, hf]

/-- Algebraic line containment is constructible in polynomial line parameters. -/
theorem isPolynomialConstructible_restriction_zero (f : Poly K)
    (a v : Fin 3 → MvPolynomial σ K) :
    IsPolynomialConstructible {z : σ → K |
      restrictLine f (fun i => MvPolynomial.eval z (a i))
        (fun i => MvPolynomial.eval z (v i)) = 0} := by
  have htest := IsPolynomialConstructible.forall_finite
    (fun n : Fin (f.totalDegree + 1) =>
      {z : σ → K | MvPolynomial.eval z ((universalRestriction f a v).coeff n) = 0})
    (fun n => isPolynomialConstructible_zero _)
  convert htest using 1
  ext z
  simp only [Set.mem_ofPred_eq, eval_coeff_universalRestriction]
  constructor
  · intro hz n
    rw [hz, Polynomial.coeff_zero]
  · intro hz
    apply polynomial_eq_zero_of_coeff_le _ _ (restrictLine_natDegree_le _ _ _)
    intro n hn
    exact hz ⟨n, by omega⟩

/-- Evaluation on a line gives polynomial nonvanishing conditions in any parameter space. -/
theorem isPolynomialConstructible_eval_ne_zero (f : Poly K)
    (a : Fin 3 → MvPolynomial σ K) :
    IsPolynomialConstructible {z : σ → K |
      MvPolynomial.eval (fun i => MvPolynomial.eval z (a i)) f ≠ 0} := by
  simpa only [eval_substitute_coordinates] using
    isPolynomialConstructible_nonzero (MvPolynomial.eval₂Hom MvPolynomial.C a f)

end ExplicitRIP.GuthZahl.RuledSurfaces
end
