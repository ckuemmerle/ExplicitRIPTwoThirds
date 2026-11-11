/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Defs

/-!
# Guth–Zahl line route: definitions for the jets branch

Finite Hasse jets encode polynomial restrictions without factorial division.
Integer polynomial systems and their specialization express the condition of having
two distinct tangent directions uniformly over fields.

* `JetIndex`
* `jetExponent`
* `translatedPolynomial`
* `hasseCoefficient`
* `finiteJet`
* `jetDirectionCoefficient`
* `JetTwoDirections`
* `integerZeroPattern`
* `integerEvaluationPrime`
* `equationPrimeLocus`
* `specializeParameters`
* `jetPullback`
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl

open Classical in
abbrev JetIndex (r : ℕ) :=
  {a : Fin 3 → Fin (r + 1) // (∑ i, (a i).val) ≤ r}

open Classical in
noncomputable def jetExponent {r : ℕ} (a : JetIndex r) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (a.val i).val)

open Classical in
/-- Coefficients in the outer variables y of the literal polynomial f(x+y). -/
noncomputable def translatedPolynomial {K : Type*} [Field K]
    (f : Poly K) : MvPolynomial (Fin 3) (Poly K) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (MvPolynomial.C : K →+* Poly K))
    (fun i => MvPolynomial.C (MvPolynomial.X i) + MvPolynomial.X i) f

open Classical in
noncomputable def hasseCoefficient {K : Type*} [Field K]
    (f : Poly K) (a : Fin 3 →₀ ℕ) : Poly K := (translatedPolynomial f).coeff a

open Classical in
noncomputable def finiteJet {K : Type*} [Field K] (r : ℕ)
    (f : Poly K) (x : Point K) : JetIndex r → K :=
  fun a => MvPolynomial.eval x (hasseCoefficient f (jetExponent a))

open Classical in
noncomputable def jetDirectionCoefficient {K : Type*} [Field K] {r : ℕ}
    (J : JetIndex r → K) (v : Point K) (j : ℕ) : K :=
  ∑ a : JetIndex r, if (∑ i, (a.val i).val) = j then
    J a * ∏ i : Fin 3, v i ^ (a.val i).val else 0

open Classical in
def JetTwoDirections {K : Type*} [Field K] {r : ℕ} (J : JetIndex r → K) : Prop :=
  ∃ v w : Point K, v ≠ 0 ∧ w ≠ 0 ∧ (¬ ∃ a : K, w = a • v) ∧
    (∀ j ≤ r, jetDirectionCoefficient J v j = 0) ∧
    (∀ j ≤ r, jetDirectionCoefficient J w j = 0)

open Classical in
noncomputable def integerZeroPattern {σ : Type*} {J : ℕ}
    (q : Fin J → MvPolynomial σ ℤ) {K : Type*} [Field K] (x : σ → K) : Fin J → Bool :=
  fun j => decide (MvPolynomial.eval₂ (Int.castRingHom K) x (q j) = 0)

open Classical in
noncomputable def integerEvaluationPrime {σ K : Type*} [Field K]
    (x : σ → K) : PrimeSpectrum (MvPolynomial σ ℤ) :=
  ⟨RingHom.ker (MvPolynomial.eval₂Hom (Int.castRingHom K) x), RingHom.ker_isPrime _⟩

open Classical in
def equationPrimeLocus {σ τ : Type*} {k : ℕ}
    (F : Fin k → MvPolynomial (σ ⊕ τ) ℤ) :
    Set (PrimeSpectrum (MvPolynomial (σ ⊕ τ) ℤ)) :=
  {P | ∀ i, F i ∈ P.asIdeal}

open Classical in
noncomputable def specializeParameters {σ τ K : Type*} [Field K]
    (x : σ → K) (F : MvPolynomial (σ ⊕ τ) ℤ) : MvPolynomial τ K :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (Int.castRingHom K))
    (Sum.elim (fun i => MvPolynomial.C (x i)) MvPolynomial.X) F

open Classical in
noncomputable def jetPullback {K : Type*} [Field K] (r : ℕ)
    (f : Poly K) (q : MvPolynomial (JetIndex r) ℤ) : Poly K :=
  MvPolynomial.eval₂Hom (Int.castRingHom (Poly K))
    (fun a => hasseCoefficient f (jetExponent a)) q

end ExplicitRIP.GuthZahl

end
