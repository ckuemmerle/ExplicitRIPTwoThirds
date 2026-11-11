/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Jets.Defs
import ExplicitRIP.GuthZahl.Jets.Constructible.Boolean

/-!
# Constructible projections and finite Boolean descriptions over the integers

Chevalley's theorem makes the image of a finite system of integer polynomial
equations constructible. A finite constructible description then supplies one
list of polynomial tests, retaining both equations and inequalities.
-/

public section

namespace ExplicitRIP.GuthZahl

open Classical in
/-- Finite-presentation projection, applied over Z once. -/
theorem integer_equation_image_constructible {σ τ : Type*} [Finite σ] [Finite τ]
    (k : ℕ) (F : Fin k → MvPolynomial (σ ⊕ τ) ℤ) :
    Topology.IsConstructible
      (PrimeSpectrum.comap (MvPolynomial.rename (Sum.inl : σ → σ ⊕ τ)).toRingHom ''
        equationPrimeLocus F) := by
  apply PrimeSpectrum.isConstructible_comap_image
  · apply RingHom.FinitePresentation.of_comp_finiteType
      (algebraMap ℤ (MvPolynomial σ ℤ))
    · have hcomp : (MvPolynomial.rename (Sum.inl : σ → σ ⊕ τ)).toRingHom.comp
          (algebraMap ℤ (MvPolynomial σ ℤ)) =
            algebraMap ℤ (MvPolynomial (σ ⊕ τ) ℤ) := by
        apply RingHom.ext
        intro z
        exact (MvPolynomial.rename (Sum.inl : σ → σ ⊕ τ)).commutes z
      rw [hcomp]
      exact RingHom.finitePresentation_algebraMap.mpr inferInstance
    · apply RingHom.FiniteType.of_finitePresentation
      exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  · have h : equationPrimeLocus F = PrimeSpectrum.zeroLocus (Set.range F) := by
      ext P
      simp only [equationPrimeLocus, Set.mem_ofPred_eq, PrimeSpectrum.mem_zeroLocus,
        Set.range_subset_iff, SetLike.mem_coe]
    rw [h]
    exact ((PrimeSpectrum.isRetrocompact_zeroLocus_compl (Set.finite_range F)).isConstructible
      (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl).of_compl

open Classical in
/-- Encode a constructible subset by one finite Boolean list, including inequalities. -/
theorem integer_constructible_boolean {σ : Type*}
    (S : Set (PrimeSpectrum (MvPolynomial σ ℤ))) (hS : Topology.IsConstructible S) :
    ∃ J : ℕ, ∃ q : Fin J → MvPolynomial σ ℤ, ∃ B : Set (Fin J → Bool),
      ∀ P : PrimeSpectrum (MvPolynomial σ ℤ),
        P ∈ S ↔ (fun j => decide (q j ∈ P.asIdeal)) ∈ B :=
  Constructible.exists_boolean_description S hS

end ExplicitRIP.GuthZahl

end
