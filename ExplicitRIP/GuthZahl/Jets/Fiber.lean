/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Jets.Defs

/-!
# Algebraic fibers and points of integer polynomial systems

The weak Nullstellensatz turns a proper finite system over an algebraically closed field
into a point. A prime over an evaluation kernel gives a nontrivial residue-field fiber;
extending scalars preserves nontriviality. Applying this to the prime quotient proves that
specializing the integer equations at the chosen parameters leaves a proper ideal.

Together these statements identify the spectrum projection with existence of a point
in the auxiliary variables over the given algebraically closed field.
-/

public section

namespace ExplicitRIP.GuthZahl

open Classical in
/-- Weak Nullstellensatz for a finite system (independent of integer geometry). -/
theorem finite_equations_have_point {τ K : Type*} [Finite τ]
    [Field K] [IsAlgClosed K] (k : ℕ) (F : Fin k → MvPolynomial τ K) :
    Ideal.span (Set.range F) ≠ ⊤ ↔ ∃ y : τ → K, ∀ i, MvPolynomial.eval y (F i) = 0 := by
  constructor
  · intro h
    obtain ⟨M, hM, hFM⟩ := Ideal.exists_le_maximal (Ideal.span (Set.range F)) h
    obtain ⟨y, hy⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hM
    refine ⟨y, fun i => ?_⟩
    have hi := hFM (Ideal.subset_span (Set.mem_range_self i))
    rw [hy, MvPolynomial.mem_vanishingIdeal_singleton_iff] at hi
    exact hi
  · rintro ⟨y, hy⟩
    have hle : Ideal.span (Set.range F) ≤ RingHom.ker (MvPolynomial.eval y) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hy i
    exact ne_top_of_le_ne_top (RingHom.ker_ne_top (MvPolynomial.eval y)) hle

open Classical in
/-- The nonempty algebraic fiber remains nonempty after the chosen field extension. Use the
residue-field fiber criterion and tensor cancellation. -/
theorem baseChange_nontrivial_of_prime_over {R S K : Type*}
    [CommRing R] [CommRing S] [Field K] [Algebra R S] [Algebra R K]
    (P : PrimeSpectrum S)
    (hP : Ideal.comap (algebraMap R S) P.asIdeal = RingHom.ker (algebraMap R K)) :
    Nontrivial (TensorProduct R K S) := by
  let p : PrimeSpectrum R := ⟨RingHom.ker (algebraMap R K), RingHom.ker_isPrime _⟩
  have : p.asIdeal.IsPrime := p.isPrime
  have hmem : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R S)) :=
    ⟨P, PrimeSpectrum.ext hP⟩
  have : Nontrivial (TensorProduct R p.asIdeal.ResidueField S) :=
    (PrimeSpectrum.nontrivial_iff_mem_rangeComap p).mpr hmem
  let f : p.asIdeal.ResidueField →ₐ[R] K :=
    Ideal.ResidueField.liftₐ p.asIdeal (Algebra.ofId R K) le_rfl (by
      intro r hr
      change IsUnit (algebraMap R K r)
      exact isUnit_iff_ne_zero.mpr hr)
  let : Algebra p.asIdeal.ResidueField K := f.toRingHom.toAlgebra
  have : IsScalarTower R p.asIdeal.ResidueField K := IsScalarTower.of_algHom f
  have : Nontrivial (TensorProduct p.asIdeal.ResidueField K
      (TensorProduct R p.asIdeal.ResidueField S)) := inferInstance
  exact
    (Algebra.TensorProduct.cancelBaseChange R p.asIdeal.ResidueField K K S).symm.toEquiv.nontrivial

open Classical in
/-- Choose a maximal ideal, use Zariski's lemma, and embed its residue field in K. This is
qualitative and has no complexity assertion. -/
theorem finiteType_algClosed_point (K A : Type*) [Field K] [IsAlgClosed K]
    [CommRing A] [Algebra K A] [Algebra.FiniteType K A] [Nontrivial A] :
    Nonempty (A →ₐ[K] K) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  let : M.IsMaximal := hM
  let : Field (A ⧸ M) := Ideal.Quotient.field M
  have : Module.Finite K (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ M)
  exact ⟨(IsAlgClosed.lift : (A ⧸ M) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K M)⟩

open Classical in
/-- Evaluation after specializing the parameter variables equals evaluation of the original integer
polynomial. -/
theorem specializeParameters_eval {σ τ K : Type*} [Field K]
    (x : σ → K) (y : τ → K) (F : MvPolynomial (σ ⊕ τ) ℤ) :
    MvPolynomial.eval y (specializeParameters x F) =
      MvPolynomial.eval₂ (Int.castRingHom K) (Sum.elim x y) F := by
  unfold specializeParameters
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval_eval₂]
  congr 1
  · exact Subsingleton.elim _ _
  · funext i
    cases i <;> simp only [Sum.elim_inl, Sum.elim_inr,
      MvPolynomial.eval_C, MvPolynomial.eval_X]

open Classical in
/-- Identify the quotient of the specialized system with the scalar extension of the universal
fiber. The residue-field fiber criterion supplies nontriviality after scalar extension. -/
theorem integer_projection_proper_specialization {σ τ K : Type*}
    [Finite σ] [Finite τ] [Field K]
    (k : ℕ) (F : Fin k → MvPolynomial (σ ⊕ τ) ℤ) (x : σ → K)
    (hx : integerEvaluationPrime x ∈
      PrimeSpectrum.comap (MvPolynomial.rename (Sum.inl : σ → σ ⊕ τ)).toRingHom ''
        equationPrimeLocus F) :
    Ideal.span (Set.range (fun i => specializeParameters x (F i))) ≠ ⊤ := by
  obtain ⟨P, hPF, hPx⟩ := hx
  let R := MvPolynomial σ ℤ
  let S := MvPolynomial (σ ⊕ τ) ℤ
  let : Algebra R S :=
    (MvPolynomial.rename (Sum.inl : σ → σ ⊕ τ)).toRingHom.toAlgebra
  let : Algebra R K := (MvPolynomial.eval₂Hom (Int.castRingHom K) x).toAlgebra
  let Q := S ⧸ P.asIdeal
  have hP : Ideal.comap (algebraMap R S) P.asIdeal = RingHom.ker (algebraMap R K) :=
    congrArg PrimeSpectrum.asIdeal hPx
  have hQ : Ideal.comap (algebraMap R Q) (⊥ : Ideal Q) =
      RingHom.ker (algebraMap R K) := by
    ext r
    change Ideal.Quotient.mk P.asIdeal (algebraMap R S r) = 0 ↔
      algebraMap R K r = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (Ideal.ext_iff.mp hP) r
  let T := TensorProduct R K Q
  have : Nontrivial T := baseChange_nontrivial_of_prime_over
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Q) hQ
  let q : S →ₐ[R] T :=
    (Algebra.TensorProduct.includeRight : Q →ₐ[R] T).comp
      (Ideal.Quotient.mkₐ R P.asIdeal)
  let g : MvPolynomial τ K →+* T :=
    MvPolynomial.eval₂Hom (algebraMap K T) (fun j => q (MvPolynomial.X (Sum.inr j)))
  let sp : S →+* MvPolynomial τ K :=
    MvPolynomial.eval₂Hom (MvPolynomial.C.comp (Int.castRingHom K))
      (Sum.elim (fun i => MvPolynomial.C (x i)) MvPolynomial.X)
  have hcomp : g.comp sp = q.toRingHom := by
    apply MvPolynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · intro i
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      cases i with
      | inl i =>
        simp only [RingHom.comp_apply, sp, MvPolynomial.eval₂Hom_X', Sum.elim_inl,
          g, MvPolynomial.eval₂Hom_C]
        have h := q.commutes (MvPolynomial.X i : R)
        change q (MvPolynomial.rename Sum.inl (MvPolynomial.X i)) = _ at h
        rw [MvPolynomial.rename_X, IsScalarTower.algebraMap_apply R K T] at h
        change q (MvPolynomial.X (Sum.inl i)) = algebraMap K T
          (MvPolynomial.eval₂Hom (Int.castRingHom K) x (MvPolynomial.X i)) at h
        simpa only [MvPolynomial.eval₂Hom_X'] using h.symm
      | inr j =>
        simp only [RingHom.comp_apply, sp, MvPolynomial.eval₂Hom_X', Sum.elim_inr, g]
  -- The specialized ideal maps to zero in the nontrivial tensor extension of the prime quotient.
  have hle : Ideal.span (Set.range (fun i => specializeParameters x (F i))) ≤
      RingHom.ker g := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change g (sp (F i)) = 0
    rw [← RingHom.comp_apply, hcomp]
    change (Algebra.TensorProduct.includeRight : Q →ₐ[R] T)
      (Ideal.Quotient.mk P.asIdeal (F i)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hPF i), map_zero]
  exact ne_top_of_le_ne_top (RingHom.ker_ne_top g) hle

open Classical in
/-- A point belongs to the projected integer spectrum locus exactly when the auxiliary equations
have a solution over the algebraically closed field. -/
theorem integer_projection_at_algClosed_point {σ τ K : Type*}
    [Finite σ] [Finite τ] [Field K] [IsAlgClosed K]
    (k : ℕ) (F : Fin k → MvPolynomial (σ ⊕ τ) ℤ) (x : σ → K) :
    integerEvaluationPrime x ∈
      PrimeSpectrum.comap (MvPolynomial.rename (Sum.inl : σ → σ ⊕ τ)).toRingHom ''
        equationPrimeLocus F ↔
      ∃ y : τ → K, ∀ i,
        MvPolynomial.eval₂ (Int.castRingHom K) (Sum.elim x y) (F i) = 0 := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (finite_equations_have_point k
      (fun i => specializeParameters x (F i))).mp
        (integer_projection_proper_specialization k F x hx)
    exact ⟨y, fun i => (specializeParameters_eval x y (F i)) ▸ hy i⟩
  · rintro ⟨y, hy⟩
    let e : MvPolynomial (σ ⊕ τ) ℤ →+* K :=
      MvPolynomial.eval₂Hom (Int.castRingHom K) (Sum.elim x y)
    refine ⟨⟨RingHom.ker e, RingHom.ker_isPrime e⟩, hy, ?_⟩
    apply PrimeSpectrum.ext
    change Ideal.comap (MvPolynomial.rename (Sum.inl : σ → σ ⊕ τ)).toRingHom
      (RingHom.ker e) = RingHom.ker (MvPolynomial.eval₂Hom (Int.castRingHom K) x)
    rw [RingHom.comap_ker]
    congr 1
    apply MvPolynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · intro i
      change e (MvPolynomial.rename (Sum.inl : σ → σ ⊕ τ) (MvPolynomial.X i)) =
        MvPolynomial.eval₂Hom (Int.castRingHom K) x (MvPolynomial.X i)
      rw [MvPolynomial.rename_X]
      simp only [e, MvPolynomial.eval₂Hom_X', Sum.elim_inl]

end ExplicitRIP.GuthZahl

end
