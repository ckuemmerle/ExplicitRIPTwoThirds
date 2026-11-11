/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Defs

/-!
# Constructible images at algebraically closed field points

The point-level lifting step uses the strong Nullstellensatz for prime ideals.
It relates constructible sets in prime spectra to actual polynomial-coordinate
witnesses, which are needed for families of affine lines.
-/

public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- A polynomial outside a prime ideal is nonzero at some common zero of that ideal. -/
theorem exists_zero_of_prime_not_mem {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime] (g : MvPolynomial σ K) (hg : g ∉ I) :
    ∃ x : σ → K, (∀ f ∈ I, MvPolynomial.eval x f = 0) ∧ MvPolynomial.eval x g ≠ 0 := by
  by_contra h
  apply hg
  have hmem : g ∈ MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K I) := by
    intro x hx
    have hzero : ∀ f ∈ I, MvPolynomial.eval x f = 0 := by
      intro f hf
      simpa only [MvPolynomial.aeval_def, Algebra.algebraMap_self, MvPolynomial.eval₂_id]
        using hx f hf
    have hval : MvPolynomial.eval x g = 0 := by
      by_contra hxg
      exact h ⟨x, hzero, hxg⟩
    simpa only [MvPolynomial.aeval_def, Algebra.algebraMap_self, MvPolynomial.eval₂_id] using hval
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus] at hmem
  exact hmem

/-- A constructible set containing a prime contains a rational point specializing that prime. -/
theorem exists_point_specialization_in_constructible {σ : Type*} [Finite σ]
    (S : Set (PrimeSpectrum (MvPolynomial σ K))) (hS : Topology.IsConstructible S)
    (P : PrimeSpectrum (MvPolynomial σ K)) (hP : P ∈ S) :
    ∃ x : σ → K, (∀ f ∈ P.asIdeal, MvPolynomial.eval x f = 0) ∧
      MvPolynomial.pointToPoint (k := K) x ∈ S := by
  obtain ⟨data, rfl⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr hS
  obtain ⟨C, hC, hPC⟩ := Set.mem_iUnion₂.mp hP
  have hg : C.f ∉ P.asIdeal := by
    intro hgf
    exact hPC.2 ((PrimeSpectrum.mem_zeroLocus _ _).2 (Set.singleton_subset_iff.mpr hgf))
  obtain ⟨x, hx, hxg⟩ := exists_zero_of_prime_not_mem P.asIdeal C.f hg
  refine ⟨x, hx, Set.mem_iUnion₂.mpr ⟨C, hC, ?_⟩⟩
  constructor
  · apply (PrimeSpectrum.mem_zeroLocus _ _).2
    rintro f ⟨i, rfl⟩
    change C.g i ∈ MvPolynomial.vanishingIdeal K {x}
    apply (MvPolynomial.mem_vanishingIdeal_singleton_iff _ _).2
    have hgi := (PrimeSpectrum.mem_zeroLocus _ _).1 hPC.1 (Set.mem_range_self i)
    simpa only [MvPolynomial.aeval_def, Algebra.algebraMap_self, MvPolynomial.eval₂_id]
      using hx _ hgi
  · intro hzero
    have hfmem := (PrimeSpectrum.mem_zeroLocus _ _).1 hzero (Set.mem_singleton C.f)
    change C.f ∈ MvPolynomial.vanishingIdeal K {x} at hfmem
    apply hxg
    simpa only [MvPolynomial.aeval_def, Algebra.algebraMap_self, MvPolynomial.eval₂_id] using
      (MvPolynomial.mem_vanishingIdeal_singleton_iff _ _).1 hfmem

omit [IsAlgClosed K] in
/-- The prime of a projected point is the comap of the prime of the point. -/
theorem pointToPoint_comp {σ τ : Type*} (j : σ → τ) (x : τ → K) :
    PrimeSpectrum.comap (MvPolynomial.rename j).toRingHom (MvPolynomial.pointToPoint (k := K) x) =
      MvPolynomial.pointToPoint (k := K) (x ∘ j) := by
  apply PrimeSpectrum.ext
  ext f
  change MvPolynomial.rename j f ∈ MvPolynomial.vanishingIdeal K {x} ↔
    f ∈ MvPolynomial.vanishingIdeal K {x ∘ j}
  simp only [MvPolynomial.mem_vanishingIdeal_singleton_iff, MvPolynomial.aeval_def,
    Algebra.algebraMap_self, MvPolynomial.eval₂_id, MvPolynomial.eval_rename]

/-- A constructible prime-spectrum projection over a rational point has a rational lift. -/
theorem exists_point_lift_of_comap_mem {σ τ : Type*} [Finite σ] [Finite τ]
    (S : Set (PrimeSpectrum (MvPolynomial (σ ⊕ τ) K))) (hS : Topology.IsConstructible S)
    (x : σ → K)
    (hx : MvPolynomial.pointToPoint (k := K) x ∈
      PrimeSpectrum.comap (MvPolynomial.rename Sum.inl).toRingHom '' S) :
    ∃ y : τ → K, MvPolynomial.pointToPoint (k := K) (Sum.elim x y) ∈ S := by
  obtain ⟨P, hP, hPx⟩ := hx
  obtain ⟨z, hz, hzS⟩ := exists_point_specialization_in_constructible S hS P hP
  have hzleft : ∀ i : σ, z (Sum.inl i) = x i := by
    intro i
    have hrel : MvPolynomial.X (Sum.inl i) - MvPolynomial.C (x i) ∈ P.asIdeal := by
      have hmem : MvPolynomial.X i - MvPolynomial.C (x i) ∈
          (MvPolynomial.pointToPoint (k := K) x).asIdeal := by
        change _ ∈ MvPolynomial.vanishingIdeal K {x}
        simp only [MvPolynomial.mem_vanishingIdeal_singleton_iff,
          map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, Algebra.algebraMap_self,
          RingHom.id_apply, sub_self]
      rw [← hPx] at hmem
      change MvPolynomial.rename Sum.inl (MvPolynomial.X i - MvPolynomial.C (x i)) ∈
        P.asIdeal at hmem
      simpa only [map_sub, MvPolynomial.rename_X, MvPolynomial.rename_C] using hmem
    have hval := hz _ hrel
    simpa only [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, sub_eq_zero] using hval
  refine ⟨z ∘ Sum.inr, ?_⟩
  have heq : Sum.elim x (z ∘ Sum.inr) = z := by
    funext i
    cases i with
    | inl i => exact (hzleft i).symm
    | inr j => rfl
  rw [heq]
  exact hzS

/-- Renaming into a finite polynomial ring is a homomorphism of finite presentation. -/
theorem finitePresentation_rename {σ τ : Type*} [Finite σ] [Finite τ] (j : σ → τ) :
    (MvPolynomial.rename (R := K) j).toRingHom.FinitePresentation := by
  apply RingHom.FinitePresentation.of_finiteType.mp
  apply RingHom.FiniteType.of_comp_finiteType (f := MvPolynomial.C)
  have hcomp : (MvPolynomial.rename (R := K) j).toRingHom.comp MvPolynomial.C =
      MvPolynomial.C := by
    apply RingHom.ext
    intro c
    exact MvPolynomial.rename_C j c
  rw [hcomp]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- Chevalley's theorem expressed as actual coordinate witnesses over an algebraically closed
field. -/
theorem constructible_projection_at_points {σ τ : Type*} [Finite σ] [Finite τ]
    (S : Set (PrimeSpectrum (MvPolynomial (σ ⊕ τ) K))) (hS : Topology.IsConstructible S) :
    ∃ T : Set (PrimeSpectrum (MvPolynomial σ K)), Topology.IsConstructible T ∧
      ∀ x : σ → K, MvPolynomial.pointToPoint (k := K) x ∈ T ↔
        ∃ y : τ → K, MvPolynomial.pointToPoint (k := K) (Sum.elim x y) ∈ S := by
  refine ⟨PrimeSpectrum.comap (MvPolynomial.rename Sum.inl).toRingHom '' S,
    PrimeSpectrum.isConstructible_comap_image (finitePresentation_rename Sum.inl) hS, ?_⟩
  intro x
  refine ⟨exists_point_lift_of_comap_mem S hS x, ?_⟩
  rintro ⟨y, hy⟩
  refine ⟨MvPolynomial.pointToPoint (k := K) (Sum.elim x y), hy, ?_⟩
  rw [pointToPoint_comp]
  rfl

end ExplicitRIP.GuthZahl.RuledSurfaces
end
