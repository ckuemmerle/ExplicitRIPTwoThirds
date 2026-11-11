/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.RuledSurfaces.Constructible
public import ExplicitRIP.GuthZahl.RuledSurfaces.OpenSet
public import ExplicitRIP.GuthZahl.RuledSurfaces.CommonLines

/-!
# Polynomial constructible sets and dense line families

Constructibility at field points is the pullback of constructibility in the
prime spectrum. A finite Boolean description is constant on a principal open
of an irreducible hypersurface after excluding its nonvanishing polynomials.
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K]

/-- Constructibility of a set of polynomial-coordinate points. -/
def IsPolynomialConstructible {σ : Type*} (S : Set (σ → K)) : Prop :=
  ∃ T : Set (PrimeSpectrum (MvPolynomial σ K)), Topology.IsConstructible T ∧
    S = MvPolynomial.pointToPoint (k := K) ⁻¹' T

/-- A basic constructible condition at a field point is a finite polynomial test. -/
theorem point_mem_basicConstructible_iff {σ : Type*}
    (C : PrimeSpectrum.BasicConstructibleSetData (MvPolynomial σ K)) (x : σ → K) :
    MvPolynomial.pointToPoint (k := K) x ∈ C.toSet ↔
      (∀ i, MvPolynomial.eval x (C.g i) = 0) ∧ MvPolynomial.eval x C.f ≠ 0 := by
  have hmem (p : MvPolynomial σ K) :
      p ∈ (MvPolynomial.pointToPoint (k := K) x).asIdeal ↔ MvPolynomial.eval x p = 0 := by
    change p ∈ MvPolynomial.vanishingIdeal K {x} ↔ _
    simp only [MvPolynomial.mem_vanishingIdeal_singleton_iff, MvPolynomial.aeval_def,
      Algebra.algebraMap_self, MvPolynomial.eval₂_id]
  change (_ ∈ PrimeSpectrum.zeroLocus (Set.range C.g) ∧
    _ ∉ PrimeSpectrum.zeroLocus {C.f}) ↔ _
  simp only [PrimeSpectrum.mem_zeroLocus, Set.range_subset_iff,
    Set.singleton_subset_iff, SetLike.mem_coe, hmem]

/-- The zero set of one polynomial is constructible at field points. -/
theorem isPolynomialConstructible_zero {σ : Type*} (p : MvPolynomial σ K) :
    IsPolynomialConstructible {x : σ → K | MvPolynomial.eval x p = 0} := by
  let C : PrimeSpectrum.BasicConstructibleSetData (MvPolynomial σ K) :=
    ⟨1, 1, fun _ => p⟩
  refine ⟨C.toSet, ?_, ?_⟩
  · have h := ( {C} : PrimeSpectrum.ConstructibleSetData (MvPolynomial σ K)).isConstructible_toSet
    simpa only [PrimeSpectrum.ConstructibleSetData.toSet, Finset.mem_singleton,
      Set.iUnion_iUnion_eq_left] using h
  · ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, point_mem_basicConstructible_iff,
      C, map_one, forall_const]
    exact ⟨fun h => ⟨h, one_ne_zero⟩, fun h => h.1⟩

/-- Boolean complements preserve polynomial constructibility. -/
theorem IsPolynomialConstructible.compl {σ : Type*} {S : Set (σ → K)}
    (hS : IsPolynomialConstructible S) : IsPolynomialConstructible Sᶜ := by
  obtain ⟨T, hT, rfl⟩ := hS
  exact ⟨Tᶜ, hT.compl, rfl⟩

/-- Finite intersections preserve polynomial constructibility. -/
theorem IsPolynomialConstructible.inter {σ : Type*} {S T : Set (σ → K)}
    (hS : IsPolynomialConstructible S) (hT : IsPolynomialConstructible T) :
    IsPolynomialConstructible (S ∩ T) := by
  obtain ⟨S', hS', rfl⟩ := hS
  obtain ⟨T', hT', rfl⟩ := hT
  exact ⟨S' ∩ T', hS'.inter hT', rfl⟩

/-- Finite unions preserve polynomial constructibility. -/
theorem IsPolynomialConstructible.union {σ : Type*} {S T : Set (σ → K)}
    (hS : IsPolynomialConstructible S) (hT : IsPolynomialConstructible T) :
    IsPolynomialConstructible (S ∪ T) := by
  obtain ⟨S', hS', rfl⟩ := hS
  obtain ⟨T', hT', rfl⟩ := hT
  exact ⟨S' ∪ T', hS'.union hT', rfl⟩

/-- A finite conjunction of constructible predicates is constructible. -/
theorem IsPolynomialConstructible.forall_finite {σ ι : Type*} [Finite ι]
    (S : ι → Set (σ → K)) (hS : ∀ i, IsPolynomialConstructible (S i)) :
    IsPolynomialConstructible {x : σ → K | ∀ i, x ∈ S i} := by
  classical
  choose T hT heq using hS
  refine ⟨⋂ i, T i, Topology.IsConstructible.iInter hT, ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_iInter, heq]

/-- A finite disjunction of constructible predicates is constructible. -/
theorem IsPolynomialConstructible.exists_finite {σ ι : Type*} [Finite ι]
    (S : ι → Set (σ → K)) (hS : ∀ i, IsPolynomialConstructible (S i)) :
    IsPolynomialConstructible {x : σ → K | ∃ i, x ∈ S i} := by
  classical
  choose T hT heq using hS
  refine ⟨⋃ i, T i, Topology.IsConstructible.iUnion hT, ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_iUnion, heq]

/-- A polynomial nonvanishing condition is constructible. -/
theorem isPolynomialConstructible_nonzero {σ : Type*} (p : MvPolynomial σ K) :
    IsPolynomialConstructible {x : σ → K | MvPolynomial.eval x p ≠ 0} :=
  (isPolynomialConstructible_zero p).compl

/-- Coordinate projection preserves polynomial constructibility over an algebraically closed
field. -/
theorem IsPolynomialConstructible.exists_coordinates [IsAlgClosed K]
    {σ τ : Type*} [Finite σ] [Finite τ] {S : Set ((σ ⊕ τ) → K)}
    (hS : IsPolynomialConstructible S) :
    IsPolynomialConstructible {x : σ → K | ∃ y : τ → K, Sum.elim x y ∈ S} := by
  obtain ⟨S', hS', rfl⟩ := hS
  obtain ⟨T, hT, hpoint⟩ := constructible_projection_at_points S' hS'
  refine ⟨T, hT, ?_⟩
  ext x
  exact (hpoint x).symm

/-- A dense constructible subset of an irreducible hypersurface contains a principal open. -/
theorem exists_principalOpen_subset_of_constructible [IsAlgClosed K]
    {f : Poly K} (hf : Irreducible f) (S : Set (Point K))
    (hS : IsPolynomialConstructible S)
    (hsub : ∀ x ∈ S, MvPolynomial.eval x f = 0)
    (hdense : ∀ q : Poly K, (∀ x ∈ S, MvPolynomial.eval x q = 0) → f ∣ q) :
    ∃ g : Poly K, ¬ f ∣ g ∧ principalOpen f g ⊆ S := by
  classical
  obtain ⟨T, hT, hST⟩ := hS
  obtain ⟨data, hdata⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr hT
  let polys : Finset (Poly K) := data.biUnion fun C => insert C.f (Finset.univ.image C.g)
  let bad : Finset (Poly K) := polys.filter fun p => ¬ f ∣ p
  let g : Poly K := ∏ p ∈ bad, p
  have hg : ¬ f ∣ g := not_dvd_finset_prod bad id hf
    (fun p hp => (Finset.mem_filter.mp hp).2)
  have hpattern (x : Point K) (hx : x ∈ principalOpen f g) (p : Poly K) (hp : p ∈ polys) :
      MvPolynomial.eval x p = 0 ↔ f ∣ p := by
    constructor
    · intro hzero
      by_contra hnot
      apply hx.2
      change MvPolynomial.eval x (∏ p ∈ bad, p) = 0
      rw [map_prod]
      apply Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨hp, hnot⟩)
      exact hzero
    · rintro ⟨r, rfl⟩
      rw [map_mul, hx.1, zero_mul]
  have hCmem (C : PrimeSpectrum.BasicConstructibleSetData (Poly K)) (hC : C ∈ data) :
      C.f ∈ polys ∧ ∀ i, C.g i ∈ polys := by
    constructor
    · exact Finset.mem_biUnion.mpr ⟨C, hC, Finset.mem_insert_self _ _⟩
    · intro i
      exact Finset.mem_biUnion.mpr ⟨C, hC, Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩
  obtain ⟨x, hxS, hxg⟩ : ∃ x ∈ S, MvPolynomial.eval x g ≠ 0 := by
    by_contra h
    push Not at h
    exact hg (hdense g h)
  have hx : x ∈ principalOpen f g := ⟨hsub x hxS, hxg⟩
  have hxT : MvPolynomial.pointToPoint (k := K) x ∈ data.toSet := by
    rw [hdata, ← Set.mem_preimage, ← hST]
    exact hxS
  obtain ⟨C, hC, hxC⟩ := Set.mem_iUnion₂.mp hxT
  obtain ⟨hxCg, hxCf⟩ := (point_mem_basicConstructible_iff C x).mp hxC
  refine ⟨g, hg, ?_⟩
  intro y hy
  rw [hST, Set.mem_preimage, ← hdata]
  apply Set.mem_iUnion₂.mpr
  refine ⟨C, hC, (point_mem_basicConstructible_iff C y).mpr ⟨?_, ?_⟩⟩
  · intro i
    exact (hpattern y hy _ ((hCmem C hC).2 i)).mpr
      ((hpattern x hx _ ((hCmem C hC).2 i)).mp (hxCg i))
  · intro hyf
    exact hxCf ((hpattern x hx _ (hCmem C hC).1).mpr
      ((hpattern y hy _ (hCmem C hC).1).mp hyf))

/-- An infinite family of contained lines has a polynomially dense union. -/
theorem dvd_of_vanishes_on_infinite_line_union [Infinite K]
    {f q : Poly K} (hf : Irreducible f) (F : Set (Line K)) (hF : F.Infinite)
    (hcontained : ∀ L ∈ F, LineOn f L)
    (hzero : ∀ L ∈ F, ∀ x ∈ L.1, MvPolynomial.eval x q = 0) : f ∣ q := by
  apply dvd_of_infinite_common_lines hf
  apply hF.mono
  intro L hL
  exact ⟨hcontained L hL, (lineOn_iff_eval_eq_zero q L).mpr (hzero L hL)⟩

/-- A constructible union of infinitely many contained lines contains a principal open. -/
theorem exists_principalOpen_subset_line_union [IsAlgClosed K]
    {f : Poly K} (hf : Irreducible f) (F : Set (Line K)) (hF : F.Infinite)
    (hcontained : ∀ L ∈ F, LineOn f L)
    (hconstructible : IsPolynomialConstructible {x : Point K | ∃ L ∈ F, x ∈ L.1}) :
    ∃ g : Poly K, ¬ f ∣ g ∧ principalOpen f g ⊆ {x : Point K | ∃ L ∈ F, x ∈ L.1} := by
  apply exists_principalOpen_subset_of_constructible hf _ hconstructible
  · rintro x ⟨L, hL, hx⟩
    exact eval_eq_zero_of_lineOn (hcontained L hL) hx
  · intro q hq
    exact dvd_of_vanishes_on_infinite_line_union hf F hF hcontained
      (fun L hL x hx => hq x ⟨L, hL, hx⟩)

end ExplicitRIP.GuthZahl.RuledSurfaces
end
