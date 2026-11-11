/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.RuledSurfaces.AffineGeometry
public import ExplicitRIP.GuthZahl.RuledSurfaces.OpenSet
public import ExplicitRIP.GuthZahl.RuledSurfaces.CommonLines

/-!
# Plane sections and finite common transversals

A plane section of a nonplane irreducible hypersurface contains finitely many
lines. Together with finite fibers in an open set, this shows that two distinct
coplanar lines have only finitely many contained common transversals there.
-/

public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K]

/-- An affine subspace of dimension at most two has a nonzero linear equation. -/
theorem exists_linear_equation_of_finrank_direction_le_two
    (S : AffineSubspace K (Point K)) (hS : (S : Set (Point K)).Nonempty)
    (hdim : Module.finrank K S.direction ≤ 2) :
    ∃ q : Poly K, q.totalDegree = 1 ∧ ∀ x ∈ S, MvPolynomial.eval x q = 0 := by
  have hproper : S.direction < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro htop
    rw [htop, finrank_top] at hdim
    have hpoint : Module.finrank K (Point K) = 3 := by
      simp only [Point, Module.finrank_pi, Fintype.card_fin]
    rw [hpoint] at hdim
    omega
  obtain ⟨φ, hφ, hker⟩ := S.direction.exists_le_ker_of_lt_top hproper
  obtain ⟨a, ha⟩ := hS
  let c : Fin 3 → K := fun i => φ (Pi.single i 1)
  let q : Poly K := ∑ i : Fin 3, MvPolynomial.C (c i) *
    (MvPolynomial.X i - MvPolynomial.C (a i))
  have hrepr (v : Point K) : φ v = ∑ i : Fin 3, c i * v i := by
    rw [LinearMap.pi_apply_eq_sum_univ]
    apply Finset.sum_congr rfl
    intro i hi
    have heq : (fun j : Fin 3 => if i = j then (1 : K) else 0) = Pi.single i 1 := by
      funext j
      simp only [Pi.single_apply, eq_comm]
    rw [heq]
    exact mul_comm _ _
  have hc : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    apply hφ
    apply LinearMap.ext
    intro v
    rw [hrepr]
    simp only [h, zero_mul, Finset.sum_const_zero, LinearMap.zero_apply]
  have hcoeff (i : Fin 3) : q.coeff (Finsupp.single i 1) = c i := by
    have hi0 : (0 : Fin 3 →₀ ℕ) ≠ Finsupp.single i 1 :=
      Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero)
    simp only [q, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_sub, MvPolynomial.coeff_X, MvPolynomial.coeff_C, hi0,
      ↓reduceIte, sub_zero, Finsupp.single_left_inj one_ne_zero]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hdegree : q.totalDegree = 1 := by
    apply le_antisymm
    · apply MvPolynomial.totalDegree_finsetSum_le
      intro i hi
      apply (MvPolynomial.totalDegree_mul _ _).trans
      simpa only [MvPolynomial.totalDegree_C, zero_add, MvPolynomial.totalDegree_X] using
        MvPolynomial.totalDegree_sub_C_le (MvPolynomial.X i : Poly K) (a i)
    · obtain ⟨i, hi⟩ := hc
      have hm : Finsupp.single i 1 ∈ q.support :=
        MvPolynomial.mem_support_iff.mpr ((hcoeff i).trans_ne hi)
      simpa only [Finsupp.sum_single_index, mul_one] using MvPolynomial.le_totalDegree hm
  refine ⟨q, hdegree, ?_⟩
  intro x hx
  have hzero : φ (x - a) = 0 := hker (AffineSubspace.vsub_mem_direction hx ha)
  rw [hrepr] at hzero
  simpa only [q, map_sum, map_mul, map_sub, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Pi.sub_apply] using hzero

/-- A nonplane irreducible hypersurface has finitely many contained lines in any plane. -/
theorem finite_lines_in_plane [Infinite K] {f : Poly K} (hf : Irreducible f)
    (hnonplane : f.totalDegree ≠ 1) (P : AffineSubspace K (Point K))
    (hP : Module.finrank K P.direction = 2) :
    {L : Line K | LineOn f L ∧ L.1 ≤ P}.Finite := by
  by_cases hne : (P : Set (Point K)).Nonempty
  · obtain ⟨q, hdegree, hq⟩ := exists_linear_equation_of_finrank_direction_le_two P hne hP.le
    apply (finite_common_lines_of_not_dvd f q hf
      (not_dvd_of_totalDegree_eq_one hf hnonplane hdegree)).subset
    intro L hL
    exact ⟨hL.1, (lineOn_iff_eval_eq_zero q L).mpr (fun x hx => hq x (hL.2 hx))⟩
  · have hempty : {L : Line K | LineOn f L ∧ L.1 ≤ P} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro L ⟨hfL, hLP⟩
      obtain ⟨x, hx⟩ := line_nonempty L
      exact hne ⟨x, hLP hx⟩
    rw [hempty]
    exact Set.finite_empty

/-- Two distinct points of a line lying in an affine subspace force the whole line into it. -/
theorem line_le_of_two_points {L : Line K} {P : AffineSubspace K (Point K)}
    {x y : Point K} (hxy : x ≠ y) (hxL : x ∈ L.1) (hyL : y ∈ L.1)
    (hxP : x ∈ P) (hyP : y ∈ P) : L.1 ≤ P := by
  have hv0 : y -ᵥ x ≠ (0 : Point K) := vsub_ne_zero.mpr hxy.symm
  have hvL := AffineSubspace.vsub_mem_direction hyL hxL
  have hvP := AffineSubspace.vsub_mem_direction hyP hxP
  intro z hz
  obtain ⟨t, rfl⟩ := (mem_line_iff_exists_smul hxL hvL hv0 z).mp hz
  simpa only [vadd_eq_add, add_comm] using
    P.vadd_mem_of_mem_direction (P.direction.smul_mem t hvP) hxP

/-- In an open set with finite incident fibers, two distinct coplanar lines have
only finitely many contained lines meeting both there. -/
theorem finite_common_transversals_of_coplanar [Infinite K] {f : Poly K}
    (hf : Irreducible f) (hnonplane : f.totalDegree ≠ 1) (O : Set (Point K))
    (hfinite : ∀ x ∈ O, {L : Line K | x ∈ L.1 ∧ LineOn f L}.Finite)
    (A B : Line K) (hAB : A ≠ B) (hcop : Coplanar A B) :
    {L : Line K | LineOn f L ∧
      (∃ x ∈ O, x ∈ L.1 ∧ x ∈ A.1) ∧ (∃ y ∈ O, y ∈ L.1 ∧ y ∈ B.1)}.Finite := by
  obtain ⟨P, hP, hAP, hBP⟩ := hcop
  have hpoints : {x : Point K | x ∈ A.1 ∧ x ∈ B.1 ∧ x ∈ O}.Finite :=
    (line_inter_subsingleton _ _ hAB).finite.subset (fun x hx => ⟨hx.1, hx.2.1⟩)
  have hbad : (⋃ x ∈ {x : Point K | x ∈ A.1 ∧ x ∈ B.1 ∧ x ∈ O},
      {L : Line K | x ∈ L.1 ∧ LineOn f L}).Finite :=
    hpoints.biUnion (fun x hx => hfinite x hx.2.2)
  apply ((finite_lines_in_plane hf hnonplane P hP).union hbad).subset
  rintro L ⟨hL, ⟨x, hxO, hxL, hxA⟩, ⟨y, hyO, hyL, hyB⟩⟩
  by_cases hxy : x = y
  · subst y
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨x, ⟨hxA, hyB, hxO⟩, hxL, hL⟩)
  · exact Or.inl ⟨hL, line_le_of_two_points hxy hxL hyL (hAP hxA) (hBP hyB)⟩

end ExplicitRIP.GuthZahl.RuledSurfaces
end
