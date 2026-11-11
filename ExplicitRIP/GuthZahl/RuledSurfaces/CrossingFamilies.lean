/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.RuledSurfaces.CrossingConstructible
public import ExplicitRIP.GuthZahl.RuledSurfaces.GenericLine
public import ExplicitRIP.GuthZahl.RuledSurfaces.PlaneLines
public import ExplicitRIP.GuthZahl.RuledSurfaces.Smooth

/-!
# Extracting three skew lines with infinitely many common transversals

The crossing-family induction uses constructible unions and principal opens.
Finite fibers in the good open then force any two distinct selected lines to
be skew. Only three induction steps are needed.
-/

public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K]

open Classical in
/-- A nonplane irreducible surface has a principal open avoiding a finite family of whole lines. -/
theorem exists_principalOpen_avoiding_lines [Infinite K] {f : Poly K}
    (hf : Irreducible f) (hnonplane : f.totalDegree ≠ 1) (B : Finset (Line K)) :
    ∃ q : Poly K, ¬ f ∣ q ∧
      ∀ x ∈ principalOpen f q, ∀ L ∈ B, x ∉ L.1 := by
  classical
  choose q hdegree hq using fun L : Line K => exists_linear_equation L
  let Q : Poly K := ∏ L ∈ B, q L
  have hQ : ¬ f ∣ Q := not_dvd_finset_prod B q hf
    (fun L hL => not_dvd_of_totalDegree_eq_one hf hnonplane (hdegree L))
  refine ⟨Q, hQ, ?_⟩
  intro x hx L hLB hxL
  apply hx.2
  change MvPolynomial.eval x (∏ L ∈ B, q L) = 0
  rw [map_prod]
  exact Finset.prod_eq_zero hLB (eval_eq_zero_of_lineOn (hq L) hxL)

open Classical in
/-- Infinitely many covered points on a line require infinitely many other lines. -/
theorem infinite_meeting_lines_of_infinite_points (F : Set (Line K)) (L : Line K)
    (O X : Set (Point K)) (hX : X.Infinite)
    (hcover : ∀ x ∈ X, x ∈ L.1 ∧ x ∈ O ∧ ∃ M ∈ F, M ≠ L ∧ x ∈ M.1) :
    {M : Line K | M ∈ F ∧ M ≠ L ∧ ∃ x ∈ O, x ∈ L.1 ∧ x ∈ M.1}.Infinite := by
  intro hfinite
  have hpoints : (⋃ M ∈ {M : Line K | M ∈ F ∧ M ≠ L ∧
      ∃ x ∈ O, x ∈ L.1 ∧ x ∈ M.1}, ((L.1 : Set (Point K)) ∩ M.1)).Finite :=
    hfinite.biUnion (fun M hM => (line_inter_subsingleton _ _ hM.2.1.symm).finite)
  apply hX
  apply hpoints.subset
  intro x hx
  obtain ⟨hxL, hxO, M, hMF, hML, hxM⟩ := hcover x hx
  exact Set.mem_iUnion₂.mpr ⟨M, ⟨hMF, hML, x, hxO, hxL, hxM⟩, hxL, hxM⟩

open Classical in
/-- One more line can be added while retaining infinitely many common transversals. -/
theorem crossingFamily_step [IsAlgClosed K] {f g : Poly K}
    (hf : Irreducible f) (hnonplane : f.totalDegree ≠ 1) (hg : ¬ f ∣ g)
    (hruled : ∀ x ∈ principalOpen f g,
      ∃ L M : Line K, L ≠ M ∧ x ∈ L.1 ∧ x ∈ M.1 ∧ LineOn f L ∧ LineOn f M)
    (G : Finset (Line K)) (hF : (crossingFamily f g G).Infinite) :
    ∃ L : Line K, LineOn f L ∧ L ∉ G ∧ (crossingFamily f g (insert L G)).Infinite := by
  classical
  let F := crossingFamily f g G
  let C : Set (Line K) := {L | LineOn f L} \ F
  have hFcontained : ∀ L ∈ F, LineOn f L := fun L hL => hL.1
  have extend (L : Line K) (hL : LineOn f L) (hLG : L ∉ G)
      (hN : {M : Line K | M ∈ F ∧ M ≠ L ∧
        ∃ x ∈ principalOpen f g, x ∈ L.1 ∧ x ∈ M.1}.Infinite) :
      ∃ L : Line K, LineOn f L ∧ L ∉ G ∧ (crossingFamily f g (insert L G)).Infinite := by
    refine ⟨L, hL, hLG, hN.mono ?_⟩
    rintro M ⟨hMF, hML, x, hxO, hxL, hxM⟩
    refine ⟨hMF.1, ?_⟩
    intro N hN
    rcases Finset.mem_insert.mp hN with rfl | hN
    · exact ⟨x, hxO, hxM, hxL⟩
    · exact hMF.2 N hN
  by_cases hC : C.Finite
  · obtain ⟨q, hq, havoid⟩ := exists_principalOpen_avoiding_lines hf hnonplane hC.toFinset
    have hgq : ¬ f ∣ g * q := fun h => (hf.prime.dvd_mul.mp h).elim hg hq
    obtain ⟨L, hLF, hLG, hX⟩ := exists_line_infinite_principalOpen hf hgq F G
      hF G.finite_toSet hFcontained
    apply extend L hLF.1 hLG
    apply infinite_meeting_lines_of_infinite_points F L (principalOpen f g)
      {x : Point K | x ∈ L.1 ∧ x ∈ principalOpen f (g * q)} hX
    intro x hx
    have hxgq : MvPolynomial.eval x g ≠ 0 ∧ MvPolynomial.eval x q ≠ 0 := by
      simpa only [map_mul, mul_ne_zero_iff] using hx.2.2
    have hxg : x ∈ principalOpen f g := ⟨hx.2.1, hxgq.1⟩
    have hxq : x ∈ principalOpen f q := ⟨hx.2.1, hxgq.2⟩
    obtain ⟨A, B, hAB, hxA, hxB, hA, hB⟩ := hruled x hxg
    have hinF (M : Line K) (hM : LineOn f M) (hxM : x ∈ M.1) : M ∈ F := by
      by_contra hnot
      have hMC : M ∈ C := ⟨hM, hnot⟩
      exact havoid x hxq M (hC.mem_toFinset.mpr hMC) hxM
    refine ⟨hx.1, hxg, ?_⟩
    by_cases hAL : A = L
    · exact ⟨B, hinF B hB hxB, fun hBL => hAB (hAL.trans hBL.symm), hxB⟩
    · exact ⟨A, hinF A hA hxA, hAL, hxA⟩
  · have hCinf : C.Infinite := hC
    obtain ⟨q, hq, hopen⟩ := exists_principalOpen_subset_line_union hf F hF hFcontained
      (isPolynomialConstructible_crossing_lineUnion f g G)
    have hgq : ¬ f ∣ g * q := fun h => (hf.prime.dvd_mul.mp h).elim hg hq
    obtain ⟨L, hLC, hLG, hX⟩ := exists_line_infinite_principalOpen hf hgq C G
      hCinf G.finite_toSet (fun M hM => hM.1)
    apply extend L hLC.1 hLG
    apply infinite_meeting_lines_of_infinite_points F L (principalOpen f g)
      {x : Point K | x ∈ L.1 ∧ x ∈ principalOpen f (g * q)} hX
    intro x hx
    have hxgq : MvPolynomial.eval x g ≠ 0 ∧ MvPolynomial.eval x q ≠ 0 := by
      simpa only [map_mul, mul_ne_zero_iff] using hx.2.2
    obtain ⟨M, hMF, hxM⟩ := hopen ⟨hx.2.1, hxgq.2⟩
    exact ⟨hx.1, ⟨hx.2.1, hxgq.1⟩, M, hMF, fun hML => hLC.2 (hML ▸ hMF), hxM⟩

open Classical in
/-- Three distinct selected lines have infinitely many contained common transversals in a good
open. -/
theorem exists_three_crossing_lines [IsAlgClosed K] {f g : Poly K}
    (hf : Irreducible f) (hnonplane : f.totalDegree ≠ 1) (hg : ¬ f ∣ g)
    (hall : {L : Line K | LineOn f L}.Infinite)
    (hruled : ∀ x ∈ principalOpen f g,
      ∃ L M : Line K, L ≠ M ∧ x ∈ L.1 ∧ x ∈ M.1 ∧ LineOn f L ∧ LineOn f M) :
    ∃ A B C : Line K, A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
      (crossingFamily f g {A, B, C}).Infinite := by
  classical
  have hzero : (crossingFamily f g ∅).Infinite := by
    simpa [crossingFamily] using hall
  obtain ⟨A, hA, hA0, hAF⟩ := crossingFamily_step hf hnonplane hg hruled ∅ hzero
  obtain ⟨B, hB, hBA, hBF⟩ := crossingFamily_step hf hnonplane hg hruled {A} hAF
  obtain ⟨C, hC, hCBA, hCF⟩ := crossingFamily_step hf hnonplane hg hruled {B, A} hBF
  have hBA' : B ≠ A := fun h => hBA (Finset.mem_singleton.mpr h)
  have hCA : C ≠ A := fun h => hCBA (by simp [h])
  have hCB : C ≠ B := fun h => hCBA (by simp [h])
  refine ⟨A, B, C, hBA'.symm, hCA.symm, hCB.symm, ?_⟩
  have heq : ({C, B, A} : Finset (Line K)) = {A, B, C} := by ext L; simp; tauto
  rwa [heq] at hCF

open Classical in
/-- Infinite common transversals in the good open force distinct selected lines to be skew. -/
theorem not_coplanar_of_infinite_crossingFamily [Infinite K] {f g : Poly K}
    (hf : Irreducible f) (hnonplane : f.totalDegree ≠ 1)
    (hfinite : ∀ x ∈ principalOpen f g, {L : Line K | x ∈ L.1 ∧ LineOn f L}.Finite)
    (G : Finset (Line K)) (hG : (crossingFamily f g G).Infinite)
    (A B : Line K) (hA : A ∈ G) (hB : B ∈ G) (hAB : A ≠ B) : ¬ Coplanar A B := by
  intro hcop
  apply hG
  apply (finite_common_transversals_of_coplanar hf hnonplane (principalOpen f g)
    hfinite A B hAB hcop).subset
  intro L hL
  exact ⟨hL.1, hL.2 A hA, hL.2 B hB⟩

open Classical in
/-- A nonplane doubly ruled irreducible surface contains three skew lines with infinitely
many contained common transversals. -/
theorem exists_skew_triple_with_infinite_transversals [IsAlgClosed K]
    {f : Poly K} (hf : Irreducible f) (hruled : DoublyRuled f)
    (hnonplane : f.totalDegree ≠ 1) :
    ∃ A B C : Line K, ¬ Coplanar A B ∧ ¬ Coplanar A C ∧ ¬ Coplanar B C ∧
      {L : Line K | LineOn f L ∧ Coplanar L A ∧ Coplanar L B ∧ Coplanar L C}.Infinite := by
  classical
  obtain ⟨g, hg, hnonempty, hgood⟩ := exists_principalOpen_finite_fibers hf hruled hnonplane
  have hfinite := fun x hx => (hgood x hx).1
  have hruledg := fun x hx => (hgood x hx).2
  obtain ⟨A, B, C, hAB, hAC, hBC, hF⟩ := exists_three_crossing_lines hf hnonplane hg
    (infinite_lines_of_doublyRuled hf hruled hnonplane) hruledg
  have hskew (L M : Line K) (hL : L ∈ ({A, B, C} : Finset (Line K)))
      (hM : M ∈ ({A, B, C} : Finset (Line K))) (hLM : L ≠ M) : ¬ Coplanar L M :=
    not_coplanar_of_infinite_crossingFamily hf hnonplane hfinite _ hF L M hL hM hLM
  refine ⟨A, B, C, hskew A B (by simp) (by simp) hAB,
    hskew A C (by simp) (by simp) hAC, hskew B C (by simp) (by simp) hBC, hF.mono ?_⟩
  intro L hL
  have hcop (M : Line K) (hM : M ∈ ({A, B, C} : Finset (Line K))) : Coplanar L M := by
    by_cases heq : L = M
    · subst M
      exact coplanar_self L
    · obtain ⟨x, hxO, hxL, hxM⟩ := hL.2 M hM
      exact coplanar_of_mem_of_ne hxL hxM heq
  exact ⟨hL.1, hcop A (by simp), hcop B (by simp), hcop C (by simp)⟩

end ExplicitRIP.GuthZahl.RuledSurfaces
end
