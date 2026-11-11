/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.RuledSurfaces.QuadricIncidence
public import ExplicitRIP.GuthZahl.RuledSurfaces.CrossingFamilies

/-!
# Complementary rulings of a quadric

Relative to one contained line, the lines coplanar with it form one ruling and
the remaining lines, together with that line itself, form the other. The
incidence lemmas give disjointness, skewness within each class, and coplanarity
across classes. Double ruling on a principal open makes both classes infinite.
-/

public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K] [Infinite K]

/-- An irreducible doubly ruled quadric with skew contained lines has complementary rulings. -/
theorem complementary_rulings_of_quadric {q : Poly K} (hq : Irreducible q)
    (hdegree : q.totalDegree = 2) (U V : Line K) (hUV : ¬ Coplanar U V)
    (hU : LineOn q U) (hV : LineOn q V) (hruled : DoublyRuled q) :
    ∃ R S : Set (Line K), R.Infinite ∧ S.Infinite ∧ Disjoint R S ∧
      (∀ L, LineOn q L ↔ L ∈ R ∨ L ∈ S) ∧
      (∀ L ∈ R, ∀ M ∈ R, L ≠ M → ¬ Coplanar L M) ∧
      (∀ L ∈ S, ∀ M ∈ S, L ≠ M → ¬ Coplanar L M) ∧
      (∀ L ∈ R, ∀ M ∈ S, Coplanar L M) ∧
      ∀ (x : Point K) (Ls : Finset (Line K)),
        (∀ L ∈ Ls, x ∈ L.1 ∧ LineOn q L) → Ls.card ≤ 2 := by
  classical
  obtain ⟨g, hg, ⟨o, ho⟩, hdouble⟩ := hruled
  obtain ⟨A, B, hAB, hoA, hoB, hA, hB⟩ := hdouble o ho
  have hcAB : Coplanar A B := coplanar_of_mem_of_ne hoA hoB hAB
  let R : Set (Line K) := {L | LineOn q L ∧ (L = A ∨ ¬ Coplanar L A)}
  let S : Set (Line K) := {L | LineOn q L ∧ L ≠ A ∧ Coplanar L A}
  have hAR : A ∈ R := ⟨hA, Or.inl rfl⟩
  have hBS : B ∈ S := ⟨hB, hAB.symm, (coplanar_comm B A).mpr hcAB⟩
  have hcoverage (L : Line K) : LineOn q L ↔ L ∈ R ∨ L ∈ S := by
    constructor
    · intro hL
      by_cases heq : L = A
      · exact Or.inl ⟨hL, Or.inl heq⟩
      · by_cases hcop : Coplanar L A
        · exact Or.inr ⟨hL, heq, hcop⟩
        · exact Or.inl ⟨hL, Or.inr hcop⟩
    · rintro (hL | hL)
      · exact hL.1
      · exact hL.1
  have hdisjoint : Disjoint R S := by
    apply Set.disjoint_left.mpr
    rintro L ⟨hL, heq | hnot⟩ hLS
    · exact hLS.2.1 heq
    · exact hnot hLS.2.2
  have hRneB (L : Line K) (hL : L ∈ R) : L ≠ B :=
    fun heq => Set.disjoint_left.mp hdisjoint (heq ▸ hL) hBS
  have hRcopB (L : Line K) (hL : L ∈ R) : Coplanar L B := by
    rcases hL.2 with rfl | hnot
    · exact hcAB
    · exact (coplanar_or_coplanar_of_quadric hq hdegree U V hUV hU hV
        A B hAB hA hB hcAB L hL.1).resolve_left hnot
  have hRskew : ∀ L ∈ R, ∀ M ∈ R, L ≠ M → ¬ Coplanar L M := by
    intro L hL M hM hLM hcop
    exact not_three_pairwise_coplanar_lines hq hdegree U V hUV hU hV L M B hLM
      (hRneB L hL) (hRneB M hM) hL.1 hM.1 hB hcop (hRcopB L hL) (hRcopB M hM)
  have hSskew : ∀ L ∈ S, ∀ M ∈ S, L ≠ M → ¬ Coplanar L M := by
    intro L hL M hM hLM hcop
    exact not_three_pairwise_coplanar_lines hq hdegree U V hUV hU hV L M A hLM
      hL.2.1 hM.2.1 hL.1 hM.1 hA hcop hL.2.2 hM.2.2
  have hcross : ∀ L ∈ R, ∀ M ∈ S, Coplanar L M := by
    intro L hL M hM
    rcases hL.2 with rfl | hnot
    · exact (coplanar_comm _ _).mpr hM.2.2
    · exact (coplanar_or_coplanar_of_quadric hq hdegree U V hUV hU hV A M
        hM.2.1.symm hA hM.1 ((coplanar_comm A M).mpr hM.2.2) L hL.1).resolve_left hnot
  have hAg : ¬ LineOn g A := fun h => ho.2 (eval_eq_zero_of_lineOn h hoA)
  have hBg : ¬ LineOn g B := fun h => ho.2 (eval_eq_zero_of_lineOn h hoB)
  have hSinf : S.Infinite := by
    have hpoints := infinite_principalOpen_on_line hA hAg
    have hneighbors := infinite_meeting_lines_of_infinite_points S A (principalOpen q g)
      {x : Point K | x ∈ A.1 ∧ x ∈ principalOpen q g} hpoints (by
        intro x hx
        obtain ⟨L, M, hLM, hxL, hxM, hL, hM⟩ := hdouble x hx.2
        have hmem (N : Line K) (hN : LineOn q N) (hxN : x ∈ N.1) (hNA : N ≠ A) :
            N ∈ S := ⟨hN, hNA, coplanar_of_mem_of_ne hxN hx.1 hNA⟩
        refine ⟨hx.1, hx.2, ?_⟩
        by_cases hLA : L = A
        · have hMA : M ≠ A := fun h => hLM (hLA.trans h.symm)
          exact ⟨M, hmem M hM hxM hMA, hMA, hxM⟩
        · exact ⟨L, hmem L hL hxL hLA, hLA, hxL⟩)
    exact hneighbors.mono (fun L hL => hL.1)
  have hRinf : R.Infinite := by
    have hpoints := infinite_principalOpen_on_line hB hBg
    have hneighbors := infinite_meeting_lines_of_infinite_points R B (principalOpen q g)
      {x : Point K | x ∈ B.1 ∧ x ∈ principalOpen q g} hpoints (by
        intro x hx
        obtain ⟨L, M, hLM, hxL, hxM, hL, hM⟩ := hdouble x hx.2
        have hmem (N : Line K) (hN : LineOn q N) (hxN : x ∈ N.1) (hNB : N ≠ B) :
            N ∈ R := by
          rcases (hcoverage N).mp hN with hNR | hNS
          · exact hNR
          · exact False.elim (hSskew N hNS B hBS hNB (coplanar_of_mem_of_ne hxN hx.1 hNB))
        refine ⟨hx.1, hx.2, ?_⟩
        by_cases hLB : L = B
        · have hMB : M ≠ B := fun h => hLM (hLB.trans h.symm)
          exact ⟨M, hmem M hM hxM hMB, hMB, hxM⟩
        · exact ⟨L, hmem L hL hxL hLB, hLB, hxL⟩)
    exact hneighbors.mono (fun L hL => hL.1)
  exact ⟨R, S, hRinf, hSinf, hdisjoint, hcoverage, hRskew, hSskew, hcross,
    card_lines_through_point_le_two hq hdegree U V hUV hU hV⟩

end ExplicitRIP.GuthZahl.RuledSurfaces
end
