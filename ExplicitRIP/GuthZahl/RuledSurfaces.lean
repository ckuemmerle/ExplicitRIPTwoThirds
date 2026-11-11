/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.RuledSurfaces.DegreeBound
public import ExplicitRIP.GuthZahl.RuledSurfaces.Rulings

/-!
# Guth–Zahl classification of doubly ruled surfaces

The degree bound follows by extracting three skew lines with infinitely many
contained common transversals and interpolating a quadric through the triple.
-/

public section

namespace ExplicitRIP.GuthZahl

theorem complementary_rulings {K : Type*} [Field K] [IsAlgClosed K]
    (h2 : (2 : K) ≠ 0) (f : Poly K) (hf : Irreducible f) (hruled : DoublyRuled f)
    (hnonplane : f.totalDegree ≠ 1) :
    ∃ R S : Set (Line K), R.Infinite ∧ S.Infinite ∧ Disjoint R S ∧
      (∀ L, LineOn f L ↔ L ∈ R ∨ L ∈ S) ∧
      (∀ L ∈ R, ∀ M ∈ R, L ≠ M → ¬ Coplanar L M) ∧
      (∀ L ∈ S, ∀ M ∈ S, L ≠ M → ¬ Coplanar L M) ∧
      (∀ L ∈ R, ∀ M ∈ S, Coplanar L M) ∧
      ∀ (x : Point K) (Ls : Finset (Line K)),
        (∀ L ∈ Ls, x ∈ L.1 ∧ LineOn f L) → Ls.card ≤ 2 := by
  have hle := doublyRuled_degree_le_two h2 f hf hruled
  have hpos := RuledSurfaces.totalDegree_pos_of_irreducible hf
  have hdegree : f.totalDegree = 2 := by omega
  obtain ⟨A, B, C, hAB, hAC, hBC, hF⟩ :=
    RuledSurfaces.exists_skew_triple_with_infinite_transversals hf hruled hnonplane
  obtain ⟨q, hq, hqdegree, hA, hB, hC, htrans⟩ :=
    RuledSurfaces.exists_quadric_containing_common_transversals A B C hAB hAC hBC
  have hdiv : f ∣ q := RuledSurfaces.dvd_of_infinite_common_lines hf (hF.mono (by
    rintro L ⟨hL, hLA, hLB, hLC⟩
    exact ⟨hL, htrans L hLA hLB hLC⟩))
  have hassoc : Associated f q := hf.associated_of_dvd hq hdiv
  exact RuledSurfaces.complementary_rulings_of_quadric hf hdegree A B hAB
    ((lineOn_iff_of_associated hassoc A).mpr hA)
    ((lineOn_iff_of_associated hassoc B).mpr hB) hruled

end ExplicitRIP.GuthZahl
end
