/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.RuledSurfaces.CrossingFamilies
public import ExplicitRIP.GuthZahl.RuledSurfaces.Transversals

/-! # The degree bound for a doubly ruled irreducible hypersurface -/

public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

theorem _root_.ExplicitRIP.GuthZahl.doublyRuled_degree_le_two {K : Type*} [Field K] [IsAlgClosed K]
    (_h2 : (2 : K) ≠ 0) (f : Poly K) (hf : Irreducible f) (hruled : DoublyRuled f) :
    f.totalDegree ≤ 2 := by
  by_cases hplane : f.totalDegree = 1
  · omega
  obtain ⟨A, B, C, hAB, hAC, hBC, hF⟩ :=
    exists_skew_triple_with_infinite_transversals hf hruled hplane
  obtain ⟨q, hq, hdegree, hA, hB, hC, htrans⟩ :=
    exists_quadric_containing_common_transversals A B C hAB hAC hBC
  have hdiv : f ∣ q := dvd_of_infinite_common_lines hf (hF.mono (by
    rintro L ⟨hL, hLA, hLB, hLC⟩
    exact ⟨hL, htrans L hLA hLB hLC⟩))
  simpa only [hdegree] using MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hq.ne_zero

end ExplicitRIP.GuthZahl.RuledSurfaces
end
