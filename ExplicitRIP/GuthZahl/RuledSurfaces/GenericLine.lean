/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.RuledSurfaces.CommonLines

/-!
# Choosing lines that meet a principal open

A line outside a hypersurface has only finitely many points on it. Together
with common-line finiteness, this allows choosing a line from any infinite
contained family which meets a prescribed principal open infinitely often.
-/

public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K] [Infinite K]

omit [Infinite K] in
/-- The affine parametrization by a nonzero direction is injective. -/
theorem line_parametrization_injective (a v : Point K) (hv : v ≠ 0) :
    Function.Injective (fun t : K => a + t • v) := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  intro t s hts
  have heq := congrFun hts i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_right_inj] at heq
  exact mul_right_cancel₀ hi heq

/-- Every affine line over an infinite field has infinitely many points. -/
theorem infinite_points_line (L : Line K) : (L.1 : Set (Point K)).Infinite := by
  obtain ⟨a, v, ha, hv, hv0, hparam⟩ := exists_line_parametrization L
  have hrange : Set.range (fun t : K => a + t • v) = (L.1 : Set (Point K)) := by
    ext x
    exact (hparam x).symm
  rw [← hrange]
  exact Set.infinite_range_of_injective (line_parametrization_injective a v hv0)

omit [Infinite K] in
/-- A line not algebraically contained in a hypersurface meets it at finitely many points. -/
theorem finite_zero_points_on_line (g : Poly K) (L : Line K) (hg : ¬ LineOn g L) :
    {x : Point K | x ∈ L.1 ∧ MvPolynomial.eval x g = 0}.Finite := by
  obtain ⟨a, v, ha, hv, hv0, hparam⟩ := exists_line_parametrization L
  have hp : restrictLine g a v ≠ 0 :=
    fun h => hg ((lineOn_iff_restrictLine_eq_zero g _ _ ha _ hv hv0).2 h)
  have hrange : {x : Point K | x ∈ L.1 ∧ MvPolynomial.eval x g = 0} =
      (fun t : K => a + t • v) '' {t : K | Polynomial.IsRoot (restrictLine g a v) t} := by
    ext x
    constructor
    · rintro ⟨hx, hxg⟩
      obtain ⟨t, rfl⟩ := (hparam x).1 hx
      exact ⟨t, by rwa [Set.mem_ofPred_eq, Polynomial.IsRoot.def, eval_restrictLine], rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(hparam _).2 ⟨t, rfl⟩, by
        rwa [Set.mem_ofPred_eq, Polynomial.IsRoot.def, eval_restrictLine] at ht⟩
  rw [hrange]
  exact (Polynomial.finite_setOfPred_isRoot hp).image _

/-- A contained line outside the exceptional hypersurface meets the principal open infinitely. -/
theorem infinite_principalOpen_on_line {f g : Poly K} {L : Line K}
    (hf : LineOn f L) (hg : ¬ LineOn g L) :
    {x : Point K | x ∈ L.1 ∧ x ∈ principalOpen f g}.Infinite := by
  have hi := (infinite_points_line L).sdiff (finite_zero_points_on_line g L hg)
  apply hi.mono
  rintro x ⟨hx, hxg⟩
  refine ⟨hx, eval_eq_zero_of_lineOn hf hx, ?_⟩
  intro hgx
  exact hxg ⟨hx, hgx⟩

/-- An infinite family of contained lines includes a line meeting a principal open
infinitely, even after excluding any finite family. -/
theorem exists_line_infinite_principalOpen {f g : Poly K} (hf : Irreducible f)
    (hg : ¬ f ∣ g) (F B : Set (Line K)) (hF : F.Infinite) (hB : B.Finite)
    (hcontained : ∀ L ∈ F, LineOn f L) :
    ∃ L ∈ F, L ∉ B ∧ {x : Point K | x ∈ L.1 ∧ x ∈ principalOpen f g}.Infinite := by
  have hbad : {L : Line K | LineOn f L ∧ LineOn g L}.Finite :=
    finite_common_lines_of_not_dvd f g hf hg
  obtain ⟨L, hLF, hLbad⟩ := (hF.sdiff (hB.union hbad)).nonempty
  have hLnotB : L ∉ B := fun h => hLbad (Or.inl h)
  have hLnotg : ¬ LineOn g L := fun h => hLbad (Or.inr ⟨hcontained L hLF, h⟩)
  exact ⟨L, hLF, hLnotB, infinite_principalOpen_on_line (hcontained L hLF) hLnotg⟩

end ExplicitRIP.GuthZahl.RuledSurfaces
end
