/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.RuledSurfaces.UniversalLine

/-!
# Constructibility of crossing line families

For a finite list of fixed lines, the contained lines meeting each of them in a
principal open form an explicitly parametrized incidence family. Its union of
points is constructible by projection of polynomial equations and inequalities.
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K]

/-- The union of the points on a family of lines. -/
def lineUnion (F : Set (Line K)) : Set (Point K) := {x | ∃ L ∈ F, x ∈ L.1}

/-- Contained lines meeting every member of a finite family in the chosen principal open. -/
def crossingFamily (f g : Poly K) (G : Finset (Line K)) : Set (Line K) :=
  {L | LineOn f L ∧ ∀ M ∈ G, ∃ x ∈ principalOpen f g, x ∈ L.1 ∧ x ∈ M.1}

/-- Equality between polynomial coordinate maps is constructible. -/
theorem isPolynomialConstructible_map_eq {σ ι : Type*} [Finite ι]
    (p q : ι → MvPolynomial σ K) :
    IsPolynomialConstructible {z : σ → K |
      (fun i => MvPolynomial.eval z (p i)) = (fun i => MvPolynomial.eval z (q i))} := by
  have h := IsPolynomialConstructible.forall_finite
    (fun i => {z : σ → K | MvPolynomial.eval z (p i - q i) = 0})
    (fun i => isPolynomialConstructible_zero _)
  convert h using 1
  ext z
  simp only [Set.mem_ofPred_eq, map_sub, sub_eq_zero, funext_iff]

/-- Nonzero polynomial coordinate vectors form a constructible set. -/
theorem isPolynomialConstructible_map_ne_zero {σ ι : Type*} [Finite ι]
    (p : ι → MvPolynomial σ K) :
    IsPolynomialConstructible {z : σ → K | (fun i => MvPolynomial.eval z (p i)) ≠ 0} := by
  have h := (isPolynomialConstructible_map_eq p (fun _ => 0)).compl
  convert h using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, map_zero, Pi.zero_def]

/-- The union of a finite crossing family is constructible at field points. -/
theorem isPolynomialConstructible_crossing_lineUnion [IsAlgClosed K]
    (f g : Poly K) (G : Finset (Line K)) :
    IsPolynomialConstructible (lineUnion (crossingFamily f g G)) := by
  classical
  choose b w hb hw hw0 hparam using fun M : G => exists_line_parametrization M.1
  let W := (Fin 3 ⊕ Fin 3) ⊕ (Unit ⊕ (G × Fin 2))
  let σ := Fin 3 ⊕ W
  let a : (σ → K) → Point K := fun z i => z (Sum.inr (Sum.inl (Sum.inl i)))
  let v : (σ → K) → Point K := fun z i => z (Sum.inr (Sum.inl (Sum.inr i)))
  let u : (σ → K) → K := fun z => z (Sum.inr (Sum.inr (Sum.inl ())))
  let s : G → (σ → K) → K := fun M z => z (Sum.inr (Sum.inr (Sum.inr (M, 0))))
  let t : G → (σ → K) → K := fun M z => z (Sum.inr (Sum.inr (Sum.inr (M, 1))))
  let A : Fin 3 → MvPolynomial σ K := fun i =>
    MvPolynomial.X (Sum.inr (Sum.inl (Sum.inl i)))
  let V : Fin 3 → MvPolynomial σ K := fun i =>
    MvPolynomial.X (Sum.inr (Sum.inl (Sum.inr i)))
  let U : MvPolynomial σ K := MvPolynomial.X (Sum.inr (Sum.inr (Sum.inl ())))
  let S : G → MvPolynomial σ K := fun M =>
    MvPolynomial.X (Sum.inr (Sum.inr (Sum.inr (M, 0))))
  let T : G → MvPolynomial σ K := fun M =>
    MvPolynomial.X (Sum.inr (Sum.inr (Sum.inr (M, 1))))
  let P : Set (σ → K) := {z | v z ≠ 0 ∧ restrictLine f (a z) (v z) = 0 ∧
    (fun i => z (Sum.inl i)) = a z + u z • v z ∧
    ∀ M : G, a z + s M z • v z = b M + t M z • w M ∧
      MvPolynomial.eval (a z + s M z • v z) g ≠ 0}
  have hnonzero : IsPolynomialConstructible {z : σ → K | v z ≠ 0} := by
    simpa only [V, v, MvPolynomial.eval_X] using isPolynomialConstructible_map_ne_zero V
  have hrestriction : IsPolynomialConstructible {z : σ → K |
      restrictLine f (a z) (v z) = 0} := by
    simpa only [A, V, a, v, MvPolynomial.eval_X] using
      isPolynomialConstructible_restriction_zero f A V
  have hpoint : IsPolynomialConstructible {z : σ → K |
      (fun i => z (Sum.inl i)) = a z + u z • v z} := by
    simpa only [A, V, U, a, v, u, map_add, map_mul, MvPolynomial.eval_X,
      Pi.add_def, Pi.smul_def, smul_eq_mul, Set.ofPred_and] using
      isPolynomialConstructible_map_eq (fun i => MvPolynomial.X (Sum.inl i))
        (fun i => A i + U * V i)
  have hcross (M : G) : IsPolynomialConstructible {z : σ → K |
      a z + s M z • v z = b M + t M z • w M ∧
      MvPolynomial.eval (a z + s M z • v z) g ≠ 0} := by
    have heq := isPolynomialConstructible_map_eq (fun i => A i + S M * V i)
      (fun i => MvPolynomial.C (b M i) + T M * MvPolynomial.C (w M i))
    have hne := isPolynomialConstructible_eval_ne_zero g (fun i => A i + S M * V i)
    simpa only [A, V, S, T, a, v, s, t, map_add, map_mul, MvPolynomial.eval_X,
      MvPolynomial.eval_C, Pi.add_def, Pi.smul_def, smul_eq_mul, Set.ofPred_and] using heq.inter hne
  have hP : IsPolynomialConstructible P :=
    hnonzero.inter (hrestriction.inter (hpoint.inter
      (IsPolynomialConstructible.forall_finite _ hcross)))
  have hprojection := hP.exists_coordinates
  have heq : {x : Point K | ∃ y : W → K, Sum.elim x y ∈ P} =
      lineUnion (crossingFamily f g G) := by
    ext x
    constructor
    · rintro ⟨y, h⟩
      let z : σ → K := Sum.elim x y
      change v z ≠ 0 ∧ restrictLine f (a z) (v z) = 0 ∧
        (fun i => z (Sum.inl i)) = a z + u z • v z ∧
        ∀ M : G, a z + s M z • v z = b M + t M z • w M ∧
          MvPolynomial.eval (a z + s M z • v z) g ≠ 0 at h
      let L : Line K := lineThrough (a z) (v z) h.1
      have haL : a z ∈ L.1 := (mem_lineThrough _ _ _ h.1).mpr ⟨0, by simp⟩
      have hvL : v z ∈ L.1.direction := by
        change v z ∈ (AffineSubspace.mk' (a z) (Submodule.span K {v z})).direction
        rw [AffineSubspace.direction_mk']
        exact Submodule.mem_span_singleton_self _
      have hfL : LineOn f L := (lineOn_iff_restrictLine_eq_zero f _ _ haL _ hvL h.1).mpr h.2.1
      refine ⟨L, ⟨hfL, ?_⟩, ?_⟩
      · intro M hM
        let m : G := ⟨M, hM⟩
        let p : Point K := a z + s m z • v z
        have hpL : p ∈ L.1 := (mem_lineThrough _ _ _ h.1).mpr ⟨s m z, rfl⟩
        have hpM : p ∈ M.1 := (hparam m p).mpr ⟨t m z, (h.2.2.2 m).1.symm⟩
        exact ⟨p, ⟨eval_eq_zero_of_lineOn hfL hpL, (h.2.2.2 m).2⟩, hpL, hpM⟩
      · apply (mem_lineThrough _ _ _ h.1).mpr
        exact ⟨u z, h.2.2.1.symm⟩
    · rintro ⟨L, hL, hxL⟩
      obtain ⟨a₀, v₀, ha₀, hv₀, hv₀0, hLparam⟩ := exists_line_parametrization L
      obtain ⟨u₀, hu₀⟩ := (hLparam x).mp hxL
      have hmeet : ∀ M : G, ∃ p : Point K,
          p ∈ principalOpen f g ∧ p ∈ L.1 ∧ p ∈ M.1.1 := by
        intro M
        exact hL.2 M.1 M.2
      choose p hpO hpL hpM using hmeet
      choose s₀ hs₀ using fun M : G => (hLparam (p M)).mp (hpL M)
      choose t₀ ht₀ using fun M : G => (hparam M (p M)).mp (hpM M)
      let y : W → K := Sum.elim (Sum.elim a₀ v₀)
        (Sum.elim (fun _ : Unit => u₀) (fun (j : G × Fin 2) => if j.2 = 0 then s₀ j.1 else t₀ j.1))
      refine ⟨y, ?_⟩
      change v (Sum.elim x y) ≠ 0 ∧ restrictLine f (a (Sum.elim x y)) (v (Sum.elim x y)) = 0 ∧
        (fun i => Sum.elim x y (Sum.inl i)) =
          a (Sum.elim x y) + u (Sum.elim x y) • v (Sum.elim x y) ∧
        ∀ M : G, a (Sum.elim x y) + s M (Sum.elim x y) • v (Sum.elim x y) =
          b M + t M (Sum.elim x y) • w M ∧
          MvPolynomial.eval (a (Sum.elim x y) + s M (Sum.elim x y) • v (Sum.elim x y)) g ≠ 0
      simp only [a, v, u, s, t, y, Sum.elim_inl, Sum.elim_inr, ↓reduceIte,
        show (1 : Fin 2) ≠ 0 by decide]
      refine ⟨hv₀0, hL.1 a₀ ha₀ v₀ hv₀, hu₀.symm, ?_⟩
      intro M
      exact ⟨(hs₀ M).trans (ht₀ M).symm, by rw [hs₀ M]; exact (hpO M).2⟩
  rw [heq] at hprojection
  exact hprojection

end ExplicitRIP.GuthZahl.RuledSurfaces
end
