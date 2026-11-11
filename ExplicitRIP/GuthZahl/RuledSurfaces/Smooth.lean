/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.RuledSurfaces.Tangent
public import ExplicitRIP.GuthZahl.RuledSurfaces.Gradient
public import ExplicitRIP.GuthZahl.RuledSurfaces.OpenSet
public import ExplicitRIP.GuthZahl.RuledSurfaces.CommonLines

/-!
# Finiteness of contained lines through smooth points

The tangent equation is linear. For a nonplane irreducible surface it is not
divisible by the surface equation, so the common-line finiteness theorem
applies to all contained lines through the point.
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K]

/-- The affine linear equation determined by the gradient at a point. -/
noncomputable def tangentEquation (f : Poly K) (x : Point K) : Poly K :=
  ∑ i : Fin 3, MvPolynomial.C (MvPolynomial.eval x (MvPolynomial.pderiv i f)) *
    (MvPolynomial.X i - MvPolynomial.C (x i))

/-- Evaluation of the tangent equation is the gradient applied to displacement. -/
theorem eval_tangentEquation (f : Poly K) (x y : Point K) :
    MvPolynomial.eval y (tangentEquation f x) = tangentFunctional f x (y - x) := by
  simp only [tangentEquation, tangentFunctional, map_sum, map_mul, map_sub,
    MvPolynomial.eval_C, MvPolynomial.eval_X, LinearMap.coe_mk, AddHom.coe_mk, mul_sub,
    Finset.sum_sub_distrib]

/-- The coefficient of a tangent equation records the corresponding partial derivative. -/
theorem coeff_tangentEquation (f : Poly K) (x : Point K) (i : Fin 3) :
    (tangentEquation f x).coeff (Finsupp.single i 1) =
      MvPolynomial.eval x (MvPolynomial.pderiv i f) := by
  have hi0 : (0 : Fin 3 →₀ ℕ) ≠ Finsupp.single i 1 :=
    Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero)
  simp only [tangentEquation, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_sub, MvPolynomial.coeff_X, MvPolynomial.coeff_C, hi0, ↓reduceIte,
    sub_zero, Finsupp.single_left_inj one_ne_zero]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- At a smooth point the tangent equation has total degree one. -/
theorem totalDegree_tangentEquation (f : Poly K) (x : Point K)
    (hsmooth : ∃ i : Fin 3, MvPolynomial.eval x (MvPolynomial.pderiv i f) ≠ 0) :
    (tangentEquation f x).totalDegree = 1 := by
  apply le_antisymm
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro i hi
    apply (MvPolynomial.totalDegree_mul _ _).trans
    simpa only [MvPolynomial.totalDegree_C, zero_add, MvPolynomial.totalDegree_X] using
      MvPolynomial.totalDegree_sub_C_le (MvPolynomial.X i : Poly K) (x i)
  · obtain ⟨i, hi⟩ := hsmooth
    have hm : Finsupp.single i 1 ∈ (tangentEquation f x).support :=
      MvPolynomial.mem_support_iff.mpr ((coeff_tangentEquation f x i).trans_ne hi)
    simpa only [Finsupp.sum_single_index, mul_one] using MvPolynomial.le_totalDegree hm

/-- A contained line through the base point is contained in the tangent equation. -/
theorem lineOn_tangentEquation [Infinite K] {f : Poly K} {L : Line K}
    (hL : LineOn f L) {x : Point K} (hx : x ∈ L.1) : LineOn (tangentEquation f x) L := by
  apply (lineOn_iff_eval_eq_zero _ L).2
  intro y hy
  rw [eval_tangentEquation]
  exact tangentFunctional_eq_zero_of_lineOn hL hx (AffineSubspace.vsub_mem_direction hy hx)

/-- A nonplane irreducible surface contains only finitely many lines through a smooth point. -/
theorem finite_lines_through_smooth_point [Infinite K] {f : Poly K}
    (hf : Irreducible f) (hnonplane : f.totalDegree ≠ 1) (x : Point K)
    (hsmooth : ∃ i : Fin 3, MvPolynomial.eval x (MvPolynomial.pderiv i f) ≠ 0) :
    {L : Line K | x ∈ L.1 ∧ LineOn f L}.Finite := by
  apply (finite_common_lines_of_not_dvd f (tangentEquation f x) hf
    (not_dvd_of_totalDegree_eq_one hf hnonplane (totalDegree_tangentEquation f x hsmooth))).subset
  intro L hL
  exact ⟨hL.2, lineOn_tangentEquation hL.2 hL.1⟩

/-- A nonplane doubly ruled irreducible surface has a nonempty principal open
with finitely many, and at least two, contained lines through every point. -/
theorem exists_principalOpen_finite_fibers [IsAlgClosed K] {f : Poly K}
    (hf : Irreducible f) (hruled : DoublyRuled f) (hnonplane : f.totalDegree ≠ 1) :
    ∃ g : Poly K, ¬ f ∣ g ∧ (principalOpen f g).Nonempty ∧
      ∀ x ∈ principalOpen f g,
        {L : Line K | x ∈ L.1 ∧ LineOn f L}.Finite ∧
        ∃ L M : Line K, L ≠ M ∧ x ∈ L.1 ∧ x ∈ M.1 ∧ LineOn f L ∧ LineOn f M := by
  obtain ⟨g, hg, -, hruled⟩ := hruled
  obtain ⟨i, hi⟩ := exists_pderiv_ne_zero hf
  have hdi := not_dvd_pderiv hf hi
  have hnotdiv : ¬ f ∣ g * MvPolynomial.pderiv i f :=
    fun hdiv => (hf.prime.dvd_mul.mp hdiv).elim hg hdi
  refine ⟨g * MvPolynomial.pderiv i f, hnotdiv, principalOpen_nonempty _ _ hf hnotdiv, ?_⟩
  intro x hx
  obtain ⟨hxf, hxg⟩ := hx
  rw [map_mul, mul_ne_zero_iff] at hxg
  exact ⟨finite_lines_through_smooth_point hf hnonplane x ⟨i, hxg.2⟩,
    hruled x ⟨hxf, hxg.1⟩⟩

end ExplicitRIP.GuthZahl.RuledSurfaces
end
