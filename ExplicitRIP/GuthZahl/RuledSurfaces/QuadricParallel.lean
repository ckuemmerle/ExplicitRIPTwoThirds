/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.RuledSurfaces.QuadricJoin
public import ExplicitRIP.GuthZahl.RuledSurfaces.LinearEquation

/-!
# Parallel lines on a quadric containing skew lines

The directional derivative is affine linear. If three parallel contained lines
annihilate it, either they lie in its plane or the derivative is identically
zero. In the latter case, a contained line in another direction generates
infinitely many parallel contained lines in a plane. Both cases are impossible.
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K]

/-- The polynomial directional derivative along a fixed vector. -/
noncomputable def directionalEquation (q : Poly K) (v : Point K) : Poly K :=
  ∑ i : Fin 3, MvPolynomial.C (v i) * MvPolynomial.pderiv i q

theorem eval_directionalEquation (q : Poly K) (v x : Point K) :
    MvPolynomial.eval x (directionalEquation q v) = tangentFunctional q x v := by
  simp only [directionalEquation, map_sum, map_mul, MvPolynomial.eval_C,
    tangentFunctional, LinearMap.coe_mk, AddHom.coe_mk, mul_comm]

theorem totalDegree_directionalEquation_le_one {q : Poly K} (hdegree : q.totalDegree = 2)
    (v : Point K) : (directionalEquation q v).totalDegree ≤ 1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  have h := totalDegree_pderiv_lt (f := q) (by omega) i
  omega

theorem lineOn_directionalEquation [Infinite K] {q : Poly K} {A : Line K}
    (hA : LineOn q A) (v : Point K) (hv : v ∈ A.1.direction) :
    LineOn (directionalEquation q v) A := by
  apply (lineOn_iff_eval_eq_zero _ _).mpr
  intro x hx
  rw [eval_directionalEquation]
  exact tangentFunctional_eq_zero_of_lineOn hA hx hv

/-- A vanishing directional derivative and a contained line in that direction exclude
contained lines in another direction on an irreducible quadric. -/
theorem direction_eq_of_directionalEquation_zero [Infinite K] {q : Poly K}
    (hq : Irreducible q) (hdegree : q.totalDegree = 2)
    (A D : Line K) (hA : LineOn q A) (hD : LineOn q D)
    (v : Point K) (hv : v ∈ A.1.direction) (hv0 : v ≠ 0)
    (hφ : directionalEquation q v = 0) : D.1.direction = A.1.direction := by
  classical
  by_contra hdir
  obtain ⟨a, ha⟩ := line_nonempty A
  obtain ⟨d, hd⟩ := line_nonempty D
  let E := lineThrough d v hv0
  have hEdir : E.1.direction = A.1.direction := by
    rw [direction_lineThrough]
    exact (eq_span_singleton_of_mem_of_finrank_eq_one A.2 hv hv0).symm
  have hDE : D ≠ E := fun h => hdir (h.symm ▸ hEdir)
  obtain ⟨P, hP, hDP, hEP⟩ := coplanar_of_mem_of_ne hd (base_mem_lineThrough d v hv0) hDE
  have hvP : v ∈ P.direction :=
    AffineSubspace.direction_le hEP (vector_mem_direction_lineThrough d v hv0)
  have : Infinite (D.1 : Set (Point K)) := Set.infinite_coe_iff.mpr (infinite_points_line D)
  let F : (D.1 : Set (Point K)) → Line K := fun z => lineThrough z.1 v hv0
  have hzF (z : (D.1 : Set (Point K))) : z.1 ∈ (F z).1 := base_mem_lineThrough _ _ _
  have hFinj : Function.Injective F := by
    intro z z' heq
    by_contra hne
    have hne' : z.1 ≠ z'.1 := fun h => hne (Subtype.ext h)
    have hz' : z'.1 ∈ (F z).1 := heq.symm ▸ hzF z'
    have hFD : F z = D := line_eq_of_le
      (line_le_of_two_points hne' (hzF z) hz' z.2 z'.2)
    apply hdir
    rw [← hFD, direction_lineThrough]
    exact (eq_span_singleton_of_mem_of_finrank_eq_one A.2 hv hv0).symm
  have hF := Set.infinite_range_of_injective hFinj
  apply hF
  apply (finite_lines_in_plane hq (by omega) P hP).subset
  rintro L ⟨z, rfl⟩
  constructor
  · apply lineOn_lineThrough_of_coefficients hdegree.le z.1 v hv0
      (eval_eq_zero_of_lineOn hD z.2)
    · rw [← eval_directionalEquation, hφ, map_zero]
    · rw [coeff_restrictLine_eq_of_totalDegree_le hdegree.le z.1 a v,
        hA a ha v hv, Polynomial.coeff_zero]
  · intro y hy
    obtain ⟨t, rfl⟩ := (mem_lineThrough z.1 v y hv0).mp hy
    simpa only [vadd_eq_add, add_comm] using
      P.vadd_mem_of_mem_direction (P.direction.smul_mem t hvP) (hDP z.2)

/-- A quadric containing two skew lines cannot contain three distinct parallel lines. -/
theorem not_three_parallel_lines [Infinite K] {q : Poly K} (hq : Irreducible q)
    (hdegree : q.totalDegree = 2) (U V : Line K) (hUV : ¬ Coplanar U V)
    (hU : LineOn q U) (hV : LineOn q V) (A B C : Line K)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hA : LineOn q A) (hB : LineOn q B) (hC : LineOn q C)
    (hdAB : A.1.direction = B.1.direction) (hdAC : A.1.direction = C.1.direction) : False := by
  obtain ⟨a, v, ha, hv, hv0, hparam⟩ := exists_line_parametrization A
  let φ := directionalEquation q v
  have hφA : LineOn φ A := lineOn_directionalEquation hA v hv
  have hφB : LineOn φ B := lineOn_directionalEquation hB v (hdAB ▸ hv)
  have hφC : LineOn φ C := lineOn_directionalEquation hC v (hdAC ▸ hv)
  by_cases hφ : φ = 0
  · have hUA := direction_eq_of_directionalEquation_zero hq hdegree A U hA hU v hv hv0 hφ
    have hVA := direction_eq_of_directionalEquation_zero hq hdegree A V hA hV v hv hv0 hφ
    exact hUV (coplanar_of_direction_eq (hUA.trans hVA.symm))
  · have hpos := totalDegree_pos_of_nonzero_not_isUnit hφ (not_isUnit_of_lineOn hφA)
    have hle : φ.totalDegree ≤ 1 := totalDegree_directionalEquation_le_one hdegree v
    have hφdegree : φ.totalDegree = 1 := by omega
    let P := tangentPlane φ a
    have hP : Module.finrank K P.direction = 2 :=
      finrank_direction_tangentPlane φ a
        (exists_pderiv_eval_ne_zero_of_totalDegree_eq_one hφdegree a)
    have hall (L : Line K) (hL : LineOn φ L) : L.1 ≤ P := by
      intro x hx
      exact mem_tangentPlane_of_eval_eq_zero_of_totalDegree_le_one hφdegree.le
        (eval_eq_zero_of_lineOn hφA ha) (eval_eq_zero_of_lineOn hL hx)
    exact not_three_lines_in_plane hq hdegree P hP A B C hAB hAC hBC hA hB hC
      (hall A hφA) (hall B hφB) (hall C hφC)

end ExplicitRIP.GuthZahl.RuledSurfaces
end
