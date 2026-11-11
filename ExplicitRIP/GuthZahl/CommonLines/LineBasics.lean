/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Basic.Restriction

/-!
# Elementary properties of the fixed line carrier

Every line has a point and a nonzero direction. A common point and a common
nonzero direction determine a line. Algebraic containment implies vanishing at
all incident points and excludes nonzero polynomials of total degree zero.
-/

public section

namespace ExplicitRIP.GuthZahl.CommonLines

theorem line_direction_ne_bot {K : Type*} [Field K] (L : Line K) : L.val.direction ≠ ⊥ := by
  intro h
  have hd := L.property
  rw [h, finrank_bot] at hd
  exact Nat.zero_ne_one hd

theorem exists_line_direction_ne_zero {K : Type*} [Field K] (L : Line K) :
    ∃ v ∈ L.val.direction, v ≠ 0 :=
  L.val.direction.ne_bot_iff.mp (line_direction_ne_bot L)

theorem line_eq_of_point_of_direction {K : Type*} [Field K]
    (L M : Line K) {a v : Point K} (haL : a ∈ L.val) (haM : a ∈ M.val)
    (hvL : v ∈ L.val.direction) (hvM : v ∈ M.val.direction) (hv : v ≠ 0) : L = M := by
  apply Subtype.ext
  apply AffineSubspace.ext_of_direction_eq _ ⟨a, haL, haM⟩
  rw [eq_span_singleton_of_mem_of_finrank_eq_one L.property hvL hv,
    eq_span_singleton_of_mem_of_finrank_eq_one M.property hvM hv]

theorem line_add_smul_mem {K : Type*} [Field K] (L : Line K)
    {a v : Point K} (ha : a ∈ L.val) (hv : v ∈ L.val.direction) (t : K) :
    a + t • v ∈ L.val := by
  simpa only [vadd_eq_add, add_comm] using
    AffineSubspace.vadd_mem_of_mem_direction (L.val.direction.smul_mem t hv) ha

theorem not_lineOn_of_totalDegree_eq_zero {K : Type*} [Field K]
    {f : Poly K} (hf : f ≠ 0) (hd : f.totalDegree = 0) (L : Line K) : ¬ LineOn f L := by
  intro h
  obtain ⟨x, hx⟩ := line_nonempty L
  have hC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hd
  have hc := eval_eq_zero_of_lineOn h hx
  rw [hC, MvPolynomial.eval_C] at hc
  apply hf
  rw [hC, hc, map_zero]

end ExplicitRIP.GuthZahl.CommonLines
end
