/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.RuledSurfaces.LineChart
public import ExplicitRIP.GuthZahl.RuledSurfaces.AffineGeometry

/-! # Direction and containment formulas for parametrized lines -/

public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K]

@[simp]
theorem direction_lineThrough (a v : Point K) (hv : v ≠ 0) :
    (lineThrough a v hv).1.direction = Submodule.span K {v} := by
  exact AffineSubspace.direction_mk' _ _

@[simp]
theorem base_mem_lineThrough (a v : Point K) (hv : v ≠ 0) :
    a ∈ (lineThrough a v hv).1 := (mem_lineThrough a v a hv).mpr ⟨0, by simp⟩

theorem vector_mem_direction_lineThrough (a v : Point K) (hv : v ≠ 0) :
    v ∈ (lineThrough a v hv).1.direction := by
  rw [direction_lineThrough]
  exact Submodule.mem_span_singleton_self _

theorem lineOn_lineThrough_iff [Infinite K] (f : Poly K) (a v : Point K) (hv : v ≠ 0) :
    LineOn f (lineThrough a v hv) ↔ restrictLine f a v = 0 :=
  lineOn_iff_restrictLine_eq_zero f _ a (base_mem_lineThrough a v hv)
    v (vector_mem_direction_lineThrough a v hv) hv

theorem coplanar_lineThrough_of_direction {A : Line K} (x v : Point K)
    (hv : v ∈ A.1.direction) (hv0 : v ≠ 0) : Coplanar (lineThrough x v hv0) A := by
  apply coplanar_of_direction_eq
  rw [direction_lineThrough]
  exact (eq_span_singleton_of_mem_of_finrank_eq_one A.2 hv hv0).symm

end ExplicitRIP.GuthZahl.RuledSurfaces
end
