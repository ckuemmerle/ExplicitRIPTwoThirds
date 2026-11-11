/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Defs
import ExplicitRIP.GuthZahl.RuledSurfaces.LineThroughFacts

/-!
# From trapped tangent directions to two contained lines

The existing parametrized-line construction turns nonproportional directions
whose restrictions vanish into distinct algebraically contained affine lines.
-/

public section

namespace ExplicitRIP.GuthZahl.Structure

open RuledSurfaces

theorem two_lines_of_trapped_directions {K : Type*} [Field K] [Infinite K]
    (f : Poly K) (x : Point K) (r : ℕ)
    (ht : TwoTangentDirections f x r)
    (htrap : ∀ v : Point K, v ≠ 0 →
      TangentToOrder f x v r → restrictLine f x v = 0) :
    ∃ L M : Line K, L ≠ M ∧ x ∈ L.1 ∧ x ∈ M.1 ∧ LineOn f L ∧ LineOn f M := by
  obtain ⟨v, w, hv, hw, hnot, htv, htw⟩ := ht
  refine ⟨lineThrough x v hv, lineThrough x w hw, ?_,
    base_mem_lineThrough x v hv, base_mem_lineThrough x w hw,
    (lineOn_lineThrough_iff f x v hv).mpr (htrap v hv htv),
    (lineOn_lineThrough_iff f x w hw).mpr (htrap w hw htw)⟩
  intro heq
  have hwmem := vector_mem_direction_lineThrough x w hw
  rw [← heq, direction_lineThrough, Submodule.mem_span_singleton] at hwmem
  obtain ⟨a, ha⟩ := hwmem
  exact hnot ⟨a, ha.symm⟩

end ExplicitRIP.GuthZahl.Structure

end
