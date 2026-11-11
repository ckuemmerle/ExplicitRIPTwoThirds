/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# The induced edge count

Source: [KM, Lemma 3].
-/

@[expose] public section

open scoped Matrix

/-- The quantity `e(U)` in [KM, Lemma 3]: the number of edges of the simple graph `G` with both
endpoints in `U`. -/
def ExplicitRIP.inducedEdgeCount {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (U : Finset V) : ℕ :=
  (U.sym2.filter (fun e => e ∈ G.edgeSet)).card
