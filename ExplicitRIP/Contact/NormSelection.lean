/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.SelectedVertices
import ExplicitRIP.HermitianForms.LightCone.FrameSelection

/-!
# Translate labels for the norm-graph selection

The scalar `r - N(c)` uniquely labels the translate containing `(c,r)`. As coordinate sets,
the norm-graph selection [KM, (15)] and the Hermitian-coordinate norm graph have the same formula;
their ambient graphs are different.
-/

@[expose] public section

namespace ExplicitRIP.Contact

/-- The translate label of a point in norm-graph coordinates. -/
noncomputable def translateLabel (p : ℕ) [Fact p.Prime]
    (x : ZMod p × ZMod p × ZMod p × ZMod p) : ZMod p :=
  x.2.2.2 - fieldNorm p (x.1, x.2.1, x.2.2.1)

theorem mem_selectedVertices_iff (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
    (T : Finset (ZMod p)) (x : ZMod p × ZMod p × ZMod p × ZMod p) :
    x ∈ selectedVertices p T ↔ translateLabel p x ∈ T := by
  change x ∈ hermitianSelectedVertices p T ↔ _
  rw [LightCone.mem_selectedVertices_iff]
  constructor
  · rintro ⟨t, ht, he⟩
    simpa only [translateLabel, he, add_sub_cancel_left] using ht
  · intro ht
    exact ⟨translateLabel p x, ht, by dsimp [translateLabel]; ring⟩

end ExplicitRIP.Contact
