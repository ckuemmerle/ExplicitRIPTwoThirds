/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.SelectedVertices

/-!
# The norm-graph selection in light-cone coordinates

The light-cone selection is cut out by `r - z - N(r + z, x, y) ∈ T`. It is the sphere-map image
of the norm graph in Hermitian coordinates, and the sphere map preserves the contact graph.
The selection `ExplicitRIP.selectedVertices` of [KM, (15)] instead uses the graph
`r - N(x, y, z) ∈ T` directly in contact coordinates.
-/

@[expose] public section

namespace ExplicitRIP.Contact

/-- The light-cone norm graph, cut out by `r - z - N(r + z, x, y) ∈ T`, obtained by applying
the sphere map to `hermitianSelectedVertices`. -/
noncomputable def lightConeSelectedVertices (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
    (T : Finset (ZMod p)) : Finset (ZMod p × ZMod p × ZMod p × ZMod p) :=
  Finset.univ.filter fun v =>
    v.2.2.2 - v.2.2.1 - fieldNorm p (v.2.2.2 + v.2.2.1, v.1, v.2.1) ∈ T

end ExplicitRIP.Contact
