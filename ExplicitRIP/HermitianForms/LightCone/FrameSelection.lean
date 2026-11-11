/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.HermitianForms.LightCone.Coordinates
public import ExplicitRIP.HermitianForms.Defs.SelectedVertices

/-!
# The Hermitian-coordinate selection in sphere coordinates

Membership in `hermitianSelectedVertices` becomes `r - z = N(r + z, x, y) + t`, `t ∈ T`, under
the sphere map. This is the light-cone image of the Hermitian norm graph; [KM, (15)] applies
the norm-graph formula directly in contact coordinates.
-/

public section

namespace ExplicitRIP.LightCone

variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

/-- Membership in the image defining the selector, including an empty translate set. -/
theorem mem_selectedVertices_iff (T : Finset (ZMod p))
    (H : ZMod p × ZMod p × ZMod p × ZMod p) :
    H ∈ hermitianSelectedVertices p T ↔
      ∃ t ∈ T, H.2.2.2 = fieldNorm p (H.1, H.2.1, H.2.2.1) + t := by
  classical
  rw [hermitianSelectedVertices, Finset.mem_image]
  constructor
  · rintro ⟨⟨w, t⟩, hwt, rfl⟩
    exact ⟨t, (Finset.mem_product.mp hwt).2, rfl⟩
  · rintro ⟨t, ht, hH⟩
    refine ⟨((H.1, H.2.1, H.2.2.1), t),
      Finset.mem_product.mpr ⟨Finset.mem_univ _, ht⟩, ?_⟩
    exact Prod.ext rfl (Prod.ext rfl (Prod.ext rfl hH.symm))

theorem mem_selectedVertices_iff_sphereCoords (T : Finset (ZMod p))
    (H : ZMod p × ZMod p × ZMod p × ZMod p) :
    H ∈ hermitianSelectedVertices p T ↔
      ∃ t ∈ T, (sphereCoords p H).2.2.2 - (sphereCoords p H).2.2.1 =
        fieldNorm p ((sphereCoords p H).2.2.2 + (sphereCoords p H).2.2.1,
          (sphereCoords p H).1, (sphereCoords p H).2.1) + t := by
  rw [mem_selectedVertices_iff]
  simp only [sphereCoords_radius_sub_height, sphereCoords_radius_add_height]
  rfl

end ExplicitRIP.LightCone
