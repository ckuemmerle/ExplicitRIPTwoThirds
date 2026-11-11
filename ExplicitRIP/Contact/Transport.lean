/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.HostGram
public import ExplicitRIP.Contact.LightConeSelection
public import ExplicitRIP.HermitianForms.Defs.HostGram
public import ExplicitRIP.HermitianForms.LightCone.FrameSelection
import ExplicitRIP.HermitianForms.HereditaryDensity.Quadratic

/-!
# Transport from Hermitian coordinates to contact coordinates

The sphere map identifies the Hermitian coordinates `(a, b₁, b₂, c)` with the coordinates
`(x, y, z, r)` of [KM, Section 4.1]. It transports the host Gram matrix without changing its
entries and maps the Hermitian norm-graph selection to the light-cone selection
`r - z - N(r + z, x, y) ∈ T`, preserving cardinality.
-/

@[expose] public section

namespace ExplicitRIP.Contact

variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

/-- The sphere map `(a, b₁, b₂, c) ↦ (b₁, b₂, (a - c)/2, (a + c)/2)` from Hermitian
coordinates to the contact coordinates of [KM, Section 4.1], as an equivalence. -/
def sphereMap : (ZMod p × ZMod p × ZMod p × ZMod p) ≃ (ZMod p × ZMod p × ZMod p × ZMod p) :=
  (LightCone.sphereEquiv p).toEquiv

theorem sphereMap_apply (x : ZMod p × ZMod p × ZMod p × ZMod p) :
    sphereMap p x = ExplicitRIP.sphereCoords p x := rfl

theorem sphereMap_symm_apply (v : ZMod p × ZMod p × ZMod p × ZMod p) :
    (sphereMap p).symm v = (v.2.2.2 + v.2.2.1, v.1, v.2.1, v.2.2.2 - v.2.2.1) := rfl

theorem sphereMap_add (x y : ZMod p × ZMod p × ZMod p × ZMod p) :
    sphereMap p (x + y) = sphereMap p x + sphereMap p y :=
  (LightCone.sphereEquiv p).map_add x y

theorem sphereMap_smul (t : ZMod p) (x : ZMod p × ZMod p × ZMod p × ZMod p) :
    sphereMap p (t • x) = t • sphereMap p x :=
  (LightCone.sphereEquiv p).map_smul t x

theorem contactGraph_adj_sphereMap (x y : ZMod p × ZMod p × ZMod p × ZMod p) :
    (ExplicitRIP.contactGraph p).Adj (sphereMap p x) (sphereMap p y) ↔
      (ExplicitRIP.hermitianGraph p).Adj x y := by
  rw [Edges.adj_iff_sphereContact, Edges.contact_iff]
  change (sphereMap p x ≠ sphereMap p y ∧
      (Edges.mq (sphereMap p x - sphereMap p y) = 0 ∨
        Edges.mq (sphereMap p y - sphereMap p x) = 0)) ↔
    x ≠ y ∧ Edges.mq (sphereMap p x - sphereMap p y) = 0
  rw [Edges.mq_sub_comm (sphereMap p y) (sphereMap p x), or_self,
    (sphereMap p).injective.ne_iff]

/-- `sphereMap` as a graph isomorphism. -/
def graphIso : ExplicitRIP.hermitianGraph p ≃g ExplicitRIP.contactGraph p where
  toEquiv := sphereMap p
  map_rel_iff' := by
    intro x y
    exact contactGraph_adj_sphereMap p x y

theorem graphIso_apply (x : ZMod p × ZMod p × ZMod p × ZMod p) : graphIso p x = sphereMap p x := rfl

theorem hostGram_sphereMap (K : Type*) [Field K] [CharZero K]
    (x y : ZMod p × ZMod p × ZMod p × ZMod p) :
    ExplicitRIP.hostGram K p (sphereMap p x) (sphereMap p y) =
      ExplicitRIP.hermitianHostGram K p x y := by
  classical
  simp only [hostGram, hermitianHostGram, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, SimpleGraph.adjMatrix_apply,
    contactGraph_adj_sphereMap, (sphereMap p).injective.eq_iff]

theorem hostGram_eq_submatrix (K : Type*) [Field K] [CharZero K] :
    ExplicitRIP.hostGram K p =
      (ExplicitRIP.hermitianHostGram K p).submatrix (sphereMap p).symm (sphereMap p).symm := by
  ext v w
  simpa only [Matrix.submatrix_apply, Equiv.apply_symm_apply] using
    hostGram_sphereMap p K ((sphereMap p).symm v) ((sphereMap p).symm w)

theorem sphereMap_mem_lightConeSelectedVertices_iff (T : Finset (ZMod p))
    (x : ZMod p × ZMod p × ZMod p × ZMod p) :
    sphereMap p x ∈ lightConeSelectedVertices p T ↔
      x ∈ ExplicitRIP.hermitianSelectedVertices p T := by
  classical
  rw [LightCone.mem_selectedVertices_iff_sphereCoords]
  simp only [lightConeSelectedVertices, Finset.mem_filter, Finset.mem_univ, true_and,
    sphereMap_apply]
  constructor
  · intro hx
    exact ⟨_, hx, by ring⟩
  · rintro ⟨t, ht, he⟩
    rwa [he, add_sub_cancel_left]

theorem lightConeSelectedVertices_eq_map (T : Finset (ZMod p)) :
    lightConeSelectedVertices p T =
      (ExplicitRIP.hermitianSelectedVertices p T).map (sphereMap p).toEmbedding := by
  classical
  ext v
  rw [Finset.mem_map_equiv]
  simpa only [Equiv.apply_symm_apply] using
    sphereMap_mem_lightConeSelectedVertices_iff p T ((sphereMap p).symm v)

theorem card_lightConeSelectedVertices (T : Finset (ZMod p)) :
    (lightConeSelectedVertices p T).card = T.card * p ^ 3 := by
  classical
  rw [lightConeSelectedVertices_eq_map, Finset.card_map, hermitianSelectedVertices]
  have hinj : Function.Injective
      (fun wt : (ZMod p × ZMod p × ZMod p) × ZMod p =>
        (wt.1.1, wt.1.2.1, wt.1.2.2, fieldNorm p wt.1 + wt.2)) := by
    intro u v h
    have hw : u.1 = v.1 :=
      Prod.ext (congrArg (fun z => z.1) h)
        (Prod.ext (congrArg (fun z => z.2.1) h) (congrArg (fun z => z.2.2.1) h))
    have ht : u.2 = v.2 := by
      have hc := congrArg (fun z => z.2.2.2) h
      dsimp only at hc
      rw [hw] at hc
      exact add_left_cancel hc
    exact Prod.ext hw ht
  rw [Finset.card_image_of_injective _ hinj]
  simp only [Finset.card_product, Finset.card_univ, Fintype.card_prod, ZMod.card]
  ring

theorem card_selectedVertices (T : Finset (ZMod p)) :
    (selectedVertices p T).card = T.card * p ^ 3 := by
  classical
  rw [selectedVertices]
  have hinj : Function.Injective
      (fun wt : (ZMod p × ZMod p × ZMod p) × ZMod p =>
        (wt.1.1, wt.1.2.1, wt.1.2.2, fieldNorm p wt.1 + wt.2)) := by
    intro u v h
    have hw : u.1 = v.1 :=
      Prod.ext (congrArg (fun z => z.1) h)
        (Prod.ext (congrArg (fun z => z.2.1) h) (congrArg (fun z => z.2.2.1) h))
    have ht : u.2 = v.2 := by
      have hc := congrArg (fun z => z.2.2.2) h
      dsimp only at hc
      rw [hw] at hc
      exact add_left_cancel hc
    exact Prod.ext hw ht
  rw [Finset.card_image_of_injective _ hinj]
  simp only [Finset.card_product, Finset.card_univ, Fintype.card_prod, ZMod.card]
  ring

end ExplicitRIP.Contact
