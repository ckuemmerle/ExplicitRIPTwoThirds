/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.HostGram
public import ExplicitRIP.HermitianForms.Defs.HostGram
public import ExplicitRIP.HermitianForms.HereditaryDensity.Quadratic
public import ExplicitRIP.Contact.Barrier.Reindex

/-!
# Coordinate transport for host Gram matrices

The sphere-coordinate equivalence identifies contact-coordinate and
Hermitian-coordinate Gram matrices, including every principal submatrix.
-/

@[expose] public section

namespace ExplicitRIP.HostCoordinates

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

/-- Identify a pulled-back column set with the original contact-coordinate set. -/
def columnEquiv (Γ : Finset (ZMod p × ZMod p × ZMod p × ZMod p)) :
    Γ.map (sphereMap p).symm.toEmbedding ≃ Γ where
  toFun x := ⟨sphereMap p x.val, by
    simpa only [Finset.mem_map_equiv, Equiv.symm_symm] using x.property⟩
  invFun x := ⟨(sphereMap p).symm x.val,
    Finset.mem_map.mpr ⟨x.val, x.property, rfl⟩⟩
  left_inv x := Subtype.ext ((sphereMap p).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((sphereMap p).apply_symm_apply x.val)

theorem columnEquiv_apply_val (Γ : Finset (ZMod p × ZMod p × ZMod p × ZMod p))
    (x : Γ.map (sphereMap p).symm.toEmbedding) :
    (columnEquiv p Γ x).val = sphereMap p x.val := rfl

end ExplicitRIP.HostCoordinates
