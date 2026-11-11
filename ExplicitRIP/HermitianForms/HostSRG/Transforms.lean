/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.HermitianForms.HostSRG.Coordinates
public import ExplicitRIP.HermitianForms.TracePairing.Basic

/-!
# Coordinate automorphisms

Elementary coordinate maps preserving the determinant-zero locus normalize pairs for the
common-neighbor counts in the Hermitian-forms model of `VO₄⁻(p)`. A nonzero second diagonal entry
need not be normalized to one: the norm-fiber count is independent of its nonzero value. These
counts give the strongly regular parameters of [KM, Section 3].
-/

@[expose] public section

namespace ExplicitRIP.Hfsrg

variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

/-- An additive coordinate equivalence preserving the determinant-zero locus
induces an automorphism of the Hermitian forms graph `hermitianGraph`. -/
def isoOfAddEquiv (e : Vertex p ≃+ Vertex p)
    (he : ∀ x, quad p (e x) = 0 ↔ quad p x = 0) :
    hermitianGraph p ≃g hermitianGraph p where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro x y
    change (hermitianGraph p).Adj (e x) (e y) ↔ _
    rw [adj_iff, adj_iff, ← map_sub, he, e.injective.ne_iff]

/-- Interchange the two diagonal coordinates. -/
def swap : Vertex p ≃+ Vertex p where
  toFun x := (x.2.2.2, x.2.1, x.2.2.1, x.1)
  invFun x := (x.2.2.2, x.2.1, x.2.2.1, x.1)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

omit [Fact (p % 4 = 3)] in
theorem quad_swap (x : Vertex p) : quad p (swap p x) = quad p x := by
  simp only [quad, swap, AddEquiv.coe_mk, Equiv.coe_fn_mk]
  ring

/-- Lower triangular Hermitian congruence with off-diagonal entry `r + i s`. -/
def shear (r s : ZMod p) : Vertex p ≃+ Vertex p where
  toFun x := (x.1, x.2.1 + r * x.1, x.2.2.1 + s * x.1,
    x.2.2.2 + 2 * r * x.2.1 + 2 * s * x.2.2.1 + (r ^ 2 + s ^ 2) * x.1)
  invFun x := (x.1, x.2.1 - r * x.1, x.2.2.1 - s * x.1,
    x.2.2.2 - 2 * r * x.2.1 - 2 * s * x.2.2.1 + (r ^ 2 + s ^ 2) * x.1)
  left_inv x := by ext <;> dsimp <;> ring
  right_inv x := by ext <;> dsimp <;> ring
  map_add' x y := by ext <;> dsimp <;> ring

omit [Fact (p % 4 = 3)] in
theorem quad_shear (r s : ZMod p) (x : Vertex p) :
    quad p (shear p r s x) = quad p x := by
  simp only [quad, shear, AddEquiv.coe_mk, Equiv.coe_fn_mk]
  ring

/-- Multiplication of every matrix entry by a nonzero base-field scalar. -/
def scale (r : ZMod p) (hr : r ≠ 0) : Vertex p ≃+ Vertex p where
  toFun x := r • x
  invFun x := r⁻¹ • x
  left_inv x := by simp [smul_smul, hr]
  right_inv x := by simp [smul_smul, hr]
  map_add' x y := smul_add r x y

omit [Fact (p % 4 = 3)] in
theorem quad_scale (r : ZMod p) (hr : r ≠ 0) (x : Vertex p) :
    quad p (scale p r hr x) = r ^ 2 * quad p x := by
  simp only [quad, scale, AddEquiv.coe_mk, Equiv.coe_fn_mk,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

def swapIso : hermitianGraph p ≃g hermitianGraph p :=
  isoOfAddEquiv p (swap p) (fun x => by rw [quad_swap])

def shearIso (r s : ZMod p) : hermitianGraph p ≃g hermitianGraph p :=
  isoOfAddEquiv p (shear p r s) (fun x => by rw [quad_shear])

def scaleIso (r : ZMod p) (hr : r ≠ 0) : hermitianGraph p ≃g hermitianGraph p :=
  isoOfAddEquiv p (scale p r hr) (fun x => by rw [quad_scale]; simp [hr])

@[simp] theorem swapIso_zero : swapIso p 0 = 0 := rfl

@[simp] theorem shearIso_zero (r s : ZMod p) : shearIso p r s 0 = 0 := by
  exact (shear p r s).map_zero

@[simp] theorem scaleIso_zero (r : ZMod p) (hr : r ≠ 0) : scaleIso p r hr 0 = 0 := by
  exact (scale p r hr).map_zero

theorem normalize_of_fst_ne_zero (d : Vertex p) (hd : d.1 ≠ 0) :
    ∃ e : hermitianGraph p ≃g hermitianGraph p,
      e 0 = 0 ∧ ∃ t : ZMod p, e d = (1, 0, 0, t) := by
  let e := (shearIso p (-d.2.1 / d.1) (-d.2.2.1 / d.1)).trans
    (scaleIso p d.1⁻¹ (inv_ne_zero hd))
  refine ⟨e, ?_, (e d).2.2.2, ?_⟩
  · simp [e, RelIso.trans_apply]
  · apply Prod.ext
    · change d.1⁻¹ * d.1 = 1
      exact inv_mul_cancel₀ hd
    · apply Prod.ext
      · change d.1⁻¹ * (d.2.1 + (-d.2.1 / d.1) * d.1) = 0
        rw [div_mul_cancel₀ _ hd, add_neg_cancel, mul_zero]
      · apply Prod.ext
        · change d.1⁻¹ * (d.2.2.1 + (-d.2.2.1 / d.1) * d.1) = 0
          rw [div_mul_cancel₀ _ hd, add_neg_cancel, mul_zero]
        · rfl

theorem normalize (d : Vertex p) (hd : d ≠ 0) :
    ∃ e : hermitianGraph p ≃g hermitianGraph p,
      e 0 = 0 ∧ ∃ t : ZMod p, e d = (1, 0, 0, t) := by
  by_cases ha : d.1 = 0
  · by_cases hc : d.2.2.2 = 0
    · have hb : d.2.1 ≠ 0 ∨ d.2.2.1 ≠ 0 := by
        by_contra h
        push Not at h
        apply hd
        exact Prod.ext ha (Prod.ext h.1 (Prod.ext h.2 hc))
      obtain ⟨r, s, hrs⟩ : ∃ r s : ZMod p, 2 * r * d.2.1 + 2 * s * d.2.2.1 ≠ 0 := by
        rcases hb with hb | hb
        · exact ⟨1, 0, by simpa using mul_ne_zero (Trace.two_ne_zero p) hb⟩
        · exact ⟨0, 1, by simpa using mul_ne_zero (Trace.two_ne_zero p) hb⟩
      let f := (swapIso p).trans ((shearIso p r s).trans (swapIso p))
      have hf : (f d).1 ≠ 0 := by
        change d.1 + 2 * r * d.2.1 + 2 * s * d.2.2.1 +
          (r ^ 2 + s ^ 2) * d.2.2.2 ≠ 0
        simpa only [ha, hc, zero_add, mul_zero, add_zero] using hrs
      obtain ⟨e, he, t, ht⟩ := normalize_of_fst_ne_zero p (f d) hf
      refine ⟨f.trans e, ?_, t, ht⟩
      simpa [f, RelIso.trans_apply] using he
    · obtain ⟨e, he, t, ht⟩ := normalize_of_fst_ne_zero p (swapIso p d) hc
      exact ⟨(swapIso p).trans e, by simpa [RelIso.trans_apply] using he, t, ht⟩
  · exact normalize_of_fst_ne_zero p d ha

/-- Translation is an automorphism because adjacency depends only on differences. -/
def translateIso (a : Vertex p) : hermitianGraph p ≃g hermitianGraph p where
  toEquiv := Equiv.addRight a
  map_rel_iff' := by
    intro x y
    change (hermitianGraph p).Adj (x + a) (y + a) ↔ _
    rw [adj_iff, adj_iff, add_sub_add_right_eq_sub]
    exact and_congr (Equiv.addRight a).injective.ne_iff Iff.rfl

theorem card_commonNeighbors_iso (e : hermitianGraph p ≃g hermitianGraph p) (x y : Vertex p) :
    Nat.card ((hermitianGraph p).commonNeighbors (e x) (e y)) =
      Nat.card ((hermitianGraph p).commonNeighbors x y) := by
  apply Nat.card_congr
  exact (e.toEquiv.subtypeEquiv (fun z => by
    change ((hermitianGraph p).Adj x z ∧ (hermitianGraph p).Adj y z) ↔
      ((hermitianGraph p).Adj (e x) (e z) ∧ (hermitianGraph p).Adj (e y) (e z))
    simp only [e.map_adj_iff])).symm

end ExplicitRIP.Hfsrg
