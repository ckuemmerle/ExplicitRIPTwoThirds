/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.HermitianForms.HereditaryDensity.Conics

/-!
# Plane equations and caps for complementary conics

The algebraic parametrization gives plane-conic bounds for the sphere-map image of the
Hermitian norm-graph selection, using line and conic avoidance. It implements the plane-conic
description of complementary conics in [KM, Section 4.1].
-/

@[expose] public section
namespace ExplicitRIP.Edges

section Field
variable {F : Type*} [Field F]
open MvPolynomial

/-- The contact quadratic restricted to an affine plane, with its constant term removed. -/
noncomputable def conicPolynomial (a u w : V4 F) : MvPolynomial (Fin 2) F :=
  C (2 * mb a u) * X 0 + C (2 * mb a w) * X 1 +
    C (mq u) * X 0 ^ 2 + C (2 * mb u w) * X 0 * X 1 + C (mq w) * X 1 ^ 2

theorem conicPolynomial_eval (a u w : V4 F) (s t : F) :
    eval ![s, t] (conicPolynomial a u w) = mq (a + s • u + t • w) - mq a := by
  simp only [conicPolynomial, map_add, map_mul, map_pow, eval_C, eval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  dsimp [mq, mb]
  ring

theorem conicPolynomial_degree (a u w : V4 F) : (conicPolynomial a u w).totalDegree ≤ 2 := by
  have hlin (c : F) (i : Fin 2) : (C c * X i : MvPolynomial (Fin 2) F).totalDegree ≤ 2 :=
    (totalDegree_mul _ _).trans (by simp)
  have hsq (c : F) (i : Fin 2) : (C c * X i ^ 2 : MvPolynomial (Fin 2) F).totalDegree ≤ 2 :=
    (totalDegree_mul _ _).trans (by simp [totalDegree_X_pow])
  have hcross (c : F) : (C c * X 0 * X 1 : MvPolynomial (Fin 2) F).totalDegree ≤ 2 := by
    apply (totalDegree_mul _ _).trans
    have h := totalDegree_mul (C c : MvPolynomial (Fin 2) F) (X 0)
    simp only [totalDegree_C, totalDegree_X, zero_add] at h ⊢
    omega
  unfold conicPolynomial
  apply (totalDegree_add _ _).trans
  apply max_le _ (hsq _ _)
  apply (totalDegree_add _ _).trans
  apply max_le _ (hcross _)
  apply (totalDegree_add _ _).trans
  apply max_le _ (hsq _ _)
  exact (totalDegree_add _ _).trans (max_le (hlin _ _) (hlin _ _))

end Field

variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
variable {A B : Set (V4 (ZMod p))}

/-- Every member of a complementary pair is contained in a nonzero quadratic plane curve. -/
theorem conic_param (h : IsComplementaryConicPair A B) :
    ∃ x₀ u w : V4 (ZMod p), LinearIndependent (ZMod p) ![u, w] ∧
      ∃ g : MvPolynomial (Fin 2) (ZMod p), g ≠ 0 ∧ g.totalDegree ≤ 2 ∧
        ∀ x ∈ A, ∃ s t : ZMod p, x = x₀ + s • u + t • w ∧ MvPolynomial.eval ![s, t] g = 0 := by
  obtain ⟨x₁, hx₁, x₂, hx₂, x₃, hx₃, hx12, hx13, hx23⟩ := exists_three_of_encard h.1.1
  obtain ⟨y₁, hy₁, y₂, hy₂, y₃, hy₃, hy12, hy13, hy23⟩ := exists_three_of_encard h.1.2.1
  have hc := h.1.2.2.1
  have h2 := Trace.two_ne_zero p
  have hlinX := complementary_independent p h hx₁ hx₂ hx₃ hx12 hx13 hx23
  have hlinY := complementary_independent p (complementary_symm h) hy₁ hy₂ hy₃ hy12 hy13 hy23
  have ho (x : V4 (ZMod p)) (hx : x ∈ A) (y : V4 (ZMod p)) (hy : y ∈ B) :
      mb (y - y₁) (x - x₁) = 0 := by
    rw [mb_comm]
    exact mb_sub_eq_zero_of_contacts h2 (hc x₁ hx₁ y₁ hy₁) (hc x hx y₁ hy₁)
      (hc x₁ hx₁ y hy) (hc x hx y hy)
  have hplane (x : V4 (ZMod p)) (hx : x ∈ A) :
      ∃ s t : ZMod p, x = x₁ + s • (x₂ - x₁) + t • (x₃ - x₁) := by
    obtain ⟨s, t, he⟩ := orth_pair_span hlinY hlinX
      (ho x₂ hx₂ y₂ hy₂) (ho x₃ hx₃ y₃ hy₃) (ho x₃ hx₃ y₂ hy₂) (ho x₂ hx₂ y₃ hy₃)
      (ho x hx y₂ hy₂) (ho x hx y₃ hy₃)
    exact ⟨s, t, by rw [add_assoc, ← he]; abel⟩
  let a := x₁ - y₁
  let u := x₂ - x₁
  let w := x₃ - x₁
  have ha : mq a = 0 := (contact_iff _ _).mp (hc x₁ hx₁ y₁ hy₁)
  have hau : mq (a + u) = 0 := by
    have he : a + u = x₂ - y₁ := by dsimp [a, u]; abel
    rw [he]
    exact (contact_iff _ _).mp (hc x₂ hx₂ y₁ hy₁)
  have hu : mq u ≠ 0 := by
    intro hz
    apply h.1.2.2.2.1 x₁ hx₁ x₂ hx₂ hx12
    rw [contact_iff, mq_sub_comm]
    exact hz
  have hgne : conicPolynomial a u w ≠ 0 := by
    intro hg
    have he : MvPolynomial.eval ![2, 0] (conicPolynomial a u w) = 2 * mq u := by
      rw [conicPolynomial_eval, zero_smul, add_zero, ha, sub_zero]
      dsimp [mq] at ha hau ⊢
      linear_combination 2 * hau - ha
    rw [hg, map_zero] at he
    exact (mul_ne_zero h2 hu) he.symm
  refine ⟨x₁, u, w, hlinX, conicPolynomial a u w, hgne, conicPolynomial_degree _ _ _, ?_⟩
  intro x hx
  obtain ⟨s, t, ht⟩ := hplane x hx
  refine ⟨s, t, ht, ?_⟩
  rw [conicPolynomial_eval, ha, sub_zero]
  have he : a + s • u + t • w = x - y₁ := by rw [ht]; dsimp [a, u, w]; abel
  rw [he]
  exact (contact_iff _ _).mp (hc x hx y₁ hy₁)

open Classical in
/-- The line and conic avoidance theorem applies to complementary conics in sphere coordinates. -/
theorem conic_cap (T : Finset (ZMod p)) (h : IsComplementaryConicPair A B) :
    ((hermitianSelectedVertices p T).filter (fun v => sphereCoords p v ∈ A)).card ≤ 6 * T.card := by
  classical
  obtain ⟨x₀, u, w, hlin, g, hg, hdeg, hparam⟩ := conic_param p h
  let e := LightCone.sphereEquiv p
  have hlin' : LinearIndependent (ZMod p) ![e.symm u, e.symm w] := by
    rw [LinearIndependent.pair_iff] at hlin ⊢
    intro s t hst
    apply hlin s t
    have he := congrArg e hst
    simpa only [map_add, map_smul, map_zero, LinearEquiv.apply_symm_apply] using he
  apply (Finset.card_le_card ?_).trans ((ExplicitRIP.Hermitian.line_conic_avoidance p T).2
    (e.symm x₀) (e.symm u) (e.symm w) hlin' g hg hdeg)
  intro v hv
  obtain ⟨hv, hvA⟩ := Finset.mem_filter.mp hv
  obtain ⟨s, t, ht, heval⟩ := hparam _ hvA
  refine Finset.mem_filter.mpr ⟨hv, s, t, ?_, heval⟩
  have he := congrArg e.symm ht
  simpa only [← LightCone.sphereEquiv_apply, e, LinearEquiv.symm_apply_apply,
    map_add, map_smul] using he

end ExplicitRIP.Edges
