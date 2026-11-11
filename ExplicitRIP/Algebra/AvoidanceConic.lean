/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Algebra.AvoidanceConic.NormPlane
public import ExplicitRIP.Algebra.AvoidanceConic.GraphIntersections

/-!
# Conic avoidance for the selected norm graphs

The conic bound follows from the line bound by polynomial interpolation and finite-dimensional
quotient spaces. In Hermitian coordinates, each translate has equation `c = N(a, b₁, b₂) + t`.
The selection in [KM, (15)] uses the same norm-graph formula `r = N(x, y, z) + t` directly in
contact coordinates.

Source: [KM, Lemma 7(b) and its proof].
-/

public section

open scoped Matrix

open Classical in
theorem ExplicitRIP.Avoidance.conic_bound (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
    (T : Finset (ZMod p))
    (hline : ∀ x₀ v : ZMod p × ZMod p × ZMod p × ZMod p, v ≠ 0 →
      ((ExplicitRIP.hermitianSelectedVertices p T).filter
        (fun x => ∃ t : ZMod p, x = x₀ + t • v)).card ≤ 3 * T.card)
    (x₀ u w : ZMod p × ZMod p × ZMod p × ZMod p) (huw : LinearIndependent (ZMod p) ![u, w])
    (g : MvPolynomial (Fin 2) (ZMod p)) (hg : g ≠ 0) (hdeg : g.totalDegree ≤ 2) :
    ((ExplicitRIP.hermitianSelectedVertices p T).filter (fun x => ∃ s t : ZMod p,
      x = x₀ + s • u + t • w ∧ MvPolynomial.eval ![s, t] g = 0)).card ≤ 6 * T.card := by
  classical
  let S := ExplicitRIP.hermitianSelectedVertices p T
  have hset : S.filter (fun x => ∃ s t : ZMod p,
      x = x₀ + s • u + t • w ∧ MvPolynomial.eval ![s, t] g = 0) =
      S.filter (fun x => ∃ q : Fin 2 → ZMod p,
        x = ExplicitRIP.Avconic.planeMap x₀ u w q ∧ MvPolynomial.eval q g = 0) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hxS, s, t, hx, hq⟩
      exact ⟨hxS, ![s, t], hx, hq⟩
    · rintro ⟨hxS, q, hx, hq⟩
      refine ⟨hxS, q 0, q 1, hx, ?_⟩
      have he : ![q 0, q 1] = q := by ext i; fin_cases i <;> rfl
      rwa [he]
  change (S.filter _).card ≤ _
  rw [hset]
  by_cases hp : p ≤ 3 * T.card
  · have hc := ExplicitRIP.Avconic.card_plane_locus_le S x₀ u w g
    have hz := ExplicitRIP.Avconic.card_zeros_le_degree_mul_card g hg
    rw [ZMod.card p] at hz
    have hp2 : 2 * p ≤ 6 * T.card := by omega
    refine le_trans ?_ (hc.trans (hz.trans ((Nat.mul_le_mul_right p hdeg).trans hp2)))
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact hx
  · have hsmall : 3 * T.card < Fintype.card (ZMod p) := by rw [ZMod.card p]; omega
    obtain ⟨N, hN, _, hNorm⟩ := (ExplicitRIP.FieldNorm.algebra_spec p).2.2.1
    let F (τ : ZMod p) := ExplicitRIP.Avconic.normPlanePolynomial N x₀ u w τ
    have hFeval (τ : ZMod p) (q : Fin 2 → ZMod p) :
        MvPolynomial.eval q (F τ) =
          ExplicitRIP.fieldNorm p (ExplicitRIP.Avconic.firstThree
            (ExplicitRIP.Avconic.planeMap x₀ u w q)) + τ -
              (ExplicitRIP.Avconic.planeMap x₀ u w q).2.2.2 := by
      dsimp only [F]
      rw [ExplicitRIP.Avconic.eval_normPlanePolynomial]
      rw [show MvPolynomial.eval (ExplicitRIP.Avconic.projection
          (ExplicitRIP.Avconic.planeMap x₀ u w q)) N =
          ExplicitRIP.fieldNorm p (ExplicitRIP.Avconic.firstThree
            (ExplicitRIP.Avconic.planeMap x₀ u w q)) from
        hNorm (ExplicitRIP.Avconic.firstThree (ExplicitRIP.Avconic.planeMap x₀ u w q))]
    let Z (τ : ZMod p) := Finset.univ.filter (fun q : Fin 2 → ZMod p =>
      MvPolynomial.eval q (F τ) = 0 ∧ MvPolynomial.eval q g = 0)
    have hZ (τ : ZMod p) (hτ : τ ∈ T) : (Z τ).card ≤ 6 :=
      ExplicitRIP.Avconic.card_normPlane_common_zeros_le p T hline hsmall
        N hN hNorm x₀ u w huw τ hτ g hg hdeg
    have hsub : S.filter (fun x => ∃ q : Fin 2 → ZMod p,
        x = ExplicitRIP.Avconic.planeMap x₀ u w q ∧ MvPolynomial.eval q g = 0) ⊆
        T.biUnion (fun τ => (Z τ).image (ExplicitRIP.Avconic.planeMap x₀ u w)) := by
      intro x hx
      obtain ⟨hxS, q, rfl, hqg⟩ := Finset.mem_filter.mp hx
      obtain ⟨τ, hτ, hτq⟩ := (ExplicitRIP.LightCone.mem_selectedVertices_iff p T _).mp hxS
      apply Finset.mem_biUnion.mpr
      refine ⟨τ, hτ, Finset.mem_image.mpr ⟨q, ?_, rfl⟩⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, hqg⟩
      rw [hFeval, ExplicitRIP.Avconic.firstThree, hτq, sub_self]
    apply (Finset.card_le_card hsub).trans
    have hc := Finset.card_biUnion_le_card_mul T
      (fun τ => (Z τ).image (ExplicitRIP.Avconic.planeMap x₀ u w)) 6
      (fun τ hτ => (Finset.card_image_le).trans (hZ τ hτ))
    simpa only [Nat.mul_comm] using hc

end
