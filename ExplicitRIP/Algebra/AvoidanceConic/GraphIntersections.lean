/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Algebra.AvoidanceConic.NormPlane
public import ExplicitRIP.Algebra.AvoidanceConic.Counting

/-!
# Intersecting one norm graph with a conic

When the field is larger than the given line bound, a restricted norm cubic has
no linear divisor. The degree-product bound then gives at most six intersections.
-/

public section

noncomputable section
namespace ExplicitRIP.Avconic

open MvPolynomial
open scoped Matrix

open Classical in
theorem card_normPlane_common_zeros_le (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
    (T : Finset (ZMod p))
    (hline : ∀ a v : FourSpace (ZMod p), v ≠ 0 →
      ((ExplicitRIP.hermitianSelectedVertices p T).filter
        (fun x => ∃ t : ZMod p, x = a + t • v)).card ≤
        3 * T.card)
    (hsmall : 3 * T.card < Fintype.card (ZMod p))
    (N : MvPolynomial (Fin 3) (ZMod p)) (hN : N.IsHomogeneous 3)
    (hNorm : ∀ z : ZMod p × ZMod p × ZMod p,
      eval ![z.1, z.2.1, z.2.2] N = ExplicitRIP.fieldNorm p z)
    (x₀ u w : FourSpace (ZMod p)) (huw : LinearIndependent (ZMod p) ![u, w])
    (τ : ZMod p) (hτ : τ ∈ T) (g : Bivariate (ZMod p)) (hg : g ≠ 0)
    (hdeg : g.totalDegree ≤ 2) :
    (Finset.univ.filter (fun q : Fin 2 → ZMod p =>
      eval q (normPlanePolynomial N x₀ u w τ) = 0 ∧ eval q g = 0)).card ≤ 6 := by
  classical
  let F := normPlanePolynomial N x₀ u w τ
  have hNzero (z : ZMod p × ZMod p × ZMod p) (hz : z ≠ 0) :
      eval ![z.1, z.2.1, z.2.2] N ≠ 0 := by
    rw [hNorm]
    exact (ExplicitRIP.FieldNorm.algebra_spec p).2.2.2.2 z hz
  have hFdeg : F.totalDegree = 3 :=
    totalDegree_normPlanePolynomial N hN hNzero x₀ u w huw τ
  have hFmem (q : Fin 2 → ZMod p) (hq : eval q F = 0) :
      planeMap x₀ u w q ∈ ExplicitRIP.hermitianSelectedVertices p T := by
    apply (LightCone.mem_selectedVertices_iff p T _).mpr
    refine ⟨τ, hτ, ?_⟩
    have he := eval_normPlanePolynomial N x₀ u w τ q
    rw [show eval (projection (planeMap x₀ u w q)) N =
      ExplicitRIP.fieldNorm p (firstThree (planeMap x₀ u w q)) from
        hNorm (firstThree (planeMap x₀ u w q))] at he
    exact (sub_eq_zero.mp (he.symm.trans hq)).symm
  have hl : ∀ L : Bivariate (ZMod p), L.totalDegree = 1 → ¬L ∣ F :=
    no_linear_dvd_of_line_bound (K := ZMod p)
      (ExplicitRIP.hermitianSelectedVertices p T) (3 * T.card)
      (fun a v hv => by
        refine le_trans ?_ (hline a v hv)
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter] at hx ⊢
        exact hx)
      hsmall x₀ u w huw F hFmem
  have hi : Irreducible F := irreducible_of_degree_three_of_no_linear_dvd F hFdeg hl
  have hr : IsRelPrime F g := hi.isRelPrime_iff_not_dvd.mpr (by
    intro hd
    have hh := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hd hg
    rw [hFdeg] at hh
    omega)
  have hc := card_common_zeros_le F g hi.ne_zero hg hr
  rw [hFdeg] at hc
  have hbound : 3 * g.totalDegree ≤ 6 := by omega
  simpa only [F, Finset.filter_congr_decidable] using hc.trans hbound

end ExplicitRIP.Avconic

end
