/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.HermitianForms.Defs.SelectedVertices
import ExplicitRIP.Algebra.AvoidanceLine.NormRoots

/-!
# Line avoidance for the selected vertices

Each translated norm graph contributes at most three points to a nonconstant line. The
Hermitian-coordinate equation `c = N(a, b₁, b₂) + t` has the same norm-graph form as the selection
in [KM, (15)].

Source: [KM, Lemma 7(a) and its proof].
-/

public section

open scoped BigOperators

open Classical in
theorem ExplicitRIP.Avoidance.line_bound (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
    (T : Finset (ZMod p)) (x₀ v : ZMod p × ZMod p × ZMod p × ZMod p) (hv : v ≠ 0) :
    ((ExplicitRIP.hermitianSelectedVertices p T).filter
      (fun x => ∃ t : ZMod p, x = x₀ + t • v)).card ≤ 3 * T.card := by
  classical
  rcases x₀ with ⟨a₀, a₁, a₂, c⟩
  rcases v with ⟨b₀, b₁, b₂, d⟩
  have hbd : (b₀, b₁, b₂) ≠ (0 : ZMod p × ZMod p × ZMod p) ∨ d ≠ 0 := by
    by_cases hb : (b₀, b₁, b₂) = (0 : ZMod p × ZMod p × ZMod p)
    · right
      intro hd
      apply hv
      exact Prod.ext (congrArg (fun w : ZMod p × ZMod p × ZMod p => w.1) hb)
        (Prod.ext (congrArg (fun w : ZMod p × ZMod p × ZMod p => w.2.1) hb)
          (Prod.ext (congrArg (fun w : ZMod p × ZMod p × ZMod p => w.2.2) hb) hd))
    · exact Or.inl hb
  let parameters (τ : ZMod p) : Finset (ZMod p) := Finset.univ.filter (fun t =>
    ExplicitRIP.fieldNorm p ((a₀, a₁, a₂) + t • (b₀, b₁, b₂)) + τ = c + t * d)
  let point (t : ZMod p) : ZMod p × ZMod p × ZMod p × ZMod p :=
    (a₀, a₁, a₂, c) + t • (b₀, b₁, b₂, d)
  have hcard (τ : ZMod p) : (parameters τ).card ≤ 3 :=
    ExplicitRIP.Avline.norm_line_card_le p (a₀, a₁, a₂) (b₀, b₁, b₂) c d τ hbd
  have hcover :
      ((ExplicitRIP.hermitianSelectedVertices p T).filter
        (fun x => ∃ t : ZMod p, x = (a₀, a₁, a₂, c) + t • (b₀, b₁, b₂, d))) ⊆
      T.biUnion (fun τ => (parameters τ).image point) := by
    intro x hx
    obtain ⟨hselected, t, hxt⟩ := Finset.mem_filter.mp hx
    obtain ⟨⟨w, τ⟩, hwτ, hgraph⟩ := Finset.mem_image.mp hselected
    have hτ : τ ∈ T := (Finset.mem_product.mp hwτ).2
    apply Finset.mem_biUnion.mpr
    refine ⟨τ, hτ, Finset.mem_image.mpr ⟨t, ?_, hxt.symm⟩⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hpoint := hgraph.trans hxt
    have hw : w = (a₀, a₁, a₂) + t • (b₀, b₁, b₂) := by
      exact Prod.ext (congrArg (fun z : ZMod p × ZMod p × ZMod p × ZMod p => z.1)
        hpoint) (Prod.ext
          (congrArg (fun z : ZMod p × ZMod p × ZMod p × ZMod p => z.2.1) hpoint)
          (congrArg (fun z : ZMod p × ZMod p × ZMod p × ZMod p => z.2.2.1) hpoint))
    have hc := congrArg (fun z => z.2.2.2) hpoint
    change ExplicitRIP.fieldNorm p w + τ = c + t * d at hc
    rw [← hw]
    exact hc
  calc
    _ ≤ (T.biUnion (fun τ => (parameters τ).image point)).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ τ ∈ T, ((parameters τ).image point).card := Finset.card_biUnion_le
    _ ≤ ∑ τ ∈ T, 3 := Finset.sum_le_sum fun τ _ =>
      Finset.card_image_le.trans (hcard τ)
    _ = 3 * T.card := by simp only [Finset.sum_const, smul_eq_mul, mul_comm]

end
