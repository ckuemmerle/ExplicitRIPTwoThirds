/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Algebra.AvoidanceConic.Plane
public import ExplicitRIP.Algebra.AvoidanceConic.Intersection
public import Mathlib

/-!
# Counting plane loci over finite fields
-/

public section

noncomputable section
namespace ExplicitRIP.Avconic

open MvPolynomial Finset

variable {K V : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V]

open Classical in
/-- The elementary total-degree bound on a finite plane. -/
theorem card_zeros_le_degree_mul_card (g : Bivariate K) (hg : g ≠ 0) :
    (univ.filter (fun q : Fin 2 → K => eval q g = 0)).card ≤
      g.totalDegree * Fintype.card K := by
  classical
  have h := schwartz_zippel_totalDegree hg (univ : Finset K)
  rw [Fintype.piFinset_univ, card_univ] at h
  have hc : (0 : ℚ≥0) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  have hh := (div_le_iff₀ (pow_pos hc 2)).mp h
  have he : (g.totalDegree / (Fintype.card K : ℚ≥0)) * Fintype.card K ^ 2 =
      g.totalDegree * Fintype.card K := by
    field_simp
  rw [he] at hh
  exact_mod_cast hh

open Classical in
/-- Mapping a plane curve into an ambient vector space cannot increase its size. -/
theorem card_plane_locus_le (S : Finset V) (x₀ u w : V) (g : Bivariate K) :
    (S.filter (fun x => ∃ q : Fin 2 → K,
      x = planeMap x₀ u w q ∧ eval q g = 0)).card ≤
      (univ.filter (fun q : Fin 2 → K => eval q g = 0)).card := by
  classical
  apply le_trans (card_le_card (t :=
    (univ.filter (fun q : Fin 2 → K => eval q g = 0)).image (planeMap x₀ u w)) ?_)
    (card_image_le)
  intro x hx
  obtain ⟨q, rfl, hq⟩ := (mem_filter.mp hx).2
  exact mem_image.mpr ⟨q, mem_filter.mpr ⟨mem_univ _, hq⟩, rfl⟩

open Classical in
/-- The finite-set version of the degree-product intersection bound. -/
theorem card_common_zeros_le (G H : Bivariate K) (hG : G ≠ 0) (hH : H ≠ 0)
    (hrel : IsRelPrime G H) :
    (univ.filter (fun q : Fin 2 → K => eval q G = 0 ∧ eval q H = 0)).card ≤
      G.totalDegree * H.totalDegree := by
  classical
  let Z := univ.filter (fun q : Fin 2 → K => eval q G = 0 ∧ eval q H = 0)
  have hd := card_le_degree_product (fun q : Z => q.val) Subtype.val_injective G H hG hH hrel
    (fun q => (mem_filter.mp q.property).2.1) (fun q => (mem_filter.mp q.property).2.2)
  simpa only [Fintype.card_coe] using hd

end ExplicitRIP.Avconic

end
