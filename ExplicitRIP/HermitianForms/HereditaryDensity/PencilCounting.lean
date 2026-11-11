/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.HermitianForms.HereditaryDensity.Pencils
public import ExplicitRIP.HermitianForms.HereditaryDensity.EdgeCounting
public import ExplicitRIP.HermitianForms.HereditaryDensity.Sums
public import ExplicitRIP.Frozen.Defs.RichPencilCount

/-!
# Counting edges by their contact pencils

A finite cover by pencils and a layer sum bound the rich-pencil contribution to the edge count
of a Hermitian norm-graph selection, using the rich-pencil estimate of [Z, Theorem 1.8].
-/

@[expose] public section
namespace ExplicitRIP.Edges
open Finset

section Field
variable {F : Type*} [Field F] [Fintype F]

/-- The finite family of pencils containing at least two points of a finite set. -/
noncomputable def pencilFamily (S : Finset (V4 F)) : Finset (Set (V4 F)) :=
  open Classical in
  (Set.toFinite {P : Set (V4 F) | IsContactPencil P ∧ 2 ≤ (S.filter (· ∈ P)).card}).toFinset

open Classical in
theorem mem_pencilFamily (S : Finset (V4 F)) (P : Set (V4 F)) :
    P ∈ pencilFamily S ↔ IsContactPencil P ∧ 2 ≤ (S.filter (· ∈ P)).card := by
  classical
  exact Set.Finite.mem_toFinset _

theorem pencilFamily_card (S : Finset (V4 F)) : (pencilFamily S).card = richPencilCount S 2 := by
  classical
  exact (Set.ncard_eq_toFinset_card _ _).symm

open Classical in
theorem pencilFamily_filter_card (S : Finset (V4 F)) (h : ℕ) (hh : 2 ≤ h) :
    ((pencilFamily S).filter (fun P => h ≤ (S.filter (· ∈ P)).card)).card =
      richPencilCount S h := by
  classical
  rw [richPencilCount, Set.ncard_eq_toFinset_card]
  congr 1
  ext P
  simp only [mem_filter, mem_pencilFamily, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hP, _⟩, hr⟩
    exact ⟨hP, hr⟩
  · rintro ⟨hP, hr⟩
    exact ⟨⟨hP, hh.trans hr⟩, hr⟩

end Field

variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

theorem card_sphere_image (V : Finset (V4 (ZMod p))) : (V.image (sphereCoords p)).card = V.card :=
  Finset.card_image_of_injective _ (LightCone.sphereEquiv p).injective

open Classical in
theorem card_sphere_image_filter (V : Finset (V4 (ZMod p))) (P : Set (V4 (ZMod p))) :
    ((V.image (sphereCoords p)).filter (· ∈ P)).card =
      (V.filter (fun x => sphereCoords p x ∈ P)).card := by
  classical
  rw [filter_image, card_sphere_image]

open Classical in
theorem pencil_richness_cap (T : Finset (ZMod p)) (V : Finset (V4 (ZMod p)))
    (hV : V ⊆ hermitianSelectedVertices p T) {P : Set (V4 (ZMod p))}
    (hP : P ∈ pencilFamily (V.image (sphereCoords p))) :
    ((V.image (sphereCoords p)).filter (· ∈ P)).card ≤ 3 * T.card := by
  classical
  obtain ⟨hPc, hcard⟩ := (mem_pencilFamily _ _).mp hP
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega :
    1 < ((V.image (sphereCoords p)).filter (· ∈ P)).card)
  have hsub := pencil_subset_lineSet p hPc (mem_filter.mp hx).2 (mem_filter.mp hy).2 hxy
  rw [card_sphere_image_filter]
  apply (card_le_card ?_).trans (line_cap p T hxy)
  intro v hv
  exact mem_filter.mpr ⟨hV (mem_filter.mp hv).1, hsub (mem_filter.mp hv).2⟩

open Classical in
/-- Every edge is covered by a pencil containing its two endpoints. -/
theorem edge_count_le_sum_pencil_sq (V : Finset (V4 (ZMod p))) :
    inducedEdgeCount (hermitianGraph p) V ≤
      ∑ P ∈ pencilFamily (V.image (sphereCoords p)),
        (((V.image (sphereCoords p)).filter (· ∈ P)).card) ^ 2 := by
  classical
  let Ps := pencilFamily (V.image (sphereCoords p))
  let pieces (P : Set (V4 (ZMod p))) := (V.filter (fun v => sphereCoords p v ∈ P)).sym2
  have hcover : V.sym2.filter (fun e => e ∈ (hermitianGraph p).edgeSet) ⊆ Ps.biUnion pieces := by
    intro e he
    obtain ⟨x, y⟩ := e
    obtain ⟨hmem, hadj⟩ := mem_filter.mp he
    obtain ⟨hx, hy⟩ := mk_mem_sym2_iff.mp hmem
    have ha := (adj_iff_sphereContact p x y).mp hadj
    let P := lineSet (sphereCoords p x) (sphereCoords p y)
    have hP : P ∈ Ps := by
      apply (mem_pencilFamily _ _).mpr
      refine ⟨isContactPencil_lineSet p ((LightCone.sphereEquiv p).injective.ne ha.1) ha.2, ?_⟩
      apply Nat.succ_le_of_lt
      apply one_lt_card.mpr
      exact ⟨sphereCoords p x, mem_filter.mpr ⟨mem_image_of_mem _ hx, left_mem_lineSet _ _⟩,
        sphereCoords p y, mem_filter.mpr ⟨mem_image_of_mem _ hy, right_mem_lineSet _ _⟩,
        (LightCone.sphereEquiv p).injective.ne ha.1⟩
    apply mem_biUnion.mpr
    exact ⟨P, hP, mk_mem_sym2_iff.mpr ⟨mem_filter.mpr ⟨hx, left_mem_lineSet _ _⟩,
      mem_filter.mpr ⟨hy, right_mem_lineSet _ _⟩⟩⟩
  apply (card_le_card hcover).trans
  apply card_biUnion_le.trans
  apply sum_le_sum
  intro P _
  rw [card_sphere_image_filter]
  dsimp only [pieces]
  rw [sym2_eq_image]
  exact card_image_le.trans (by rw [card_product, pow_two])

end ExplicitRIP.Edges

namespace ExplicitRIP.Edges
open Finset
variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

open Classical in
/-- The rich-pencil contribution with an explicit absolute coefficient. -/
theorem edge_count_le_rich_two_add (T : Finset (ZMod p)) (V : Finset (V4 (ZMod p)))
    (hV : V ⊆ hermitianSelectedVertices p T) (hL : 1 ≤ T.card) (C : ℝ) (hC : 0 ≤ C)
    (hRich : ∀ h : ℕ, 3 ≤ h →
      (richPencilCount (V.image (sphereCoords p)) h : ℝ) ≤
        C * (V.card : ℝ) ^ (3 / 2 : ℝ) * (h : ℝ) ^ (-(3 / 2 : ℝ))) :
    (inducedEdgeCount (hermitianGraph p) V : ℝ) ≤
      6 * (richPencilCount (V.image (sphereCoords p)) 2 : ℝ) +
        12 * C * Real.sqrt T.card * (V.card : ℝ) ^ (3 / 2 : ℝ) := by
  let S := V.image (sphereCoords p)
  let Ps := pencilFamily S
  let k (P : Set (V4 (ZMod p))) := (S.filter (· ∈ P)).card
  let R := C * (V.card : ℝ) ^ (3 / 2 : ℝ)
  let f (i : ℕ) : ℝ := 2 * (i + 1) * ((Ps.filter (fun P => i + 1 ≤ k P)).card : ℝ)
  have hR : 0 ≤ R := mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hk : ∀ P ∈ Ps, k P ≤ 3 * T.card + 2 := by
    intro P hP
    exact (pencil_richness_cap p T V hV hP).trans (by omega)
  have hnat := (edge_count_le_sum_pencil_sq p V).trans (sum_sq_le_layers Ps k (3 * T.card + 2) hk)
  have hlay : (inducedEdgeCount (hermitianGraph p) V : ℝ) ≤ ∑ i ∈ range (3 * T.card + 2), f i := by
    dsimp only [f]
    exact_mod_cast hnat
  have hsmall (i : ℕ) (hi : i < 2) :
      f i = 2 * (i + 1) * (richPencilCount S 2 : ℝ) := by
    dsimp [f]
    congr 2
    rw [filter_eq_self.mpr, pencilFamily_card]
    intro P hP
    have h := ((mem_pencilFamily S P).mp hP).2
    dsimp [k]
    omega
  have hstart : ∑ i ∈ range 2, f i = 6 * (richPencilCount S 2 : ℝ) := by
    rw [sum_range_succ, sum_range_succ, sum_range_zero, hsmall 0 (by decide), hsmall 1 (by decide)]
    norm_num
    ring
  have htail (i : ℕ) : f (i + 2) ≤ (2 * R) * (1 / Real.sqrt (i + 3)) := by
    have hi : (0 : ℝ) < i + 3 := by positivity
    have h := hRich (i + 3) (by omega)
    dsimp [f]
    rw [show i + 2 + 1 = i + 3 by omega, pencilFamily_filter_card S (i + 3) (by omega)]
    push_cast at h ⊢
    rw [show (i : ℝ) + 2 + 1 = i + 3 by ring]
    calc
      _ ≤ 2 * (i + 3) * (R * (i + 3) ^ (-(3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
      _ = (2 * R) * (1 / Real.sqrt (i + 3)) := by
        rw [show 2 * (i + 3) * (R * (i + 3) ^ (-(3 / 2 : ℝ))) =
          (2 * R) * ((i + 3) * (i + 3) ^ (-(3 / 2 : ℝ))) by ring,
          mul_rpow_neg_three_halves _ hi]
  have hsum : (∑ i ∈ range (3 * T.card), (1 : ℝ) / Real.sqrt (i + 3)) ≤
      2 * Real.sqrt (3 * T.card + 2) := by
    have h := sum_one_div_sqrt_le (3 * T.card + 2)
    rw [show 3 * T.card + 2 = 2 + 3 * T.card by omega, sum_range_add] at h
    have hnon : 0 ≤ ∑ i ∈ range 2, (1 : ℝ) / Real.sqrt (i + 1) :=
      sum_nonneg (fun _ _ => by positivity)
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h
    have he : (∑ i ∈ range (3 * T.card), (1 : ℝ) / Real.sqrt (2 + (i : ℝ) + 1)) =
        ∑ i ∈ range (3 * T.card), (1 : ℝ) / Real.sqrt (i + 3) := by
      apply sum_congr rfl
      intro i _
      congr 2
      ring
    rw [he, show (2 : ℝ) + 3 * T.card = 3 * T.card + 2 by ring] at h
    linarith
  have hsqrt : Real.sqrt (3 * (T.card : ℝ) + 2) ≤ 3 * Real.sqrt T.card := by
    have hLr : (1 : ℝ) ≤ T.card := by exact_mod_cast hL
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt (Nat.cast_nonneg T.card)]
  rw [show 3 * T.card + 2 = 2 + 3 * T.card by omega, sum_range_add, hstart] at hlay
  have htailSum : ∑ i ∈ range (3 * T.card), f (2 + i) ≤
      (2 * R) * (2 * Real.sqrt (3 * (T.card : ℝ) + 2)) := by
    calc
      _ ≤ ∑ i ∈ range (3 * T.card), (2 * R) * (1 / Real.sqrt (i + 3)) := by
        apply sum_le_sum
        intro i _
        simpa only [Nat.add_comm 2 i] using htail i
      _ = (2 * R) * ∑ i ∈ range (3 * T.card), 1 / Real.sqrt (i + 3) := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  have hlast := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ 4 * R by positivity)
  dsimp [R, S] at *
  nlinarith only [hlay, htailSum, hlast]

end ExplicitRIP.Edges
