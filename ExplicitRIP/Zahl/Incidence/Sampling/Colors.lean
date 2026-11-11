/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Incidence.Sampling.Counts

/-! # Nonempty color blocks and their independence -/

public section

namespace ExplicitRIP.Zahl

open scoped BigOperators

namespace Sampling

open Classical in
lemma expect_zero_color {α : Type*} [DecidableEq α] [Fintype α] (k : ℕ) (hk : 0 < k) (i : α) :
    Finset.expect (Finset.univ : Finset (α → Fin k))
      (fun χ => if (χ i).val = 0 then (1 : ℝ) else 0) = 1 / (k : ℝ) := by
  let : NeZero k := ⟨hk.ne'⟩
  rw [expect_eval i (fun c : Fin k => if c.val = 0 then (1 : ℝ) else 0),
    Finset.expect_eq_sum_div_card]
  simp [Fin.val_eq_zero_iff]

open Classical in
lemma expect_two_zero_colors {α : Type*} [DecidableEq α] [Fintype α] (k : ℕ) (hk : 0 < k)
    (i j : α) (hij : i ≠ j) :
    Finset.expect (Finset.univ : Finset (α → Fin k))
      (fun χ => if (χ i).val = 0 ∧ (χ j).val = 0 then (1 : ℝ) else 0) =
        1 / (k : ℝ) ^ 2 := by
  let : NeZero k := ⟨hk.ne'⟩
  have heq (χ : α → Fin k) :
      (if (χ i).val = 0 ∧ (χ j).val = 0 then (1 : ℝ) else 0) =
        (if (χ i).val = 0 then 1 else 0) * (if (χ j).val = 0 then 1 else 0) := by
    split_ifs <;> simp_all
  simp_rw [heq]
  rw [expect_pair i j hij (fun c : Fin k => if c.val = 0 then (1 : ℝ) else 0)
    (fun c : Fin k => if c.val = 0 then (1 : ℝ) else 0)]
  have hz : Finset.expect Finset.univ (fun c : Fin k => if c.val = 0 then (1 : ℝ) else 0) =
      1 / (k : ℝ) := by
    rw [Finset.expect_eq_sum_div_card]
    simp [Fin.val_eq_zero_iff]
  rw [hz]
  ring

open Classical in
lemma colorSample_inter_congr {α : Type*} (L W : Finset α) {k : ℕ}
    (χ ψ : ↥L → Fin k) (h : ∀ a : ↥L, a.val ∈ W → χ a = ψ a) :
    colorSample L χ ∩ W = colorSample L ψ ∩ W := by
  ext a
  simp only [Finset.mem_inter, mem_colorSample_iff]
  constructor
  · rintro ⟨⟨ha, hh⟩, hw⟩
    exact ⟨⟨ha, by rw [← h ⟨a, ha⟩ hw]; exact hh⟩, hw⟩
  · rintro ⟨⟨ha, hh⟩, hw⟩
    exact ⟨⟨ha, by rw [h ⟨a, ha⟩ hw]; exact hh⟩, hw⟩

end Sampling

open Classical in
theorem mean_nonempty_color_block_lower {α : Type*}
    (L W : Finset α) (hWL : W ⊆ L) (k : ℕ) (hk : 0 < k) :
    (W.card : ℝ) / (k : ℝ) -
        (W.card : ℝ) * ((W.card : ℝ) - 1) / (2 * (k : ℝ) ^ 2) ≤
      finiteMean (Finset.univ : Finset (↥L → Fin k))
        (fun χ => if (colorSample L χ ∩ W).Nonempty then 1 else 0) := by
  classical
  let p (χ : ↥L → Fin k) (a : ↥W) := (χ ⟨a.val, hWL a.property⟩).val = 0
  have h₁ (a : ↥W) (_ha : a ∈ W.attach) :
      Finset.expect Finset.univ (fun χ => if p χ a then (1 : ℝ) else 0) =
        1 / (k : ℝ) := Sampling.expect_zero_color (α := ↥L) k hk ⟨a.val, hWL a.property⟩
  have h₂ (a : ↥W) (_ha : a ∈ W.attach) (b : ↥W) (_hb : b ∈ W.attach) (hab : a ≠ b) :
      Finset.expect Finset.univ (fun χ => if p χ a ∧ p χ b then (1 : ℝ) else 0) =
        1 / (k : ℝ) ^ 2 := by
    apply Sampling.expect_two_zero_colors (α := ↥L) k hk
      ⟨a.val, hWL a.property⟩ ⟨b.val, hWL b.property⟩
    intro h
    exact hab (Subtype.ext (congrArg (fun x : ↥L => x.val) h))
  have h := Sampling.expect_nonempty_lower W.attach Finset.univ p
    (1 / (k : ℝ)) (1 / (k : ℝ) ^ 2) h₁ h₂
  simp only [Finset.card_attach] at h
  have heq (χ : ↥L → Fin k) :
      (colorSample L χ ∩ W).Nonempty ↔ (W.attach.filter (p χ)).Nonempty := by
    rw [Sampling.colorSample_inter_eq L W hWL χ, Finset.image_nonempty]
  simpa only [finiteMean, heq, div_eq_mul_inv, mul_inv, one_div, mul_one,
    mul_assoc, mul_left_comm, mul_comm] using h

open Classical in
theorem mean_disjoint_color_blocks {α : Type*}
    (L : Finset α) (blocks : Fin 3 → Finset α)
    (hblocks : ∀ i, blocks i ⊆ L)
    (hdisjoint : Pairwise (fun i j => Disjoint (blocks i) (blocks j)))
    (k : ℕ) (hk : 0 < k) :
    finiteMean (Finset.univ : Finset (↥L → Fin k))
      (fun χ => ∏ i : Fin 3,
        if (colorSample L χ ∩ blocks i).Nonempty then (1 : ℝ) else 0) =
      ∏ i : Fin 3, finiteMean (Finset.univ : Finset (↥L → Fin k))
        (fun χ => if (colorSample L χ ∩ blocks i).Nonempty then (1 : ℝ) else 0) := by
  classical
  let : NeZero k := ⟨hk.ne'⟩
  let D (i : Fin 3) : Finset ↥L := L.attach.filter (fun a => a.val ∈ blocks i)
  let f (i : Fin 3) (χ : ↥L → Fin k) : ℝ :=
    if (colorSample L χ ∩ blocks i).Nonempty then 1 else 0
  have hD (i j : Fin 3) (hij : i ≠ j) : Disjoint (D i) (D j) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact Finset.disjoint_left.mp (hdisjoint hij)
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  have hf (i : Fin 3) (χ ψ : ↥L → Fin k)
      (h : ∀ a ∈ D i, χ a = ψ a) : f i χ = f i ψ := by
    dsimp [f]
    rw [Sampling.colorSample_inter_congr L (blocks i) χ ψ (fun a ha =>
      h ⟨a.val, hblocks i ha⟩ (Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, ha⟩))]
  have h12 := Sampling.expect_mul_of_disjoint (D 1) (D 2) (hD 1 2 (by decide))
    (f 1) (f 2) (hf 1) (hf 2)
  have h0 := Sampling.expect_mul_of_disjoint (D 0) (D 1 ∪ D 2)
    (Finset.disjoint_union_right.mpr ⟨hD 0 1 (by decide), hD 0 2 (by decide)⟩)
    (f 0) (fun χ => f 1 χ * f 2 χ) (hf 0) (by
      intro χ ψ h
      rw [hf 1 χ ψ (fun a ha => h a (Finset.mem_union_left _ ha)),
        hf 2 χ ψ (fun a ha => h a (Finset.mem_union_right _ ha))])
  simpa only [finiteMean, Fin.prod_univ_three, mul_assoc, f] using
    h0.trans (congrArg (Finset.expect Finset.univ (f 0) * ·) h12)

end ExplicitRIP.Zahl
