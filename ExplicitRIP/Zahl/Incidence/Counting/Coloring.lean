/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Defs

/-!
# Uniform colorings and coordinate averages

Splitting the function space at a coordinate makes its uniform distribution
explicit. Summing the zero-color indicators gives the expected sample size.
-/

public section

namespace ExplicitRIP.Zahl

open scoped BigOperators

open Classical in
/-- Averaging a function of one coordinate of a uniform function. -/
theorem finiteMean_fun_apply {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [Nonempty β]
    (a : α) (f : β → ℝ) :
    finiteMean Finset.univ (fun χ : α → β => f (χ a)) = finiteMean Finset.univ f := by
  classical
  unfold finiteMean
  rw [Fintype.expect_equiv (Equiv.funSplitAt a β)
    (fun χ : α → β => f (χ a)) (fun p => f p.1) (fun _ => rfl)]
  rw [← Finset.univ_product_univ, Finset.expect_product]
  simp only [Fintype.expect_const]

open Classical in
/-- Averaging a function of two distinct coordinates of a uniform function. -/
theorem finiteMean_fun_apply_two {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [Nonempty β]
    (a b : α) (hab : a ≠ b) (f : β → β → ℝ) :
    finiteMean Finset.univ (fun χ : α → β => f (χ a) (χ b)) =
      finiteMean Finset.univ (fun x => finiteMean Finset.univ (f x)) := by
  classical
  calc
    _ = finiteMean Finset.univ
        (fun p : β × ({j : α // j ≠ a} → β) => f p.1 (p.2 ⟨b, hab.symm⟩)) :=
      Fintype.expect_equiv (Equiv.funSplitAt a β)
        (fun χ : α → β => f (χ a) (χ b)) _ (fun _ => rfl)
    _ = finiteMean Finset.univ (fun x : β => finiteMean Finset.univ
        (fun ψ : {j : α // j ≠ a} → β => f x (ψ ⟨b, hab.symm⟩))) := by
      unfold finiteMean
      rw [← Finset.univ_product_univ, Finset.expect_product]
    _ = _ := by
      apply Finset.expect_congr rfl
      intro x _
      exact finiteMean_fun_apply (⟨b, hab.symm⟩ : {j : α // j ≠ a}) (f x)

open Classical in
/-- Membership in the sampled zero color class. -/
theorem mem_colorSample_iff {α : Type*} (L : Finset α) {k : ℕ}
    (χ : ↥L → Fin k) (a : α) :
    a ∈ colorSample L χ ↔ ∃ h : a ∈ L, (χ ⟨a, h⟩).val = 0 := by
  classical
  simp only [colorSample, Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b.property, hb⟩
  · rintro ⟨h, hh⟩
    exact ⟨⟨a, h⟩, hh, rfl⟩

open Classical in
/-- A color sample is a subfamily of the original finite family. -/
theorem colorSample_subset {α : Type*} (L : Finset α) {k : ℕ} (χ : ↥L → Fin k) :
    colorSample L χ ⊆ L := by
  intro a ha
  exact ((mem_colorSample_iff L χ a).mp ha).choose

open Classical in
/-- The sample cardinality is the sum of the coordinate indicators. -/
theorem colorSample_card_eq_sum {α : Type*} (L : Finset α) {k : ℕ}
    (χ : ↥L → Fin k) :
    ((colorSample L χ).card : ℝ) = ∑ a : ↥L, if (χ a).val = 0 then 1 else 0 := by
  classical
  rw [colorSample, Finset.card_image_of_injective _ Subtype.val_injective]
  simp only [Finset.sum_boole, Finset.attach_eq_univ]

open Classical in
/-- The expected zero color class has size `L.card / k`. -/
theorem mean_colorSample_card {α : Type*} (L : Finset α) (k : ℕ) (hk : 0 < k) :
    finiteMean (Finset.univ : Finset (↥L → Fin k))
      (fun χ => ((colorSample L χ).card : ℝ)) = (L.card : ℝ) / (k : ℝ) := by
  classical
  let : NeZero k := ⟨Nat.ne_of_gt hk⟩
  calc
    _ = finiteMean Finset.univ
        (fun χ : ↥L → Fin k => ∑ a : ↥L, if (χ a).val = 0 then 1 else 0) := by
      apply Finset.expect_congr rfl
      intro χ _
      exact colorSample_card_eq_sum L χ
    _ = ∑ a : ↥L, finiteMean Finset.univ
        (fun χ : ↥L → Fin k => if (χ a).val = 0 then 1 else 0) :=
      Finset.expect_sum_comm _ _ _
    _ = ∑ _a : ↥L, (1 : ℝ) / (k : ℝ) := by
      apply Finset.sum_congr rfl
      intro a _
      calc
        _ = finiteMean Finset.univ (fun c : Fin k => if c.val = 0 then (1 : ℝ) else 0) :=
          finiteMean_fun_apply a (fun c : Fin k => if c.val = 0 then (1 : ℝ) else 0)
        _ = (1 : ℝ) / (k : ℝ) := by
          simp only [finiteMean, Finset.expect_eq_sum_div_card, Finset.card_univ,
            Fintype.card_fin]
          have hzero (c : Fin k) : c.val = 0 ↔ c = (⟨0, hk⟩ : Fin k) := by
            exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
          simp only [hzero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    _ = (L.card : ℝ) / (k : ℝ) := by simp [div_eq_mul_inv]

end ExplicitRIP.Zahl
