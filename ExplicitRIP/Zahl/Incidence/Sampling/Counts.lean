/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Incidence.Sampling.Mean

/-! # Indicator counts and their first two factorial moments -/

public section

namespace ExplicitRIP.Zahl.Sampling

open scoped BigOperators

lemma offDiag_card_real {α : Type*} (s : Finset α) :
    (s.offDiag.card : ℝ) = (s.card : ℝ) * ((s.card : ℝ) - 1) := by
  rw [Finset.offDiag_card]
  have h : s.card ≤ s.card * s.card := by
    rcases Nat.eq_zero_or_pos s.card with h | h
    · simp only [h, zero_mul, le_refl]
    · nlinarith
  rw [Nat.cast_sub h, Nat.cast_mul]
  ring

open Classical in
lemma expect_card_filter {α Ω : Type*} (s : Finset α) (A : Finset Ω)
    (p : Ω → α → Prop) [∀ ω, DecidablePred (p ω)] (a : ℝ)
    (h : ∀ i ∈ s, Finset.expect A (fun ω => if p ω i then (1 : ℝ) else 0) = a) :
    Finset.expect A (fun ω => ((s.filter (p ω)).card : ℝ)) = (s.card : ℝ) * a := by
  simp_rw [← Finset.sum_boole]
  rw [Finset.expect_sum_comm]
  calc
    _ = ∑ _i ∈ s, a := Finset.sum_congr rfl h
    _ = _ := by simp

open Classical in
lemma expect_card_filter_factorial {α Ω : Type*} (s : Finset α) (A : Finset Ω)
    (p : Ω → α → Prop) [∀ ω, DecidablePred (p ω)] (b : ℝ)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Finset.expect A (fun ω => if p ω i ∧ p ω j then (1 : ℝ) else 0) = b) :
    Finset.expect A (fun ω => ((s.filter (p ω)).card : ℝ) *
      (((s.filter (p ω)).card : ℝ) - 1)) =
        (s.card : ℝ) * ((s.card : ℝ) - 1) * b := by
  have heq (ω) : (s.filter (p ω)).offDiag =
      s.offDiag.filter (fun ij => p ω ij.1 ∧ p ω ij.2) := by
    ext ij
    simp only [Finset.mem_offDiag, Finset.mem_filter]
    tauto
  simp_rw [← offDiag_card_real, heq]
  apply expect_card_filter s.offDiag A (fun ω ij => p ω ij.1 ∧ p ω ij.2) b
  intro ij hij
  obtain ⟨hi, hj, hne⟩ := Finset.mem_offDiag.mp hij
  exact h ij.1 hi ij.2 hj hne

lemma bonferroni_two (n : ℕ) :
    (n : ℝ) - (n : ℝ) * ((n : ℝ) - 1) / 2 ≤ if 0 < n then 1 else 0 := by
  rcases n with _ | n
  · norm_num
  rcases n with _ | n
  · norm_num
  simp only [Nat.cast_add, Nat.cast_one, Nat.succ_pos, ite_true]
  nlinarith [sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]

open Classical in
lemma expect_nonempty_lower {α Ω : Type*} (s : Finset α) (A : Finset Ω)
    (p : Ω → α → Prop) [∀ ω, DecidablePred (p ω)] (a b : ℝ)
    (h₁ : ∀ i ∈ s, Finset.expect A (fun ω => if p ω i then (1 : ℝ) else 0) = a)
    (h₂ : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Finset.expect A (fun ω => if p ω i ∧ p ω j then (1 : ℝ) else 0) = b) :
    (s.card : ℝ) * a - (s.card : ℝ) * ((s.card : ℝ) - 1) * b / 2 ≤
      Finset.expect A (fun ω => if (s.filter (p ω)).Nonempty then 1 else 0) := by
  calc
    _ = Finset.expect A (fun ω => ((s.filter (p ω)).card : ℝ) -
        ((s.filter (p ω)).card : ℝ) * (((s.filter (p ω)).card : ℝ) - 1) / 2) := by
      rw [Finset.expect_sub_distrib, ← Finset.expect_div,
        expect_card_filter _ _ _ a h₁, expect_card_filter_factorial _ _ _ b h₂]
    _ ≤ _ := Finset.expect_le_expect fun ω _ => by
      simpa only [Finset.card_pos] using bonferroni_two (s.filter (p ω)).card

end ExplicitRIP.Zahl.Sampling
