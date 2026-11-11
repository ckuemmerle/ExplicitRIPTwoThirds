/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.IsTwoDistanceTightFrame
public import ExplicitRIP.Analysis.RIPOneTwo.Basic

/-!
# The smaller inner product of a two-distance tight frame

The smaller absolute inner product is attained and is small when the ambient
dimension is large. The larger absolute inner product equals the coherence.

The barrier argument needs less than the predicate
`ExplicitRIP.IsTwoDistanceTightFrame`: unit-norm columns, `F Fᵀ = c I` for some `c`, and at most
two inner products of distinct columns. The results of this directory are stated for that weaker
predicate, `IsWeakTwoDistanceTightFrame`, which `ExplicitRIP.IsTwoDistanceTightFrame` implies
(`isWeakTwoDistanceTightFrame_of`).

Source: [KM, proof of Proposition 10].
-/

public section

open scoped Matrix BigOperators

namespace ExplicitRIP.TwoDistanceBarrier

/-- Unit-norm columns, a tight frame (`F Fᵀ = c I` for some `c`), and at most two inner products
of distinct columns: the hypotheses that the barrier argument uses. -/
@[expose] def IsWeakTwoDistanceTightFrame {m N : Type*} [Fintype m] [Fintype N] [DecidableEq m]
    (F : Matrix m N ℝ) : Prop :=
  (∀ j, ∑ i, F i j ^ 2 = 1) ∧ (∃ c : ℝ, F * Fᵀ = c • (1 : Matrix m m ℝ)) ∧
    ∃ α β : ℝ, ∀ i j, i ≠ j → (Fᵀ * F) i j = α ∨ (Fᵀ * F) i j = β

/-- A two-distance tight frame satisfies the weaker hypotheses: the diagonal entries of `Fᵀ F`
are the squared column norms. -/
theorem isWeakTwoDistanceTightFrame_of {m N : Type*} [Fintype m] [Fintype N] [DecidableEq m]
    {F : Matrix m N ℝ} (hF : IsTwoDistanceTightFrame F) : IsWeakTwoDistanceTightFrame F := by
  obtain ⟨a, b, c, -, hdiag, h, hc⟩ := hF
  refine ⟨fun j => ?_, ⟨c, hc⟩, a, b, h⟩
  have := hdiag j
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at this
  simpa [sq] using this

/-- A function with at most two values has two attained values ordered by magnitude. -/
theorem ordered_values {P : Type*} [Nonempty P] (f : P → ℝ)
    (h : ∃ α β, ∀ x, f x = α ∨ f x = β) :
    ∃ η θ, (∃ x, f x = η) ∧ (∃ x, f x = θ) ∧ |η| ≤ |θ| ∧
      ∀ x, f x = η ∨ f x = θ := by
  classical
  obtain ⟨α, β, h⟩ := h
  have hex : ∃ a b, (∃ x, f x = a) ∧ (∃ x, f x = b) ∧
      ∀ x, f x = a ∨ f x = b := by
    by_cases ha : ∃ x, f x = α
    · by_cases hb : ∃ x, f x = β
      · exact ⟨α, β, ha, hb, h⟩
      · exact ⟨α, α, ha, ha, fun x => Or.inl ((h x).resolve_right
          (fun hx => hb ⟨x, hx⟩))⟩
    · have hb : ∀ x, f x = β := fun x => (h x).resolve_left (fun hx => ha ⟨x, hx⟩)
      exact ⟨β, β, ⟨Classical.arbitrary P, hb _⟩, ⟨Classical.arbitrary P, hb _⟩,
        fun x => Or.inl (hb x)⟩
  obtain ⟨a, b, ha, hb, hab⟩ := hex
  by_cases hle : |a| ≤ |b|
  · exact ⟨a, b, ha, hb, hle, hab⟩
  · exact ⟨b, a, hb, ha, le_of_not_ge hle, fun x => (hab x).symm⟩

/-- The unit-column condition identifies each diagonal Gram entry. -/
theorem gram_diag {m N : ℕ} (F : Matrix (Fin m) (Fin N) ℝ)
    (hunit : ∀ j, ∑ i, F i j ^ 2 = 1) (j : Fin N) : (Fᵀ * F) j j = 1 := by
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, ← pow_two] using hunit j

/-- Normalize the two inner products, retaining only values actually attained by the frame. -/
theorem frame_distances {m N : ℕ} (F : Matrix (Fin m) (Fin N) ℝ)
    (hF : IsWeakTwoDistanceTightFrame F) (hN : 2 ≤ N) :
    ∃ η : ℝ, |η| ≤ coherence F ∧
      (∀ i j, i ≠ j → |η| ≤ |(Fᵀ * F) i j|) ∧
      (∀ i j, i ≠ j → (Fᵀ * F) i j = η ∨ |(Fᵀ * F) i j| = coherence F) := by
  classical
  let P := {ij : Fin N × Fin N // ij.1 ≠ ij.2}
  have h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by
    intro h
    have he : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  have : Nonempty P := ⟨⟨(⟨0, by omega⟩, ⟨1, by omega⟩), h01⟩⟩
  let f : P → ℝ := fun x => (Fᵀ * F) x.val.1 x.val.2
  obtain ⟨η, θ, _, ⟨x, hx⟩, hle, hv⟩ := ordered_values f (by
    obtain ⟨α, β, h⟩ := hF.2.2
    exact ⟨α, β, fun x => h _ _ x.property⟩)
  have hμ : coherence F = |θ| := by
    apply le_antisymm
    · apply ciSup_le
      intro y
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, Real.norm_eq_abs]
      rcases hv y with hy | hy
      · change |f y| ≤ |θ|
        rwa [hy]
      · change |f y| ≤ |θ|
        rw [hy]
    · have h := RIPOneTwo.gram_norm_le_coherence F x.val.1 x.val.2 x.property
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, Real.norm_eq_abs] at h
      change |f x| ≤ coherence F at h
      rwa [hx] at h
  refine ⟨η, hμ ▸ hle, ?_, ?_⟩
  · intro i j hij
    rcases hv ⟨(i, j), hij⟩ with he | he
    · change |η| ≤ |f ⟨(i, j), hij⟩|
      rw [he]
    · change |η| ≤ |f ⟨(i, j), hij⟩|
      rwa [he]
  · intro i j hij
    rcases hv ⟨(i, j), hij⟩ with he | he
    · exact Or.inl he
    · exact Or.inr (by change |f ⟨(i, j), hij⟩| = coherence F; rw [he, hμ])

/-- The smaller absolute inner product is at most one half once `m ≥ 8`. -/
theorem small_distance_le_half {m N : ℕ} (F : Matrix (Fin m) (Fin N) ℝ)
    (hF : IsWeakTwoDistanceTightFrame F) (hm : 8 ≤ m) (hN : 2 ≤ N) (η : ℝ)
    (hη : ∀ i j, i ≠ j → |η| ≤ |(Fᵀ * F) i j|) : |η| ≤ 1 / 2 := by
  classical
  obtain ⟨hunit, ⟨c, htight⟩, _⟩ := hF
  let G := Fᵀ * F
  have hdiag : ∀ j, G j j = 1 := gram_diag F hunit
  have hc : c * (m : ℝ) = (N : ℝ) := by
    have htr : Matrix.trace (Fᵀ * F) = (N : ℝ) := by
      simp only [Matrix.trace, Matrix.diag, gram_diag F hunit, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have h := congrArg Matrix.trace htight
    rw [Matrix.trace_mul_comm, htr] at h
    simpa only [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
      using h.symm
  have hsq : G * G = c • G := by
    change (Fᵀ * F) * (Fᵀ * F) = c • (Fᵀ * F)
    calc
      _ = Fᵀ * (F * Fᵀ) * F := by simp only [Matrix.mul_assoc]
      _ = c • (Fᵀ * F) := by rw [htight]; simp only [Matrix.mul_smul,
        Matrix.mul_one, Matrix.smul_mul]
  have hsymm : ∀ i j, G i j = G j i := by
    intro i j
    have he : Gᵀ = G := by
      simp only [G, Matrix.transpose_mul, Matrix.transpose_transpose]
    exact congrArg (fun A : Matrix (Fin N) (Fin N) ℝ => A i j) he.symm
  let j : Fin N := ⟨0, by omega⟩
  have hcol : ∑ i, G i j ^ 2 = c := by
    have h := congrArg (fun A : Matrix (Fin N) (Fin N) ℝ => A j j) hsq
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, hdiag, mul_one] at h
    simpa only [hsymm j, ← pow_two] using h
  have hlower : ((N : ℝ) - 1) * η ^ 2 ≤ c := by
    calc
      _ = ∑ i ∈ Finset.univ.erase j, η ^ 2 := by
        simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j),
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ N),
          Nat.cast_one]
      _ ≤ ∑ i ∈ Finset.univ.erase j, G i j ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact (sq_le_sq).mpr (by simpa only [abs_abs] using hη i j (Finset.mem_erase.mp hi).1)
      _ ≤ ∑ i, G i j ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.erase_subset _ _) (fun i _ _ => sq_nonneg _)
      _ = c := hcol
  have hm' : (8 : ℝ) ≤ m := by exact_mod_cast hm
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hmul := mul_le_mul_of_nonneg_right hlower (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  rw [hc] at hmul
  have hn : (0 : ℝ) < N - 1 := by linarith only [hN']
  have hsqη : η ^ 2 ≤ 1 / 4 := by
    have h8 := mul_le_mul_of_nonneg_right hm'
      (mul_nonneg (le_of_lt hn) (sq_nonneg η))
    nlinarith only [hmul, h8, hN']
  nlinarith only [sq_abs η, hsqη, abs_nonneg η]

end ExplicitRIP.TwoDistanceBarrier
