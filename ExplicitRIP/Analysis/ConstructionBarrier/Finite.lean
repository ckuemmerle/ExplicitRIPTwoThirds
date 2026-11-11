/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.ConstructionBarrier.Star
public import ExplicitRIP.Analysis.ConstructionBarrier.Parameters

/-!
# The finite construction barrier

The row-energy, large-star, and unsaturated-star estimates apply to any selected columns of the
Hermitian-forms model of the host frame with parameters [KM, (13)]. These give a host-specific
version of the star argument in [KM, proof of Proposition 10].
-/

public section

open scoped Matrix BigOperators

namespace ExplicitRIP.Actbar

theorem selected_gram_diag (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
    (Γ : Finset (ZMod p × ZMod p × ZMod p × ZMod p))
    (Φ : Matrix (Fin (rowCount p)) Γ ℝ)
    (hGram : Φᵀ * Φ = (hermitianHostGram ℝ p).submatrix Subtype.val Subtype.val) (v : Γ) :
    (Φᴴ * Φ : Matrix Γ Γ ℝ) v v = 1 := by
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, hGram]
  exact HostFrame.hostGram_apply_self p v.val

open Classical in
theorem selected_gram_offdiag (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
    (Γ : Finset (ZMod p × ZMod p × ZMod p × ZMod p))
    (Φ : Matrix (Fin (rowCount p)) Γ ℝ)
    (hGram : Φᵀ * Φ = (hermitianHostGram ℝ p).submatrix Subtype.val Subtype.val)
    (v w : Γ) (hvw : v ≠ w) :
    (Φᴴ * Φ - 1 : Matrix Γ Γ ℝ) v w =
      if (hermitianGraph p).Adj v.val w.val then -largeEntry p else smallEntry p := by
  rw [Matrix.sub_apply, Matrix.one_apply_ne hvw, sub_zero,
    Matrix.conjTranspose_eq_transpose_of_trivial, hGram]
  exact hostGram_offdiag p v.val w.val (fun h => hvw (Subtype.ext h))

/-- Below the full-star energy, sparsity is controlled by the central-column norm. -/
theorem finite_barrier (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
    (Γ : Finset (ZMod p × ZMod p × ZMod p × ZMod p))
    (Φ : Matrix (Fin (rowCount p)) Γ ℝ) (hΓ : Γ.Nonempty)
    (hGram : Φᵀ * Φ = (hermitianHostGram ℝ p).submatrix Subtype.val Subtype.val)
    (k : ℕ) (hδ : ripConstant Φ k ^ 2 < (Γ.card : ℝ) / rowCount p - 2) :
    (k : ℝ) ≤ 1 + 4 * ripConstant Φ k ^ 2 * (p : ℝ) ^ 2 := by
  classical
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  let : Nonempty Γ := hΓ.to_subtype
  have hu (j : Γ) : ∑ i, ‖Φ i j‖ ^ 2 = 1 := by
    have h := selected_gram_diag p Γ Φ hGram j
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
      Real.norm_eq_abs, sq_abs, ← pow_two] using h
  obtain ⟨v, hv⟩ := exists_large_column (rowCount p) Φ (rowCount_pos hp) hu
  simp only [Fintype.card_coe] at hv
  let N : Finset Γ := Finset.univ.filter fun i => (hermitianGraph p).Adj i.val v.val
  have hvN : v ∉ N := by simp [N]
  have hN (i : Γ) (hi : i ∈ N) : (Φᴴ * Φ - 1 : Matrix Γ Γ ℝ) i v = -largeEntry p := by
    have hadj := (Finset.mem_filter.mp hi).2
    have hiv : i ≠ v := fun h => hadj.ne (congrArg Subtype.val h)
    rw [selected_gram_offdiag p Γ Φ hGram i v hiv, ite_eq_left hadj]
  have hentry (i : Γ) : ((Φᴴ * Φ - 1 : Matrix Γ Γ ℝ) i v) ^ 2 ≤
      (if i ∈ N then largeEntry p ^ 2 else 0) + smallEntry p ^ 2 := by
    by_cases hi : i ∈ N
    · rw [hN i hi, neg_sq, ite_eq_left hi]
      exact le_add_of_nonneg_right (sq_nonneg _)
    · rw [ite_eq_right hi, zero_add]
      by_cases hiv : i = v
      · subst i
        rw [Matrix.sub_apply, selected_gram_diag p Γ Φ hGram v, Matrix.one_apply_eq,
          sub_self, zero_pow (by decide : 2 ≠ 0)]
        exact sq_nonneg _
      · have hnot : ¬ (hermitianGraph p).Adj i.val v.val := by simpa [N] using hi
        rw [selected_gram_offdiag p Γ Φ hGram i v hiv, ite_eq_right hnot]
  have hupper := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hentry i)
  have hsum : (∑ i : Γ, ((if i ∈ N then largeEntry p ^ 2 else 0) + smallEntry p ^ 2)) =
      (N.card : ℝ) * largeEntry p ^ 2 + Γ.card * smallEntry p ^ 2 := by
    simp only [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.univ_inter, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  rw [hsum] at hupper
  have hsmall := small_energy_le_one (host_card_le p Γ)
  have hlarge : ripConstant Φ k ^ 2 < (N.card : ℝ) * largeEntry p ^ 2 := by
    linarith only [hv, hupper, hsmall, hδ]
  by_cases hk : k = 0
  · subst k
    simp only [Nat.cast_zero]
    positivity
  · have hk1 : 1 ≤ k := by omega
    have hstar := star_energy_le Φ v N (largeEntry p) hvN hN k hk1
    have hlt : k - 1 < N.card := by
      by_contra! h
      rw [min_eq_right h] at hstar
      exact (not_lt_of_ge hstar) hlarge
    rw [min_eq_left hlt.le] at hstar
    have ha := one_le_four_mul_sq_largeEntry hp
    have hmul := mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg (k - 1) : (0 : ℝ) ≤ (k - 1 : ℕ))
    have hstar' := mul_le_mul_of_nonneg_left hstar (by positivity : (0 : ℝ) ≤ 4 * (p : ℝ) ^ 2)
    rw [Nat.cast_sub hk1, Nat.cast_one] at hmul hstar'
    nlinarith only [hmul, hstar']

end ExplicitRIP.Actbar
