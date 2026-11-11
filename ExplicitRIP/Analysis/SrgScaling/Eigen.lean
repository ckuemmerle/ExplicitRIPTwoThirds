/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.SrgScaling.Gram

/-!
# Adjacency action on a two-angle Gram matrix

The scalar adjacency action determines both common-neighbor parameters, as in
[KM, Appendix A].
-/

public section

open scoped Matrix

namespace ExplicitRIP.SrgScaling

variable {V : Type*} [Fintype V] [DecidableEq V]
  (Γ : SimpleGraph V) [DecidableRel Γ.Adj]

omit [Fintype V] in
/-- The complementary adjacency matrix is the all-ones matrix minus the diagonal and edges. -/
theorem complement_adjacency :
    Γᶜ.adjMatrix ℝ = Matrix.of 1 - 1 - Γ.adjMatrix ℝ := by
  ext x y
  by_cases hxy : x = y <;> by_cases ha : Γ.Adj x y <;>
    simp_all [SimpleGraph.adjMatrix_apply, SimpleGraph.compl_adj]

omit [DecidableEq V] in
/-- A regular adjacency matrix maps the constant matrix to its degree times that matrix. -/
theorem adjacency_mul_ones {v k l c : ℕ} (h : Γ.IsSRGWith v k l c) :
    Γ.adjMatrix ℝ * Matrix.of 1 = (k : ℝ) • Matrix.of 1 := by
  ext x y
  simpa only [Matrix.mul_apply, Matrix.of_apply, Pi.one_apply, mul_one,
    Matrix.smul_apply, smul_eq_mul] using
    (sum_adjacency Γ x).trans (congrArg (Nat.cast : ℕ → ℝ) (h.regular.degree_eq x))

/-- Multiplying by the Gram matrix can be evaluated using the SRG matrix identity. -/
theorem adjacency_gram_apply {v k l c : ℕ} (h : Γ.IsSRGWith v k l c)
    (μ ν ε : ℝ) (x y : V) :
    (Γ.adjMatrix ℝ * (1 + ε • (μ • Γ.adjMatrix ℝ - ν • Γᶜ.adjMatrix ℝ))) x y =
      Γ.adjMatrix ℝ x y + ε *
        ((μ + ν) * ((k : ℝ) * (1 : Matrix V V ℝ) x y +
          (l : ℝ) * Γ.adjMatrix ℝ x y + (c : ℝ) * Γᶜ.adjMatrix ℝ x y) +
          ν * Γ.adjMatrix ℝ x y - ν * k) := by
  have hsq : Γ.adjMatrix ℝ * Γ.adjMatrix ℝ =
      (k : ℝ) • (1 : Matrix V V ℝ) + (l : ℝ) • Γ.adjMatrix ℝ +
        (c : ℝ) • Γᶜ.adjMatrix ℝ := by
    simpa only [pow_two, Nat.cast_smul_eq_nsmul] using (h.matrix_eq (α := ℝ))
  have hc := complement_adjacency Γ
  have hprod : Γ.adjMatrix ℝ * Γᶜ.adjMatrix ℝ =
      (k : ℝ) • Matrix.of 1 - Γ.adjMatrix ℝ - Γ.adjMatrix ℝ * Γ.adjMatrix ℝ := by
    conv_lhs => rw [hc]
    rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, adjacency_mul_ones Γ h]
  simp only [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_sub]
  rw [hprod]
  simp only [hsq, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.of_apply, Pi.one_apply]
  ring

/-- The eigenvalue and the two common-neighbor identities follow entry by entry. -/
theorem eigenvalue_parameters {v k l c : ℕ} [Nontrivial V]
    (h : Γ.IsSRGWith v k l c) (hconn : Γ.Connected) (hcompl : Γᶜ.Connected)
    (P : Matrix V V ℝ) (m θ μ ν ε : ℝ)
    (hAP : Γ.adjMatrix ℝ * P = θ • P)
    (hG : ((v : ℝ) / m) • P =
      1 + ε • (μ • Γ.adjMatrix ℝ - ν • Γᶜ.adjMatrix ℝ))
    (hε : ε = 1 ∨ ε = -1) :
    θ = ε * k * μ ∧
      (μ + ν) * c = (k : ℝ) * ν * (1 - ε * μ) ∧
      (μ + ν) * l = ((k : ℝ) - 1) * ν + ε * ((k : ℝ) * μ ^ 2 - 1) := by
  let G := 1 + ε • (μ • Γ.adjMatrix ℝ - ν • Γᶜ.adjMatrix ℝ)
  have heigen : Γ.adjMatrix ℝ * G = θ • G := by
    calc
      Γ.adjMatrix ℝ * G = ((v : ℝ) / m) • (Γ.adjMatrix ℝ * P) := by
        rw [show G = ((v : ℝ) / m) • P from hG.symm, Matrix.mul_smul]
      _ = ((v : ℝ) / m) • (θ • P) := by rw [hAP]
      _ = θ • (((v : ℝ) / m) • P) := smul_comm _ _ _
      _ = θ • G := congrArg (fun M : Matrix V V ℝ => θ • M) hG
  let x : V := Classical.choice inferInstance
  have hθ : θ = ε * k * μ := by
    have hd := congrArg (fun M : Matrix V V ℝ => M x x) heigen
    rw [adjacency_gram_apply Γ h μ ν ε] at hd
    rw [Matrix.smul_apply, show G x x = 1 from gram_diag Γ μ ν ε x] at hd
    simp only [SimpleGraph.adjMatrix_apply, SimpleGraph.irrefl, ite_false,
      Matrix.one_apply_eq, mul_one, mul_zero, add_zero, zero_add, smul_eq_mul] at hd
    linarith only [hd]
  refine ⟨hθ, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hcompl.preconnected.exists_adj_of_nontrivial x
    have hxy := Γᶜ.ne_of_adj hy
    have hna := (SimpleGraph.compl_adj Γ x y).mp hy |>.2
    have hn := congrArg (fun M : Matrix V V ℝ => M x y) heigen
    rw [adjacency_gram_apply Γ h μ ν ε] at hn
    simp only [G, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul,
      SimpleGraph.adjMatrix_apply, hy, hna, ite_true, ite_false, Matrix.one_apply_ne hxy,
      mul_zero, mul_one, zero_sub, zero_add, add_zero, hθ] at hn
    rcases hε with rfl | rfl <;> nlinarith only [hn]
  · obtain ⟨y, hy⟩ := hconn.preconnected.exists_adj_of_nontrivial x
    have hxy := Γ.ne_of_adj hy
    have hna : ¬Γᶜ.Adj x y := by simp only [SimpleGraph.compl_adj, hy, not_true_eq_false,
      and_false, not_false_eq_true]
    have he := congrArg (fun M : Matrix V V ℝ => M x y) heigen
    rw [adjacency_gram_apply Γ h μ ν ε] at he
    simp only [G, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul,
      SimpleGraph.adjMatrix_apply, hy, hna, ite_true, ite_false, Matrix.one_apply_ne hxy,
      mul_zero, mul_one, sub_zero, zero_add, add_zero, hθ] at he
    rcases hε with rfl | rfl <;> nlinarith only [he]

end ExplicitRIP.SrgScaling
