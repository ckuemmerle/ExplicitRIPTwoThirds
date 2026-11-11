/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# Two-angle Gram matrix identities

Diagonal and row-sum identities for a scaled projection supported on a regular graph.
These are the first identities in [KM, Appendix A].
-/

public section

open scoped Matrix

namespace ExplicitRIP.SrgScaling

variable {V : Type*} [Fintype V] [DecidableEq V]
  (Γ : SimpleGraph V) [DecidableRel Γ.Adj]

omit [DecidableEq V] in
/-- A row of an adjacency matrix sums to the degree. -/
theorem sum_adjacency (x : V) : ∑ y, Γ.adjMatrix ℝ x y = Γ.degree x := by
  simpa only [Matrix.mulVec, dotProduct, Function.const_apply, mul_one] using
    (SimpleGraph.adjMatrix_mulVec_const_apply (G := Γ) (a := (1 : ℝ)) (v := x))

/-- The complementary degree, expressed in the real numbers. -/
theorem compl_degree_real {v k l c : ℕ} (h : Γ.IsSRGWith v k l c) (x : V) :
    (Γᶜ.degree x : ℝ) = (v : ℝ) - 1 - k := by
  have hk : k < v := by simpa only [h.regular.degree_eq, h.card] using Γ.degree_lt_card_verts x
  rw [SimpleGraph.degree_compl, h.card, h.regular.degree_eq]
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]

/-- Row sums of a matrix constant on the diagonal, edges and complementary edges. -/
theorem sum_three_values {v k l c : ℕ} (h : Γ.IsSRGWith v k l c)
    (a b d : ℝ) (x : V) :
    ∑ y, (a • (1 : Matrix V V ℝ) + b • Γ.adjMatrix ℝ + d • Γᶜ.adjMatrix ℝ) x y =
      a + b * k + d * ((v : ℝ) - 1 - k) := by
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, Matrix.one_apply]
  rw [sum_adjacency, sum_adjacency, h.regular.degree_eq, compl_degree_real Γ h]
  simp

omit [Fintype V] in
/-- The diagonal of the two-angle matrix is one. -/
theorem gram_diag (μ ν ε : ℝ) (x : V) :
    (1 + ε • (μ • Γ.adjMatrix ℝ - ν • Γᶜ.adjMatrix ℝ)) x x = 1 := by
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    SimpleGraph.adjMatrix_apply, SimpleGraph.irrefl, ite_false, smul_zero, sub_self,
    Matrix.one_apply_eq, add_zero]

omit [Fintype V] in
/-- A scaled projection with unit diagonal has positive dimension. -/
theorem projection_dimension_pos [Nonempty V] (P : Matrix V V ℝ)
    (v m : ℕ) (μ ν ε : ℝ)
    (hG : ((v : ℝ) / m) • P =
      1 + ε • (μ • Γ.adjMatrix ℝ - ν • Γᶜ.adjMatrix ℝ)) : 0 < m := by
  by_contra hm
  have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
  let x : V := Classical.choice inferInstance
  have hd := congrArg (fun M : Matrix V V ℝ => M x x) hG
  simp only [hm0, Nat.cast_zero, div_zero, zero_smul, Matrix.zero_apply, gram_diag] at hd
  exact zero_ne_one hd

/-- A unit-diagonal matrix annihilating constants requires at least two vertices. -/
theorem projection_nontrivial [Nonempty V] (P : Matrix V V ℝ)
    (v m μ ν ε : ℝ) (hzero : P *ᵥ (fun _ => (1 : ℝ)) = 0)
    (hG : (v / m) • P =
      1 + ε • (μ • Γ.adjMatrix ℝ - ν • Γᶜ.adjMatrix ℝ)) : Nontrivial V := by
  rcases subsingleton_or_nontrivial V with hsub | hnontriv
  · have := hsub
    let x : V := Classical.choice inferInstance
    have hrow : (1 + ε • (μ • Γ.adjMatrix ℝ - ν • Γᶜ.adjMatrix ℝ)) *ᵥ
        (fun _ => (1 : ℝ)) = 0 := by
      rw [← hG, Matrix.smul_mulVec, hzero, smul_zero]
    have hr := congrFun hrow x
    simp only [Matrix.mulVec, dotProduct, mul_one, Pi.zero_apply] at hr
    rw [Fintype.sum_subsingleton _ x, gram_diag] at hr
    exact (one_ne_zero hr).elim
  · exact hnontriv

/-- The squared norm of a Gram row is determined by the two off-diagonal values. -/
theorem gram_square_diag {v k l c : ℕ} (h : Γ.IsSRGWith v k l c)
    (μ ν ε : ℝ) (hε : ε = 1 ∨ ε = -1) (x : V) :
    let G := 1 + ε • (μ • Γ.adjMatrix ℝ - ν • Γᶜ.adjMatrix ℝ)
    (G * G) x x = 1 + (k : ℝ) * μ ^ 2 + ((v : ℝ) - 1 - k) * ν ^ 2 := by
  dsimp
  rw [Matrix.mul_apply]
  have heq : ∀ y : V,
      (1 + ε • (μ • Γ.adjMatrix ℝ - ν • Γᶜ.adjMatrix ℝ)) x y *
        (1 + ε • (μ • Γ.adjMatrix ℝ - ν • Γᶜ.adjMatrix ℝ)) y x =
      ((1 : ℝ) • (1 : Matrix V V ℝ) + μ ^ 2 • Γ.adjMatrix ℝ +
        ν ^ 2 • Γᶜ.adjMatrix ℝ) x y := by
    intro y
    rcases hε with rfl | rfl <;>
      by_cases hxy : x = y <;> by_cases ha : Γ.Adj x y <;>
      simp_all [SimpleGraph.adjMatrix_apply, SimpleGraph.compl_adj,
        Γ.adj_comm, eq_comm] <;> ring
  simp_rw [heq]
  rw [sum_three_values Γ h]
  ring

/-- Idempotence and the vanishing row sum yield the two scalar moment identities. -/
theorem projection_moments {v k l c : ℕ} [Nonempty V]
    (h : Γ.IsSRGWith v k l c) (P : Matrix V V ℝ) (m μ ν ε : ℝ)
    (hP : P * P = P) (hzero : P *ᵥ (fun _ => (1 : ℝ)) = 0)
    (hG : ((v : ℝ) / m) • P =
      1 + ε • (μ • Γ.adjMatrix ℝ - ν • Γᶜ.adjMatrix ℝ))
    (hε : ε = 1 ∨ ε = -1) :
    1 + (k : ℝ) * μ ^ 2 + ((v : ℝ) - 1 - k) * ν ^ 2 = (v : ℝ) / m ∧
      (k : ℝ) * (μ + ν) = ((v : ℝ) - 1) * ν - ε := by
  let G := 1 + ε • (μ • Γ.adjMatrix ℝ - ν • Γᶜ.adjMatrix ℝ)
  have hscale : G = ((v : ℝ) / m) • P := hG.symm
  have hsquare : G * G = ((v : ℝ) / m) • G := by
    simp only [hscale, Matrix.smul_mul, Matrix.mul_smul, hP]
  have hrow : G *ᵥ (fun _ => (1 : ℝ)) = 0 := by
    rw [hscale, Matrix.smul_mulVec, hzero, smul_zero]
  let x : V := Classical.choice inferInstance
  constructor
  · have hd := congrArg (fun M : Matrix V V ℝ => M x x) hsquare
    rw [gram_square_diag Γ h μ ν ε hε x] at hd
    have hdiag : G x x = 1 := gram_diag Γ μ ν ε x
    simpa only [Matrix.smul_apply, hdiag, smul_eq_mul, mul_one] using hd
  · have hr := congrFun hrow x
    have hs : ∑ y, G x y = 1 + ε * (μ * k - ν * ((v : ℝ) - 1 - k)) := by
      change ∑ y, (1 + ε • (μ • Γ.adjMatrix ℝ - ν • Γᶜ.adjMatrix ℝ)) x y = _
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [sum_adjacency, sum_adjacency, h.regular.degree_eq, compl_degree_real Γ h]
      simp [Matrix.one_apply]
    change ∑ y, G x y * 1 = 0 at hr
    simp only [mul_one] at hr
    rw [hs] at hr
    rcases hε with rfl | rfl <;> linarith only [hr]

/-- Eliminating the degree from the two moment identities gives the product identity. -/
theorem eliminate_degree (v k m μ ν ε : ℝ)
    (hsquare : 1 + k * μ ^ 2 + (v - 1 - k) * ν ^ 2 = v / m)
    (hrow : k * (μ + ν) = (v - 1) * ν - ε) :
    v / m - 1 = (v - 1) * μ * ν - ε * (μ - ν) := by
  have h := congrArg (fun t : ℝ => (μ - ν) * t) hrow
  nlinarith only [hsquare, h]

end ExplicitRIP.SrgScaling
