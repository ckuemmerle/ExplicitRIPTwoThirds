/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Contact.HostFrame.Transport

/-!
# Adjacency and Gram identities for the contact graph

The SRG quadratic identity identifies the range of the host Gram matrix with the least adjacency
eigenspace, giving the host-frame construction of [KM, Section 3, (13)].
-/

public section

open Matrix
open scoped BigOperators Matrix

namespace ExplicitRIP.Contact.HostFrame

/-- The SRG polynomial acts on its lower spectral projection by the lower root. -/
theorem adj_mul_projection_polynomial {V : Type*} [Fintype V] [DecidableEq V]
    (A J : Matrix V V ℝ) (x : ℝ) (hx : 1 < x)
    (hAA : A * A = ((x - 1) * (x ^ 2 + 1)) • (1 : Matrix V V ℝ) +
      (x - 2) • A + (x * (x - 1)) • (J - 1 - A))
    (hAJ : A * J = ((x - 1) * (x ^ 2 + 1)) • J) :
    let m := (x - 1) * (x ^ 2 + 1)
    let G := (x ^ 2 / m) • ((x - 1) • (1 : Matrix V V ℝ) - A) + ((x - 1) / m) • J
    A * G = (-(x ^ 2 - x + 1)) • G := by
  have hx1 : x - 1 ≠ 0 := by linarith
  have hxq : x ^ 2 + 1 ≠ 0 := by positivity
  dsimp only
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, hAA, hAJ]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  ring

variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

omit [Fact (p % 4 = 3)] in
theorem dimension_cast : (((p - 1) * (p ^ 2 + 1) : ℕ) : ℝ) =
    ((p : ℝ) - 1) * ((p : ℝ) ^ 2 + 1) := by
  simp only [Nat.cast_mul, Nat.cast_sub (Fact.out : p.Prime).one_le,
    Nat.cast_add, Nat.cast_pow, Nat.cast_one]

open Classical in
theorem hostGram_eq_polynomial :
    hostGram ℝ p =
      ((p : ℝ) ^ 2 / (((p : ℝ) - 1) * ((p : ℝ) ^ 2 + 1))) •
        (((p : ℝ) - 1) • 1 - (contactGraph p).adjMatrix ℝ) +
      (((p : ℝ) - 1) / (((p : ℝ) - 1) * ((p : ℝ) ^ 2 + 1))) •
        Matrix.of (fun _ _ => (1 : ℝ)) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpq : (p : ℝ) ^ 2 + 1 ≠ 0 := by positivity
  unfold hostGram
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, of_apply]
  field_simp
  ring

open Classical in
theorem adj_mul_adj :
    let A := (contactGraph p).adjMatrix ℝ
    let J := Matrix.of (fun _ _ : ZMod p × ZMod p × ZMod p × ZMod p => (1 : ℝ))
    A * A = (((p : ℝ) - 1) * ((p : ℝ) ^ 2 + 1)) • (1 : Matrix _ _ ℝ) +
      ((p : ℝ) - 2) • A + ((p : ℝ) * ((p : ℝ) - 1)) • (J - 1 - A) := by
  let A := (contactGraph p).adjMatrix ℝ
  let J := Matrix.of (fun _ _ : ZMod p × ZMod p × ZMod p × ZMod p => (1 : ℝ))
  have hcompl : (contactGraph p)ᶜ.adjMatrix ℝ = J - 1 - A := by
    apply (eq_sub_iff_add_eq).mpr
    rw [add_comm]
    exact (SimpleGraph.IsCompl.adjMatrix_add_adjMatrix_eq_adjMatrix_completeGraph ℝ
      isCompl_compl).trans (SimpleGraph.adjMatrix_completeGraph_eq_of_one_sub_one ℝ _)
  have h := (isSRGWith p).matrix_eq (α := ℝ)
  rw [pow_two, hcompl, ← Nat.cast_smul_eq_nsmul ℝ,
    ← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ] at h
  simpa only [dimension_cast, Nat.cast_sub (Fact.out : p.Prime).one_le,
    Nat.cast_sub (Fact.out : p.Prime).two_le, Nat.cast_mul, Nat.cast_add, Nat.cast_pow,
    Nat.cast_one, Nat.cast_ofNat] using h

open Classical in
theorem adj_mul_ones :
    (contactGraph p).adjMatrix ℝ * Matrix.of (fun _ _ => (1 : ℝ)) =
      (((p : ℝ) - 1) * ((p : ℝ) ^ 2 + 1)) • Matrix.of (fun _ _ => (1 : ℝ)) := by
  ext i j
  simp only [SimpleGraph.adjMatrix_mul_apply, of_apply, Finset.sum_const,
    Matrix.smul_apply, smul_eq_mul, mul_one, nsmul_eq_mul,
    SimpleGraph.card_neighborFinset_eq_degree, (isSRGWith p).regular.degree_eq,
    dimension_cast]

open Classical in
theorem ones_mul_adj :
    Matrix.of (fun _ _ => (1 : ℝ)) * (contactGraph p).adjMatrix ℝ =
      (((p : ℝ) - 1) * ((p : ℝ) ^ 2 + 1)) • Matrix.of (fun _ _ => (1 : ℝ)) := by
  ext i j
  simp only [SimpleGraph.mul_adjMatrix_apply, of_apply, Finset.sum_const,
    Matrix.smul_apply, smul_eq_mul, mul_one, nsmul_eq_mul,
    SimpleGraph.card_neighborFinset_eq_degree, (isSRGWith p).regular.degree_eq,
    dimension_cast]

open Classical in
theorem adj_mul_hostGram :
    (contactGraph p).adjMatrix ℝ * hostGram ℝ p =
      (-((p : ℝ) ^ 2 - p + 1)) • hostGram ℝ p := by
  rw [hostGram_eq_polynomial]
  exact adj_mul_projection_polynomial _ _ (p : ℝ)
    (by exact_mod_cast (Fact.out : p.Prime).one_lt) (adj_mul_adj p) (adj_mul_ones p)

end ExplicitRIP.Contact.HostFrame
