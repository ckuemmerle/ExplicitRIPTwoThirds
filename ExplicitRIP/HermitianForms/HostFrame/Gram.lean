/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.HermitianForms.Defs.HostGram

/-!
# The host Gram matrix is a scaled projection

The SRG identity and regularity suffice to check the quadratic equation directly for the
Hermitian-forms model of the host Gram matrix of [KM, Section 3, (13)]. The sphere map reindexes
this matrix to the contact-coordinate Gram matrix used in [KM, proof of Theorem 1].
-/

public section

open Matrix
open scoped BigOperators Matrix

namespace ExplicitRIP.HostFrame

/-- The polynomial calculation behind the projection onto the lower eigenspace. -/
theorem projection_polynomial {V : Type*} [Fintype V] [DecidableEq V]
    (A J : Matrix V V ℝ) (x : ℝ) (hx : 1 < x)
    (hAA : A * A = ((x - 1) * (x ^ 2 + 1)) • (1 : Matrix V V ℝ) +
      (x - 2) • A + (x * (x - 1)) • (J - 1 - A))
    (hAJ : A * J = ((x - 1) * (x ^ 2 + 1)) • J)
    (hJA : J * A = ((x - 1) * (x ^ 2 + 1)) • J)
    (hJJ : J * J = x ^ 4 • J) :
    let m := (x - 1) * (x ^ 2 + 1)
    let T := (x ^ 2 / m) • ((x - 1) • (1 : Matrix V V ℝ) - A) + ((x - 1) / m) • J
    T * T = (x ^ 4 / m) • T := by
  have hx1 : x - 1 ≠ 0 := by linarith
  have hxq : x ^ 2 + 1 ≠ 0 := by positivity
  dsimp only
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hAA, hAJ, hJA, hJJ]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  ring

open Classical in
/-- The host Gram formula in its spectral polynomial form. -/
theorem hostGram_eq_polynomial (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)] :
    hermitianHostGram ℝ p =
      ((p : ℝ) ^ 2 / (((p : ℝ) - 1) * ((p : ℝ) ^ 2 + 1))) •
        (((p : ℝ) - 1) • 1 - (hermitianGraph p).adjMatrix ℝ) +
      (((p : ℝ) - 1) / (((p : ℝ) - 1) * ((p : ℝ) ^ 2 + 1))) •
        Matrix.of (fun _ _ => (1 : ℝ)) := by
  classical
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpq : (p : ℝ) ^ 2 + 1 ≠ 0 := by positivity
  unfold hermitianHostGram
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, of_apply]
  field_simp
  ring

/-- Symmetry of the two-distance host Gram matrix. -/
theorem hostGram_isHermitian (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)] :
    (hermitianHostGram ℝ p).IsHermitian := by
  classical
  rw [isHermitian_iff_isSymm, hermitianHostGram]
  exact (isSymm_one.sub ((hermitianGraph p).isSymm_adjMatrix.smul _)).add
    (((show (Matrix.of (fun _ _ => (1 : ℝ))).IsSymm from rfl).sub isSymm_one).sub
      (hermitianGraph p).isSymm_adjMatrix |>.smul _)

/-- The trace equals the vertex count. -/
theorem hostGram_trace (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)] :
    (hermitianHostGram ℝ p).trace = (p : ℝ) ^ 4 := by
  classical
  simp only [trace, diag_apply, hostGram_apply_self, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, Fintype.card_prod, ZMod.card]
  push_cast
  ring

open Classical in
theorem hostGram_mul_self_of_isSRGWith (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
    (hSRG : (hermitianGraph p).IsSRGWith (p ^ 4) ((p - 1) * (p ^ 2 + 1)) (p - 2)
      (p * (p - 1))) :
    hermitianHostGram ℝ p * hermitianHostGram ℝ p =
      ((p : ℝ) ^ 4 / (((p - 1) * (p ^ 2 + 1) : ℕ) : ℝ)) • hermitianHostGram ℝ p := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  let A := (hermitianGraph p).adjMatrix ℝ
  let J := Matrix.of (fun _ _ : ZMod p × ZMod p × ZMod p × ZMod p => (1 : ℝ))
  have hm : (((p - 1) * (p ^ 2 + 1) : ℕ) : ℝ) =
      ((p : ℝ) - 1) * ((p : ℝ) ^ 2 + 1) := by
    simp only [Nat.cast_mul, Nat.cast_sub hp1, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
  have hcompl : (hermitianGraph p)ᶜ.adjMatrix ℝ = J - 1 - A := by
    apply (eq_sub_iff_add_eq).mpr
    rw [add_comm]
    exact (SimpleGraph.IsCompl.adjMatrix_add_adjMatrix_eq_adjMatrix_completeGraph ℝ
      isCompl_compl).trans (SimpleGraph.adjMatrix_completeGraph_eq_of_one_sub_one ℝ _)
  have hAA : A * A = (((p : ℝ) - 1) * ((p : ℝ) ^ 2 + 1)) •
      (1 : Matrix _ _ ℝ) + ((p : ℝ) - 2) • A +
      ((p : ℝ) * ((p : ℝ) - 1)) • (J - 1 - A) := by
    have h := hSRG.matrix_eq (α := ℝ)
    rw [pow_two, hcompl, ← Nat.cast_smul_eq_nsmul ℝ,
      ← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ] at h
    simpa only [hm, Nat.cast_sub hp1, Nat.cast_sub hp2, Nat.cast_mul, Nat.cast_one,
      Nat.cast_ofNat] using h
  have hAJ : A * J = (((p : ℝ) - 1) * ((p : ℝ) ^ 2 + 1)) • J := by
    ext i j
    simp only [A, SimpleGraph.adjMatrix_mul_apply, J, of_apply, Finset.sum_const,
      Matrix.smul_apply, smul_eq_mul, mul_one, nsmul_eq_mul,
      SimpleGraph.card_neighborFinset_eq_degree,
      hSRG.regular.degree_eq, hm]
  have hJA : J * A = (((p : ℝ) - 1) * ((p : ℝ) ^ 2 + 1)) • J := by
    ext i j
    simp only [A, SimpleGraph.mul_adjMatrix_apply, J, of_apply, Finset.sum_const,
      Matrix.smul_apply, smul_eq_mul, mul_one, nsmul_eq_mul,
      SimpleGraph.card_neighborFinset_eq_degree,
      hSRG.regular.degree_eq, hm]
  have hJJ : J * J = (p : ℝ) ^ 4 • J := by
    ext i j
    simp only [J, mul_apply, of_apply, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, Fintype.card_prod, ZMod.card, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [hm, hostGram_eq_polynomial]
  exact projection_polynomial A J (p : ℝ) hp hAA hAJ hJA hJJ

end ExplicitRIP.HostFrame
