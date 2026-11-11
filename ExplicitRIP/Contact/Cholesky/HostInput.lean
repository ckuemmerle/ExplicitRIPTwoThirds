/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.LexGram
public import ExplicitRIP.Contact.HostFrame.Transport
import ExplicitRIP.HermitianForms.Anchors.HostFrame

/-!
# Rational input for the contact-coordinate Cholesky construction

The host Gram matrix of [KM, proof of Theorem 1], with parameters [KM, (13)], is positive
semidefinite and has rank `(p - 1) * (p ^ 2 + 1)`. The real frame properties are transported from
the Hermitian-forms model. The rational input is used for the factorization in [KM, footnote 4].
-/

public section

open scoped Matrix

namespace ExplicitRIP.Contact.Cholesky

variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

/-- Casting the rational two-distance formula gives the real host Gram. -/
theorem hostGram_map_ratCast :
    (hostGram ℚ p).map (fun q : ℚ => (q : ℝ)) = hostGram ℝ p := by
  classical
  ext i j
  simp only [hostGram, Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.one_apply,
    SimpleGraph.adjMatrix_apply]
  split_ifs <;> push_cast <;> ring

/-- Casting commutes with the fixed lexicographic reindexing. -/
theorem lexGram_map_ratCast :
    (lexGram p).map (fun q : ℚ => (q : ℝ)) =
      (hostGram ℝ p).submatrix (lexEquiv p).symm (lexEquiv p).symm := by
  rw [lexGram, ← Matrix.submatrix_map, hostGram_map_ratCast]

/-- The rational host Gram is positive semidefinite. -/
theorem hostGram_posSemidef_rat : (hostGram ℚ p).PosSemidef := by
  classical
  have hsymm : (hostGram ℚ p).IsHermitian := by
    rw [Matrix.isHermitian_iff_isSymm, hostGram]
    exact (Matrix.isSymm_one.sub ((contactGraph p).isSymm_adjMatrix.smul _)).add
      (((show (Matrix.of (fun _ _ => (1 : ℚ))).IsSymm from rfl).sub
        Matrix.isSymm_one).sub (contactGraph p).isSymm_adjMatrix |>.smul _)
  obtain ⟨B, hB, _⟩ := (Hermitian.hermitian_graph_frame.1 p).2
  have hreal : (hermitianHostGram ℝ p).PosSemidef := by
    rw [← hB, ← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact Matrix.posSemidef_conjTranspose_mul_self B
  have hcontact : (hostGram ℝ p).PosSemidef := by
    rw [Contact.hostGram_eq_submatrix]
    exact hreal.submatrix (Contact.sphereMap p).symm
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hsymm
  intro x
  have hx := hcontact.dotProduct_mulVec_nonneg (fun i => (x i : ℝ))
  rw [← hostGram_map_ratCast p] at hx
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, star_trivial] at hx ⊢
  exact_mod_cast hx

/-- The ordered rational host input satisfies the PSD specification of LDL. -/
theorem lexGram_posSemidef : (lexGram p).PosSemidef :=
  (hostGram_posSemidef_rat p).submatrix (lexEquiv p).symm

end ExplicitRIP.Contact.Cholesky
