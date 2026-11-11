/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.FieldNorm
import ExplicitRIP.Frozen.FirstIrreducibleCubicSpec
import ExplicitRIP.Algebra.NormForm

/-!
# The field norm is a nonvanishing cubic form

The power basis of the first monic irreducible cubic identifies the field norm with a
homogeneous cubic whose only zero is the origin.

The statement also records scaling and the total degree for algebraic restrictions.
-/

public section

theorem ExplicitRIP.FieldNorm.algebra_spec :
    ∀ (p : ℕ) [Fact p.Prime],
      IsField (AdjoinRoot (ExplicitRIP.firstIrreducibleCubic p)) ∧
      (∃ b : Module.Basis (Fin 3) (ZMod p) (AdjoinRoot (ExplicitRIP.firstIrreducibleCubic p)),
        ∀ i : Fin 3, b i = AdjoinRoot.root (ExplicitRIP.firstIrreducibleCubic p) ^ (i : ℕ)) ∧
      (∃ F : MvPolynomial (Fin 3) (ZMod p),
        F.IsHomogeneous 3 ∧ F.totalDegree = 3 ∧
          ∀ w : ZMod p × ZMod p × ZMod p,
            MvPolynomial.eval ![w.1, w.2.1, w.2.2] F = ExplicitRIP.fieldNorm p w) ∧
      (∀ (c : ZMod p) (w : ZMod p × ZMod p × ZMod p),
        ExplicitRIP.fieldNorm p (c • w) = c ^ 3 * ExplicitRIP.fieldNorm p w) ∧
      ∀ w : ZMod p × ZMod p × ZMod p, w ≠ 0 → ExplicitRIP.fieldNorm p w ≠ 0 :=
by
  intro p hp
  obtain ⟨c₂, c₁, c₀, hf, hi, _⟩ := ExplicitRIP.firstIrreducibleCubic_spec p
  have hf' : ExplicitRIP.firstIrreducibleCubic p =
      Polynomial.C (1 : ZMod p) * Polynomial.X ^ 3 + Polynomial.C c₂ * Polynomial.X ^ 2 +
        Polynomial.C c₁ * Polynomial.X + Polynomial.C c₀ := by
    simpa only [Polynomial.C_1, one_mul] using hf
  have hm : (ExplicitRIP.firstIrreducibleCubic p).Monic := by
    rw [hf']
    exact Polynomial.leadingCoeff_cubic one_ne_zero
  have hd : (ExplicitRIP.firstIrreducibleCubic p).natDegree = 3 := by
    rw [hf']
    exact Polynomial.natDegree_cubic one_ne_zero
  simpa only [ExplicitRIP.fieldNorm, ExplicitRIP.NormForm.value] using
    ExplicitRIP.NormForm.cubic_norm_spec (ExplicitRIP.firstIrreducibleCubic p) hm hi hd
