/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.FieldNorm
import ExplicitRIP.Algebra.FieldNorm
import ExplicitRIP.Algebra.AvoidanceLine.Restriction

/-!
# The field norm is a nonvanishing cubic form

Source: [KM, Section 4.2, the claim before (15), and footnote 3].

The power basis of the first monic irreducible cubic identifies `𝔽_p³` with `𝔽_{p³}` as in
[KM, footnote 3]. The field norm is a homogeneous cubic whose only zero is the origin; its
restriction to `c + s v` has cubic coefficient `N(v)`.
-/

public section

theorem ExplicitRIP.Provider.fieldNorm_spec :
    ∀ (p : ℕ) [Fact p.Prime],
      IsField (AdjoinRoot (ExplicitRIP.firstIrreducibleCubic p)) ∧
      (∃ b : Module.Basis (Fin 3) (ZMod p) (AdjoinRoot (ExplicitRIP.firstIrreducibleCubic p)),
        ∀ i : Fin 3, b i = AdjoinRoot.root (ExplicitRIP.firstIrreducibleCubic p) ^ (i : ℕ)) ∧
      (∃ F : MvPolynomial (Fin 3) (ZMod p),
        F.IsHomogeneous 3 ∧
          (∀ w : ZMod p × ZMod p × ZMod p,
            MvPolynomial.eval ![w.1, w.2.1, w.2.2] F = ExplicitRIP.fieldNorm p w) ∧
          ∀ c v : ZMod p × ZMod p × ZMod p,
            (MvPolynomial.aeval ![Polynomial.C c.1 + Polynomial.C v.1 * Polynomial.X,
                Polynomial.C c.2.1 + Polynomial.C v.2.1 * Polynomial.X,
                Polynomial.C c.2.2 + Polynomial.C v.2.2 * Polynomial.X] F).coeff 3 =
              ExplicitRIP.fieldNorm p v) ∧
      ∀ v : ZMod p × ZMod p × ZMod p, v ≠ 0 → ExplicitRIP.fieldNorm p v ≠ 0 := by
  intro p _
  obtain ⟨hf, hb, ⟨F, hF, _, he⟩, _, hn⟩ := ExplicitRIP.FieldNorm.algebra_spec p
  refine ⟨hf, hb, ⟨F, hF, he, ?_⟩, hn⟩
  intro c v
  rw [← he v]
  have hvec :
      (fun i : Fin 3 => Polynomial.C (![c.1, c.2.1, c.2.2] i) +
        Polynomial.C (![v.1, v.2.1, v.2.2] i) * Polynomial.X) =
      ![Polynomial.C c.1 + Polynomial.C v.1 * Polynomial.X,
        Polynomial.C c.2.1 + Polynomial.C v.2.1 * Polynomial.X,
        Polynomial.C c.2.2 + Polynomial.C v.2.2 * Polynomial.X] := by
    funext i
    fin_cases i <;> rfl
  simpa only [ExplicitRIP.Avline.restrictLine, ExplicitRIP.Avline.affinePolynomial,
    MvPolynomial.aeval_eq_eval₂Hom, Polynomial.algebraMap_eq,
    MvPolynomial.coe_eval₂Hom, hvec] using
    ExplicitRIP.Avline.restrictLine_coeff hF ![c.1, c.2.1, c.2.2] ![v.1, v.2.1, v.2.2]
