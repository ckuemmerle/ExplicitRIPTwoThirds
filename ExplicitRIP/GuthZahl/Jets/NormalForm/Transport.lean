/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Jets.Defs
import ExplicitRIP.GuthZahl.Jets.Hasse

/-!
# Transport between finite jets and polynomial conditions

Restriction coefficients identify the two-direction condition with its finite-jet
version. Evaluation of a jet pullback preserves the Boolean zero pattern.
-/

public section

namespace ExplicitRIP.GuthZahl.Jets.NormalForm

theorem two_tangent_directions_iff_jet {K : Type*} [Field K]
    (r : ℕ) (f : Poly K) (x : Point K) :
    TwoTangentDirections f x r ↔ JetTwoDirections (finiteJet r f x) := by
  have ht (v : Point K) : TangentToOrder f x v r ↔
      ∀ j ≤ r, jetDirectionCoefficient (finiteJet r f x) v j = 0 := by
    unfold TangentToOrder
    apply forall_congr'
    intro j
    apply forall_congr'
    intro hj
    rw [restriction_coeff_from_jet r f x v j hj]
  simp only [TwoTangentDirections, JetTwoDirections, ht]

theorem zeroPattern_jetPullback {K : Type*} [Field K] {J : ℕ}
    (r : ℕ) (f : Poly K) (q : Fin J → MvPolynomial (JetIndex r) ℤ)
    (x : Point K) :
    zeroPattern (fun j => jetPullback r f (q j)) x =
      integerZeroPattern q (finiteJet r f x) := by
  classical
  funext j
  change decide (MvPolynomial.eval x (jetPullback r f (q j)) = 0) =
    decide (MvPolynomial.eval₂ (Int.castRingHom K) (finiteJet r f x) (q j) = 0)
  rw [(jetPullback_spec r f (q j)).2 x]

end ExplicitRIP.GuthZahl.Jets.NormalForm

end
