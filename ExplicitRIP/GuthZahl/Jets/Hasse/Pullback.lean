/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Jets.Hasse.Translation

/-!
# Pullback of integer jet equations

Substitution gives the degree bound, and evaluation commutes with the substitution.
-/

public section

namespace ExplicitRIP.GuthZahl

namespace Hasse

/-- Pullback along the finite jet commutes with evaluation and multiplies the degree bound by at
most the surface degree. -/
theorem _root_.ExplicitRIP.GuthZahl.jetPullback_spec {K : Type*} [Field K] (r : ℕ) (f : Poly K)
    (q : MvPolynomial (JetIndex r) ℤ) :
    (jetPullback r f q).totalDegree ≤ q.totalDegree * f.totalDegree ∧
      ∀ x, MvPolynomial.eval x (jetPullback r f q) =
        MvPolynomial.eval₂ (Int.castRingHom K) (finiteJet r f x) q := by
  constructor
  · unfold jetPullback
    rw [show Int.castRingHom (Poly K) =
      MvPolynomial.C.comp (Int.castRingHom K) from Subsingleton.elim _ _]
    exact totalDegree_eval₂_le (Int.castRingHom K)
      (fun a => hasseCoefficient f (jetExponent a)) q f.totalDegree
      (fun a => hasseCoefficient_totalDegree_le f (jetExponent a))
  · intro x
    rw [jetPullback, MvPolynomial.map_eval₂Hom]
    rw [show (MvPolynomial.eval x).comp (Int.castRingHom (Poly K)) =
      Int.castRingHom K from Subsingleton.elim _ _]
    rfl

end Hasse

end ExplicitRIP.GuthZahl

end
