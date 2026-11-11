/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Defs

/-!
# Nonempty principal opens in irreducible hypersurfaces

The strong Nullstellensatz identifies vanishing on an irreducible hypersurface with
divisibility by its defining polynomial.
-/

public section

namespace ExplicitRIP.GuthZahl

theorem dvd_of_vanishes_on_irreducible {K : Type*} [Field K] [IsAlgClosed K]
    (f g : Poly K) (hf : Irreducible f)
    (h : ∀ x : Point K, MvPolynomial.eval x f = 0 → MvPolynomial.eval x g = 0) :
    f ∣ g := by
  let I : Ideal (Poly K) := Ideal.span {f}
  have : I.IsPrime := Ideal.isPrime_span_singleton_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hf)
  apply Ideal.mem_span_singleton.mp
  change g ∈ I
  rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := K) I]
  intro x hx
  apply h x
  exact hx f (Ideal.mem_span_singleton_self f)

theorem principalOpen_nonempty {K : Type*} [Field K] [IsAlgClosed K]
    (f g : Poly K) (hf : Irreducible f) (hfg : ¬ f ∣ g) :
    (principalOpen f g).Nonempty := by
  classical
  by_contra h
  apply hfg
  apply dvd_of_vanishes_on_irreducible f g hf
  intro x hx
  by_contra hg
  exact h ⟨x, hx, hg⟩

end ExplicitRIP.GuthZahl

end
