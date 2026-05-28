import Mathlib.NumberTheory.Cyclotomic.Gal

/-!
## Cyclotomic extensions are abelian (algebraic interface)

Sharifi’s cyclotomic base case uses that `Gal(K(ζₙ)/K)` is abelian.

Mathlib identifies `Gal(K(ζₙ)/K)` with a subgroup of `(ZMod n)ˣ`, and under irreducibility of the
cyclotomic polynomial it gives an isomorphism
`IsCyclotomicExtension.autEquivPow : Gal(L/K) ≃* (ZMod n)ˣ`.

We record the commutativity of `Gal(L/K)` as an explicit lemma, avoiding any global instance
changes.
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev

open scoped Classical Cyclotomic

open Polynomial IsCyclotomicExtension

section

theorem cyclotomic_gal_mul_comm {n : ℕ} [NeZero n]
    (K : Type*) [Field K]
    (L : Type*) [Field L] [Algebra K L] [IsCyclotomicExtension {n} K L]
    (h : Irreducible (cyclotomic n K)) (σ τ : Gal(L/K)) : σ * τ = τ * σ := by
  -- Transport commutativity along the group isomorphism to `(ZMod n)ˣ`.
  let e : Gal(L/K) ≃* (ZMod n)ˣ := IsCyclotomicExtension.autEquivPow (n := n) (K := K) L h
  apply e.injective
  -- In the target, multiplication is commutative.
  simp [e, mul_comm]

end

end Chebotarev

end PrimeNumberTheoremAnd

