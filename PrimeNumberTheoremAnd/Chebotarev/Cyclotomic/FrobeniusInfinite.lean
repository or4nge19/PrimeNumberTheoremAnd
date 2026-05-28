import PrimeNumberTheoremAnd.Chebotarev.Cyclotomic.FrobeniusPrimeSet
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
## Cyclotomic case: infinitude of Frobenius prime sets

Sharifi’s cyclotomic base case identifies Frobenius conditions with congruence classes modulo `n`.
Independently of any density statement, this already implies **infinitely many** primes in each
Frobenius class (Dirichlet’s theorem on primes in arithmetic progressions).

This file records that consequence in a mathlib-native way, by reducing directly to
`Nat.infinite_setOf_prime_and_eq_mod`.
-/

namespace PrimeNumberTheoremAnd
namespace Chebotarev
namespace Cyclotomic

open scoped Classical Cyclotomic NumberField
open IsCyclotomicExtension NumberField

section

variable {n : ℕ} [NeZero n]

theorem congrPrimeSet_infinite (a : (ZMod n)ˣ) :
    (congrPrimeSet (n := n) a).Infinite := by
  -- This is exactly Dirichlet's theorem for the unit `a : ZMod n`.
  simpa [congrPrimeSet] using
    (Nat.infinite_setOf_prime_and_eq_mod (q := n) (a := (a : ZMod n)) a.isUnit)

theorem frobPrimeSet_infinite (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {n} ℚ L]
    (σ : Gal(L/ℚ)) :
    (frobPrimeSet (n := n) (L := L) σ).Infinite := by
  -- By definition, this is a congruence class prime set.
  simpa [frobPrimeSet] using
    congrPrimeSet_infinite (n := n) ((zeta_spec n ℚ L).autToPow ℚ σ)

end

end Cyclotomic
end Chebotarev
end PrimeNumberTheoremAnd

