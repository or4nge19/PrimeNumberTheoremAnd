import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Data.Nat.Prime.Defs

/-!
## Unramified-at-`n` for primes over `(p)`

Sharifi’s cyclotomic step needs the elementary fact:
if a prime ideal `Q` lies over `(p)` and `p ∤ n`, then `n ∉ Q`.

This is a purely ideal-theoretic statement about `ℤ`-algebras, and is used to discharge the
hypothesis `(n : S) ∉ Q` in the Frobenius-on-roots-of-unity lemma.
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev

open scoped Classical

section

variable {S : Type*} [CommRing S] [Algebra ℤ S]

/--
If `Q` lies over `(p)` and `p ∤ n`, then `(n : S) ∉ Q`.

Here `(p)` is `Ideal.span {(p : ℤ)}`.
-/
lemma natCast_not_mem_of_liesOver_span_prime {p n : ℕ} [Fact (Nat.Prime p)]
    (Q : Ideal S) [Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (hn : ¬ p ∣ n) :
    (n : S) ∉ Q := by
  intro hnQ
  have hnQ' : algebraMap ℤ S (n : ℤ) ∈ Q := by
    -- `algebraMap ℤ S (n : ℤ)` is definitional equal to `(n : S)`.
    simpa using hnQ
  have hspan : (n : ℤ) ∈ Ideal.span ({(p : ℤ)} : Set ℤ) := by
    -- transport membership along `LiesOver`.
    exact (Ideal.mem_of_liesOver (A := ℤ) (B := S) (P := Q)
      (p := Ideal.span ({(p : ℤ)} : Set ℤ)) (x := (n : ℤ))).2 hnQ'
  have : (p : ℤ) ∣ (n : ℤ) := by
    -- In `ℤ`, membership in the principal ideal is divisibility.
    simpa [Ideal.mem_span_singleton] using hspan
  exact hn ((Int.natCast_dvd_natCast).1 this)

end

end Chebotarev

end PrimeNumberTheoremAnd

