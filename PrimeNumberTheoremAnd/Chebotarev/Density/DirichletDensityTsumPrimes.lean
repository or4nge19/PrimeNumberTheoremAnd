import PrimeNumberTheoremAnd.Chebotarev.Density.DirichletDensity
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
## Dirichlet-density prime series as a `tsum` over primes

For a set of primes `S : Set ℕ`, our Dirichlet-density development uses the prime Dirichlet series
`series S s = LSeries (coeff S) (s : ℂ)`.

This file provides a small algebraic bridge: for `s > 1`, this series can be written as a `tsum`
indexed by `Nat.Primes`. This matches how Euler products and logarithmic manipulations in mathlib
are naturally organized.

No analytic estimates are used here.
-/

namespace PrimeNumberTheoremAnd

namespace DirichletDensity

open scoped Classical
open scoped LSeries.notation

open LSeries

section

variable (S : Set ℕ)

lemma support_term_coeff_subset_isPrimePow (s : ℂ) :
    Function.support (LSeries.term (coeff S) s) ⊆ {m : ℕ | IsPrimePow m} := by
  intro m hm
  have hm0 : m ≠ 0 := by
    intro h
    subst h
    simp [LSeries.term] at hm
  have hprime : m.Prime := by
    by_contra hprime
    have : coeff S m = 0 := by simp [coeff, hprime]
    have : LSeries.term (coeff S) s m = 0 := by simp [LSeries.term, hm0, this]
    exact hm (by simpa [Function.mem_support] using this)
  exact hprime.isPrimePow

open Nat.Primes in
theorem series_eq_tsum_primes {s : ℝ} (hs : 1 < s) :
    series (S := S) s = ∑' p : Nat.Primes, LSeries.term (coeff S) (s : ℂ) p := by
  have hsum : Summable (LSeries.term (coeff S) (s : ℂ)) :=
    (summable_series (S := S) hs)
  have hsupport := support_term_coeff_subset_isPrimePow (S := S) (s := (s : ℂ))
  have hdecomp :=
    (tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers
      (f := LSeries.term (coeff S) (s : ℂ)) hsum hsupport)
  have hpow_zero :
      (∑' (p : Nat.Primes) (k : ℕ), LSeries.term (coeff S) (s : ℂ) (p ^ (k + 2))) = 0 := by
    have h0 : ∀ (p : Nat.Primes) (k : ℕ), LSeries.term (coeff S) (s : ℂ) (p ^ (k + 2)) = 0 := by
      intro p k
      have hnp : ¬ (p.1 ^ (k + 2)).Prime := by
        have : (2 : ℕ) ≤ k + 2 := Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k))
        exact Nat.Prime.not_prime_pow (x := p.1) (n := k + 2) this
      have hn0 : (p.1 ^ (k + 2)) ≠ 0 := pow_ne_zero _ p.2.ne_zero
      simp [LSeries.term, coeff, hnp]
    simp [h0]
  simpa [series, LSeries, hpow_zero, add_zero] using hdecomp

open Nat.Primes in
theorem seriesAll_eq_tsum_primes {s : ℝ} (hs : 1 < s) :
    seriesAll s =
      ∑' p : Nat.Primes, (1 : ℂ) / ((p : ℂ) ^ (s : ℂ)) := by
  have h := (series_eq_tsum_primes (S := (Set.univ : Set ℕ)) hs)
  refine h.trans ?_
  refine tsum_congr (fun p ↦ ?_)
  have hp0 : (p.1 : ℕ) ≠ 0 := p.2.ne_zero
  simp [LSeries.term, coeff, p.2, hp0, div_eq_mul_inv]

end

end DirichletDensity

end PrimeNumberTheoremAnd
