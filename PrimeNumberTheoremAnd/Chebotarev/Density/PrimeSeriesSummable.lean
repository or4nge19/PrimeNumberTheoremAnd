import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
## Summability of prime power series (Dirichlet-density infrastructure)

This file provides a small analytic lemma used repeatedly in Dirichlet-density arguments:
for real `s > 1`, the prime-indexed series `∑' p, 1 / p^s` (in `ℂ`) is summable.

We state it over `Nat.Primes` since this is the index type used by the Euler product library and
by our prime-indexed rewrites of `DirichletDensity.series` in the Chebotarev development.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical

open Nat.Primes

open Complex

lemma summable_primes_one_div_cpow_of_one_lt_real {s : ℝ} (hs : 1 < s) :
    Summable (fun p : Nat.Primes ↦ (1 : ℂ) / ((p : ℂ) ^ (s : ℂ))) := by
  -- First reduce to the corresponding real `rpow` statement.
  have hs' : (-s : ℝ) < -1 := by linarith
  have hR : Summable (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s)) :=
    (Nat.Primes.summable_rpow (r := (-s : ℝ))).2 hs'
  have hR' : Summable (fun p : Nat.Primes ↦ ((p : ℝ) ^ s)⁻¹) := by
    simpa [Real.rpow_neg] using hR
  -- Identify the norms with `p ^ (-s)` and conclude.
  have hnorm :
      (fun p : Nat.Primes ↦ ‖(1 : ℂ) / ((p : ℂ) ^ (s : ℂ))‖) =
        fun p : Nat.Primes ↦ ((p : ℝ) ^ s)⁻¹ := by
    funext p
    have hsC : (s : ℂ).re ≠ 0 := by
      -- `0 < s` since `1 < s`
      simpa using (ne_of_gt (show 0 < s by linarith))
    -- `‖1 / p^s‖ = (p^s)⁻¹ = p^(-s)`
    calc
      ‖(1 : ℂ) / ((p : ℂ) ^ (s : ℂ))‖
          = ‖((p : ℂ) ^ (s : ℂ))⁻¹‖ := by simp [one_div]
      _ = ‖(p : ℂ) ^ (s : ℂ)‖⁻¹ := by simp
      _ = ((p : ℝ) ^ ((s : ℂ).re))⁻¹ := by
            simp [norm_natCast_cpow_of_re_ne_zero _ hsC]
      _ = ((p : ℝ) ^ s)⁻¹ := by simp
  have : Summable (fun p : Nat.Primes ↦ ‖(1 : ℂ) / ((p : ℂ) ^ (s : ℂ))‖) := by
    simpa [hnorm] using hR'
  exact this.of_norm

end PrimeNumberTheoremAnd
