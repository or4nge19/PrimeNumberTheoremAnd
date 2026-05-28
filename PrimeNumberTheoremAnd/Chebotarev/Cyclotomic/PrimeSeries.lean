import PrimeNumberTheoremAnd.Chebotarev.Density.DirichletDensity
import PrimeNumberTheoremAnd.Chebotarev.Cyclotomic.Orthogonality
import PrimeNumberTheoremAnd.Chebotarev.Algebraic.EnoughRootsOfUnityComplex
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Data.Complex.Basic

/-!
## Cyclotomic case: prime Dirichlet series decomposition via orthogonality

This file expresses the purely algebraic decomposition of the prime Dirichlet series for a
congruence class modulo `n` into a normalized finite sum over Dirichlet characters.

This is the step in Sharifi’s cyclotomic argument **before** introducing analytic limits:
we rewrite the indicator of a congruence class as a normalized character sum, then sum over primes.

Analytic input (e.g. limits of `log L(s,χ)` as `s → 1⁺`) is not used here.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical
open scoped LSeries.notation

namespace Chebotarev

namespace Cyclotomic

section

variable {n : ℕ} [NeZero n]

open PrimeNumberTheoremAnd.DirichletDensity

/-- The set of natural primes congruent to a given unit `a` modulo `n`. -/
def congrPrimeSet (a : (ZMod n)ˣ) : Set ℕ :=
  {m | m.Prime ∧ (m : ZMod n) = (a : ZMod n)}

/-- Prime-filtered coefficient attached to a Dirichlet character. -/
noncomputable def primeCoeff (χ : DirichletCharacter ℂ n) : ℕ → ℂ :=
  fun m => if m.Prime then χ m else 0

lemma coeff_congrPrimeSet_eq (a : (ZMod n)ˣ) (m : ℕ) :
    coeff (congrPrimeSet (n := n) a) m =
      ((1 : ℂ) / (n.totient : ℂ)) *
        ∑ χ : DirichletCharacter ℂ n,
          χ ((a : ZMod n)⁻¹) * primeCoeff (n := n) χ m := by
  by_cases hm : m.Prime
  · have ha : IsUnit (a : ZMod n) := (a : (ZMod n)ˣ).isUnit
    have hcoeff :
        coeff (congrPrimeSet (n := n) a) m =
          (if (m : ZMod n) = (a : ZMod n) then (1 : ℂ) else 0) := by
      rw [DirichletDensity.coeff_apply]
      simp [congrPrimeSet, hm]
    have hind :
        (if (m : ZMod n) = (a : ZMod n) then (1 : ℂ) else 0) =
          ((1 : ℂ) / (n.totient : ℂ)) *
            ∑ χ : DirichletCharacter ℂ n, χ ((a : ZMod n)⁻¹) * χ (m : ZMod n) := by
      have := Dirichlet.sum_char_inv_mul_char_eq_indicator (n := n) (a := (a : ZMod n)) ha (m : ZMod n)
      simpa [div_eq_mul_inv, eq_comm, one_div, mul_assoc, mul_left_comm, mul_comm] using this.symm
    calc
      coeff (congrPrimeSet (n := n) a) m
          = (if (m : ZMod n) = (a : ZMod n) then 1 else 0) := hcoeff
      _ = ((1 : ℂ) / (n.totient : ℂ)) *
            ∑ χ : DirichletCharacter ℂ n, χ ((a : ZMod n)⁻¹) * χ (m : ZMod n) := hind
      _ = ((1 : ℂ) / (n.totient : ℂ)) *
            ∑ χ : DirichletCharacter ℂ n,
              χ ((a : ZMod n)⁻¹) * primeCoeff (n := n) χ m := by
            simp [primeCoeff, hm, mul_comm]
  · rw [coeff_of_not_prime (congrPrimeSet (n := n) a) hm]
    simp only [primeCoeff, hm, ↓reduceIte, Finset.sum_const_zero, mul_zero]

end

end Cyclotomic

end Chebotarev

end PrimeNumberTheoremAnd
