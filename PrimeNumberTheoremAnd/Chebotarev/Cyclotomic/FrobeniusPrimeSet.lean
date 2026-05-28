import PrimeNumberTheoremAnd.Chebotarev.Cyclotomic.PrimeSeries
import PrimeNumberTheoremAnd.Chebotarev.Algebraic.EnoughRootsOfUnityComplex
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.Gal

/-!
## Cyclotomic case: the Frobenius prime set as a congruence class

In Sharifi’s cyclotomic base case, for `p ∤ n` the condition `arithFrobAt(Q) = σ` is equivalent to
a congruence condition `p ≡ a(σ) (mod n)`, where `a(σ)` is the exponent by which `σ` acts on `ζₙ`.

This file expresses that equivalence as an explicit set of primes and immediately rewrites its
Dirichlet-density coefficients as a normalized Dirichlet-character sum (purely algebraic; no limits).
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev
namespace Cyclotomic

open scoped Classical Cyclotomic NumberField

open IsCyclotomicExtension NumberField

open PrimeNumberTheoremAnd.DirichletDensity

section

variable {n : ℕ} [NeZero n]

variable (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {n} ℚ L]

/-- The “cyclotomic Frobenius prime set” attached to `σ`: primes congruent to `autToPow σ` mod `n`. -/
def frobPrimeSet (σ : Gal(L/ℚ)) : Set ℕ :=
  congrPrimeSet (n := n) ((zeta_spec n ℚ L).autToPow ℚ σ)

/-- Dirichlet-density coefficients of the Frobenius prime set as a normalized character sum. -/
lemma coeff_frobPrimeSet_eq (σ : Gal(L/ℚ)) (m : ℕ) :
    coeff (frobPrimeSet (n := n) (L := L) σ) m =
      ((1 : ℂ) / (n.totient : ℂ)) *
        ∑ χ : DirichletCharacter ℂ n,
          χ ((((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n)⁻¹) *
            primeCoeff (n := n) χ m := by
  simpa [frobPrimeSet] using
    (coeff_congrPrimeSet_eq (n := n)
      (a := ((zeta_spec n ℚ L).autToPow ℚ σ)) m)

/-!
### Prime specialization
-/

lemma coeff_frobPrimeSet_eq_prime (σ : Gal(L/ℚ)) {p : ℕ} (hp : p.Prime) :
    coeff (frobPrimeSet (n := n) (L := L) σ) p =
      ((1 : ℂ) / (n.totient : ℂ)) *
        ∑ χ : DirichletCharacter ℂ n,
          χ ((((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n)⁻¹) *
            χ (p : ZMod n) := by
  rw [coeff_frobPrimeSet_eq (n := n) (L := L) (σ := σ)]
  simp only [primeCoeff, hp, ↓reduceIte]

end

end Cyclotomic
end Chebotarev

end PrimeNumberTheoremAnd
