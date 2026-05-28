import PrimeNumberTheoremAnd.Chebotarev.Cyclotomic.FrobeniusPrimeSet

/-!
## Cyclotomic case: prime Dirichlet series rewrite (safe, non-rearranging form)

This file provides a direct rewrite of the prime Dirichlet series of `frobPrimeSet σ` using the
coefficient identity from orthogonality, without rearranging infinite sums.

This is the “series-level” formulation needed as input to later analytic arguments; any further
algebraic manipulation (e.g. exchanging the finite character sum with `tsum`) should be done later
under explicit summability hypotheses.
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev
namespace Cyclotomic

open scoped Classical Cyclotomic NumberField

open IsCyclotomicExtension
open PrimeNumberTheoremAnd.DirichletDensity

section

variable {n : ℕ} [NeZero n]
variable [HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod n)ˣ)]

variable (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {n} ℚ L]

/--
Rewrite the prime Dirichlet series of `frobPrimeSet σ` using orthogonality, without rearranging
the resulting infinite sum.
-/
theorem series_frobPrimeSet_eq_LSeries (σ : Gal(L/ℚ)) (s : ℝ) :
    series (frobPrimeSet (n := n) (L := L) σ) s =
      LSeries
        (fun m : ℕ ↦
          ((1 : ℂ) / (n.totient : ℂ)) *
            ∑ χ : DirichletCharacter ℂ n,
              χ ((((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n)⁻¹) *
                primeCoeff (n := n) χ m)
        (s : ℂ) := by
  classical
  let a : (ZMod n)ˣ := (zeta_spec n ℚ L).autToPow ℚ σ
  have hcoeff :
      ∀ {m : ℕ}, m ≠ 0 →
        coeff (frobPrimeSet (n := n) (L := L) σ) m =
          ((1 : ℂ) / (n.totient : ℂ)) *
            ∑ χ : DirichletCharacter ℂ n, χ ((a : ZMod n)⁻¹) * primeCoeff (n := n) χ m := by
    intro m _hm
    simpa [a] using (coeff_frobPrimeSet_eq (n := n) (L := L) (σ := σ) (m := m))
  simpa [series, a] using (LSeries_congr (s := (s : ℂ)) hcoeff)

end

end Cyclotomic
end Chebotarev

end PrimeNumberTheoremAnd
