import PrimeNumberTheoremAnd.Chebotarev.Density.DirichletDensity
import PrimeNumberTheoremAnd.Chebotarev.Cyclotomic.FrobeniusPrimeSet
import PrimeNumberTheoremAnd.Chebotarev.Algebraic.EnoughRootsOfUnityComplex

/-!
## Cyclotomic case: Dirichlet-density ratio for Frobenius prime sets (algebraic rewrite)

This file rewrites the Dirichlet-density ratio for the cyclotomic Frobenius prime set
`frobPrimeSet σ` as a ratio of `LSeries` whose coefficients are given by a normalized sum over
Dirichlet characters.

Importantly, we do **not** rearrange infinite sums here; later analytic arguments can do further
manipulations under explicit summability hypotheses.
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev
namespace Cyclotomic

open scoped Classical Cyclotomic NumberField

open IsCyclotomicExtension
open PrimeNumberTheoremAnd.DirichletDensity

section

variable {n : ℕ} [NeZero n]

variable (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {n} ℚ L]

/--
Algebraic rewrite of the Dirichlet-density ratio for `frobPrimeSet σ`.

This is a direct consequence of the coefficient identity `coeff_frobPrimeSet_eq`, together with
`LSeries_congr` (congruence away from `0`).
-/
theorem ratio_frobPrimeSet_eq (σ : Gal(L/ℚ)) {s : ℝ} (hs : 1 < s) :
    ratioDefault (frobPrimeSet (n := n) (L := L) σ) s =
      LSeries
        (fun m : ℕ ↦
          ((1 : ℂ) / (n.totient : ℂ)) *
            ∑ χ : DirichletCharacter ℂ n,
              χ ((((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n)⁻¹) *
                primeCoeff (n := n) χ m)
        (s : ℂ) / seriesAll s := by
  classical
  rw [ratioDefault_of_one_lt _ hs]
  -- unfold `series` / `seriesAll`
  simp only [series, seriesAll]
  -- rewrite `series (frobPrimeSet σ)` via the coefficient identity
  let a : (ZMod n)ˣ := (zeta_spec n ℚ L).autToPow ℚ σ
  have hcoeff :
      ∀ {m : ℕ}, m ≠ 0 →
        coeff (frobPrimeSet (n := n) (L := L) σ) m =
          ((1 : ℂ) / (n.totient : ℂ)) *
            ∑ χ : DirichletCharacter ℂ n,
              χ ((((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n)⁻¹) *
                primeCoeff (n := n) χ m := by
    intro m _hm
    simpa [a] using (coeff_frobPrimeSet_eq (n := n) (L := L) (σ := σ) (m := m))
  -- apply congruence of `LSeries`
  simpa using (congrArg (fun z : ℂ ↦ z / series (S := (Set.univ : Set ℕ)) s)
    (LSeries_congr (s := (s : ℂ)) hcoeff))

end

end Cyclotomic
end Chebotarev

end PrimeNumberTheoremAnd

