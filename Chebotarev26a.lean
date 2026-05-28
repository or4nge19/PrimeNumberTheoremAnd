import PrimeNumberTheoremAnd.Chebotarev.Density.DirichletDensity
import PrimeNumberTheoremAnd.Chebotarev.Density.DirichletDensityIdeals
import PrimeNumberTheoremAnd.Chebotarev.Density.DirichletDensityIntBridge
import PrimeNumberTheoremAnd.Chebotarev.Density.DirichletDensityIntSummability
import PrimeNumberTheoremAnd.Chebotarev.Density.DirichletDensityLimitCriterion
import PrimeNumberTheoremAnd.Chebotarev.Density.SeriesAllDivergesNearOne
import PrimeNumberTheoremAnd.Chebotarev.Cyclotomic.FrobeniusDensity
import PrimeNumberTheoremAnd.Chebotarev.Algebraic.OpenHypotheses
import PrimeNumberTheoremAnd.Chebotarev.Algebraic.ReductionStep2Counting
import PrimeNumberTheoremAnd.Chebotarev.Algebraic.FrobeniusRestriction
import PrimeNumberTheoremAnd.Chebotarev.Algebraic.FixedFieldCyclic
import PrimeNumberTheoremAnd.Chebotarev.Algebraic.ChebotarevPrimeIdeals

/-!
# Chebotarev density (Sharifi Ch. 7)

Library root: `lake build Chebotarev`.

## Module map

| File | Content |
|------|---------|
| `DirichletDensity.lean` | `HasDensity`, `ratioAt`, `coeff` API for sets of rational primes |
| `DirichletDensityIdeals.lean` | `HasIdealDensity` for sets of prime ideals |
| `DirichletDensityIntBridge.lean` | `(p) ↔ p`, `natPrimeImageOf`, `primeIdealOptionEquiv` |
| `DirichletDensityIntSummability.lean` | `IdealSeriesSummable_int` |
| `DirichletDensityLimitCriterion.lean` | limit criterion for `HasDensity` |
| `SeriesAllDivergesNearOne.lean` | full prime series diverges as `s → 1⁺` |
| `Cyclotomic/FrobeniusDensity.lean` | cyclotomic Frobenius density |
| `Algebraic/ReductionStep2*.lean` | Step 2 field/counting scaffolding |
| `Algebraic/OpenHypotheses.lean` | open targets (`sorry`) |

## Proof status (summary)

**Proved:** cyclotomic Frobenius density; `HasDensity` infrastructure; Step 2 guardrails
(`step2FrobClassInGalLK_eq`, tower splitting, orbit–stabilizer, residue cardinality);
`IdealSeriesSummable` for `R = ℤ` at `s > 1`.

**Open (`sorry` in `OpenHypotheses.lean`):** Step 2 fiber counting; Frobenius restriction
along `galInclusion`; general ideal-series summability (`idealSeriesSummable_of_one_lt`);
`HasIdealDensity S δ ↔ HasDensity (natPrimeImageOf S) δ`.

**Open (not yet stated):** `frobPrimeSet σ` vs `chebotarevPrimeIdealSet`; Artin L-series input.
-/

namespace Chebotarev

open scoped Classical

section ProofStatus

open PrimeNumberTheoremAnd.DirichletDensity
open PrimeNumberTheoremAnd.Chebotarev

/-- Cyclotomic Frobenius set has Dirichlet density `1/φ(n)`. -/
theorem cyclotomic_frobPrimeSet_hasDensity
    {n : ℕ} [NeZero n]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {n} ℚ L]
    (σ : Gal(L/ℚ)) :
    HasDensity (PrimeNumberTheoremAnd.Chebotarev.Cyclotomic.frobPrimeSet (n := n) (L := L) σ)
      ((1 : ℂ) / (n.totient : ℂ)) :=
  PrimeNumberTheoremAnd.Chebotarev.Cyclotomic.hasDensity_frobPrimeSet (n := n) (L := L) σ

/-- Abstract Step 2 class identification in `Gal(L/K)`. -/
theorem step2_frobClassInGalLK_eq (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (σ : Gal(L/K)) :
    step2FrobClassInGalLK (K := K) (L := L) σ = ConjClasses.mk σ :=
  step2FrobClassInGalLK_eq (K := K) (L := L) σ

/-- Ideal-norm Dirichlet series summability for `R = ℤ` at `s > 1`. -/
theorem idealSeriesSummable_int {S : Set (PrimeIdeal ℤ)} {s : ℝ} (hs : 1 < s) :
    IdealSeriesSummable (R := ℤ) S s :=
  PrimeNumberTheoremAnd.DirichletDensity.IdealSeriesSummable_int (S := S) hs

end ProofStatus

end Chebotarev
