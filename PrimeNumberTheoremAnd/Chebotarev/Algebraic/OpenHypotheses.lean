import PrimeNumberTheoremAnd.Chebotarev.Algebraic.ReductionStep2RingOfIntegers
import PrimeNumberTheoremAnd.Chebotarev.Algebraic.ReductionStep2Counting
import PrimeNumberTheoremAnd.Chebotarev.Density.DirichletDensityIdeals
import PrimeNumberTheoremAnd.Chebotarev.Density.DirichletDensityIntBridge

/-!
# Open hypotheses (Sharifi Step 2 and ideal density)

Theorems with `sorry` for the remaining proof-tree gaps. Each names a target already
spelled out as a `Prop` elsewhere; once a target is proved, replace the `sorry` with
a proof (or move the theorem to the appropriate file).

For `R = ℤ`, ideal-series summability at `s > 1` is proved: use
`DirichletDensity.IdealSeriesSummable_int` in `DirichletDensityIntSummability.lean`.
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev

section OpenHypotheses

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]
variable (σ : Gal(L/K))
variable [Finite (Gal(L/K))]
variable [IsGalois K L]
variable [IsGalois K ↥(step2FixedField (K := K) (L := L) σ)]

/--
Sharifi Thm 7.2.2 Step 2 (counting): for `p ∈ S_{Cl(σ)}`, the fiber of `T_σ` above `p`
has cardinality `[Gal(L/K) : Z(σ)]`.

See `Step2PrimeCountingHypothesisRO` in `ReductionStep2Counting.lean`.
-/
theorem step2PrimeCountingHypothesisRO :
    Step2PrimeCountingHypothesisRO (K := K) (L := L) σ := by
  sorry

/--
Prime-level Frobenius restriction along `galInclusion` for the `arithFrobAt` classes.

See `Step2FrobRestrictionHypothesisRO` in `ReductionStep2Counting.lean`.
-/
theorem step2FrobRestrictionHypothesisRO :
    Step2FrobRestrictionHypothesisRO (K := K) (L := L) σ := by
  sorry

/--
Ideal-norm Dirichlet series summability at `s > 1` for a general Dedekind domain `R`.

For `R = ℤ` this is proved (`DirichletDensity.IdealSeriesSummable_int`); use that theorem
instead of this one in the `ℤ` case.
-/
theorem idealSeriesSummable_of_one_lt {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] (S : Set (DirichletDensity.PrimeIdeal R)) {s : ℝ}
    (hs : 1 < s) :
    DirichletDensity.IdealSeriesSummable (R := R) S s ∧
      DirichletDensity.IdealSeriesSummable (R := R) (Set.univ : Set (DirichletDensity.PrimeIdeal R)) s := by
  sorry

/--
Ideal-norm Dirichlet density on `PrimeIdeal ℤ` agrees with rational-prime density on the
reindexed set `natPrimeImageOf S`.

See `DirichletDensityIntBridge.lean` for the `(p) ↔ p` infrastructure.
-/
theorem hasIdealDensity_iff_hasDensity_natPrimeImageOf
    (S : Set (DirichletDensity.PrimeIdeal ℤ)) (δ : ℂ) :
    DirichletDensity.HasIdealDensity (R := ℤ) S δ ↔
      DirichletDensity.HasDensity (DirichletDensity.natPrimeImageOf S) δ := by
  sorry

end OpenHypotheses

end Chebotarev

end PrimeNumberTheoremAnd
