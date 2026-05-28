import PrimeNumberTheoremAnd.Chebotarev.Artin.RepresentationSum
import PrimeNumberTheoremAnd.Chebotarev.Artin.LocalCoeffs

/-!
## Artin local coefficients: direct sums

For a fixed conjugacy-class assignment `c(p)`, the local coefficient system attached to the direct
sum representation `ρ₁ ⊕ ρ₂` is the pointwise Cauchy product of the local coefficient systems
attached to `ρ₁` and `ρ₂`.

This is purely algebraic: it is the statement that Euler factors multiply under direct sums.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical BigOperators

namespace ArtinLSeries

namespace ArtinRep

variable {G : Type*} [Group G]

variable (ρ₁ ρ₂ : ArtinLSeries.ArtinRep G)
variable (c : Nat.Primes → ConjClasses G)

/--
Local coefficients for the direct sum representation are the product of local coefficients.
-/
theorem localCoeffsOfConj_sum :
    ArtinRep.localCoeffsOfConj (ρ := ArtinRep.sum (ρ₁ := ρ₁) (ρ₂ := ρ₂)) c
      =
    PrimeNumberTheoremAnd.ArtinLike.LocalCoeffs.mul
      (ArtinRep.localCoeffsOfConj (ρ := ρ₁) c)
      (ArtinRep.localCoeffsOfConj (ρ := ρ₂) c) := by
  classical
  -- Two `LocalCoeffs` are equal if their `a` agree.
  ext p e
  simp only [PrimeNumberTheoremAnd.ArtinLike.LocalCoeffs.mul, ArtinRep.localCoeffsOfConj]
  refine Quotient.inductionOn (c p) (fun g => ?_)
  simpa [ArtinRep.eulerCoeffClass, ArtinRep.eulerCoeffAt, ArtinRep.eulerFactorAt, ArtinLSeries.eulerCoeff] using
    (ArtinLSeries.eulerCoeff_fromBlocks (m := ρ₁.n) (n := ρ₂.n) (A := ρ₁.mat g) (D := ρ₂.mat g) e)

end ArtinRep

end ArtinLSeries

end PrimeNumberTheoremAnd
