import PrimeNumberTheoremAnd.Chebotarev.Algebraic.Frobenius
import PrimeNumberTheoremAnd.Chebotarev.Artin.LocalCoeffs

import Mathlib.NumberTheory.LSeries.Basic

/-!
## Chebotarev × Artin: ℕ-Dirichlet coefficients from Frobenius classes

Composes `Chebotarev.frobClassOverNat` with `ArtinLSeries.coeffNat`. The Euler-product
theorems are imported from `ArtinLSeries` / `ArtinLike`; this file only records the Chebotarev
specialization.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical
open scoped LSeries.notation

namespace Chebotarev

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G S] [SMulCommClass G R S] [Algebra.IsInvariant R S G]

variable (ρ : ArtinLSeries.ArtinRep G)

/-- Global `ℕ`-coefficients for an Artin representation and Frobenius data at each rational prime. -/
noncomputable def artinCoeffNat (P : Nat.Primes → Ideal R)
    (hP : HasFiniteResidueOverNat (R := R) (S := S) P) : ℕ → ℂ :=
  ArtinLSeries.coeffNat (ρ := ρ) (frobClassOverNat (R := R) (S := S) (G := G) P hP)

theorem artinCoeffNat_congr (P : Nat.Primes → Ideal R)
    (hP hP' : HasFiniteResidueOverNat (R := R) (S := S) P) :
    artinCoeffNat (R := R) (S := S) (G := G) ρ P hP =
      artinCoeffNat (R := R) (S := S) (G := G) ρ P hP' := by
  simp [artinCoeffNat]

theorem LSeries_eulerProduct_hasProd {P : Nat.Primes → Ideal R}
    {hP : HasFiniteResidueOverNat (R := R) (S := S) P}
    {s : ℂ} (hsum : LSeriesSummable (artinCoeffNat (R := R) (S := S) (G := G) ρ P hP) s) :
    HasProd (fun p : Nat.Primes =>
      ∑' e : ℕ, LSeries.term (artinCoeffNat (R := R) (S := S) (G := G) ρ P hP) s (p.1 ^ e))
      (LSeries (artinCoeffNat (R := R) (S := S) (G := G) ρ P hP) s) := by
  simpa [artinCoeffNat] using
    (ArtinLSeries.LSeries_eulerProduct_hasProd (ρ := ρ)
      (c := frobClassOverNat (R := R) (S := S) (G := G) P hP) hsum)

theorem LSeries_eulerProduct_hasProd_congr (P : Nat.Primes → Ideal R)
    (hP hP' : HasFiniteResidueOverNat (R := R) (S := S) P) {s : ℂ}
    (hsum : LSeriesSummable (artinCoeffNat (R := R) (S := S) (G := G) ρ P hP) s) :
    HasProd (fun p : Nat.Primes =>
      ∑' e : ℕ, LSeries.term (artinCoeffNat (R := R) (S := S) (G := G) ρ P hP') s (p.1 ^ e))
      (LSeries (artinCoeffNat (R := R) (S := S) (G := G) ρ P hP') s) := by
  have hsum' :
      LSeriesSummable (artinCoeffNat (R := R) (S := S) (G := G) ρ P hP') s := by
    simpa [artinCoeffNat_congr (R := R) (S := S) (G := G) (ρ := ρ) (P := P) hP hP'] using hsum
  simpa using (LSeries_eulerProduct_hasProd (R := R) (S := S) (G := G) (ρ := ρ) (P := P)
    (hP := hP') (s := s) hsum')

end

end Chebotarev

end PrimeNumberTheoremAnd
