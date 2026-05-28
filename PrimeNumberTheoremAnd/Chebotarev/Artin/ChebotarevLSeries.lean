import PrimeNumberTheoremAnd.Chebotarev.Artin.Nat

import Mathlib.NumberTheory.EulerProduct.Basic

/-!
## Chebotarev × Artin: the naive Artin L-series (algebraic expresse)

Defines the naive Artin L-series `LSeries (artinCoeffNat ρ P hP) s` and restates the Euler-product
theorem from `ArtinLSeries`, under an explicit `LSeriesSummable` hypothesis.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical
open scoped LSeries.notation

namespace Chebotarev

open Filter Nat Topology

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G S] [SMulCommClass G R S] [Algebra.IsInvariant R S G]

variable (ρ : ArtinLSeries.ArtinRep G)

/-- The naive Artin L-series attached to Frobenius data `(P, hP)`. -/
noncomputable def artinLSeries (P : Nat.Primes → Ideal R)
    (hP : HasFiniteResidueOverNat (R := R) (S := S) P) (s : ℂ) : ℂ :=
  LSeries (artinCoeffNat (R := R) (S := S) (G := G) ρ P hP) s

theorem artinLSeries_congr (P : Nat.Primes → Ideal R)
    (hP hP' : HasFiniteResidueOverNat (R := R) (S := S) P) (s : ℂ) :
    artinLSeries (R := R) (S := S) (G := G) ρ P hP s =
      artinLSeries (R := R) (S := S) (G := G) ρ P hP' s := by
  simp [artinLSeries, artinCoeffNat_congr (R := R) (S := S) (G := G) (ρ := ρ) (P := P) hP hP']

theorem artinLSeries_eulerProduct_hasProd {P : Nat.Primes → Ideal R}
    {hP : HasFiniteResidueOverNat (R := R) (S := S) P} {s : ℂ}
    (hsum : LSeriesSummable (artinCoeffNat (R := R) (S := S) (G := G) ρ P hP) s) :
    HasProd (fun p : Nat.Primes =>
      ∑' e : ℕ, LSeries.term (artinCoeffNat (R := R) (S := S) (G := G) ρ P hP) s (p.1 ^ e))
      (artinLSeries (R := R) (S := S) (G := G) ρ P hP s) := by
  simpa [artinLSeries] using
    (LSeries_eulerProduct_hasProd (R := R) (S := S) (G := G) (ρ := ρ) (P := P) (hP := hP)
      (s := s) hsum)

theorem artinLSeries_eulerProduct_tprod {P : Nat.Primes → Ideal R}
    {hP : HasFiniteResidueOverNat (R := R) (S := S) P} {s : ℂ}
    (hsum : LSeriesSummable (artinCoeffNat (R := R) (S := S) (G := G) ρ P hP) s) :
    ∏' p : Nat.Primes, ∑' e : ℕ,
        LSeries.term (artinCoeffNat (R := R) (S := S) (G := G) ρ P hP) s (p ^ e) =
      artinLSeries (R := R) (S := S) (G := G) ρ P hP s := by
  simpa [artinLSeries, artinCoeffNat, frobClassOverNat] using
    (ArtinLSeries.LSeries_eulerProduct_tprod (ρ := ρ)
      (c := frobClassOverNat (R := R) (S := S) (G := G) P hP) hsum)

theorem artinLSeries_eulerProduct {P : Nat.Primes → Ideal R}
    {hP : HasFiniteResidueOverNat (R := R) (S := S) P} {s : ℂ}
    (hsum : LSeriesSummable (artinCoeffNat (R := R) (S := S) (G := G) ρ P hP) s) :
    Tendsto (fun n : ℕ => ∏ p ∈ primesBelow n, ∑' e : ℕ,
        LSeries.term (artinCoeffNat (R := R) (S := S) (G := G) ρ P hP) s (p ^ e)) atTop
      (𝓝 (artinLSeries (R := R) (S := S) (G := G) ρ P hP s)) := by
  simpa [artinLSeries, artinCoeffNat, frobClassOverNat] using
    (ArtinLSeries.LSeries_eulerProduct (ρ := ρ)
      (c := frobClassOverNat (R := R) (S := S) (G := G) P hP) hsum)

end

end Chebotarev

end PrimeNumberTheoremAnd
