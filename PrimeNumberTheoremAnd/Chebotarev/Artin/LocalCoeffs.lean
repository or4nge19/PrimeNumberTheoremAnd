import PrimeNumberTheoremAnd.Chebotarev.Artin.Representation
import PrimeNumberTheoremAnd.Chebotarev.Artin.LikeLSeries

import Mathlib.NumberTheory.LSeries.Basic

/-!
## Artin L-series (algebraic layer): local coefficients and global `coeffNat`

Given:
- a group `G`,
- an Artin representation `ρ : G → GL(n, ℂ)`,
- an assignment of conjugacy classes `c(p) : ConjClasses G` to primes `p`,

we define the resulting local prime-power coefficients
\[
  a_p(e) := [X^e] \det(I - X ρ(c(p)))^{-1},
\]
as an `ArtinLike.LocalCoeffs`, and the induced global coefficient function `coeffNat : ℕ → ℂ`.

We also restate the Euler-product theorems from `ArtinLikeLSeries` for this specialization.

This is purely algebraic: no convergence is asserted without an explicit `LSeriesSummable`
hypothesis.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical BigOperators
open scoped LSeries.notation

namespace ArtinLSeries

open Matrix Filter Nat Topology

section

variable {G : Type*} [Group G]
variable (ρ : ArtinLSeries.ArtinRep G)
variable (c : Nat.Primes → ConjClasses G)

namespace ArtinRep

lemma eulerCoeffAt_zero (g : G) : ρ.eulerCoeffAt g 0 = 1 := by
  simp [ArtinRep.eulerCoeffAt, ArtinRep.eulerFactorAt, ArtinLSeries.eulerFactor, ArtinRep.mat]

lemma eulerCoeffClass_zero (C : ConjClasses G) : ρ.eulerCoeffClass 0 C = 1 := by
  refine Quotient.inductionOn C (fun g => ?_)
  simpa [ArtinRep.eulerCoeffClass] using (ρ.eulerCoeffAt_zero (g := g))

/--
Build `ArtinLike.LocalCoeffs` from an Artin representation and a prime-indexed conjugacy-class
assignment.
-/
noncomputable def localCoeffsOfConj (c : Nat.Primes → ConjClasses G) : ArtinLike.LocalCoeffs where
  a p e := ρ.eulerCoeffClass e (c p)
  a_zero p := by
    simpa using (ρ.eulerCoeffClass_zero (C := c p))

end ArtinRep

/-- The local prime-power coefficients coming from `ρ` and `c`. -/
noncomputable def localCoeffs : ArtinLike.LocalCoeffs :=
  ArtinRep.localCoeffsOfConj (ρ := ρ) c

/-- The induced global coefficient function on `ℕ`. -/
noncomputable def coeffNat : ℕ → ℂ :=
  (localCoeffs (ρ := ρ) c).coeff

@[simp] lemma coeffNat_zero : coeffNat (ρ := ρ) c 0 = 0 := by
  simp [coeffNat, localCoeffs, ArtinLike.LocalCoeffs.coeff_zero]

@[simp] lemma coeffNat_one : coeffNat (ρ := ρ) c 1 = 1 := by
  simp [coeffNat, localCoeffs, ArtinLike.LocalCoeffs.coeff_one]

open ArtinLike

/--
Euler product for the naive ℕ-Dirichlet series attached to `ρ` and `c`,
under an explicit `LSeriesSummable` hypothesis.
-/
theorem LSeries_eulerProduct_hasProd {s : ℂ} (hsum : LSeriesSummable (coeffNat (ρ := ρ) c) s) :
    HasProd (fun p : Nat.Primes =>
      ∑' e : ℕ, LSeries.term (coeffNat (ρ := ρ) c) s (p ^ e))
      (LSeries (coeffNat (ρ := ρ) c) s) := by
  simpa [coeffNat, localCoeffs, ArtinLike.term] using
    (ArtinLike.LSeries_eulerProduct_hasProd (A := localCoeffs (ρ := ρ) c) (s := s) hsum)

/-- `tprod` version of `LSeries_eulerProduct_hasProd`. -/
theorem LSeries_eulerProduct_tprod {s : ℂ} (hsum : LSeriesSummable (coeffNat (ρ := ρ) c) s) :
    ∏' p : Nat.Primes, ∑' e : ℕ, LSeries.term (coeffNat (ρ := ρ) c) s (p ^ e) =
      LSeries (coeffNat (ρ := ρ) c) s := by
  simpa [coeffNat, localCoeffs, ArtinLike.term] using
    (ArtinLike.LSeries_eulerProduct_tprod (A := localCoeffs (ρ := ρ) c) (s := s) hsum)

/-- Finite partial-product version of `LSeries_eulerProduct_hasProd`. -/
theorem LSeries_eulerProduct {s : ℂ} (hsum : LSeriesSummable (coeffNat (ρ := ρ) c) s) :
    Tendsto (fun n : ℕ => ∏ p ∈ primesBelow n, ∑' e : ℕ,
        LSeries.term (coeffNat (ρ := ρ) c) s (p ^ e)) atTop
      (𝓝 (LSeries (coeffNat (ρ := ρ) c) s)) := by
  simpa [coeffNat, localCoeffs, ArtinLike.term] using
    (ArtinLike.LSeries_eulerProduct (A := localCoeffs (ρ := ρ) c) (s := s) hsum)

end

end ArtinLSeries

end PrimeNumberTheoremAnd
