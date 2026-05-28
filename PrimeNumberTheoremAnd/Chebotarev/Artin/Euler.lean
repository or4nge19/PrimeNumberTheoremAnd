import PrimeNumberTheoremAnd.Chebotarev.Algebraic.Frobenius
import PrimeNumberTheoremAnd.Chebotarev.Artin.Representation
import PrimeNumberTheoremAnd.Chebotarev.Artin.LocalCoeffs

/-!
## Chebotarev × Artin (algebraic layer): Euler factors from Frobenius classes

This file connects two algebraic prerequisites:

- `PrimeNumberTheoremAnd.Chebotarev.frobClass` / `frobClassOver`: Frobenius conjugacy classes, and
- `PrimeNumberTheoremAnd.ArtinLSeries.ArtinRep.eulerFactorClass`: Euler factors depending only on
  conjugacy class for an Artin representation.

As a result, given an Artin representation `ρ : G → GL(n, ℂ)`, we can attach a formal Euler factor
in `ℂ⟦X⟧` to a prime ideal `Q` (or to a base prime `P` via `frobClassOver`), purely algebraically.

No analytic input is used.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical

namespace Chebotarev

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G S] [SMulCommClass G R S] [Algebra.IsInvariant R S G]

variable (ρ : ArtinLSeries.ArtinRep G)

/-- The Artin Euler factor attached to a prime ideal `Q` via its Frobenius conjugacy class. -/
noncomputable def artinEulerFactor (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] : PowerSeries ℂ :=
  (PrimeNumberTheoremAnd.ArtinLSeries.ArtinRep.eulerFactorClass (ρ := ρ))
    (PrimeNumberTheoremAnd.Chebotarev.frobClass (R := R) (G := G) (Q := Q))

/-- The `e`-th coefficient of the Artin Euler factor at `Q`. -/
noncomputable def artinEulerCoeff (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] (e : ℕ) : ℂ :=
  (PrimeNumberTheoremAnd.ArtinLSeries.ArtinRep.eulerCoeffClass (ρ := ρ) e)
    (PrimeNumberTheoremAnd.Chebotarev.frobClass (R := R) (G := G) (Q := Q))

theorem artinEulerFactor_eq_of_under_eq (Q Q' : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    [Q'.IsPrime] [Finite (S ⧸ Q')] (h : Q.under R = Q'.under R) :
    artinEulerFactor (R := R) (S := S) (G := G) ρ Q =
      artinEulerFactor (R := R) (S := S) (G := G) ρ Q' := by
  -- The Euler factor only depends on the Frobenius conjugacy class, and `frobClass` is
  -- independent of the choice of prime over the same base prime.
  classical
  simpa [artinEulerFactor] using
    congrArg (PrimeNumberTheoremAnd.ArtinLSeries.ArtinRep.eulerFactorClass (ρ := ρ))
      (PrimeNumberTheoremAnd.Chebotarev.frobClass_eq_of_under_eq
        (R := R) (S := S) (G := G) (Q := Q) (Q' := Q') h)

theorem artinEulerCoeff_eq_of_under_eq (Q Q' : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    [Q'.IsPrime] [Finite (S ⧸ Q')] (e : ℕ) (h : Q.under R = Q'.under R) :
    artinEulerCoeff (R := R) (S := S) (G := G) ρ Q e =
      artinEulerCoeff (R := R) (S := S) (G := G) ρ Q' e := by
  classical
  simpa [artinEulerCoeff] using
    congrArg (PrimeNumberTheoremAnd.ArtinLSeries.ArtinRep.eulerCoeffClass (ρ := ρ) e)
      (PrimeNumberTheoremAnd.Chebotarev.frobClass_eq_of_under_eq
        (R := R) (S := S) (G := G) (Q := Q) (Q' := Q') h)

@[simp] lemma artinEulerCoeff_zero (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] :
    artinEulerCoeff (R := R) (S := S) (G := G) ρ Q 0 = 1 := by
  -- This is the normalization `a_p(0)=1` for Euler factors.
  simpa [artinEulerCoeff] using
    (PrimeNumberTheoremAnd.ArtinLSeries.ArtinRep.eulerCoeffClass_zero (ρ := ρ)
      (C := PrimeNumberTheoremAnd.Chebotarev.frobClass (R := R) (G := G) (Q := Q)))

/--
The Artin Euler factor attached to a base ideal `P : Ideal R`,
using the choice-free Frobenius conjugacy class `frobClassOver P hP`.
-/
noncomputable def artinEulerFactorOver (P : Ideal R)
    (hP : HasFiniteResidueOver (R := R) (S := S) P) : PowerSeries ℂ :=
  (PrimeNumberTheoremAnd.ArtinLSeries.ArtinRep.eulerFactorClass (ρ := ρ))
    (PrimeNumberTheoremAnd.Chebotarev.frobClassOver (R := R) (S := S) (G := G) P hP)

theorem artinEulerFactorOver_congr (P : Ideal R)
    (hP hP' : HasFiniteResidueOver (R := R) (S := S) P) :
    artinEulerFactorOver (R := R) (S := S) (G := G) ρ P hP =
      artinEulerFactorOver (R := R) (S := S) (G := G) ρ P hP' := by
  simp [artinEulerFactorOver]

/-- The `e`-th coefficient of the Artin Euler factor at a base ideal `P`, via `frobClassOver`. -/
noncomputable def artinEulerCoeffOver (P : Ideal R)
    (hP : HasFiniteResidueOver (R := R) (S := S) P) (e : ℕ) : ℂ :=
  (PrimeNumberTheoremAnd.ArtinLSeries.ArtinRep.eulerCoeffClass (ρ := ρ) e)
    (PrimeNumberTheoremAnd.Chebotarev.frobClassOver (R := R) (S := S) (G := G) P hP)

theorem artinEulerCoeffOver_congr (P : Ideal R)
    (hP hP' : HasFiniteResidueOver (R := R) (S := S) P) (e : ℕ) :
    artinEulerCoeffOver (R := R) (S := S) (G := G) ρ P hP e =
      artinEulerCoeffOver (R := R) (S := S) (G := G) ρ P hP' e := by
  simp [artinEulerCoeffOver]

@[simp] lemma artinEulerCoeffOver_zero (P : Ideal R)
    (hP : HasFiniteResidueOver (R := R) (S := S) P) :
    artinEulerCoeffOver (R := R) (S := S) (G := G) ρ P hP 0 = 1 := by
  simpa [artinEulerCoeffOver] using
    (PrimeNumberTheoremAnd.ArtinLSeries.ArtinRep.eulerCoeffClass_zero (ρ := ρ)
      (C := PrimeNumberTheoremAnd.Chebotarev.frobClassOver (R := R) (S := S) (G := G) P hP))

theorem artinEulerFactorOver_eq_artinEulerFactor (P : Ideal R)
    (hP : HasFiniteResidueOver (R := R) (S := S) P) (Q : Ideal.primesOver P S)
    [Finite (S ⧸ (Q.1 : Ideal S))] :
    artinEulerFactorOver (R := R) (S := S) (G := G) ρ P hP =
      artinEulerFactor (R := R) (S := S) (G := G) ρ (Q := (Q.1 : Ideal S)) := by
  classical
  -- Reduce to the corresponding choice-independence statement for Frobenius classes.
  simpa [artinEulerFactorOver, artinEulerFactor] using
    congrArg (PrimeNumberTheoremAnd.ArtinLSeries.ArtinRep.eulerFactorClass (ρ := ρ))
      (PrimeNumberTheoremAnd.Chebotarev.frobClassOver_eq_frobClass
        (R := R) (S := S) (G := G) (P := P) (hP := hP) (Q := Q))

theorem artinEulerCoeffOver_eq_artinEulerCoeff (P : Ideal R)
    (hP : HasFiniteResidueOver (R := R) (S := S) P) (Q : Ideal.primesOver P S)
    [Finite (S ⧸ (Q.1 : Ideal S))] (e : ℕ) :
    artinEulerCoeffOver (R := R) (S := S) (G := G) ρ P hP e =
      artinEulerCoeff (R := R) (S := S) (G := G) ρ (Q := (Q.1 : Ideal S)) e := by
  classical
  simpa [artinEulerCoeffOver, artinEulerCoeff] using
    congrArg (PrimeNumberTheoremAnd.ArtinLSeries.ArtinRep.eulerCoeffClass (ρ := ρ) e)
      (PrimeNumberTheoremAnd.Chebotarev.frobClassOver_eq_frobClass
        (R := R) (S := S) (G := G) (P := P) (hP := hP) (Q := Q))

end

end Chebotarev

end PrimeNumberTheoremAnd
