import PrimeNumberTheoremAnd.Chebotarev.Algebraic.Sets
import PrimeNumberTheoremAnd.Chebotarev.Density.DirichletDensityIdeals

/-!
## Chebotarev sets at prime ideals

Sharifi's Chebotarev sets are subsets of prime ideals. This file reindexes them as
`DirichletDensity.PrimeIdeal R`, the index type used for ideal-norm Dirichlet density.
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev

open scoped Classical

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G S] [SMulCommClass G R S] [Algebra.IsInvariant R S G]

open Ideal

/-- Pack a prime ideal as a `PrimeIdeal`. -/
def primeIdealMk (P : Ideal R) (hP : P.IsPrime) : DirichletDensity.PrimeIdeal R :=
  ⟨P, hP⟩

@[simp] lemma primeIdealMk_val (P : Ideal R) (hP : P.IsPrime) :
    (primeIdealMk (R := R) P hP).1 = P := rfl

/--
Chebotarev set for the class `C`, viewed as a set of prime ideals (Sharifi's index set).
-/
def chebotarevPrimeIdealSet (C : ConjClasses G) : Set (DirichletDensity.PrimeIdeal R) :=
  {P | P.1 ∈ chebotarevSet (R := R) (S := S) (G := G) C}

theorem mem_chebotarevPrimeIdealSet_iff (C : ConjClasses G) (P : DirichletDensity.PrimeIdeal R) :
    P ∈ chebotarevPrimeIdealSet (R := R) (S := S) (G := G) C ↔
      P.1 ∈ chebotarevSet (R := R) (S := S) (G := G) C :=
  Iff.rfl

theorem mem_chebotarevPrimeIdealSet_iff_hasUnramifiedFrobClass (C : ConjClasses G)
    (P : DirichletDensity.PrimeIdeal R) :
    P ∈ chebotarevPrimeIdealSet (R := R) (S := S) (G := G) C ↔
      HasUnramifiedFrobClass (R := R) (S := S) (G := G) P.1 C := by
  simp [chebotarevPrimeIdealSet, mem_chebotarevSet_iff]

end

end Chebotarev

end PrimeNumberTheoremAnd
