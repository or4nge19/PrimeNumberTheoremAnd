import Mathlib.RingTheory.Frobenius
import Mathlib.Algebra.Group.Conj
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.NumberTheory.NumberField.Basic

/-!
## Frobenius conjugacy classes (algebraic prerequisite for Chebotarev)

This file expresses the **Frobenius conjugacy class** attached to a prime lying over a base prime,
using the existing mathlib Frobenius API in `Mathlib/RingTheory/Frobenius.lean`.

### Design principles

* We do not redefine Frobenius: we use `arithFrobAt` and `IsArithFrobAt`.
* The correct object for Chebotarev should be a **conjugacy class** in the Galois group (TBC) , so we work in
  `ConjClasses G`.
* Finiteness hypotheses are expressed once as `HasFiniteResidueOver`.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical
open NumberField

namespace Chebotarev

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G S] [SMulCommClass G R S] [Algebra.IsInvariant R S G]

open Ideal

/--
There exists a prime of `S` lying over `P` with finite residue field.

This is exactly the finiteness needed to define `arithFrobAt` / `frobClassOver`.
-/
def HasFiniteResidueOver (P : Ideal R) : Prop :=
  ∃ Q : Ideal.primesOver P S, Finite (S ⧸ (Q.1 : Ideal S))

theorem hasFiniteResidueOver_of_primesOver (P : Ideal R) (Q : Ideal.primesOver P S)
    [Finite (S ⧸ (Q.1 : Ideal S))] :
    HasFiniteResidueOver (R := R) (S := S) P :=
  ⟨Q, inferInstance⟩

variable (R G)

/--
The Frobenius element at a prime ideal `Q` of `S`, expressed as a conjugacy class in `G`.

It is definitionally `ConjClasses.mk` of mathlib's canonical choice `arithFrobAt`.
-/
noncomputable abbrev frobClass (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] : ConjClasses G :=
  ConjClasses.mk (arithFrobAt (R := R) (G := G) Q)

variable {R G}

@[simp]
theorem frobClass_eq_of_under_eq (Q Q' : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    [Q'.IsPrime] [Finite (S ⧸ Q')] (h : Q.under R = Q'.under R) :
    frobClass (R := R) (G := G) Q = frobClass (R := R) (G := G) Q' := by
  classical
  apply (ConjClasses.mk_eq_mk_iff_isConj).2
  simpa using (_root_.isConj_arithFrobAt (R := R) (S := S) (G := G) (Q := Q) (Q' := Q') h)

end

section primesOver

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G S] [SMulCommClass G R S] [Algebra.IsInvariant R S G]

open Ideal

/--
The Frobenius conjugacy class attached to a base prime `P`, using mathlib's `arithFrobAt`.

The output does not depend on the choice of prime above `P` nor on the finiteness witness.
-/
noncomputable def frobClassOver (P : Ideal R) (hP : HasFiniteResidueOver (R := R) (S := S) P) :
    ConjClasses G := by
  classical
  let Q0 : Ideal.primesOver P S := Classical.choose hP
  letI : Finite (S ⧸ (Q0.1 : Ideal S)) := Classical.choose_spec hP
  exact frobClass (R := R) (G := G) (Q := (Q0.1 : Ideal S))

theorem frobClassOver_eq_frobClass (P : Ideal R) (hP : HasFiniteResidueOver (R := R) (S := S) P)
    (Q : Ideal.primesOver P S) [Finite (S ⧸ (Q.1 : Ideal S))] :
    frobClassOver (R := R) (S := S) (G := G) P hP =
      frobClass (R := R) (G := G) (Q := (Q.1 : Ideal S)) := by
  classical
  let Q0 : Ideal.primesOver P S := Classical.choose hP
  letI : Finite (S ⧸ (Q0.1 : Ideal S)) := Classical.choose_spec hP
  have hQ0_under : (Q0.1 : Ideal S).under R = P := Q0.2.2.over.symm
  have hQ_under : (Q.1 : Ideal S).under R = P := Q.2.2.over.symm
  have hunder : (Q0.1 : Ideal S).under R = (Q.1 : Ideal S).under R := by
    simp [hQ0_under, hQ_under]
  have : frobClassOver (R := R) (S := S) (G := G) P hP =
      frobClass (R := R) (G := G) (Q := (Q0.1 : Ideal S)) := by
    simp [frobClassOver, Q0]
  simpa [this] using (frobClass_eq_of_under_eq (R := R) (S := S) (G := G)
    (Q := (Q0.1 : Ideal S)) (Q' := (Q.1 : Ideal S)) hunder)

theorem frobClassOver_congr (P : Ideal R)
    (hP hP' : HasFiniteResidueOver (R := R) (S := S) P) :
    frobClassOver (R := R) (S := S) (G := G) P hP =
      frobClassOver (R := R) (S := S) (G := G) P hP' := by
  classical
  let Q : Ideal.primesOver P S := Classical.choose hP
  letI : Finite (S ⧸ (Q.1 : Ideal S)) := Classical.choose_spec hP
  have h1 :
      frobClassOver (R := R) (S := S) (G := G) P hP =
        frobClass (R := R) (G := G) (Q := (Q.1 : Ideal S)) := by
    simpa using
      (frobClassOver_eq_frobClass (R := R) (S := S) (G := G) (P := P) (hP := hP) Q)
  have h2 :
      frobClassOver (R := R) (S := S) (G := G) P hP' =
        frobClass (R := R) (G := G) (Q := (Q.1 : Ideal S)) := by
    simpa using
      (frobClassOver_eq_frobClass (R := R) (S := S) (G := G) (P := P) (hP := hP') Q)
  simp [h1, h2]

end primesOver

section natPrimes

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G S] [SMulCommClass G R S] [Algebra.IsInvariant R S G]

open Ideal

def HasFiniteResidueOverNat (P : Nat.Primes → Ideal R) : Prop :=
  ∀ p : Nat.Primes, HasFiniteResidueOver (R := R) (S := S) (P p)

/--
From a `Nat.Primes`-indexed family of base ideals and finiteness witnesses, produce the
corresponding Frobenius conjugacy-class assignment.
-/
noncomputable def frobClassOverNat (P : Nat.Primes → Ideal R)
    (hP : HasFiniteResidueOverNat (R := R) (S := S) P) :
    Nat.Primes → ConjClasses G :=
  fun p => frobClassOver (R := R) (S := S) (G := G) (P p) (hP p)

theorem frobClassOverNat_congr (P : Nat.Primes → Ideal R)
    (hP hP' : HasFiniteResidueOverNat (R := R) (S := S) P) :
    frobClassOverNat (R := R) (S := S) (G := G) P hP =
      frobClassOverNat (R := R) (S := S) (G := G) P hP' := by
  classical
  funext p
  simpa [frobClassOverNat] using
    (frobClassOver_congr (R := R) (S := S) (G := G) (P := P p) (hP := hP p) (hP' := hP' p))

end natPrimes

section hasFiniteQuotients

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G S] [SMulCommClass G R S] [Algebra.IsInvariant R S G]

open Ideal

/--
When `S` has finite quotients and `S/R` is integral, every nonzero base prime has a finite
residue witness above it (mathlib `exists_ideal_over_prime_of_isIntegral`).
-/
theorem hasFiniteResidueOver_of_hasFiniteQuotients
    [IsDomain R] [Nontrivial S] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]
    [Ring.HasFiniteQuotients S] (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) :
    HasFiniteResidueOver (R := R) (S := S) P := by
  classical
  let Q : primesOver P S := Classical.arbitrary _
  refine ⟨Q, Ring.HasFiniteQuotients.finiteQuotient (I := (Q.1 : Ideal S)) ?_⟩
  exact ne_bot_of_liesOver_of_ne_bot hP Q.1

theorem hasFiniteResidueOverNat_of_hasFiniteQuotients
    [IsDomain R] [Nontrivial S] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]
    [Ring.HasFiniteQuotients S] (P : Nat.Primes → Ideal R)
    (hPrime : ∀ p, (P p).IsPrime) (hNe : ∀ p, P p ≠ ⊥) :
    HasFiniteResidueOverNat (R := R) (S := S) P :=
  fun p => hasFiniteResidueOver_of_hasFiniteQuotients (P := P p) (hP := hNe p)

section NumberField

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- In a number-field extension, finite residue fields are automatic (no repeated hypothesis). -/
theorem hasFiniteResidueOver_of_numberField (P : Ideal (RingOfIntegers K)) [P.IsPrime]
    (hP : P ≠ ⊥) :
    HasFiniteResidueOver (R := RingOfIntegers K) (S := RingOfIntegers L) P :=
  hasFiniteResidueOver_of_hasFiniteQuotients (P := P) (hP := hP)

theorem hasFiniteResidueOverNat_of_numberField (P : Nat.Primes → Ideal (RingOfIntegers K))
    (hPrime : ∀ p, (P p).IsPrime) (hNe : ∀ p, P p ≠ ⊥) :
    HasFiniteResidueOverNat (R := RingOfIntegers K) (S := RingOfIntegers L) P :=
  hasFiniteResidueOverNat_of_hasFiniteQuotients (P := P) hPrime hNe

end NumberField

end hasFiniteQuotients

end Chebotarev

end PrimeNumberTheoremAnd
