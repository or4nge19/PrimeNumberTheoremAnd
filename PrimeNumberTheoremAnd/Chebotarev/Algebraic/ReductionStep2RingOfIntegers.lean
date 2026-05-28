import PrimeNumberTheoremAnd.Chebotarev.Algebraic.ReductionStep2
import PrimeNumberTheoremAnd.Chebotarev.Algebraic.GaloisInstances
import PrimeNumberTheoremAnd.Chebotarev.Algebraic.ChebotarevPrimeIdeals

import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
## Sharifi Step 2 at rings of integers

The generic Step 2 predicates in `ReductionStep2.lean` index prime ideals of the **fields** `K`
and `E`. For number fields the correct Sharifi index set is `𝓞 K` and `𝓞 E`; this file
expresses Step 2 on rings of integers with the Galois AKLB instances from `GaloisInstances`.

The tower identity `step2_ncard_primesOver_mul_ncard_primesOver` (in
`ReductionStep2Splitting.lean`) is stated and proved on these types.
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev

open scoped Classical Pointwise
open NumberField

section Step2RingOfIntegers

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]
variable (σ : Gal(L/K))
variable [Finite (Gal(L/K))]
variable [IsGalois K L]

attribute [local instance] FractionRing.liftAlgebra

noncomputable local instance instIsGaloisGroupGalLK :
    IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing (G := Gal(L/K)) (A := 𝓞 K) (B := 𝓞 L) (K := K) (L := L)

noncomputable local instance instIsGaloisGroupGalLE :
    IsGaloisGroup Gal(L/↥(step2FixedField (K := K) (L := L) σ)) (𝓞 ↥(step2FixedField (K := K) (L := L) σ))
    (𝓞 L) := by
  haveI : IsGalois (↥(step2FixedField (K := K) (L := L) σ)) L :=
    isGalois_fixedFieldZpowers_L (K := K) (L := L) σ
  exact IsGaloisGroup.of_isFractionRing (G := Gal(L/↥(step2FixedField (K := K) (L := L) σ)))
    (A := 𝓞 ↥(step2FixedField (K := K) (L := L) σ)) (B := 𝓞 L)
    (K := ↥(step2FixedField (K := K) (L := L) σ)) (L := L)

open Ideal

/-- Sharifi's intermediate field `E = L^{⟨σ⟩}` as a number field. -/
noncomputable abbrev step2E : Type _ :=
  ↥(step2FixedField (K := K) (L := L) σ)

instance step2E_numberField : NumberField (step2E (K := K) (L := L) σ) :=
  NumberField.of_intermediateField (step2FixedField (K := K) (L := L) σ)

/-- Sharifi's base Chebotarev set `S_{Cl(σ)}` at prime ideals of `𝓞 K`. -/
def step2ChebotarevSetRO : Set (Ideal (𝓞 K)) :=
  chebotarevSet (R := 𝓞 K) (S := 𝓞 L) (G := Gal(L/K))
    (step2FrobClassInGalLK (K := K) (L := L) σ)

theorem step2ChebotarevSetRO_eq :
    step2ChebotarevSetRO (K := K) (L := L) σ =
      chebotarevSet (R := 𝓞 K) (S := 𝓞 L) (G := Gal(L/K)) (ConjClasses.mk σ) := by
  simp [step2ChebotarevSetRO, step2FrobClassInGalLK_eq (K := K) (L := L) σ]

theorem mem_step2ChebotarevSetRO_iff (p : Ideal (𝓞 K)) :
    p ∈ step2ChebotarevSetRO (K := K) (L := L) σ ↔
      HasUnramifiedFrobClass (R := 𝓞 K) (S := 𝓞 L) (G := Gal(L/K)) p (ConjClasses.mk σ) := by
  simp [step2ChebotarevSetRO, mem_chebotarevSet_iff, step2FrobClassInGalLK_eq (K := K) (L := L) σ]

theorem mem_step2ChebotarevSetRO_iff_frobClassOver (p : Ideal (𝓞 K)) [p.IsMaximal] (hpne : p ≠ ⊥) :
    p ∈ step2ChebotarevSetRO (K := K) (L := L) σ ↔
      Ideal.IsUnramifiedIn (R := 𝓞 K) (S := 𝓞 L) p ∧
        frobClassOver (R := 𝓞 K) (S := 𝓞 L) (G := Gal(L/K)) p
          (hasFiniteResidueOver_of_numberField (K := K) (L := L) p hpne) = ConjClasses.mk σ := by
  rw [mem_step2ChebotarevSetRO_iff, hasUnramifiedFrobClass_iff_frobClassOver_numberField (K := K) (L := L)
    (P := p) (C := ConjClasses.mk σ) (hP := hpne)]

/--
Sharifi's Frobenius condition in `Gal(L/E)` at an intermediate prime `Q` of `𝓞 E`.
This is the `HasFrobClass` layer in the fiber definition (before witness elimination).
-/
def step2HasIntermediateFrobClassRO (Q : Ideal (𝓞 (step2E (K := K) (L := L) σ))) : Prop :=
  HasFrobClass (R := 𝓞 (step2E (K := K) (L := L) σ)) (S := 𝓞 L)
    (G := Gal(L/↥(step2FixedField (K := K) (L := L) σ))) Q (step2FrobClass (K := K) (L := L) σ)

theorem step2HasIntermediateFrobClassRO_iff (Q : Ideal (𝓞 (step2E (K := K) (L := L) σ))) :
    step2HasIntermediateFrobClassRO (K := K) (L := L) σ Q ↔
      HasFrobClass (R := 𝓞 (step2E (K := K) (L := L) σ)) (S := 𝓞 L)
        (G := Gal(L/↥(step2FixedField (K := K) (L := L) σ))) Q (step2FrobClass (K := K) (L := L) σ) :=
  Iff.rfl

theorem step2HasIntermediateFrobClassRO_iff_frobClassOver
    (Q : Ideal (𝓞 (step2E (K := K) (L := L) σ))) [Q.IsMaximal] (hQne : Q ≠ ⊥) :
    step2HasIntermediateFrobClassRO (K := K) (L := L) σ Q ↔
      frobClassOver (R := 𝓞 (step2E (K := K) (L := L) σ)) (S := 𝓞 L)
        (G := Gal(L/↥(step2FixedField (K := K) (L := L) σ))) Q
        (hasFiniteResidueOver_of_numberField (K := step2E (K := K) (L := L) σ) (L := L) Q hQne) =
          step2FrobClass (K := K) (L := L) σ :=
  hasFrobClass_iff_frobClassOver_eq_numberField (K := step2E (K := K) (L := L) σ) (L := L)
    (P := Q) (hP := hQne) (C := step2FrobClass (K := K) (L := L) σ)

/-- Intermediate primes of `𝓞 E` with Frobenius class `step2FrobClass σ` in `Gal(L/E)`. -/
def step2IntermediateFrobClassPrimeSetRO : Set (Ideal (𝓞 (step2E (K := K) (L := L) σ))) :=
  {Q | step2HasIntermediateFrobClassRO (K := K) (L := L) σ Q}

theorem mem_step2IntermediateFrobClassPrimeSetRO_iff
    (Q : Ideal (𝓞 (step2E (K := K) (L := L) σ))) :
    Q ∈ step2IntermediateFrobClassPrimeSetRO (K := K) (L := L) σ ↔
      step2HasIntermediateFrobClassRO (K := K) (L := L) σ Q :=
  Iff.rfl

/-- Sharifi's intermediate set `T_σ` at prime ideals of `𝓞 E`. -/
def step2DegreeOneChebotarevSetRO : Set (Ideal (𝓞 (step2E (K := K) (L := L) σ))) :=
  degreeOneChebotarevSet (R := 𝓞 K) (T := 𝓞 (step2E (K := K) (L := L) σ)) (S := 𝓞 L)
    (G := Gal(L/↥(step2FixedField (K := K) (L := L) σ)))
    (step2FrobClass (K := K) (L := L) σ)

theorem mem_step2DegreeOneChebotarevSetRO_iff (Q : Ideal (𝓞 (step2E (K := K) (L := L) σ))) :
    Q ∈ step2DegreeOneChebotarevSetRO (K := K) (L := L) σ ↔
      ∃ p : Ideal (𝓞 K),
        degreeOneChebotarevPrime (R := 𝓞 K) (T := 𝓞 (step2E (K := K) (L := L) σ)) (S := 𝓞 L)
          (G := Gal(L/↥(step2FixedField (K := K) (L := L) σ))) p Q
          (step2FrobClass (K := K) (L := L) σ) := by
  simp [step2DegreeOneChebotarevSetRO, mem_degreeOneChebotarevSet_iff]

theorem mem_step2DegreeOneChebotarevSetRO_iff_of_liesOver
    (p : Ideal (𝓞 K)) (Q : Ideal (𝓞 (step2E (K := K) (L := L) σ))) (hp : Q.LiesOver p) :
    Q ∈ step2DegreeOneChebotarevSetRO (K := K) (L := L) σ ↔
      degreeOneChebotarevPrime (R := 𝓞 K) (T := 𝓞 (step2E (K := K) (L := L) σ)) (S := 𝓞 L)
        (G := Gal(L/↥(step2FixedField (K := K) (L := L) σ))) p Q
        (step2FrobClass (K := K) (L := L) σ) :=
  mem_degreeOneChebotarevSet_iff_of_liesOver (C := step2FrobClass (K := K) (L := L) σ) p Q hp

/-- Fiber of `T_σ → S_{Cl(σ)}` above a base prime `p` of `𝓞 K`. -/
def step2FiberOverRO (p : Ideal (𝓞 K)) : Set (Ideal (𝓞 (step2E (K := K) (L := L) σ))) :=
  degreeOneChebotarevPrimeSet (R := 𝓞 K) (T := 𝓞 (step2E (K := K) (L := L) σ)) (S := 𝓞 L)
    (G := Gal(L/↥(step2FixedField (K := K) (L := L) σ))) p
    (step2FrobClass (K := K) (L := L) σ)

theorem mem_step2FiberOverRO_iff (p : Ideal (𝓞 K))
    (Q : Ideal (𝓞 (step2E (K := K) (L := L) σ))) :
    Q ∈ step2FiberOverRO (K := K) (L := L) σ p ↔
      degreeOneChebotarevPrime (R := 𝓞 K) (T := 𝓞 (step2E (K := K) (L := L) σ)) (S := 𝓞 L)
        (G := Gal(L/↥(step2FixedField (K := K) (L := L) σ))) p Q
        (step2FrobClass (K := K) (L := L) σ) :=
  Iff.rfl

/--
Sharifi's intermediate set `T_σ` is the union of the Step 2 fibers over all base primes.
-/
theorem mem_step2DegreeOneChebotarevSetRO_iff_exists_fiber
    (Q : Ideal (𝓞 (step2E (K := K) (L := L) σ))) :
    Q ∈ step2DegreeOneChebotarevSetRO (K := K) (L := L) σ ↔
      ∃ p : Ideal (𝓞 K), Q ∈ step2FiberOverRO (K := K) (L := L) σ p := by
  simp [mem_step2DegreeOneChebotarevSetRO_iff, mem_step2FiberOverRO_iff]

theorem step2DegreeOneChebotarevSetRO_eq_iUnion_step2FiberOverRO :
    step2DegreeOneChebotarevSetRO (K := K) (L := L) σ =
      ⋃ p : Ideal (𝓞 K), step2FiberOverRO (K := K) (L := L) σ p := by
  ext Q
  simp [mem_step2DegreeOneChebotarevSetRO_iff_exists_fiber, Set.mem_iUnion]

/-- All prime ideals of `𝓞 E` lying over the base prime `p` of `𝓞 K`. -/
def step2PrimesOverRO (p : Ideal (𝓞 K)) : Set (Ideal (𝓞 (step2E (K := K) (L := L) σ))) :=
  p.primesOver (𝓞 (step2E (K := K) (L := L) σ))

theorem mem_step2PrimesOverRO_iff (p : Ideal (𝓞 K))
    (Q : Ideal (𝓞 (step2E (K := K) (L := L) σ))) :
    Q ∈ step2PrimesOverRO (K := K) (L := L) σ p ↔ Q.IsPrime ∧ Q.LiesOver p :=
  Iff.rfl

theorem step2FiberOverRO_subset_step2PrimesOverRO (p : Ideal (𝓞 K)) :
    step2FiberOverRO (K := K) (L := L) σ p ⊆ step2PrimesOverRO (K := K) (L := L) σ p := by
  intro Q hQ
  exact ⟨hQ.1, hQ.2.1⟩

theorem mem_step2FiberOverRO_of_mem_step2DegreeOneRO (p : Ideal (𝓞 K))
    (Q : Ideal (𝓞 (step2E (K := K) (L := L) σ)))
    (hQ : Q ∈ step2DegreeOneChebotarevSetRO (K := K) (L := L) σ) (hp : Q.LiesOver p) :
    Q ∈ step2FiberOverRO (K := K) (L := L) σ p := by
  rcases hQ with ⟨p', hp'⟩
  have hp'eq : p' = p := hp'.2.1.over.trans hp.over.symm
  subst hp'eq
  exact hp'

def step2ChebotarevPrimeIdealSetRO : Set (DirichletDensity.PrimeIdeal (𝓞 K)) :=
  chebotarevPrimeIdealSet (R := 𝓞 K) (S := 𝓞 L) (G := Gal(L/K))
    (step2FrobClassInGalLK (K := K) (L := L) σ)

def step2DegreeOneChebotarevPrimeIdealSetRO :
    Set (DirichletDensity.PrimeIdeal (𝓞 (step2E (K := K) (L := L) σ))) :=
  {Q | Q.1 ∈ step2DegreeOneChebotarevSetRO (K := K) (L := L) σ}

theorem step2_card_conjClass_eq_centralizerIndexRO :
    Nat.card (ConjClasses.mk σ).carrier =
      (Subgroup.centralizer ({σ} : Set (Gal(L/K)))).index :=
  step2_card_conjClass_eq_centralizerIndex (K := K) (L := L) σ

/--
Sharifi Step 2 counting target at rings of integers.

**Status: open.** See `OpenHypotheses.step2PrimeCountingHypothesisRO` (`sorry`) until a proof is found.
The field-level `Step2PrimeCountingHypothesis` in `ReductionStep2.lean` is legacy scaffold.
-/
def Step2PrimeCountingHypothesisRO : Prop :=
  ∀ p : Ideal (𝓞 K), p ∈ step2ChebotarevSetRO (K := K) (L := L) σ →
    Nat.card (step2FiberOverRO (K := K) (L := L) σ p) =
      (Subgroup.centralizer ({σ} : Set (Gal(L/K)))).index

theorem Step2PrimeCountingHypothesisRO_iff_conjClassCard :
    Step2PrimeCountingHypothesisRO (K := K) (L := L) σ ↔
      ∀ p : Ideal (𝓞 K), p ∈ step2ChebotarevSetRO (K := K) (L := L) σ →
        Nat.card (step2FiberOverRO (K := K) (L := L) σ p) =
          Nat.card (ConjClasses.mk σ).carrier := by
  constructor
  · intro h p hp
    rw [step2_card_conjClass_eq_centralizerIndexRO (K := K) (L := L) σ]
    exact h p hp
  · intro h p hp
    rw [← step2_card_conjClass_eq_centralizerIndexRO (K := K) (L := L) σ]
    exact h p hp

/--
For an unramified base prime, the decomposition group at any prime above has order equal to
the inertia degree (`Ideal.card_stabilizer_eq` in the Galois, unramified regime).
This is the raw prime-splitting input behind Sharifi's fiber cardinality.
-/
theorem card_stabilizer_eq_inertiaDegIn_of_unramifiedIn
    (p : Ideal (𝓞 K)) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal (𝓞 L)) [P.IsMaximal] [P.LiesOver p]
    (hunram : Ideal.IsUnramifiedIn (R := 𝓞 K) (S := 𝓞 L) p)
    [Algebra.IsSeparable (𝓞 K ⧸ p) (𝓞 L ⧸ P)] :
    Nat.card (MulAction.stabilizer Gal(L/K) P) = p.inertiaDegIn (𝓞 L) := by
  have hram : p.ramificationIdx P = 1 := hunram inferInstance inferInstance
  have hIdxIn : p.ramificationIdxIn (𝓞 L) = 1 := by
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (p := p) (P := P) (G := Gal(L/K))]
    exact hram
  simpa [hIdxIn, one_mul] using
    Ideal.card_stabilizer_eq (G := Gal(L/K)) (R := 𝓞 K) (S := 𝓞 L) p hp P

end Step2RingOfIntegers

end Chebotarev

end PrimeNumberTheoremAnd
