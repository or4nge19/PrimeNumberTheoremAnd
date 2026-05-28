import PrimeNumberTheoremAnd.Chebotarev.Algebraic.FixedFieldGenerator
import PrimeNumberTheoremAnd.Chebotarev.Algebraic.DegreeOne
import PrimeNumberTheoremAnd.Chebotarev.Algebraic.Sets
import PrimeNumberTheoremAnd.Chebotarev.Algebraic.Reduction
import PrimeNumberTheoremAnd.Chebotarev.Algebraic.FrobeniusRestriction
import PrimeNumberTheoremAnd.Chebotarev.Algebraic.ConjugacyCounting

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.NumberField.Basic

set_option linter.unusedSectionVars false

/-!
## Sharifi Step 2: reduction to a cyclic subextension

Sharifi Thm 7.2.2 (Step 1) fixes `σ ∈ Gal(L/K)`, sets `E = L^{⟨σ⟩}`, and compares

* `S_C`: unramified base primes in `K` with Frobenius conjugacy class `C = Cl(σ)` in `Gal(L/K)`;
* `T_σ`: primes of `E` unramified in `L`, of degree `1` over `K`, with Frobenius
  `sigmaGalFixedFieldZpowers σ` in `Gal(L/E)`.

Class identification `step2FrobClassInGalLK σ = Cl(σ)` is in
`Chebotarev.Algebraic.FrobeniusRestriction`. The prime-splitting bijection
(`Step2PrimeCountingHypothesis`) and density equivalence remain open.

**Note:** the predicates below index `Ideal K` (field-level scaffold). For Sharifi's correct
index set use `ReductionStep2RingOfIntegers` (`Ideal (𝓞 K)`).
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev

open scoped Classical

section IdealPredicates

variable {R T S : Type*} [CommRing R] [CommRing T] [CommRing S]
variable [Algebra R T] [Algebra T S] [Algebra R S] [IsScalarTower R T S]
variable {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G S] [SMulCommClass G T S] [Algebra.IsInvariant T S G]

open Ideal

def degreeOneChebotarevPrime (p : Ideal R) (Q : Ideal T) (C : ConjClasses G) : Prop :=
  Q.IsPrime ∧
    Q.LiesOver p ∧
      Ideal.IsUnramifiedAbove (T := T) (S := S) Q ∧
        p.inertiaDeg Q = 1 ∧
          HasFrobClass (R := T) (S := S) (G := G) Q C

theorem degreeOneChebotarevPrime_iff (p : Ideal R) (Q : Ideal T) (C : ConjClasses G) :
    degreeOneChebotarevPrime (R := R) (T := T) (S := S) (G := G) p Q C ↔
      Q.IsPrime ∧
        Q.LiesOver p ∧
          Ideal.IsUnramifiedAbove (T := T) (S := S) Q ∧
            p.inertiaDeg Q = 1 ∧
              HasFrobClass (R := T) (S := S) (G := G) Q C :=
  Iff.rfl

/-- Sharifi's degree-1-over-`R` condition at an intermediate prime `Q` above base `p`. -/
def degreeOneOverBase (p : Ideal R) (Q : Ideal T) : Prop :=
  Q.LiesOver p ∧ p.inertiaDeg Q = 1

theorem degreeOneOverBase_iff (p : Ideal R) (Q : Ideal T) :
    degreeOneOverBase (R := R) (T := T) p Q ↔ Q.LiesOver p ∧ p.inertiaDeg Q = 1 :=
  Iff.rfl

theorem degreeOneChebotarevPrime_iff_degreeOneOverBase_frob (p : Ideal R) (Q : Ideal T)
    (C : ConjClasses G) :
    degreeOneChebotarevPrime (R := R) (T := T) (S := S) (G := G) p Q C ↔
      Q.IsPrime ∧
        degreeOneOverBase (R := R) (T := T) p Q ∧
          Ideal.IsUnramifiedAbove (T := T) (S := S) Q ∧
            HasFrobClass (R := T) (S := S) (G := G) Q C := by
  simp [degreeOneChebotarevPrime, degreeOneOverBase]
  tauto

def degreeOneChebotarevPrimeSet (p : Ideal R) (C : ConjClasses G) : Set (Ideal T) :=
  {Q | degreeOneChebotarevPrime (R := R) (T := T) (S := S) (G := G) p Q C}

def degreeOneChebotarevSet (C : ConjClasses G) : Set (Ideal T) :=
  {Q | ∃ p : Ideal R, degreeOneChebotarevPrime (R := R) (T := T) (S := S) (G := G) p Q C}

theorem mem_degreeOneChebotarevSet_iff (C : ConjClasses G) (Q : Ideal T) :
    Q ∈ degreeOneChebotarevSet (R := R) (T := T) (S := S) (G := G) C ↔
      ∃ p : Ideal R, degreeOneChebotarevPrime (R := R) (T := T) (S := S) (G := G) p Q C :=
  Iff.rfl

/--
When `Q` already lies over a base prime `p`, membership in Sharifi's `T_σ` is equivalent to the
fiber predicate at that `p` (the existential base prime is unique).
-/
theorem mem_degreeOneChebotarevSet_iff_of_liesOver (C : ConjClasses G) (p : Ideal R) (Q : Ideal T)
    (hp : Q.LiesOver p) :
    Q ∈ degreeOneChebotarevSet (R := R) (T := T) (S := S) (G := G) C ↔
      degreeOneChebotarevPrime (R := R) (T := T) (S := S) (G := G) p Q C := by
  constructor
  · rintro ⟨p', hp'⟩
    have hp'eq : p' = p := hp'.2.1.over.trans hp.over.symm
    subst hp'eq
    exact hp'
  · exact fun h => ⟨p, h⟩

end IdealPredicates

section BaseChebotarevPredicates

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G S] [SMulCommClass G R S] [Algebra.IsInvariant R S G]

open Ideal

abbrev chebotarevSetFor (σ : G) : Set (Ideal R) :=
  chebotarevSet (R := R) (S := S) (G := G) (ConjClasses.mk σ)

end BaseChebotarevPredicates

section DensityTargets

variable {G : Type*} [Group G] [Finite G]

/--
Predicted Dirichlet density of the Chebotarev set for the conjugacy class of `g` (`|C|/|G|`).
This is the target in Sharifi Thm 7.2.2, not a definition of density.
-/
noncomputable def chebotarevDensityTarget (g : G) : ℂ :=
  (Nat.card (ConjClasses.mk g).carrier : ℂ) / (Nat.card G : ℂ)

/--
Predicted density of Sharifi's intermediate set `T_σ` in Step 2 (`1/|⟨σ⟩|`).
-/
noncomputable def cyclicSubextensionDensityTarget (σ : G) : ℂ :=
  (Nat.card (Subgroup.zpowers σ) : ℂ)⁻¹

end DensityTargets

section Step2Galois

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
variable (σ : Gal(L/K))
variable [Finite (Gal(L/K))]

lemma step2IntermediateDensityTarget_eq_inv_finrank :
    cyclicSubextensionDensityTarget (G := Gal(L/K)) σ =
      (Module.finrank (step2FixedField (K := K) (L := L) σ) L : ℂ)⁻¹ := by
  rw [cyclicSubextensionDensityTarget,
    ← Chebotarev.finrank_fixedFieldZpowers_eq_natCard_zpowers (K := K) (L := L) σ]

end Step2Galois

section Step2NumberField

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]
variable (σ : Gal(L/K))
variable [Finite (Gal(L/K))]
variable [MulSemiringAction (Gal(L/K)) L] [SMulCommClass (Gal(L/K)) K L]
variable [Algebra.IsInvariant K L (Gal(L/K))]
variable [MulSemiringAction (Gal(L/↥(step2FixedField (K := K) (L := L) σ))) L]
variable [SMulCommClass (Gal(L/↥(step2FixedField (K := K) (L := L) σ))) (↥(step2FixedField (K := K) (L := L) σ)) L]
variable [Algebra.IsInvariant (↥(step2FixedField (K := K) (L := L) σ)) L
  (Gal(L/↥(step2FixedField (K := K) (L := L) σ)))]

open Ideal

/-- Sharifi's `T_σ` set with `G = Gal(L/E)` and Frobenius class `step2FrobClass σ`. -/
def step2DegreeOneChebotarevSet : Set (Ideal (↥(step2FixedField (K := K) (L := L) σ))) :=
  degreeOneChebotarevSet (R := K) (T := ↥(step2FixedField (K := K) (L := L) σ)) (S := L)
    (G := Gal(L/↥(step2FixedField (K := K) (L := L) σ)))
    (step2FrobClass (K := K) (L := L) σ)

/-- Sharifi's base set `S_{Cl(σ)}` for the Galois extension `L/K`. -/
def step2ChebotarevSet : Set (Ideal K) :=
  chebotarevSetFor (R := K) (S := L) (G := Gal(L/K)) σ

theorem step2ChebotarevSet_eq :
    step2ChebotarevSet (K := K) (L := L) σ =
      chebotarevSet (R := K) (S := L) (G := Gal(L/K))
        (step2FrobClassInGalLK (K := K) (L := L) σ) := by
  simp [step2ChebotarevSet, chebotarevSetFor, step2FrobClassInGalLK_eq (K := K) (L := L) σ]

theorem mem_step2DegreeOneChebotarevSet_iff
    (Q : Ideal (↥(step2FixedField (K := K) (L := L) σ))) :
    Q ∈ step2DegreeOneChebotarevSet (K := K) (L := L) σ ↔
      Q ∈ degreeOneChebotarevSet (R := K) (T := ↥(step2FixedField (K := K) (L := L) σ)) (S := L)
        (G := Gal(L/↥(step2FixedField (K := K) (L := L) σ)))
        (step2FrobClass (K := K) (L := L) σ) :=
  Iff.rfl

theorem mem_step2ChebotarevSet_iff (p : Ideal K) :
    p ∈ step2ChebotarevSet (K := K) (L := L) σ ↔
      p ∈ chebotarevSet (R := K) (S := L) (G := Gal(L/K))
        (step2FrobClassInGalLK (K := K) (L := L) σ) := by
  rw [step2ChebotarevSet_eq (K := K) (L := L), mem_chebotarevSet_iff]

theorem exists_basePrime_of_mem_step2DegreeOneChebotarevSet
    (Q : Ideal (↥(step2FixedField (K := K) (L := L) σ)))
    (hQ : Q ∈ step2DegreeOneChebotarevSet (K := K) (L := L) σ) :
    ∃ p : Ideal K,
      degreeOneChebotarevPrime (R := K) (T := ↥(step2FixedField (K := K) (L := L) σ)) (S := L)
        (G := Gal(L/↥(step2FixedField (K := K) (L := L) σ))) p Q
        (step2FrobClass (K := K) (L := L) σ) := by
  simpa [step2DegreeOneChebotarevSet, degreeOneChebotarevSet] using hQ

/-- Fiber of `T_σ → S_{Cl(σ)}` above a base prime `p`. -/
def step2FiberOver (p : Ideal K) : Set (Ideal (↥(step2FixedField (K := K) (L := L) σ))) :=
  degreeOneChebotarevPrimeSet (R := K) (T := ↥(step2FixedField (K := K) (L := L) σ)) (S := L)
    (G := Gal(L/↥(step2FixedField (K := K) (L := L) σ))) p
    (step2FrobClass (K := K) (L := L) σ)

theorem mem_step2FiberOver_iff (p : Ideal K)
    (Q : Ideal (↥(step2FixedField (K := K) (L := L) σ))) :
    Q ∈ step2FiberOver (K := K) (L := L) σ p ↔
      degreeOneChebotarevPrime (R := K) (T := ↥(step2FixedField (K := K) (L := L) σ)) (S := L)
        (G := Gal(L/↥(step2FixedField (K := K) (L := L) σ))) p Q
        (step2FrobClass (K := K) (L := L) σ) :=
  Iff.rfl

theorem mem_step2FiberOver_of_mem_step2DegreeOne (p : Ideal K)
    (Q : Ideal (↥(step2FixedField (K := K) (L := L) σ)))
    (hQ : Q ∈ step2DegreeOneChebotarevSet (K := K) (L := L) σ) (hp : Q.LiesOver p) :
    Q ∈ step2FiberOver (K := K) (L := L) σ p := by
  rcases hQ with ⟨p', hp'⟩
  have hp'eq : p' = p := hp'.2.1.over.trans hp.over.symm
  subst hp'eq
  exact hp'

/-- Sharifi's combinatorial identity `|Cl(σ)| = [G : Z(σ)]`. -/
theorem step2_card_conjClass_eq_centralizerIndex :
    Nat.card (ConjClasses.mk σ).carrier =
      (Subgroup.centralizer ({σ} : Set (Gal(L/K)))).index :=
  Chebotarev.nat_card_conjClass_eq_index_centralizer (G := Gal(L/K)) σ

/--
Sharifi Step 2 counting target (open): for `p ∈ S_{Cl(σ)}`, the fiber of `T_σ` above `p` has
cardinality `[G : Z(σ)]`.
-/
def Step2PrimeCountingHypothesis : Prop :=
  ∀ p : Ideal K, p ∈ step2ChebotarevSet (K := K) (L := L) σ →
    Nat.card (step2FiberOver (K := K) (L := L) σ p) =
      (Subgroup.centralizer ({σ} : Set (Gal(L/K)))).index

/--
The counting target equivalently asks for the fiber cardinality to equal `|Cl(σ)|`
(`step2_card_conjClass_eq_centralizerIndex`).
-/
theorem Step2PrimeCountingHypothesis_iff_conjClassCard :
    Step2PrimeCountingHypothesis (K := K) (L := L) σ ↔
      ∀ p : Ideal K, p ∈ step2ChebotarevSet (K := K) (L := L) σ →
        Nat.card (step2FiberOver (K := K) (L := L) σ p) =
          Nat.card (ConjClasses.mk σ).carrier := by
  constructor
  · intro h p hp
    rw [step2_card_conjClass_eq_centralizerIndex (K := K) (L := L) σ]
    exact h p hp
  · intro h p hp
    rw [← step2_card_conjClass_eq_centralizerIndex (K := K) (L := L) σ]
    exact h p hp

/-- Sharifi's predicted densities at Step 2: `|C|/|G|` vs `1/[L:E]`. -/
theorem step2DensityTargets_eq :
    chebotarevDensityTarget (G := Gal(L/K)) σ =
      (Nat.card (ConjClasses.mk σ).carrier : ℂ) / (Nat.card (Gal(L/K)) : ℂ) ∧
    cyclicSubextensionDensityTarget (G := Gal(L/K)) σ =
      (Module.finrank (step2FixedField (K := K) (L := L) σ) L : ℂ)⁻¹ := by
  constructor
  · rfl
  · exact step2IntermediateDensityTarget_eq_inv_finrank (K := K) (L := L) σ

end Step2NumberField

end Chebotarev

end PrimeNumberTheoremAnd
