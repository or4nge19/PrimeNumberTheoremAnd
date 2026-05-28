import PrimeNumberTheoremAnd.Chebotarev.Algebraic.ReductionStep2
import PrimeNumberTheoremAnd.Chebotarev.Algebraic.ChebotarevPrimeIdeals
import PrimeNumberTheoremAnd.Chebotarev.Algebraic.GaloisInstances

import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
## Sharifi Step 2: splitting and fiber counting (scaffold)

Sharifi's Step 2 bijection compares

* base Chebotarev primes `p ∈ S_{Cl(σ)}` in `K`;
* intermediate primes `Q` of `E = L^{⟨σ⟩}` lying over `p`, unramified in `L/E`, of degree `1` over `K`,
  with Frobenius `σ` in `Gal(L/E)`.

This file connects the fiber `step2FiberOver p` to mathlib's `p.primesOver E` and proves the
Galois tower identity from `Ideal.ncard_primesOver_mul_ncard_primesOver` (under `[IsGalois K E]`)
as algebraic input toward `Step2PrimeCountingHypothesis`.
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev

open scoped Classical

section Step2Splitting

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]
variable (σ : Gal(L/K))
variable [Finite (Gal(L/K))]
variable [IsGalois K L]
variable [MulSemiringAction (Gal(L/K)) L] [SMulCommClass (Gal(L/K)) K L]
variable [Algebra.IsInvariant K L (Gal(L/K))]
variable [MulSemiringAction (Gal(L/↥(step2FixedField (K := K) (L := L) σ))) L]
variable [SMulCommClass (Gal(L/↥(step2FixedField (K := K) (L := L) σ)))
  (↥(step2FixedField (K := K) (L := L) σ)) L]
variable [Algebra.IsInvariant (↥(step2FixedField (K := K) (L := L) σ)) L
  (Gal(L/↥(step2FixedField (K := K) (L := L) σ)))]

open Ideal NumberField

/-- All prime ideals of `E = L^{⟨σ⟩}` lying over the base prime `p`. -/
def step2PrimesOver (p : Ideal K) : Set (Ideal (↥(step2FixedField (K := K) (L := L) σ))) :=
  p.primesOver (↥(step2FixedField (K := K) (L := L) σ))

theorem mem_step2PrimesOver_iff (p : Ideal K)
    (Q : Ideal (↥(step2FixedField (K := K) (L := L) σ))) :
    Q ∈ step2PrimesOver (K := K) (L := L) σ p ↔ Q.IsPrime ∧ Q.LiesOver p :=
  Iff.rfl

theorem step2FiberOver_subset_step2PrimesOver (p : Ideal K) :
    step2FiberOver (K := K) (L := L) σ p ⊆ step2PrimesOver (K := K) (L := L) σ p := by
  intro Q hQ
  exact ⟨hQ.1, hQ.2.1⟩

/--
Sharifi's `T_σ` set, reindexed as prime ideals of `E` (for ideal Dirichlet density).
-/
def step2DegreeOneChebotarevPrimeIdealSet :
    Set (DirichletDensity.PrimeIdeal (↥(step2FixedField (K := K) (L := L) σ))) :=
  {Q | Q.1 ∈ step2DegreeOneChebotarevSet (K := K) (L := L) σ}

theorem mem_step2DegreeOneChebotarevPrimeIdealSet_iff
    (Q : DirichletDensity.PrimeIdeal (↥(step2FixedField (K := K) (L := L) σ))) :
    Q ∈ step2DegreeOneChebotarevPrimeIdealSet (K := K) (L := L) σ ↔
      Q.1 ∈ step2DegreeOneChebotarevSet (K := K) (L := L) σ :=
  Iff.rfl

/--
Sharifi's base Chebotarev set `S_{Cl(σ)}`, reindexed as prime ideals of `K`.
-/
def step2ChebotarevPrimeIdealSet : Set (DirichletDensity.PrimeIdeal K) :=
  chebotarevPrimeIdealSet (R := K) (S := L) (G := Gal(L/K))
    (step2FrobClassInGalLK (K := K) (L := L) σ)

theorem mem_step2ChebotarevPrimeIdealSet_iff (P : DirichletDensity.PrimeIdeal K) :
    P ∈ step2ChebotarevPrimeIdealSet (K := K) (L := L) σ ↔
      P.1 ∈ step2ChebotarevSet (K := K) (L := L) σ := by
  simp [step2ChebotarevPrimeIdealSet, mem_chebotarevPrimeIdealSet_iff,
    step2ChebotarevSet_eq (K := K) (L := L) σ, mem_chebotarevSet_iff]

/--
Sharifi Step 2 counting target, expressed using `Nat.card` on the fiber over `p.primesOver E`.
This is definitionally the same as `Step2PrimeCountingHypothesis`.
-/
theorem step2PrimeCountingHypothesis_iff :
    Step2PrimeCountingHypothesis (K := K) (L := L) σ ↔
      ∀ p : Ideal K, p ∈ step2ChebotarevSet (K := K) (L := L) σ →
        Nat.card (step2FiberOver (K := K) (L := L) σ p) =
          (Subgroup.centralizer ({σ} : Set (Gal(L/K)))).index :=
  Iff.rfl

end Step2Splitting

section Step2TowerIdentity

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]
variable (σ : Gal(L/K))
variable [Finite (Gal(L/K))]
variable [IsGalois K L]
variable [IsGalois K (↥(step2FixedField (K := K) (L := L) σ))]

open Ideal NumberField

/--
The Galois tower identity underlying Sharifi's counting at rings of integers:
`(p.primesOver 𝓞E).ncard * (Q.primesOver 𝓞L).ncard = (p.primesOver 𝓞L).ncard`.

This is `Ideal.ncard_primesOver_mul_ncard_primesOver` in the `𝓞K / 𝓞E / 𝓞L` tower.
The Step 2 bijection then filters to degree-one intermediate primes and identifies Frobenius `σ`.

**Note:** `E/K` must be Galois for the base step of the tower (`Gal(E/K)` on `𝓞E`). The top step
`L/E` is always Galois when `L/K` is Galois (`isGalois_step2FixedField_L`).
-/
def Step2TowerCountingHypothesis : Prop :=
  ∀ (p : Ideal (𝓞 K)) [p.IsMaximal] (hp : p ≠ ⊥)
    (Q : Ideal (𝓞 ↥(step2FixedField (K := K) (L := L) σ))) [Q.IsMaximal] [Q.LiesOver p],
    (p.primesOver (𝓞 ↥(step2FixedField (K := K) (L := L) σ))).ncard *
      (Q.primesOver (𝓞 L)).ncard = (p.primesOver (𝓞 L)).ncard

/-- `L / L^{⟨σ⟩}` is Galois when `L/K` is Galois (Sharifi Step 2 cyclic subextension). -/
theorem isGalois_step2FixedField_L : IsGalois (↥(step2FixedField (K := K) (L := L) σ)) L :=
  isGalois_fixedFieldZpowers_L (K := K) (L := L) σ

/-- Sharifi Step 2: prime-counting tower identity in the `𝓞K / 𝓞E / 𝓞L` tower. -/
theorem step2_ncard_primesOver_mul_ncard_primesOver
    (p : Ideal (𝓞 K)) [p.IsMaximal] (hp : p ≠ ⊥)
    (Q : Ideal (𝓞 ↥(step2FixedField (K := K) (L := L) σ))) [Q.IsMaximal] [Q.LiesOver p] :
    (p.primesOver (𝓞 ↥(step2FixedField (K := K) (L := L) σ))).ncard *
      (Q.primesOver (𝓞 L)).ncard = (p.primesOver (𝓞 L)).ncard := by
  let E := ↥(step2FixedField (K := K) (L := L) σ)
  haveI : IsGalois E L := isGalois_step2FixedField_L (K := K) (L := L) σ
  haveI : NumberField E :=
    NumberField.of_intermediateField (step2FixedField (K := K) (L := L) σ)
  exact Ideal.ncard_primesOver_mul_ncard_primesOver (A := 𝓞 K) (B := 𝓞 E) (C := 𝓞 L)
    (P := Q) hp (G := Gal(E/K)) (GAC := Gal(L/K)) (GBC := Gal(L/E))

theorem step2TowerCountingHypothesis :
    Step2TowerCountingHypothesis (K := K) (L := L) σ :=
  fun p _ hp Q _ _ =>
    step2_ncard_primesOver_mul_ncard_primesOver (K := K) (L := L) σ p hp Q

/-- When `⟨σ⟩ ⊴ Gal(L/K)`, the intermediate field `E = L^{⟨σ⟩}` is Galois over `K`. -/
instance step2IsGaloisIntermediateField [Subgroup.Normal (Subgroup.zpowers σ)] :
    IsGalois K (↥(step2FixedField (K := K) (L := L) σ)) := by
  simpa [step2FixedField, fixedFieldZpowers] using
    isGalois_fixedFieldZpowers_K (K := K) (L := L) σ

end Step2TowerIdentity

end Chebotarev

end PrimeNumberTheoremAnd
