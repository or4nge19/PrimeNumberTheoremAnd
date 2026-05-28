import PrimeNumberTheoremAnd.Chebotarev.Algebraic.ReductionStep2RingOfIntegers
import PrimeNumberTheoremAnd.Chebotarev.Algebraic.ReductionStep2Splitting
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.RamificationInertia.UnramifiedBase

import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.Data.Set.Card

set_option linter.unusedSectionVars false

/-!
## Sharifi Step 2: counting scaffold (rings of integers)

This file connects the proved tower identity (`ReductionStep2Splitting`) and the canonical
Step 2 sets on rings of integers (`ReductionStep2RingOfIntegers`) to the open fiber-counting
target `Step2PrimeCountingHypothesisRO`.

The bijection identifying `|step2FiberOverRO p|` with `[Gal(L/K) : Z(σ)]` remains open;
this module records the proved guardrails, splitting formulas, and the refined sub-hypotheses.

**Proved here:** unramified splitting identities (`r·f = |G|` at `𝓞 L` and `𝓞 E`), tower link
to `step2PrimesOverRO`, `frobClassOver = Cl(σ)` on `step2ChebotarevSetRO`, orbit–stabilizer
identities, trivial decomposition groups on the fiber (`|D(Q)| = 1`), fiber factorization on
`S_{Cl(σ)}`, and matching residue cardinalities at degree-one intermediate primes
(`natCard_residue_eq_of_mem_step2DegreeOnePrimesOverRO`).

The open targets are `Step2FrobRestrictionHypothesisRO` and
`Step2PrimeCountingHypothesisRO` (both `sorry` in `OpenHypotheses.lean`).
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev

open scoped Classical Pointwise
open NumberField

section Step2Counting

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]
variable (σ : Gal(L/K))
variable [Finite (Gal(L/K))]
variable [IsGalois K L]
variable [IsGalois K (↥(step2FixedField (K := K) (L := L) σ))]

attribute [local instance] FractionRing.liftAlgebra

noncomputable local instance instIsGaloisGroupGalLKCounting :
    IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing (G := Gal(L/K)) (A := 𝓞 K) (B := 𝓞 L) (K := K) (L := L)

noncomputable local instance instIsGaloisGroupGalEK :
    IsGaloisGroup Gal(↥(step2FixedField (K := K) (L := L) σ)/K) (𝓞 K)
    (𝓞 (step2E (K := K) (L := L) σ)) :=
  IsGaloisGroup.of_isFractionRing (G := Gal(↥(step2FixedField (K := K) (L := L) σ)/K))
    (A := 𝓞 K) (B := 𝓞 (step2E (K := K) (L := L) σ)) (K := K)
    (L := ↥(step2FixedField (K := K) (L := L) σ))

noncomputable local instance instIsGaloisGroupGalLECounting :
    IsGaloisGroup Gal(L/↥(step2FixedField (K := K) (L := L) σ))
    (𝓞 (step2E (K := K) (L := L) σ)) (𝓞 L) := by
  haveI : IsGalois (↥(step2FixedField (K := K) (L := L) σ)) L :=
    isGalois_fixedFieldZpowers_L (K := K) (L := L) σ
  exact IsGaloisGroup.of_isFractionRing (G := Gal(L/↥(step2FixedField (K := K) (L := L) σ)))
    (A := 𝓞 (step2E (K := K) (L := L) σ)) (B := 𝓞 L)
    (K := ↥(step2FixedField (K := K) (L := L) σ)) (L := L)

open Ideal

private lemma ramificationIdxIn_eq_one_of_isUnramifiedIn
    {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra (𝓞 K) S]
    (p : Ideal (𝓞 K)) [p.IsMaximal] (P : Ideal S) [P.IsMaximal] [P.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G (𝓞 K) S]
    (hunram : Ideal.IsUnramifiedIn (R := 𝓞 K) (S := S) p) :
    p.ramificationIdxIn S = 1 := by
  have hram : p.ramificationIdx P = 1 := hunram inferInstance inferInstance
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (p := p) (P := P) (G := G)]
  exact hram

/-- Intermediate primes of `𝓞 E` over `p` that have inertia degree `1` over `𝓞 K`. -/
def step2DegreeOnePrimesOverRO (p : Ideal (𝓞 K)) :
    Set (Ideal (𝓞 (step2E (K := K) (L := L) σ))) :=
  {Q | Q ∈ step2PrimesOverRO (K := K) (L := L) σ p ∧ p.inertiaDeg Q = 1}

theorem mem_step2DegreeOnePrimesOverRO_iff (p : Ideal (𝓞 K))
    (Q : Ideal (𝓞 (step2E (K := K) (L := L) σ))) :
    Q ∈ step2DegreeOnePrimesOverRO (K := K) (L := L) σ p ↔
      Q.IsPrime ∧ Q.LiesOver p ∧ p.inertiaDeg Q = 1 := by
  simp [step2DegreeOnePrimesOverRO, mem_step2PrimesOverRO_iff, and_assoc]

theorem step2DegreeOnePrimesOverRO_subset_step2PrimesOverRO (p : Ideal (𝓞 K)) :
    step2DegreeOnePrimesOverRO (K := K) (L := L) σ p ⊆
      step2PrimesOverRO (K := K) (L := L) σ p := by
  intro Q hQ
  exact hQ.1

theorem step2FiberOverRO_subset_step2DegreeOneChebotarevSetRO (p : Ideal (𝓞 K)) :
    step2FiberOverRO (K := K) (L := L) σ p ⊆
      step2DegreeOneChebotarevSetRO (K := K) (L := L) σ := by
  intro Q hQ
  rw [mem_step2FiberOverRO_iff] at hQ
  exact ⟨p, hQ⟩

theorem step2FiberOverRO_subset_step2DegreeOnePrimesOverRO (p : Ideal (𝓞 K)) :
    step2FiberOverRO (K := K) (L := L) σ p ⊆
      step2DegreeOnePrimesOverRO (K := K) (L := L) σ p := by
  intro Q hQmem
  rw [mem_step2FiberOverRO_iff] at hQmem
  have hOver : Q ∈ step2PrimesOverRO (K := K) (L := L) σ p :=
    step2FiberOverRO_subset_step2PrimesOverRO (K := K) (L := L) σ p hQmem
  exact ⟨hOver, hQmem.2.2.2.1⟩

/--
When `Q` is degree-one over `p`, the Frobenius congruence at `P` above `Q` uses the same
residue cardinality `#(𝓞 K/p) = #(𝓞 E/Q)` (`natCard_residue_eq_of_mem_step2DegreeOnePrimesOverRO`).
This is the input behind `Step2FrobRestrictionHypothesisRO`.
-/
theorem natCard_residue_eq_of_mem_step2DegreeOnePrimesOverRO
    (p : Ideal (𝓞 K)) [p.IsMaximal] (hpne : p ≠ ⊥)
    (Q : Ideal (𝓞 (step2E (K := K) (L := L) σ))) [Q.IsMaximal] [Q.LiesOver p]
    (hQ : Q ∈ step2DegreeOnePrimesOverRO (K := K) (L := L) σ p) :
    Nat.card (𝓞 K ⧸ p) = Nat.card (𝓞 (step2E (K := K) (L := L) σ) ⧸ Q) := by
  have hpprime : p.IsPrime := inferInstance
  rw [← Submodule.cardQuot_apply (R := 𝓞 K) (M := 𝓞 K),
    ← Submodule.cardQuot_apply (R := 𝓞 (step2E (K := K) (L := L) σ)) (M := 𝓞 (step2E (K := K) (L := L) σ)),
    ← Ideal.absNorm_apply (S := 𝓞 K), ← Ideal.absNorm_apply (S := 𝓞 (step2E (K := K) (L := L) σ)),
    Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver Q p hpprime hpne, hQ.2, pow_one]

theorem natCard_residue_eq_of_mem_step2FiberOverRO
    (p : Ideal (𝓞 K)) [p.IsMaximal] (hpne : p ≠ ⊥)
    (Q : Ideal (𝓞 (step2E (K := K) (L := L) σ))) [Q.IsMaximal] [Q.LiesOver p]
    (hQ : Q ∈ step2FiberOverRO (K := K) (L := L) σ p) :
    Nat.card (𝓞 K ⧸ p) = Nat.card (𝓞 (step2E (K := K) (L := L) σ) ⧸ Q) :=
  natCard_residue_eq_of_mem_step2DegreeOnePrimesOverRO (K := K) (L := L) σ p hpne Q
    (step2FiberOverRO_subset_step2DegreeOnePrimesOverRO (K := K) (L := L) σ p hQ)

theorem mem_step2FiberOverRO_iff_unpacked (p : Ideal (𝓞 K))
    (Q : Ideal (𝓞 (step2E (K := K) (L := L) σ))) :
    Q ∈ step2FiberOverRO (K := K) (L := L) σ p ↔
      Q.IsPrime ∧
        Q.LiesOver p ∧
          Ideal.IsUnramifiedAbove (T := 𝓞 (step2E (K := K) (L := L) σ)) (S := 𝓞 L) Q ∧
            p.inertiaDeg Q = 1 ∧
              HasFrobClass (R := 𝓞 (step2E (K := K) (L := L) σ)) (S := 𝓞 L)
                (G := Gal(L/↥(step2FixedField (K := K) (L := L) σ))) Q
                (step2FrobClass (K := K) (L := L) σ) := by
  simp [mem_step2FiberOverRO_iff, degreeOneChebotarevPrime]

theorem step2FiberOverRO_ncard_le_step2PrimesOverRO_ncard (p : Ideal (𝓞 K)) [p.IsMaximal] :
    (step2FiberOverRO (K := K) (L := L) σ p).ncard ≤
      (step2PrimesOverRO (K := K) (L := L) σ p).ncard := by
  rw [step2PrimesOverRO]
  refine Set.ncard_le_ncard (step2FiberOverRO_subset_step2PrimesOverRO (K := K) (L := L) σ p) ?_
  exact IsDedekindDomain.primesOver_finite (p := p) (B := 𝓞 (step2E (K := K) (L := L) σ))

theorem isUnramifiedIn_of_mem_step2ChebotarevSetRO (p : Ideal (𝓞 K))
    (hp : p ∈ step2ChebotarevSetRO (K := K) (L := L) σ) :
    Ideal.IsUnramifiedIn (R := 𝓞 K) (S := 𝓞 L) p := by
  rw [mem_step2ChebotarevSetRO_iff] at hp
  exact hp.2.1

theorem isPrime_of_mem_step2ChebotarevSetRO (p : Ideal (𝓞 K))
    (hp : p ∈ step2ChebotarevSetRO (K := K) (L := L) σ) :
    p.IsPrime := by
  rw [mem_step2ChebotarevSetRO_iff] at hp
  exact hp.1

theorem hasFiniteResidueOver_of_mem_step2ChebotarevSetRO (p : Ideal (𝓞 K))
    (hp : p ∈ step2ChebotarevSetRO (K := K) (L := L) σ) :
    HasFiniteResidueOver (R := 𝓞 K) (S := 𝓞 L) p := by
  rw [mem_step2ChebotarevSetRO_iff] at hp
  rcases hp.2.2 with ⟨hP, _⟩
  exact hP

theorem frobClassOver_eq_mk_of_mem_step2ChebotarevSetRO (p : Ideal (𝓞 K))
    (hp : p ∈ step2ChebotarevSetRO (K := K) (L := L) σ) :
    frobClassOver (R := 𝓞 K) (S := 𝓞 L) (G := Gal(L/K)) p
      (hasFiniteResidueOver_of_mem_step2ChebotarevSetRO (K := K) (L := L) σ p hp) =
      ConjClasses.mk σ := by
  rw [mem_step2ChebotarevSetRO_iff] at hp
  rw [hasUnramifiedFrobClass_iff (P := p) (C := ConjClasses.mk σ)
    (hP := hasFiniteResidueOver_of_mem_step2ChebotarevSetRO (K := K) (L := L) σ p hp)] at hp
  exact hp.2.2

theorem isUnramifiedIn_of_mem_step2ChebotarevSetRO_at_E (p : Ideal (𝓞 K)) [p.IsMaximal]
    (hpne : p ≠ ⊥) (hp : p ∈ step2ChebotarevSetRO (K := K) (L := L) σ) :
    Ideal.IsUnramifiedIn (R := 𝓞 K) (S := 𝓞 (step2E (K := K) (L := L) σ)) p :=
  Ideal.isUnramifiedIn_trans (P := p) (hPne := hpne)
    (isUnramifiedIn_of_mem_step2ChebotarevSetRO (K := K) (L := L) σ p hp)

/--
Every intermediate prime over `p ∈ S_{Cl(σ)}` is unramified above in `𝓞 L / 𝓞 E`.
-/
theorem isUnramifiedAbove_of_mem_step2ChebotarevSetRO
    (p : Ideal (𝓞 K)) [p.IsMaximal] (hpne : p ≠ ⊥)
    (Q : Ideal (𝓞 (step2E (K := K) (L := L) σ))) [Q.IsPrime] [Q.LiesOver p]
    (hp : p ∈ step2ChebotarevSetRO (K := K) (L := L) σ) :
    Ideal.IsUnramifiedAbove (T := 𝓞 (step2E (K := K) (L := L) σ)) (S := 𝓞 L) Q :=
  Ideal.isUnramifiedAbove_of_isUnramifiedIn (P := p) (hPne := hpne)
    (isUnramifiedIn_of_mem_step2ChebotarevSetRO (K := K) (L := L) σ p hp)

theorem inertiaDegIn_eq_one_of_mem_step2DegreeOnePrimesOverRO
    (p : Ideal (𝓞 K)) [p.IsMaximal]
    (Q : Ideal (𝓞 (step2E (K := K) (L := L) σ))) [Q.IsMaximal] [Q.LiesOver p]
    (hQ : Q ∈ step2DegreeOnePrimesOverRO (K := K) (L := L) σ p) :
    p.inertiaDegIn (𝓞 (step2E (K := K) (L := L) σ)) = 1 := by
  rw [Ideal.inertiaDegIn_eq_inertiaDeg (p := p) (P := Q)
    (G := Gal(↥(step2FixedField (K := K) (L := L) σ)/K))]
  exact hQ.2

theorem mem_step2FiberOverRO_iff_degreeOne_frob_of_mem_step2ChebotarevSetRO
    (p : Ideal (𝓞 K)) [p.IsMaximal] (hpne : p ≠ ⊥)
    (hp : p ∈ step2ChebotarevSetRO (K := K) (L := L) σ)
    (Q : Ideal (𝓞 (step2E (K := K) (L := L) σ))) :
    Q ∈ step2FiberOverRO (K := K) (L := L) σ p ↔
      Q ∈ step2DegreeOnePrimesOverRO (K := K) (L := L) σ p ∧
        step2HasIntermediateFrobClassRO (K := K) (L := L) σ Q := by
  constructor
  · intro hQmem
    rw [mem_step2FiberOverRO_iff_unpacked] at hQmem
    exact ⟨step2FiberOverRO_subset_step2DegreeOnePrimesOverRO (K := K) (L := L) σ p hQmem,
      hQmem.2.2.2.2⟩
  · intro hQmem
    rw [mem_step2FiberOverRO_iff_unpacked]
    rcases hQmem with ⟨hdeg, hfrob⟩
    rw [mem_step2DegreeOnePrimesOverRO_iff] at hdeg
    haveI : Q.IsPrime := hdeg.1
    haveI : Q.LiesOver p := hdeg.2.1
    exact ⟨hdeg.1, hdeg.2.1,
      isUnramifiedAbove_of_mem_step2ChebotarevSetRO (K := K) (L := L) σ p hpne Q hp, hdeg.2.2, hfrob⟩

/--
On `p ∈ S_{Cl(σ)}`, Sharifi's fiber is exactly the degree-one primes above `p` with
intermediate Frobenius class `step2FrobClass σ` (unramified-above is automatic on this base set).
-/
theorem step2FiberOverRO_eq_degreeOne_inter_frob_of_mem_step2ChebotarevSetRO
    (p : Ideal (𝓞 K)) [p.IsMaximal] (hpne : p ≠ ⊥)
    (hp : p ∈ step2ChebotarevSetRO (K := K) (L := L) σ) :
    step2FiberOverRO (K := K) (L := L) σ p =
      step2DegreeOnePrimesOverRO (K := K) (L := L) σ p ∩
        step2IntermediateFrobClassPrimeSetRO (K := K) (L := L) σ := by
  ext Q
  simp only [Set.mem_inter_iff, mem_step2IntermediateFrobClassPrimeSetRO_iff,
    step2HasIntermediateFrobClassRO_iff]
  exact mem_step2FiberOverRO_iff_degreeOne_frob_of_mem_step2ChebotarevSetRO (K := K) (L := L) σ p hpne hp Q

/--
On `p ∈ S_{Cl(σ)}`, fiber membership in witness-free form at the intermediate prime.
-/
theorem mem_step2FiberOverRO_iff_frobClassOver_of_mem_step2ChebotarevSetRO
    (p : Ideal (𝓞 K)) [p.IsMaximal] (hpne : p ≠ ⊥)
    (hp : p ∈ step2ChebotarevSetRO (K := K) (L := L) σ)
    (Q : Ideal (𝓞 (step2E (K := K) (L := L) σ))) [Q.IsMaximal] (hQne : Q ≠ ⊥) :
    Q ∈ step2FiberOverRO (K := K) (L := L) σ p ↔
      Q ∈ step2DegreeOnePrimesOverRO (K := K) (L := L) σ p ∧
        frobClassOver (R := 𝓞 (step2E (K := K) (L := L) σ)) (S := 𝓞 L)
          (G := Gal(L/↥(step2FixedField (K := K) (L := L) σ))) Q
          (hasFiniteResidueOver_of_numberField (K := step2E (K := K) (L := L) σ) (L := L) Q hQne) =
            step2FrobClass (K := K) (L := L) σ := by
  rw [mem_step2FiberOverRO_iff_degreeOne_frob_of_mem_step2ChebotarevSetRO (K := K) (L := L) σ p hpne hp,
    step2HasIntermediateFrobClassRO_iff_frobClassOver (K := K) (L := L) σ Q hQne]

/--
For `Q` degree-one over `p`, inertia degree in the tower `𝓞 K / 𝓞 E / 𝓞 L` satisfies
`p.inertiaDeg P = Q.inertiaDeg P` for any `P` above `Q`.
-/
theorem inertiaDeg_at_OL_eq_inertiaDeg_from_E_of_mem_step2DegreeOnePrimesOverRO
    (p : Ideal (𝓞 K)) [p.IsMaximal]
    (Q : Ideal (𝓞 (step2E (K := K) (L := L) σ))) [Q.IsMaximal] [Q.LiesOver p]
    (P : Ideal (𝓞 L)) [P.IsMaximal] [P.LiesOver Q]
    (hQ : Q ∈ step2DegreeOnePrimesOverRO (K := K) (L := L) σ p) :
    p.inertiaDeg P = Q.inertiaDeg P := by
  have hpdeg : p.inertiaDeg Q = 1 := hQ.2
  have htower := Ideal.inertiaDeg_algebra_tower (R := 𝓞 K) (S := 𝓞 (step2E (K := K) (L := L) σ))
    (T := 𝓞 L) p Q P
  rw [hpdeg, one_mul] at htower
  exact htower

/--
Fundamental identity at `𝓞 L` for an unramified base prime: `r * f = |Gal(L/K)|`.
-/
theorem ncard_primesOverOL_mul_inertiaDegIn_eq_card_gal_of_unramifiedIn
    (p : Ideal (𝓞 K)) [p.IsMaximal] (hp : p ≠ ⊥)
    (hunram : Ideal.IsUnramifiedIn (R := 𝓞 K) (S := 𝓞 L) p) :
    (p.primesOver (𝓞 L)).ncard * p.inertiaDegIn (𝓞 L) = Nat.card (Gal(L/K)) := by
  obtain ⟨P, hPmax, hPOver⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := 𝓞 K) (S := 𝓞 L) p
  haveI : P.IsMaximal := hPmax
  have hram : p.ramificationIdxIn (𝓞 L) = 1 :=
    ramificationIdxIn_eq_one_of_isUnramifiedIn (K := K) p P (G := Gal(L/K)) hunram
  have hmain := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (A := 𝓞 K) (B := 𝓞 L) hp (G := Gal(L/K))
  simp only [Nat.card_eq_fintype_card] at hmain
  aesop

/--
Fundamental identity at `𝓞 E` for an unramified base prime: `r_E * f_E = |Gal(E/K)|`.
-/
theorem ncard_primesOverOE_mul_inertiaDegIn_eq_card_galEK_of_unramifiedIn
    (p : Ideal (𝓞 K)) [p.IsMaximal] (hp : p ≠ ⊥)
    (hunram : Ideal.IsUnramifiedIn (R := 𝓞 K) (S := 𝓞 L) p) :
    (p.primesOver (𝓞 (step2E (K := K) (L := L) σ))).ncard *
      p.inertiaDegIn (𝓞 (step2E (K := K) (L := L) σ)) =
      Nat.card (Gal(↥(step2FixedField (K := K) (L := L) σ)/K)) := by
  let E := step2E (K := K) (L := L) σ
  have hunramE : Ideal.IsUnramifiedIn (R := 𝓞 K) (S := 𝓞 E) p :=
    Ideal.isUnramifiedIn_trans (P := p) (hPne := hp) hunram
  obtain ⟨Q, hQmax, hQOver⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := 𝓞 K) (S := 𝓞 E) p
  haveI : Q.IsMaximal := hQmax
  have hram : p.ramificationIdxIn (𝓞 E) = 1 :=
    ramificationIdxIn_eq_one_of_isUnramifiedIn (K := K) (S := 𝓞 E) p Q
      (G := Gal(↥(step2FixedField (K := K) (L := L) σ)/K)) hunramE
  have hmain := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (A := 𝓞 K) (B := 𝓞 E) hp (G := Gal(↥(step2FixedField (K := K) (L := L) σ)/K))
  simp only [fixedFieldZpowers_def] at hmain
  aesop

/--
Sharifi Step 2 tower identity for `step2PrimesOverRO` (specialization of
`step2_ncard_primesOver_mul_ncard_primesOver`).
-/
theorem step2_ncard_primesOverRO_mul_ncard_primesOver
    (p : Ideal (𝓞 K)) [p.IsMaximal] (hp : p ≠ ⊥)
    (Q : Ideal (𝓞 (step2E (K := K) (L := L) σ))) [Q.IsMaximal] [Q.LiesOver p] :
    (step2PrimesOverRO (K := K) (L := L) σ p).ncard * (Q.primesOver (𝓞 L)).ncard =
      (p.primesOver (𝓞 L)).ncard := by
  simpa [step2PrimesOverRO] using
    step2_ncard_primesOver_mul_ncard_primesOver (K := K) (L := L) σ p hp Q

theorem step2_ncard_primesOverRO_mul_inertiaDegIn_eq_card_galEK_of_mem_step2ChebotarevSetRO
    (p : Ideal (𝓞 K)) [p.IsMaximal] (hpne : p ≠ ⊥)
    (hp : p ∈ step2ChebotarevSetRO (K := K) (L := L) σ) :
    (step2PrimesOverRO (K := K) (L := L) σ p).ncard *
      p.inertiaDegIn (𝓞 (step2E (K := K) (L := L) σ)) =
      Nat.card (Gal(↥(step2FixedField (K := K) (L := L) σ)/K)) := by
  simpa [step2PrimesOverRO] using
    ncard_primesOverOE_mul_inertiaDegIn_eq_card_galEK_of_unramifiedIn (K := K) (L := L) (σ := σ) p hpne
      (isUnramifiedIn_of_mem_step2ChebotarevSetRO (K := K) (L := L) σ p hp)

/--
Sharifi's combinatorial identification of fiber cardinality with the centralizer index.
This is the hard Step 2 counting target, expressed on rings of integers.
-/
theorem step2PrimeCountingHypothesisRO_iff :
    Step2PrimeCountingHypothesisRO (K := K) (L := L) σ ↔
      ∀ p : Ideal (𝓞 K), p ∈ step2ChebotarevSetRO (K := K) (L := L) σ →
        Nat.card (step2FiberOverRO (K := K) (L := L) σ p) =
          (Subgroup.centralizer ({σ} : Set (Gal(L/K)))).index :=
  Iff.rfl

theorem step2PrimeCountingTarget_eq_card_conjClass :
    (Subgroup.centralizer ({σ} : Set (Gal(L/K)))).index =
      Nat.card (ConjClasses.mk σ).carrier :=
  (step2_card_conjClass_eq_centralizerIndexRO (K := K) (L := L) σ).symm

theorem step2PrimeCountingHypothesisRO_iff_card_conjClass :
    Step2PrimeCountingHypothesisRO (K := K) (L := L) σ ↔
      ∀ p : Ideal (𝓞 K), p ∈ step2ChebotarevSetRO (K := K) (L := L) σ →
        Nat.card (step2FiberOverRO (K := K) (L := L) σ p) =
          Nat.card (ConjClasses.mk σ).carrier := by
  simp [Step2PrimeCountingHypothesisRO, step2PrimeCountingTarget_eq_card_conjClass (K := K) (L := L) σ]

-- Fiber membership is `mem_step2FiberOverRO_iff`; the open Step 2 content is its cardinality.

theorem ncard_primesOverOL_mul_inertiaDegIn_eq_card_gal_of_mem_step2ChebotarevSetRO
    (p : Ideal (𝓞 K)) [p.IsMaximal] (hpne : p ≠ ⊥)
    (hp : p ∈ step2ChebotarevSetRO (K := K) (L := L) σ) :
    (p.primesOver (𝓞 L)).ncard * p.inertiaDegIn (𝓞 L) = Nat.card (Gal(L/K)) :=
  ncard_primesOverOL_mul_inertiaDegIn_eq_card_gal_of_unramifiedIn (K := K) (L := L) p hpne
    (isUnramifiedIn_of_mem_step2ChebotarevSetRO (K := K) (L := L) σ p hp)

theorem ncard_primesOverOE_mul_inertiaDegIn_eq_card_galEK_of_mem_step2ChebotarevSetRO
    (p : Ideal (𝓞 K)) [p.IsMaximal] (hpne : p ≠ ⊥)
    (hp : p ∈ step2ChebotarevSetRO (K := K) (L := L) σ) :
    (p.primesOver (𝓞 (step2E (K := K) (L := L) σ))).ncard *
      p.inertiaDegIn (𝓞 (step2E (K := K) (L := L) σ)) =
      Nat.card (Gal(↥(step2FixedField (K := K) (L := L) σ)/K)) :=
  ncard_primesOverOE_mul_inertiaDegIn_eq_card_galEK_of_unramifiedIn (K := K) (L := L) (σ := σ) p hpne
    (isUnramifiedIn_of_mem_step2ChebotarevSetRO (K := K) (L := L) σ p hp)

section OrbitStabilizer

open MulAction

/--
Orbit–stabilizer at `𝓞 L`: `|primesOver p| · |D(P)| = |Gal(L/K)|` for an unramified base prime.
-/
theorem ncard_primesOverOL_mul_card_stabilizer_eq_card_gal_of_unramifiedIn
    (p : Ideal (𝓞 K)) [p.IsMaximal]
    (P : Ideal (𝓞 L)) [P.IsMaximal] [P.LiesOver p]
    [Algebra.IsSeparable (𝓞 K ⧸ p) (𝓞 L ⧸ P)] :
    (p.primesOver (𝓞 L)).ncard * Nat.card (stabilizer Gal(L/K) P) = Nat.card (Gal(L/K)) := by
  have h := Ideal.ncard_primesOver_mul_card_inertia_mul_finrank (G := Gal(L/K)) (R := 𝓞 K)
    (S := 𝓞 L) p P
  rw [mul_assoc, ← Ideal.card_stabilizer_eq_card_inertia_mul_finrank (G := Gal(L/K)) (R := 𝓞 K)
    (S := 𝓞 L) p P] at h
  exact (Nat.card_eq_fintype_card (α := Gal(L/K))).symm ▸ h

/--
Orbit–stabilizer at `𝓞 E`: `|primesOver p| · |D(Q)| = |Gal(E/K)|` for an unramified base prime.
-/
theorem ncard_primesOverOE_mul_card_stabilizerGalEK_eq_card_galEK_of_unramifiedIn
    (p : Ideal (𝓞 K)) [p.IsMaximal]
    (Q : Ideal (𝓞 (step2E (K := K) (L := L) σ))) [Q.IsMaximal] [Q.LiesOver p]
    [Algebra.IsSeparable (𝓞 K ⧸ p) (𝓞 (step2E (K := K) (L := L) σ) ⧸ Q)] :
    (p.primesOver (𝓞 (step2E (K := K) (L := L) σ))).ncard *
      Nat.card (stabilizer Gal(↥(step2FixedField (K := K) (L := L) σ)/K) Q) =
      Nat.card (Gal(↥(step2FixedField (K := K) (L := L) σ)/K)) := by
  have h := Ideal.ncard_primesOver_mul_card_inertia_mul_finrank
    (G := Gal(↥(step2FixedField (K := K) (L := L) σ)/K)) (R := 𝓞 K)
    (S := 𝓞 (step2E (K := K) (L := L) σ)) p Q
  rw [mul_assoc, ← Ideal.card_stabilizer_eq_card_inertia_mul_finrank
    (G := Gal(↥(step2FixedField (K := K) (L := L) σ)/K)) (R := 𝓞 K)
    (S := 𝓞 (step2E (K := K) (L := L) σ)) p Q] at h
  exact (Nat.card_eq_fintype_card (α := Gal(↥(step2FixedField (K := K) (L := L) σ)/K))).symm ▸ h

theorem ncard_step2PrimesOverRO_mul_card_stabilizerGalEK_eq_card_galEK_of_unramifiedIn
    (p : Ideal (𝓞 K)) [p.IsMaximal]
    (Q : Ideal (𝓞 (step2E (K := K) (L := L) σ))) [Q.IsMaximal] [Q.LiesOver p]
    [Algebra.IsSeparable (𝓞 K ⧸ p) (𝓞 (step2E (K := K) (L := L) σ) ⧸ Q)] :
    (step2PrimesOverRO (K := K) (L := L) σ p).ncard *
      Nat.card (stabilizer Gal(↥(step2FixedField (K := K) (L := L) σ)/K) Q) =
      Nat.card (Gal(↥(step2FixedField (K := K) (L := L) σ)/K)) := by
  simpa [step2PrimesOverRO] using
    ncard_primesOverOE_mul_card_stabilizerGalEK_eq_card_galEK_of_unramifiedIn (K := K) (L := L)
      (σ := σ) p Q

theorem card_stabilizerGalEK_eq_inertiaDegIn_of_unramifiedIn_at_E
    (p : Ideal (𝓞 K)) [p.IsMaximal] (hp : p ≠ ⊥)
    (Q : Ideal (𝓞 (step2E (K := K) (L := L) σ))) [Q.IsMaximal] [Q.LiesOver p]
    (hunram : Ideal.IsUnramifiedIn (R := 𝓞 K) (S := 𝓞 L) p)
    [Algebra.IsSeparable (𝓞 K ⧸ p) (𝓞 (step2E (K := K) (L := L) σ) ⧸ Q)] :
    Nat.card (stabilizer Gal(↥(step2FixedField (K := K) (L := L) σ)/K) Q) =
      p.inertiaDegIn (𝓞 (step2E (K := K) (L := L) σ)) := by
  let E := step2E (K := K) (L := L) σ
  have hunramE : Ideal.IsUnramifiedIn (R := 𝓞 K) (S := 𝓞 E) p :=
    Ideal.isUnramifiedIn_trans (P := p) (hPne := hp) hunram
  have hram : p.ramificationIdxIn (𝓞 E) = 1 :=
    ramificationIdxIn_eq_one_of_isUnramifiedIn (K := K) (S := 𝓞 E) p Q
      (G := Gal(↥(step2FixedField (K := K) (L := L) σ)/K)) hunramE
  simpa [hram, one_mul] using
    Ideal.card_stabilizer_eq (G := Gal(↥(step2FixedField (K := K) (L := L) σ)/K)) (R := 𝓞 K)
      (S := 𝓞 E) p hp Q

/--
On the Sharifi fiber, inertia degree over `𝓞 K` is `1`, hence the decomposition group in
`Gal(E/K)` is trivial (`|D(Q)| = 1`).
-/
theorem card_stabilizerGalEK_eq_one_of_mem_step2FiberOverRO
    (p : Ideal (𝓞 K)) [p.IsMaximal] (hpne : p ≠ ⊥)
    (hp : p ∈ step2ChebotarevSetRO (K := K) (L := L) σ)
    (Q : Ideal (𝓞 (step2E (K := K) (L := L) σ))) [Q.IsMaximal] [Q.LiesOver p]
    (hQ : Q ∈ step2FiberOverRO (K := K) (L := L) σ p)
    [Algebra.IsSeparable (𝓞 K ⧸ p) (𝓞 (step2E (K := K) (L := L) σ) ⧸ Q)] :
    Nat.card (stabilizer Gal(↥(step2FixedField (K := K) (L := L) σ)/K) Q) = 1 := by
  let E := step2E (K := K) (L := L) σ
  have hunram : Ideal.IsUnramifiedIn (R := 𝓞 K) (S := 𝓞 L) p :=
    isUnramifiedIn_of_mem_step2ChebotarevSetRO (K := K) (L := L) σ p hp
  have hf : p.inertiaDegIn (𝓞 E) = 1 :=
    inertiaDegIn_eq_one_of_mem_step2DegreeOnePrimesOverRO (K := K) (L := L) σ p Q
      (step2FiberOverRO_subset_step2DegreeOnePrimesOverRO (K := K) (L := L) σ p hQ)
  have h := card_stabilizerGalEK_eq_inertiaDegIn_of_unramifiedIn_at_E (K := K) (L := L) (σ := σ) p
    hpne Q hunram
  rw [hf] at h
  exact h

theorem step2_ncard_primesOverRO_le_card_galEK_of_mem_step2ChebotarevSetRO
    (p : Ideal (𝓞 K)) [p.IsMaximal] (hpne : p ≠ ⊥)
    (hp : p ∈ step2ChebotarevSetRO (K := K) (L := L) σ) :
    (step2PrimesOverRO (K := K) (L := L) σ p).ncard ≤
      Nat.card (Gal(↥(step2FixedField (K := K) (L := L) σ)/K)) := by
  let E := step2E (K := K) (L := L) σ
  have hprod :=
    step2_ncard_primesOverRO_mul_inertiaDegIn_eq_card_galEK_of_mem_step2ChebotarevSetRO (K := K)
      (L := L) (σ := σ) p hpne hp
  have hfpos : 0 < p.inertiaDegIn (𝓞 E) := by
    have hfne : p.inertiaDegIn (𝓞 E) ≠ 0 :=
      Ideal.inertiaDegIn_ne_zero (G := Gal(↥(step2FixedField (K := K) (L := L) σ)/K))
    exact Nat.pos_of_ne_zero hfne
  have hf : 1 ≤ p.inertiaDegIn (𝓞 E) := Nat.one_le_of_lt hfpos
  have hle : (step2PrimesOverRO (K := K) (L := L) σ p).ncard ≤
      (step2PrimesOverRO (K := K) (L := L) σ p).ncard * p.inertiaDegIn (𝓞 E) := by
    simpa [Nat.mul_one] using Nat.mul_le_mul_left _ hf
  exact hle.trans_eq hprod

theorem step2DegreeOnePrimesOverRO_ncard_le_card_galEK_of_mem_step2ChebotarevSetRO
    (p : Ideal (𝓞 K)) [p.IsMaximal] (hpne : p ≠ ⊥)
    (hp : p ∈ step2ChebotarevSetRO (K := K) (L := L) σ) :
    (step2DegreeOnePrimesOverRO (K := K) (L := L) σ p).ncard ≤
      Nat.card (Gal(↥(step2FixedField (K := K) (L := L) σ)/K)) :=
  Nat.le_trans
    (Set.ncard_le_ncard (step2DegreeOnePrimesOverRO_subset_step2PrimesOverRO (K := K) (L := L) σ p)
      (IsDedekindDomain.primesOver_finite (p := p) (B := 𝓞 (step2E (K := K) (L := L) σ))))
    (step2_ncard_primesOverRO_le_card_galEK_of_mem_step2ChebotarevSetRO (K := K) (L := L) (σ := σ)
      p hpne hp)

theorem step2FiberOverRO_ncard_le_card_galEK_of_mem_step2ChebotarevSetRO
    (p : Ideal (𝓞 K)) [p.IsMaximal] (hpne : p ≠ ⊥)
    (hp : p ∈ step2ChebotarevSetRO (K := K) (L := L) σ) :
    (step2FiberOverRO (K := K) (L := L) σ p).ncard ≤
      Nat.card (Gal(↥(step2FixedField (K := K) (L := L) σ)/K)) :=
  Nat.le_trans (step2FiberOverRO_ncard_le_step2PrimesOverRO_ncard (K := K) (L := L) σ p)
    (step2_ncard_primesOverRO_le_card_galEK_of_mem_step2ChebotarevSetRO (K := K) (L := L) (σ := σ)
      p hpne hp)

/--
Open refinement: identify `|step2FiberOverRO p|` with the number of degree-one intermediate
primes above `p` whose Frobenius in `Gal(L/E)` is `step2FrobClass σ`, using decomposition groups
and the known identity `frobClassOver p = Cl(σ)`.
-/
def Step2FiberFrobeniusCountHypothesisRO : Prop :=
  ∀ p : Ideal (𝓞 K), p ∈ step2ChebotarevSetRO (K := K) (L := L) σ →
    (step2FiberOverRO (K := K) (L := L) σ p).ncard =
      Nat.card (ConjClasses.mk σ).carrier

theorem step2PrimeCountingHypothesisRO_iff_fiberFrobeniusCount :
    Step2PrimeCountingHypothesisRO (K := K) (L := L) σ ↔
      Step2FiberFrobeniusCountHypothesisRO (K := K) (L := L) σ := by
  simp [Step2PrimeCountingHypothesisRO, Step2FiberFrobeniusCountHypothesisRO,
    step2PrimeCountingTarget_eq_card_conjClass (K := K) (L := L) σ]

/--
Open (prime-level Frobenius restriction): for unramified `p` and a tower `P` above `Q` above `p`,
the Frobenius class at `P` in `Gal(L/E)` (base `𝓞 E`) pushes forward under `galInclusion` to
the Frobenius class at `P` in `Gal(L/K)` (base `𝓞 K`). This is the missing Galois input for
Sharifi's fiber bijection; the abstract class-level version is `step2FrobClassInGalLK_eq`.
On the fiber, `#(𝓞 K/p) = #(𝓞 E/Q)` is proved (`natCard_residue_eq_of_mem_step2FiberOverRO`).
-/
def Step2FrobRestrictionHypothesisRO : Prop :=
  ∀ (p : Ideal (𝓞 K)) [p.IsMaximal],
    Ideal.IsUnramifiedIn (R := 𝓞 K) (S := 𝓞 L) p →
      ∀ (Q : Ideal (𝓞 (step2E (K := K) (L := L) σ))) [Q.IsMaximal] [Q.LiesOver p]
        (P : Ideal (𝓞 L)) [P.IsMaximal] [P.LiesOver Q] [Finite (𝓞 L ⧸ P)],
        ConjClasses.map (galInclusion (K := K) (L := L) (step2FixedField (K := K) (L := L) σ))
            (frobClass (R := 𝓞 (step2E (K := K) (L := L) σ))
              (G := Gal(L/↥(step2FixedField (K := K) (L := L) σ))) (Q := P)) =
          frobClass (R := 𝓞 K) (G := Gal(L/K)) (Q := P)

end OrbitStabilizer

end Step2Counting

end Chebotarev

end PrimeNumberTheoremAnd
