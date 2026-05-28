import PrimeNumberTheoremAnd.Chebotarev.Algebraic.FixedFieldGenerator
import PrimeNumberTheoremAnd.Chebotarev.Algebraic.FixedFieldCyclic
import PrimeNumberTheoremAnd.Mathlib.Algebra.Group.ConjClasses

import Mathlib.FieldTheory.Galois.Basic

/-!
## Frobenius conjugacy classes under Galois restriction (Sharifi Step 2)

Sharifi's `T_σ` predicate uses Frobenius in `Gal(L/E)`, while the base Chebotarev set uses
`Gal(L/K)`. This file records the canonical inclusion `Gal(L/E) ↪ Gal(L/K)` and Sharifi's
named intermediate field / generator data.
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev

open scoped Classical

section GaloisInclusion

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
variable (E : IntermediateField K L)

/-- The canonical inclusion `Gal(L/E) ↪ Gal(L/K)`. -/
noncomputable def galInclusion : Gal(L/E) →* Gal(L/K) :=
  (IntermediateField.fixingSubgroup E).subtype.comp (E.fixingSubgroupEquiv.symm.toMonoidHom)

end GaloisInclusion

section Step2Generator

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
variable (σ : Gal(L/K))

/-- Sharifi's fixed field `E = L^{⟨σ⟩}`. -/
abbrev step2FixedField : IntermediateField K L :=
  fixedFieldZpowers (K := K) (L := L) σ

/-- Sharifi's canonical generator of `Gal(L/E)` corresponding to `σ`. -/
noncomputable abbrev step2Generator : Gal(L/step2FixedField (K := K) (L := L) σ) :=
  sigmaGalFixedFieldZpowers (K := K) (L := L) σ

/-- Frobenius conjugacy class target for Sharifi's `T_σ`, in `Gal(L/E)`. -/
noncomputable abbrev step2FrobClass : ConjClasses (Gal(L/step2FixedField (K := K) (L := L) σ)) :=
  ConjClasses.mk (step2Generator (K := K) (L := L) σ)

/--
The same class, viewed in `Gal(L/K)` via restriction along `Gal(L/E) ↪ Gal(L/K)`.
Equals `ConjClasses.mk σ` by `step2FrobClassInGalLK_eq`.
-/
noncomputable def step2FrobClassInGalLK : ConjClasses (Gal(L/K)) :=
  ConjClasses.map (galInclusion (K := K) (L := L) (step2FixedField (K := K) (L := L) σ))
    (step2FrobClass (K := K) (L := L) σ)

/-- `σ` fixes its own fixed field `L^{⟨σ⟩}`. -/
private lemma mem_fixingSubgroup_step2FixedField (σ : Gal(L/K)) :
    σ ∈ (step2FixedField (K := K) (L := L) σ).fixingSubgroup := by
  simp [step2FixedField, fixedFieldZpowers, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact hx σ (Subgroup.mem_zpowers _)

/--
`galInclusion` sends Sharifi's canonical generator back to `σ`.
-/
theorem galInclusion_step2Generator (σ : Gal(L/K)) :
    galInclusion (K := K) (L := L) (step2FixedField (K := K) (L := L) σ)
      (step2Generator (K := K) (L := L) σ) = σ := by
  classical
  let E := step2FixedField (K := K) (L := L) σ
  have hσ : σ ∈ E.fixingSubgroup := mem_fixingSubgroup_step2FixedField (K := K) (L := L) σ
  unfold galInclusion step2Generator sigmaGalFixedFieldZpowers step2FixedField fixedFieldZpowers
  ext x
  simp [IntermediateField.subgroupEquivAlgEquiv, fixingSubgroup_fixedFieldZpowers (K := K) (L := L) σ,
    IntermediateField.fixingSubgroupEquiv, hσ, IntermediateField.mem_fixingSubgroup_iff,
    Subgroup.mem_zpowers]

/-- Sharifi's base-side class `Cl(σ)` in `Gal(L/K)` is the pushforward of `step2FrobClass`. -/
theorem step2FrobClassInGalLK_eq (σ : Gal(L/K)) :
    step2FrobClassInGalLK (K := K) (L := L) σ = ConjClasses.mk σ := by
  dsimp only [step2FrobClassInGalLK, step2FrobClass]
  rw [ConjClasses.map_mk, galInclusion_step2Generator (K := K) (L := L) σ]

end Step2Generator

end Chebotarev

end PrimeNumberTheoremAnd
