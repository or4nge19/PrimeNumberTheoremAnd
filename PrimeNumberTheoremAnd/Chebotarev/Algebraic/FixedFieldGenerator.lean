import PrimeNumberTheoremAnd.Chebotarev.Algebraic.FixedFieldCyclic

import Mathlib.FieldTheory.Galois.Basic

/-!
## Chebotarev reduction: a canonical generator for `Gal(L / L^{⟨σ⟩})`

For Sharifi’s reduction step we fix `σ : Gal(L/K)` and set `E = L^{⟨σ⟩}`.
Then `Gal(L/E)` is cyclic, and we want an explicit element of `Gal(L/E)` corresponding to `σ`.

We define this element using the canonical group isomorphism from the Galois correspondence
(`IntermediateField.subgroupEquivAlgEquiv`).

No arithmetic or analytic content appears here.
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev

open scoped Classical

section

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
variable (σ : Gal(L/K))

/-- The element of `Gal(L / L^{⟨σ⟩})` corresponding to `σ`. -/
noncomputable def sigmaGalFixedFieldZpowers :
    Gal(L / fixedFieldZpowers (K := K) (L := L) σ) :=
  (IntermediateField.subgroupEquivAlgEquiv (F := K) (E := L) (H := Subgroup.zpowers σ))
    ⟨σ, by simp⟩

@[simp] lemma sigmaGalFixedFieldZpowers_def :
    sigmaGalFixedFieldZpowers (K := K) (L := L) σ
      =
    (IntermediateField.subgroupEquivAlgEquiv (F := K) (E := L) (H := Subgroup.zpowers σ))
      ⟨σ, by simp⟩ := rfl

end

end Chebotarev

end PrimeNumberTheoremAnd

