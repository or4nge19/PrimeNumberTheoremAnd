import Mathlib.RingTheory.Invariant.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.Gal

/-!
## Shared cyclotomic AKLB instances for Frobenius elaboration

Several cyclotomic Frobenius lemmas need the *same* noncomputable `MulSemiringAction` on `𝓞 L`
when forming `arithFrobAt`. This file defines that action once.

**Consumer pattern** (required in each file that calls `arithFrobAt` on `𝓞 L`):

```lean
noncomputable local instance instMulSemiringAction : MulSemiringAction Gal(L/ℚ) (𝓞 L) :=
  Cyclotomic.mulSemiringActionGalOnRingOfIntegers L

local instance instIsInvariant [IsGalois ℚ L] :
    Algebra.IsInvariant ℤ (𝓞 L) Gal(L/ℚ) := by
  simpa using (Algebra.isInvariant_of_isGalois (A := ℤ) (K := ℚ) (L := L) (B := (𝓞 L)))
```

`local instance` does not persist across files, so each consumer must repeat this block.
Using the default `RingOfIntegers.instMulSemiringAction` breaks definitional agreement with
lemmas proved in sibling files.
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev
namespace Cyclotomic

open scoped Cyclotomic

open IsCyclotomicExtension NumberField

section

variable {n : ℕ} [NeZero n]

variable (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {n} ℚ L]

attribute [local instance] FractionRing.liftAlgebra

/-- Canonical Galois action of `Gal(L/ℚ)` on the ring of integers `𝓞 L`. -/
@[reducible] noncomputable
def mulSemiringActionGalOnRingOfIntegers : MulSemiringAction Gal(L/ℚ) (𝓞 L) :=
  IsIntegralClosure.MulSemiringAction ℤ ℚ L (𝓞 L)

local instance instSMulCommClassGalOnRingOfIntegers :
    SMulCommClass Gal(L/ℚ) ℤ (𝓞 L) := by
  infer_instance

end

end Cyclotomic
end Chebotarev
end PrimeNumberTheoremAnd
