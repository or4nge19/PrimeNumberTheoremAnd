import Mathlib.RingTheory.Invariant.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Galois.IsGaloisGroup

/-!
## Galois AKLB instances for number fields

Sharifi's Chebotarev development needs `MulSemiringAction` and `Algebra.IsInvariant` on rings of
integers. Mathlib provides these from `[IsGalois K L]` via `Algebra.isInvariant_of_isGalois`.

This file expresses the standard number-field specialization once, so downstream files (Frobenius,
Step 2, Artin L-series) can `attribute [local instance]` rather than repeating the cyclotomic-only
pattern in `Chebotarev/Cyclotomic/Instances.lean`.

**Note:** `local instance` does not persist across files; consumers still need a one-line
`attribute [local instance]` in each module that forms `arithFrobAt`.
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev

namespace GaloisInstances

open NumberField

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] FractionRing.liftAlgebra

/-- Canonical Galois action of `Gal(L/K)` on `𝓞 L`. -/
@[reducible] noncomputable
def mulSemiringActionRingOfIntegers : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
  IsIntegralClosure.MulSemiringAction (A := RingOfIntegers K) K L (RingOfIntegers L)

noncomputable local instance instMulSemiringActionRingOfIntegers :
    MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
  mulSemiringActionRingOfIntegers K L

noncomputable local instance instIsGaloisGroupRingOfIntegers :
    IsGaloisGroup Gal(L/K) (RingOfIntegers K) (RingOfIntegers L) :=
  IsGaloisGroup.of_isFractionRing (G := Gal(L/K)) (A := RingOfIntegers K) (B := RingOfIntegers L)
    (K := K) (L := L)

noncomputable local instance instIsInvariantRingOfIntegers :
    Algebra.IsInvariant (RingOfIntegers K) (RingOfIntegers L) Gal(L/K) :=
  Algebra.isInvariant_of_isGalois (A := RingOfIntegers K) K L (RingOfIntegers L)

section IntermediateField

variable (E : IntermediateField K L)

variable [IsGalois E L]

/-- Galois action of `Gal(L/E)` on `𝓞 L` for an intermediate field `E`. -/
@[reducible] noncomputable
def mulSemiringActionRingOfIntegersIntermediate :
    MulSemiringAction Gal(L/E) (RingOfIntegers L) :=
  IsIntegralClosure.MulSemiringAction (A := RingOfIntegers ↥E) ↥E L (RingOfIntegers L)

noncomputable local instance instMulSemiringActionRingOfIntegersIntermediate :
    MulSemiringAction Gal(L/E) (RingOfIntegers L) :=
  mulSemiringActionRingOfIntegersIntermediate K L E

noncomputable local instance instIsInvariantRingOfIntegersIntermediate :
    Algebra.IsInvariant (RingOfIntegers ↥E) (RingOfIntegers L) Gal(L/E) :=
  Algebra.isInvariant_of_isGalois (A := RingOfIntegers ↥E) ↥E L (RingOfIntegers L)

end IntermediateField

end GaloisInstances

end Chebotarev

end PrimeNumberTheoremAnd
