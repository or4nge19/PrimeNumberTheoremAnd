import Mathlib.RingTheory.Frobenius
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.Ideal.Pointwise

/-!
## Decomposition and inertia; Frobenius in the quotient `D(Q)/I(Q)`

This file develops the **purely algebraic** prerequisite that the Frobenius element is canonical
in `D(Q)/I(Q)`, using mathlib's native subgroups:

* `MulAction.stabilizer G Q` for the decomposition group `D(Q)`;
* `Ideal.inertia G Q` for the inertia subgroup `I(Q)`;
* `IsArithFrobAt.mem_stabilizer` and `IsArithFrobAt.mul_inv_mem_inertia` from
  `Mathlib/RingTheory/Frobenius.lean`.

No analytic input is used.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical Pointwise

namespace Chebotarev

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]

open MulAction Ideal

/-- The inertia subgroup viewed inside the decomposition subgroup. -/
abbrev inertiaSubgroupOf (Q : Ideal S) : Subgroup (stabilizer G Q) :=
  (inertia G Q).subgroupOf (stabilizer G Q)

/-- The inertia subgroup is normal in the decomposition subgroup (as a kernel). -/
instance inertiaSubgroupOf_normal (Q : Ideal S) :
    (inertiaSubgroupOf (G := G) Q).Normal := by
  classical
  infer_instance

section frobQuot

variable {Q : Ideal S}

/--
Given an arithmetic Frobenius element `σ` at `Q`, its image in the quotient `D(Q) ⧸ I(Q)`.
-/
noncomputable def frobQuotOf (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    (σ : G) (hσ : IsArithFrobAt (R := R) σ Q) :
    stabilizer G Q ⧸ inertiaSubgroupOf (G := G) Q :=
  QuotientGroup.mk ⟨σ, IsArithFrobAt.mem_stabilizer (R := R) hσ⟩

theorem frobQuotOf_eq_of_isArithFrobAt (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    {σ σ' : G} (hσ : IsArithFrobAt (R := R) σ Q) (hσ' : IsArithFrobAt (R := R) σ' Q) :
    frobQuotOf (R := R) (S := S) (G := G) Q σ hσ =
      frobQuotOf (R := R) (S := S) (G := G) Q σ' hσ' := by
  classical
  let a : stabilizer G Q := ⟨σ, IsArithFrobAt.mem_stabilizer (R := R) hσ⟩
  let b : stabilizer G Q := ⟨σ', IsArithFrobAt.mem_stabilizer (R := R) hσ'⟩
  unfold frobQuotOf
  change ((a : stabilizer G Q ⧸ inertiaSubgroupOf (G := G) Q) =
      (b : stabilizer G Q ⧸ inertiaSubgroupOf (G := G) Q))
  rw [QuotientGroup.eq_iff_div_mem]
  have : σ * σ'⁻¹ ∈ inertia G Q :=
    IsArithFrobAt.mul_inv_mem_inertia (R := R) (Q := Q) hσ hσ'
  simpa [a, b, inertiaSubgroupOf, div_eq_mul_inv] using this

/--
The canonical Frobenius element in `D(Q)/I(Q)`, using mathlib's choice `arithFrobAt`.
-/
noncomputable def frobQuot (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] [Finite G]
    [Algebra.IsInvariant R S G] :
    stabilizer G Q ⧸ inertiaSubgroupOf (G := G) Q :=
  frobQuotOf (R := R) (S := S) (G := G) Q (arithFrobAt (R := R) (G := G) Q)
    (IsArithFrobAt.arithFrobAt (R := R) (S := S) (G := G) (Q := Q))

end frobQuot

end

end Chebotarev

end PrimeNumberTheoremAnd
