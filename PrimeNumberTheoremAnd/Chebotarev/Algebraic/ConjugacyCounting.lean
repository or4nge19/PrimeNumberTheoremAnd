import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Index
import Mathlib.SetTheory.Cardinal.Finite

/-!
## Conjugacy counting (Sharifi, Step 2 algebra)

Sharifi uses the basic combinatorial identity
\(|C| = [G : Z(\sigma)]\), where `Z(σ)` is the centralizer of `σ`.

In mathlib, `ConjClasses.mk g` is the conjugacy class of `g`, and
`Subgroup.centralizer ({g} : Set G)` is the centralizer subgroup.

We record the orbit-stabilizer computation in a form convenient for later Chebotarev reductions.
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev

open scoped Classical

section

variable {G : Type*} [Group G] [Finite G]

/--
Orbit-stabilizer for the conjugation action, rewritten as the standard identity
\(|\mathrm{Cl}(g)| \cdot |Z(g)| = |G|\).

Here `Cl(g)` is `ConjClasses.mk g` and `Z(g)` is `Subgroup.centralizer {g}`.
-/
theorem nat_card_conjClass_mul_nat_card_centralizer_eq_nat_card (g : G) :
    Nat.card (ConjClasses.mk g).carrier *
        Nat.card (Subgroup.centralizer ({g} : Set G)) =
      Nat.card G := by
  cases nonempty_fintype G
  have h :=
    (MulAction.card_orbit_mul_card_stabilizer_eq_card_group (α := ConjAct G) (β := G) g)
  simpa [ConjAct.orbit_eq_carrier_conjClasses, ConjAct.stabilizer_eq_centralizer, ConjAct.card,
    Nat.card_eq_fintype_card] using h

/-- Sharifi's `|C| = [G : Z(g)]`, as an equality with `Subgroup.index`. -/
theorem nat_card_conjClass_eq_index_centralizer (g : G) :
    Nat.card (ConjClasses.mk g).carrier =
      (Subgroup.centralizer ({g} : Set G)).index := by
  letI : Fintype G := Fintype.ofFinite G
  let Z : Subgroup G := Subgroup.centralizer ({g} : Set G)
  have h1 := nat_card_conjClass_mul_nat_card_centralizer_eq_nat_card (G := G) g
  have h2 :
      Nat.card (G ⧸ Z) * Nat.card Z =
        Nat.card G := by
    simpa [Z] using
      (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := Z)).symm
  have :
      Nat.card (ConjClasses.mk g).carrier * Nat.card Z =
        Nat.card (G ⧸ Z) * Nat.card Z := by
    simpa [Z] using h1.trans h2.symm
  have hZpos : 0 < Nat.card Z := by
    letI : Fintype Z := Fintype.ofFinite Z
    have : Nonempty Z := ⟨1⟩
    simpa [Nat.card_eq_fintype_card] using (Fintype.card_pos_iff.2 this)
  have hcard : Nat.card (ConjClasses.mk g).carrier = Nat.card (G ⧸ Z) :=
    Nat.mul_right_cancel hZpos this
  simpa [Subgroup.index, Z] using hcard

end

end Chebotarev

end PrimeNumberTheoremAnd
