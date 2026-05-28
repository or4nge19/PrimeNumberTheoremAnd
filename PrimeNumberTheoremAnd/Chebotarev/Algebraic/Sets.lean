import PrimeNumberTheoremAnd.Chebotarev.Algebraic.Frobenius
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.RamificationInertia.UnramifiedBase

import Mathlib.NumberTheory.NumberField.Basic

/-!
## Chebotarev sets (algebraic prerequisite)

This file defines Sharifi's Chebotarev set attached to a conjugacy class:

* **choice-free** at the definition level (`HasFrobClass` is existential over finiteness witnesses);
* **Sharifi-correct** in requiring base-side unramifiedness (`Ideal.IsUnramifiedIn`);
* bridged to the canonical `frobClassOver` once `HasFiniteResidueOver` is available.

### Definition hierarchy (treat each layer as a contract)

1. `HasFiniteResidueOver P` — existence of a prime above with finite residue (Frobenius input).
2. `frobClassOver P hP` — canonical conjugacy class (witness-independent by `frobClassOver_congr`).
3. `HasFrobClass P C` — ∃ witness with `frobClassOver P = C` (logically equivalent to (2) given any fixed witness).
4. `HasUnramifiedFrobClass P C` — prime + unramified in + `HasFrobClass`.
5. `chebotarevSet C` — `{P | HasUnramifiedFrobClass P C}`; this is Sharifi's `S_C`.

In number fields, (3)–(5) admit **witness-free** characterizations via
`hasFiniteResidueOver_of_numberField` (`hasUnramifiedFrobClass_iff_frobClassOver_numberField`).

No analytic input is used here.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical
open NumberField

namespace Chebotarev

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G S] [SMulCommClass G R S] [Algebra.IsInvariant R S G]

open Ideal

/--
Choice-free predicate: some prime above `P` (with finite residue) has Frobenius class `C`.
-/
def HasFrobClass (P : Ideal R) (C : ConjClasses G) : Prop :=
  ∃ hP : HasFiniteResidueOver (R := R) (S := S) P, frobClassOver (R := R) (S := S) (G := G) P hP = C

/--
Sharifi's Chebotarev predicate at a base prime: a prime ideal, unramified in `S/R`,
with Frobenius class `C`.
-/
def HasUnramifiedFrobClass (P : Ideal R) (C : ConjClasses G) : Prop :=
  P.IsPrime ∧
    Ideal.IsUnramifiedIn (R := R) (S := S) P ∧
      HasFrobClass (R := R) (S := S) (G := G) P C

/--
The Chebotarev set attached to a conjugacy class `C`: unramified prime ideals of `R` whose
Frobenius class equals `C`.
-/
def chebotarevSet (C : ConjClasses G) : Set (Ideal R) :=
  {P | HasUnramifiedFrobClass (R := R) (S := S) (G := G) P C}

theorem mem_chebotarevSet_iff (C : ConjClasses G) (P : Ideal R) :
    P ∈ chebotarevSet (R := R) (S := S) (G := G) C ↔
      HasUnramifiedFrobClass (R := R) (S := S) (G := G) P C :=
  Iff.rfl

theorem hasFrobClass_iff_frobClassOver_eq (P : Ideal R) (C : ConjClasses G)
    (hP : HasFiniteResidueOver (R := R) (S := S) P) :
    HasFrobClass (R := R) (S := S) (G := G) P C ↔
      frobClassOver (R := R) (S := S) (G := G) P hP = C := by
  constructor
  · rintro ⟨hP', hC⟩
    exact (frobClassOver_congr (R := R) (S := S) (G := G) P hP' hP).trans hC
  · intro hC
    exact ⟨hP, hC⟩

theorem hasUnramifiedFrobClass_iff (P : Ideal R) (C : ConjClasses G)
    (hP : HasFiniteResidueOver (R := R) (S := S) P) :
    HasUnramifiedFrobClass (R := R) (S := S) (G := G) P C ↔
      P.IsPrime ∧
        Ideal.IsUnramifiedIn (R := R) (S := S) P ∧
          frobClassOver (R := R) (S := S) (G := G) P hP = C := by
  simp [HasUnramifiedFrobClass, hasFrobClass_iff_frobClassOver_eq (P := P) (C := C) hP]

section NumberField

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G (𝓞 L)] [SMulCommClass G (𝓞 K) (𝓞 L)]
  [Algebra.IsInvariant (𝓞 K) (𝓞 L) G]

/--
In a number-field extension, `HasFrobClass` is equivalent to the canonical `frobClassOver` with
the standard finiteness witness (no existential over witnesses).
-/
theorem hasFrobClass_iff_frobClassOver_eq_numberField
    (P : Ideal (𝓞 K)) [P.IsPrime] (hP : P ≠ ⊥) (C : ConjClasses G) :
    HasFrobClass (R := 𝓞 K) (S := 𝓞 L) (G := G) P C ↔
      frobClassOver (R := 𝓞 K) (S := 𝓞 L) (G := G) P
        (hasFiniteResidueOver_of_numberField (K := K) (L := L) P hP) = C :=
  hasFrobClass_iff_frobClassOver_eq (P := P) (C := C)
    (hP := hasFiniteResidueOver_of_numberField (K := K) (L := L) P hP)

/--
Sharifi's unramified Frobenius predicate at a nonzero prime of `𝓞 K`, in witness-free form.
-/
theorem hasUnramifiedFrobClass_iff_frobClassOver_numberField
    (P : Ideal (𝓞 K)) [P.IsPrime] (hP : P ≠ ⊥) (C : ConjClasses G) :
    HasUnramifiedFrobClass (R := 𝓞 K) (S := 𝓞 L) (G := G) P C ↔
      Ideal.IsUnramifiedIn (R := 𝓞 K) (S := 𝓞 L) P ∧
        frobClassOver (R := 𝓞 K) (S := 𝓞 L) (G := G) P
          (hasFiniteResidueOver_of_numberField (K := K) (L := L) P hP) = C := by
  constructor
  · intro ⟨_hPprime, hunram, hfrob⟩
    exact ⟨hunram, (hasFrobClass_iff_frobClassOver_eq_numberField (K := K) (L := L) P hP C).mp hfrob⟩
  · intro ⟨hunram, hfrobc⟩
    refine ⟨inferInstance, hunram, ?_⟩
    exact (hasFrobClass_iff_frobClassOver_eq_numberField (K := K) (L := L) P hP C).mpr hfrobc

theorem mem_chebotarevSet_iff_frobClassOver_numberField (C : ConjClasses G)
    (P : Ideal (𝓞 K)) [P.IsPrime] (hP : P ≠ ⊥) :
    P ∈ chebotarevSet (R := 𝓞 K) (S := 𝓞 L) (G := G) C ↔
      Ideal.IsUnramifiedIn (R := 𝓞 K) (S := 𝓞 L) P ∧
        frobClassOver (R := 𝓞 K) (S := 𝓞 L) (G := G) P
          (hasFiniteResidueOver_of_numberField (K := K) (L := L) P hP) = C := by
  rw [mem_chebotarevSet_iff, hasUnramifiedFrobClass_iff_frobClassOver_numberField (K := K) (L := L)]
  tauto

end NumberField

end

end Chebotarev

end PrimeNumberTheoremAnd
