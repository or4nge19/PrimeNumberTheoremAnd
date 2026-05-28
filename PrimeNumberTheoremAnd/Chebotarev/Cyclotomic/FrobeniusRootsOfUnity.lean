import Mathlib.RingTheory.Frobenius

/-!
## Frobenius elements and roots of unity

Sharifi’s cyclotomic step uses that an arithmetic Frobenius at `Q` acts on roots of unity by
raising to the size of the residue field.

Mathlib proves this for an `R`-algebra endomorphism `φ : S →ₐ[R] S` satisfying
`AlgHom.IsArithFrobAt φ Q` as `AlgHom.IsArithFrobAt.apply_of_pow_eq_one`.

Here we reexpresse it for the **group-action** Frobenius predicate `IsArithFrobAt R σ Q`.
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev

open scoped Classical

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]

variable {Q : Ideal S} {σ : G}

/--
If `σ` is an arithmetic Frobenius at `Q`, then it acts on any `m`-th root of unity `ζ`
with `m ∉ Q` by `ζ ↦ ζ ^ #(R / Q.under R)`.

This is the group-action specialization of `AlgHom.IsArithFrobAt.apply_of_pow_eq_one`.
-/
lemma IsArithFrobAt.smul_of_pow_eq_one [IsDomain S]
    (hσ : IsArithFrobAt (R := R) σ Q) {ζ : S} {m : ℕ} (hζ : ζ ^ m = 1) (hm : (m : S) ∉ Q) :
    σ • ζ = ζ ^ Nat.card (R ⧸ Q.under R) := by
  -- Unfold `IsArithFrobAt` and apply the `AlgHom` lemma.
  simpa [IsArithFrobAt] using
    (AlgHom.IsArithFrobAt.apply_of_pow_eq_one (R := R) (S := S)
      (φ := MulSemiringAction.toAlgHom R S σ) (Q := Q) hσ hζ hm)

end

end Chebotarev

end PrimeNumberTheoremAnd
