import PrimeNumberTheoremAnd.Chebotarev.Cyclotomic.Instances
import PrimeNumberTheoremAnd.Chebotarev.Algebraic.UnramifiedNat
import PrimeNumberTheoremAnd.Chebotarev.Cyclotomic.OverPrime
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.SetTheory.Cardinal.Finite
import PrimeNumberTheoremAnd.Chebotarev.Algebraic.EnoughRootsOfUnityComplex

/-!
## Cyclotomic step: Frobenius sends `ζₙ ↦ ζₙ^p` (algebraic core)

Sharifi’s Step 1 (cyclotomic base case) uses that for `p ∤ n`, the arithmetic Frobenius at a
prime above `(p)` acts on `ζₙ` by `ζₙ ↦ ζₙ^p`.

This file proves that statement in a **mathlib-native** way, using:

- `arithFrobAt` / `IsArithFrobAt` from `Mathlib/RingTheory/Frobenius.lean`,
- the “unramified-at-`n`” lemma `ChebotarevUnramifiedNat.natCast_not_mem_of_liesOver_span_prime`,
- the computation `Nat.card (ℤ/(p)) = p`.

We state it for a general cyclotomic extension `L/ℚ` (as a number field), and for its ring of
integers `𝓞 L`.
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev

open scoped Classical Cyclotomic

open IsCyclotomicExtension NumberField

section

variable {n p : ℕ} [NeZero n] [Fact (Nat.Prime p)]

variable (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {n} ℚ L]

local notation "𝓞L" => (𝓞 L)

noncomputable local instance instMulSemiringAction : MulSemiringAction Gal(L/ℚ) 𝓞L :=
  Cyclotomic.mulSemiringActionGalOnRingOfIntegers L

local instance instIsInvariant [IsGalois ℚ L] :
    Algebra.IsInvariant ℤ 𝓞L Gal(L/ℚ) := by
  simpa using (Algebra.isInvariant_of_isGalois (A := ℤ) (K := ℚ) (L := L) (B := 𝓞L))

/--
Let `Q` be a prime ideal of `𝓞L` lying over `(p)` with finite residue field.
If `p ∤ n`, then the arithmetic Frobenius at `Q` sends the integral cyclotomic generator `ζₙ`
to `ζₙ^p`.
-/
theorem arithFrobAt_zeta_toInteger_eq_pow (Q : Ideal 𝓞L)
    [Q.IsPrime] [Finite (𝓞L ⧸ Q)] [Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    [IsGalois ℚ L] (hn : ¬ p ∣ n) :
    let ζ₀ : 𝓞L := (zeta_spec n ℚ L).toInteger
    (arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q) • (ζ₀ : 𝓞L) = (ζ₀ : 𝓞L) ^ p := by
  classical
  intro ζ₀
  -- First: `n ∉ Q` since `Q` lies over `(p)` and `p ∤ n`.
  have hnQ : (n : 𝓞L) ∉ Q :=
    natCast_not_mem_of_liesOver_span_prime (S := 𝓞L) (p := p) (n := n) Q hn
  -- Apply `IsArithFrobAt.smul_of_pow_eq_one` to the Frobenius at `Q`.
  have hF : IsArithFrobAt (R := ℤ) (arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q) Q :=
    IsArithFrobAt.arithFrobAt (R := ℤ) (S := 𝓞L) (G := Gal(L/ℚ)) (Q := Q)
  have hz_pow : (ζ₀ : 𝓞L) ^ n = 1 := by
    -- `ζ₀` is a primitive `n`-th root of unity in `𝓞L`.
    simpa using (zeta_spec n ℚ L).toInteger_isPrimitiveRoot.pow_eq_one
  have hpow :=
    IsArithFrobAt.smul_of_pow_eq_one (R := ℤ) (S := 𝓞L) (σ := arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q)
      (Q := Q) hF hz_pow (by simpa using hnQ)
  -- Rewrite the residue field size `Nat.card (ℤ ⧸ Q.under ℤ)` as `p` using `LiesOver`.
  have hunder : Q.under ℤ = Ideal.span ({(p : ℤ)} : Set ℤ) := by
    simpa [Ideal.under_def] using (Q.over_def (Ideal.span ({(p : ℤ)} : Set ℤ))).symm
  -- Now finish by rewriting the exponent.
  simpa [hunder, nat_card_int_quot_span_prime (p := p)] using hpow

/-!
### Transport to the field: `σ(ζₙ) = ζₙ^p`
-/

/--
The previous lemma transported to the field `L`: the arithmetic Frobenius at `Q` sends
`zeta n ℚ L` to its `p`-th power (for `p ∤ n`).
-/
theorem arithFrobAt_zeta_eq_pow (Q : Ideal 𝓞L)
    [Q.IsPrime] [Finite (𝓞L ⧸ Q)] [Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    [IsGalois ℚ L] (hn : ¬ p ∣ n) :
    (arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q) (zeta n ℚ L) = (zeta n ℚ L) ^ p := by
  classical
  -- Work with the integral version `ζ₀ : 𝓞L` and map to `L`.
  let ζ₀ : 𝓞L := (zeta_spec n ℚ L).toInteger
  have hζ₀ : (arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q) • (ζ₀ : 𝓞L) = (ζ₀ : 𝓞L) ^ p :=
    arithFrobAt_zeta_toInteger_eq_pow (L := L) (n := n) (p := p) (Q := Q) hn
  -- Apply `algebraMap 𝓞L L`.
  have hmap := congrArg (algebraMap 𝓞L L) hζ₀
  -- Rewrite the action on `𝓞L` as `galRestrict`, then use compatibility with `algebraMap`.
  -- (`σ • x` is definitional for our `instMulSemiringAction`.)
  have hleft :
      algebraMap 𝓞L L ((arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q) • ζ₀) =
        (arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q) (algebraMap 𝓞L L ζ₀) := by
    -- `algebraMap_galRestrict_apply` is the compatibility lemma.
    simpa [instMulSemiringAction, IsIntegralClosure.MulSemiringAction, MulSemiringAction.compHom] using
      (algebraMap_galRestrict_apply (A := ℤ) (K := ℚ) (L := L) (B := 𝓞L)
        (σ := arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q) (x := ζ₀))
  have hzeta : algebraMap 𝓞L L ζ₀ = zeta n ℚ L := by
    simp [ζ₀]
  have := hmap
  simpa [hleft, hzeta, map_pow] using this

/-!
### `autToPow` identifies Frobenius with `p (mod n)`
-/

/--
In the cyclotomic setup above, the powering exponent of the Frobenius at `Q` (as an element of
`ZMod n`) is `p`.

This is the algebraic content behind the statement “Frobenius corresponds to `p mod n`”.
-/
theorem arithFrobAt_autToPow_eq_natCast (Q : Ideal 𝓞L)
    [Q.IsPrime] [Finite (𝓞L ⧸ Q)] [Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    [IsGalois ℚ L] (hn : ¬ p ∣ n) :
    ((zeta_spec n ℚ L).autToPow ℚ (arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q) : ZMod n) = p := by
  classical
  let σ : Gal(L/ℚ) := arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q
  -- `autToPow_spec` gives the characterizing powering formula on `ζₙ`.
  have hspec :
      (zeta n ℚ L) ^ (((zeta_spec n ℚ L).autToPow ℚ σ : ZMod n)).val = σ (zeta n ℚ L) := by
    simp [σ]
  -- Substitute the Frobenius action `σ(ζₙ) = ζₙ^p`.
  have hfrob : σ (zeta n ℚ L) = (zeta n ℚ L) ^ p := by
    simpa [σ] using (arithFrobAt_zeta_eq_pow (L := L) (n := n) (p := p) (Q := Q) hn)
  have hpows :
      (zeta n ℚ L) ^ (((zeta_spec n ℚ L).autToPow ℚ σ : ZMod n)).val = (zeta n ℚ L) ^ p := by
    simp [hfrob]
  -- Work in the unit group to use cancellation (`pow_eq_pow_iff_modEq`).
  have hn0 : n ≠ 0 := NeZero.ne n
  let ζu : Lˣ := (zeta_spec n ℚ L).isUnit hn0 |>.unit
  have hζu : IsPrimitiveRoot ζu n :=
    (zeta_spec n ℚ L).isUnit_unit hn0
  have hpowsU :
      ζu ^ (((zeta_spec n ℚ L).autToPow ℚ σ : ZMod n)).val = ζu ^ p := by
    ext
    -- reduce to the previously proved equality in `L`
    -- and use that `ζu` coerces to `zeta`.
    simpa [ζu, Units.val_pow_eq_pow_val] using hpows
  have hnord : orderOf ζu = n := by
    simpa using hζu.eq_orderOf.symm
  have hmod :
      (((zeta_spec n ℚ L).autToPow ℚ σ : ZMod n)).val ≡ p [MOD n] := by
    simpa [hnord] using (pow_eq_pow_iff_modEq.mp hpowsU)
  -- Turn the congruence into equality in `ZMod n`.
  have : (((((zeta_spec n ℚ L).autToPow ℚ σ : ZMod n)).val : ℕ) : ZMod n) = (p : ZMod n) :=
    (ZMod.natCast_eq_natCast_iff ..).2 hmod
  -- Replace `natCast` of `.val` by the element itself.
  simpa [σ] using (by
    -- `ZMod.natCast_zmod_val` says `((a.val : ZMod n)) = a`.
    simpa using (ZMod.natCast_zmod_val (n := n) ((zeta_spec n ℚ L).autToPow ℚ σ : ZMod n)) ▸ this)

end

end Chebotarev

end PrimeNumberTheoremAnd
