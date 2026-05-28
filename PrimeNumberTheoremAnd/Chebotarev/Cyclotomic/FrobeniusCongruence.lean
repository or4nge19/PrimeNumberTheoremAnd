import PrimeNumberTheoremAnd.Chebotarev.Cyclotomic.Instances
import PrimeNumberTheoremAnd.Chebotarev.Cyclotomic.FrobeniusZeta
import PrimeNumberTheoremAnd.Chebotarev.Cyclotomic.FrobeniusPrimeSet
import PrimeNumberTheoremAnd.Chebotarev.Algebraic.EnoughRootsOfUnityComplex

/-!
## Cyclotomic case: Frobenius ↔ congruence class ↔ prime-set coefficient

In a cyclotomic extension, an automorphism is determined by the exponent by which it sends `ζₙ`.
For an arithmetic Frobenius at a prime above `p`, we characterize `arithFrobAt Q = σ` via
`autToPow σ = p` in `ZMod n`, and connect that to the Dirichlet coefficient of `frobPrimeSet σ`.
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev
namespace Cyclotomic

open scoped Classical Cyclotomic NumberField

open IsCyclotomicExtension NumberField
open PrimeNumberTheoremAnd.DirichletDensity

section

variable {n p : ℕ} [NeZero n] [Fact (Nat.Prime p)]

variable (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {n} ℚ L]

noncomputable local instance instMulSemiringAction : MulSemiringAction Gal(L/ℚ) (𝓞 L) :=
  Cyclotomic.mulSemiringActionGalOnRingOfIntegers L

local instance instIsInvariant [IsGalois ℚ L] :
    Algebra.IsInvariant ℤ (𝓞 L) Gal(L/ℚ) := by
  simpa using (Algebra.isInvariant_of_isGalois (A := ℤ) (K := ℚ) (L := L) (B := (𝓞 L)))

variable (Q : Ideal (𝓞 L)) [Q.IsPrime] [Finite ((𝓞 L) ⧸ Q)]
variable [Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] [IsGalois ℚ L]

variable (σ : Gal(L/ℚ))

/--
For primes `p ∤ n`, equality with the Frobenius element at `Q` is equivalent to equality of the
associated exponents in `ZMod n`.
-/
theorem arithFrobAt_eq_iff_autToPow_eq_natCast :
    (hn : ¬ p ∣ n) →
    arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q = σ ↔
      ((zeta_spec n ℚ L).autToPow ℚ σ : ZMod n) = (p : ZMod n) := by
  classical
  intro hn
  let σF : Gal(L/ℚ) := arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q
  have hFrobZMod :
      ((zeta_spec n ℚ L).autToPow ℚ σF : ZMod n) = p := by
    simpa [σF] using
      (arithFrobAt_autToPow_eq_natCast (L := L) (n := n) (p := p) (Q := Q) hn)
  have hinj : Function.Injective ((zeta_spec n ℚ L).autToPow ℚ) :=
    (zeta_spec n ℚ L).autToPow_injective (K := ℚ)
  constructor
  · intro h
    subst h
    simpa [σF] using hFrobZMod
  · intro hZ
    have hU :
        (zeta_spec n ℚ L).autToPow ℚ σF = (zeta_spec n ℚ L).autToPow ℚ σ := by
      apply Units.ext
      simpa [hFrobZMod] using hZ.symm
    have : σF = σ := hinj hU
    simpa [σF] using this

/--
For `p ∤ n`, the Frobenius indicator at `Q` equals the Dirichlet coefficient of `frobPrimeSet σ`.
-/
theorem frob_indicator_eq_coeff_frobPrimeSet (hn : ¬ p ∣ n) :
    (if arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q = σ then (1 : ℂ) else 0)
      =
    coeff (frobPrimeSet (n := n) (L := L) σ) p := by
  classical
  have hp : p.Prime := Fact.out
  have hcond :
      (arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q = σ) =
        (((zeta_spec n ℚ L).autToPow ℚ σ : ZMod n) = (p : ZMod n)) :=
    propext (arithFrobAt_eq_iff_autToPow_eq_natCast (n := n) (p := p) (L := L) (Q := Q) (σ := σ) hn)
  simp [coeff, frobPrimeSet, congrPrimeSet, hp, hcond, eq_comm]

theorem frob_indicator_eq_character_sum (hn : ¬ p ∣ n) :
    (if arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q = σ then (1 : ℂ) else 0)
      =
    ((1 : ℂ) / (n.totient : ℂ)) *
      ∑ χ : DirichletCharacter ℂ n,
        χ ((((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n)⁻¹) * χ (p : ZMod n) := by
  classical
  have hp : p.Prime := Fact.out
  simpa [coeff_frobPrimeSet_eq_prime (n := n) (L := L) (σ := σ) hp] using
    (frob_indicator_eq_coeff_frobPrimeSet (n := n) (p := p) (L := L) (Q := Q) (σ := σ) hn)

end

end Cyclotomic
end Chebotarev

end PrimeNumberTheoremAnd
