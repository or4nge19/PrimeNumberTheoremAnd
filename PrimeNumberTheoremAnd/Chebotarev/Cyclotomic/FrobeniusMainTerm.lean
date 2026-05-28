import PrimeNumberTheoremAnd.Chebotarev.Cyclotomic.FrobeniusRatioTsumPrimes
import PrimeNumberTheoremAnd.Chebotarev.Algebraic.EnoughRootsOfUnityComplex

/-!
## Cyclotomic case: isolate the trivial-character main term

Starting from `ratio_frobPrimeSet_eq_tsum_primes_character_split`, we simplify the *trivial*
Dirichlet character contribution:

- the factor `(1 : DirichletCharacter ℂ n)` evaluated at a unit is `1`;
- the value at a prime `p` is `0` iff `p ∣ n`, and otherwise `1`.

This is the algebraic step needed before passing to the limit \(s \to 1^+\):
the finitely many primes dividing `n` contribute only a finite correction.
-/

namespace PrimeNumberTheoremAnd
namespace Chebotarev
namespace Cyclotomic

open scoped Classical Cyclotomic NumberField

open IsCyclotomicExtension
open PrimeNumberTheoremAnd.DirichletDensity

section

variable {n : ℕ} [NeZero n]

variable (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {n} ℚ L]

open Nat.Primes

omit [NeZero n] in
lemma trivChar_apply_prime (p : Nat.Primes) :
    (1 : DirichletCharacter ℂ n) (p : ZMod n) = if (p.1 ∣ n) then 0 else 1 := by
  classical
  by_cases hp : (p.1 ∣ n)
  · have hnu : ¬ IsUnit (p.1 : ZMod n) := by
      intro hu
      have : ¬ (p.1 ∣ n) := (ZMod.isUnit_prime_iff_not_dvd p.2).1 hu
      exact this hp
    -- non-units map to `0`
    simpa [hp] using (MulChar.map_nonunit (χ := (1 : DirichletCharacter ℂ n)) (a := (p.1 : ZMod n))
      hnu)
  · have hu : IsUnit (p.1 : ZMod n) := (ZMod.isUnit_prime_iff_not_dvd p.2).2 hp
    -- units map to `1`
    simp [hp, MulChar.one_apply (R := ZMod n) (R' := ℂ) (x := (p.1 : ZMod n)) hu]

lemma trivChar_apply_autToPow_inv (σ : Gal(L/ℚ)) :
    (1 : DirichletCharacter ℂ n)
        ((((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n)⁻¹) = 1 := by
  classical
  set u : (ZMod n)ˣ := (zeta_spec n ℚ L).autToPow ℚ σ
  have hu0 : IsUnit ((u : (ZMod n)ˣ) : ZMod n) := u.isUnit
  have huR : IsUnit (Ring.inverse ((u : (ZMod n)ˣ) : ZMod n)) := IsUnit.ringInverse hu0
  have hu : IsUnit (((u : (ZMod n)ˣ) : ZMod n)⁻¹) := by
    simp
  exact MulChar.one_apply (R := ZMod n) (R' := ℂ) (x := (((u : (ZMod n)ˣ) : ZMod n)⁻¹)) hu

open Complex

theorem ratio_frobPrimeSet_eq_tsum_primes_character_split_main (σ : Gal(L/ℚ)) {s : ℝ} (hs : 1 < s) :
    ratioDefault (frobPrimeSet (n := n) (L := L) σ) s =
      (∑' p : Nat.Primes,
          (((1 : ℂ) / (n.totient : ℂ)) *
              ((if (p.1 ∣ n) then 0 else 1) +
                ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)),
                  χ ((((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n)⁻¹) *
                    χ (p : ZMod n))) /
            ((p : ℂ) ^ (s : ℂ))) /
        (∑' p : Nat.Primes, (1 : ℂ) / ((p : ℂ) ^ (s : ℂ))) := by
  classical
  have h :=
    ratio_frobPrimeSet_eq_tsum_primes_character_split (n := n) (L := L) (σ := σ) hs
  simpa [trivChar_apply_autToPow_inv (n := n) (L := L) (σ := σ),
    trivChar_apply_prime (n := n)] using h

end

end Cyclotomic
end Chebotarev
end PrimeNumberTheoremAnd
