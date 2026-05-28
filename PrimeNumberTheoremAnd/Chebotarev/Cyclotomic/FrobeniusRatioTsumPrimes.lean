import PrimeNumberTheoremAnd.Chebotarev.Cyclotomic.FrobeniusDensityRatio
import PrimeNumberTheoremAnd.Chebotarev.Density.DirichletDensityTsumPrimes
import PrimeNumberTheoremAnd.Chebotarev.Cyclotomic.FrobeniusPrimeTsumPrimes
import PrimeNumberTheoremAnd.Chebotarev.Algebraic.EnoughRootsOfUnityComplex

/-!
## Cyclotomic case: Dirichlet-density ratio as a quotient of prime-indexed sums

For `s > 1`, we can rewrite the Dirichlet-density ratio for the cyclotomic Frobenius prime set
as a quotient of two `tsum` indexed by `Nat.Primes`:

- the numerator is the Frobenius prime Dirichlet series, rewritten as a normalized Dirichlet
  character sum at each prime;
- the denominator is the “all primes” Dirichlet series `∑' p, 1 / p^s`.

This is the exact prime-indexed algebraic form immediately preceding the analytic `log L` step.
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

open Nat.Primes in
theorem ratio_frobPrimeSet_eq_tsum_primes_character (σ : Gal(L/ℚ)) {s : ℝ} (hs : 1 < s) :
    ratioDefault (frobPrimeSet (n := n) (L := L) σ) s =
      (∑' p : Nat.Primes,
          (((1 : ℂ) / (n.totient : ℂ)) *
              ∑ χ : DirichletCharacter ℂ n,
                χ ((((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n)⁻¹) * χ (p : ZMod n)) /
            ((p : ℂ) ^ (s : ℂ))) /
        (∑' p : Nat.Primes, (1 : ℂ) / ((p : ℂ) ^ (s : ℂ))) := by
  rw [ratioDefault_of_one_lt (frobPrimeSet (n := n) (L := L) σ) hs]
  rw [series_frobPrimeSet_eq_tsum_primes_character (n := n) (L := L) (σ := σ) hs,
    seriesAll_eq_tsum_primes hs]

open Nat.Primes in
/--
Variant of `ratio_frobPrimeSet_eq_tsum_primes_character` splitting off the trivial Dirichlet character
in the inner sum over characters.

This is the form used when passing to analytic statements: the trivial character contributes the
main term, while nontrivial characters contribute an error term.
-/
theorem ratio_frobPrimeSet_eq_tsum_primes_character_split (σ : Gal(L/ℚ)) {s : ℝ} (hs : 1 < s) :
    ratioDefault (frobPrimeSet (n := n) (L := L) σ) s =
      (∑' p : Nat.Primes,
          (((1 : ℂ) / (n.totient : ℂ)) *
              (( (1 : DirichletCharacter ℂ n)
                    ((((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n)⁻¹) *
                  (1 : DirichletCharacter ℂ n) (p : ZMod n)) +
                ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)),
                  χ ((((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n)⁻¹) * χ (p : ZMod n))) /
            ((p : ℂ) ^ (s : ℂ))) /
        (∑' p : Nat.Primes, (1 : ℂ) / ((p : ℂ) ^ (s : ℂ))) := by
  classical
  -- Start from the unsplit formula and rewrite the inner `Fintype.sum`.
  have h := ratio_frobPrimeSet_eq_tsum_primes_character (n := n) (L := L) (σ := σ) hs
  -- Rewrite each inner sum using `Fintype.sum_eq_add_sum_compl`.
  -- (The complement is the finset `{1}ᶜ`.)
  refine h.trans ?_
  refine congrArg (fun z : ℂ => z / (∑' p : Nat.Primes, (1 : ℂ) / ((p : ℂ) ^ (s : ℂ)))) ?_
  refine tsum_congr (fun p => ?_)
  -- Expand the inner `Fintype` sum as `f 1 + ∑ χ∈{1}ᶜ, f χ`, in the *same order* as produced by simp.
  -- (This avoids commutativity bookkeeping.)
  have hsplit :
      (∑ χ : DirichletCharacter ℂ n,
          χ (p : ZMod n) *
            (χ (((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n))⁻¹)
        =
        ( (1 : DirichletCharacter ℂ n) (p : ZMod n) *
            ((1 : DirichletCharacter ℂ n)
              (((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n))⁻¹) +
          ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)),
            χ (p : ZMod n) *
              (χ (((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n))⁻¹ := by
    simpa using
      (Fintype.sum_eq_add_sum_compl (a := (1 : DirichletCharacter ℂ n))
        (f := fun χ : DirichletCharacter ℂ n =>
          χ (p : ZMod n) *
            (χ (((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n))⁻¹))
  -- Now rewrite the integrand using this split.
  -- Note: the unsplit formula is already in `χ p * (χ a)⁻¹` form after simplification.
  simp [hsplit, mul_add, mul_comm, div_eq_mul_inv]

end

end Cyclotomic
end Chebotarev

end PrimeNumberTheoremAnd

