import PrimeNumberTheoremAnd.Chebotarev.Cyclotomic.FrobeniusMainTerm
import PrimeNumberTheoremAnd.Chebotarev.Cyclotomic.FiniteCorrectionBound
import PrimeNumberTheoremAnd.Chebotarev.Density.PrimeSeriesSummable
import PrimeNumberTheoremAnd.Chebotarev.Density.DirichletDensityLimitCriterion
import PrimeNumberTheoremAnd.Chebotarev.Density.SeriesAllDivergesNearOne

import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
## Cyclotomic case: Dirichlet density assuming bounded nontrivial prime error

This file proves the clean conditional reduction:

If the prime `tsum` coming from nontrivial Dirichlet characters is bounded as `s → 1⁺`, then the
cyclotomic Frobenius prime set has Dirichlet density `1/φ(n)`.

All other ingredients are unconditional and already established in this project:
- the prime-`tsum` expression for the ratio;
- divergence of `‖seriesAll s‖` as `s → 1⁺`;
- boundedness of the finite correction from primes dividing `n`.
-/

namespace PrimeNumberTheoremAnd
namespace Chebotarev
namespace Cyclotomic

open scoped Classical Cyclotomic NumberField

open Filter Nat.Primes

open PrimeNumberTheoremAnd.DirichletDensity
open IsCyclotomicExtension

section

variable {n : ℕ} [NeZero n]
variable (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {n} ℚ L]

noncomputable
def nontrivPrimeError (σ : Gal(L/ℚ)) (s : ℝ) : ℂ :=
  ∑' p : Nat.Primes,
    (((1 : ℂ) / (n.totient : ℂ)) *
        (∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)),
          χ ((((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n)⁻¹) *
            χ (p : ZMod n))) /
      ((p : ℂ) ^ (s : ℂ))

lemma ratio_frobPrimeSet_eq_main_add_div (σ : Gal(L/ℚ)) {s : ℝ} (hs : 1 < s)
    (h0 : seriesAll s ≠ 0) :
    ratioDefault (frobPrimeSet (n := n) (L := L) σ) s =
      ((1 : ℂ) / (n.totient : ℂ)) +
        (nontrivPrimeError (n := n) (L := L) σ s -
            ((1 : ℂ) / (n.totient : ℂ)) *
              (∑' p : Nat.Primes, (if (p.1 ∣ n) then (1 : ℂ) else 0) / ((p : ℂ) ^ (s : ℂ)))) /
          seriesAll s := by
  classical
  -- Start from the main-term split in terms of prime `tsum`.
  have h :=
    ratio_frobPrimeSet_eq_tsum_primes_character_split_main (n := n) (L := L) (σ := σ) hs
  -- Replace the denominator `tsum` by `seriesAll s`.
  have hden : (∑' p : Nat.Primes, (1 : ℂ) / ((p : ℂ) ^ (s : ℂ))) = seriesAll s := by
    simpa using (seriesAll_eq_tsum_primes (s := s) hs).symm

  -- Abbreviations.
  set c : ℂ := (1 : ℂ) / (n.totient : ℂ)
  set base : Nat.Primes → ℂ := fun p ↦ (1 : ℂ) / ((p : ℂ) ^ (s : ℂ))
  set ind : Nat.Primes → ℂ := fun p ↦ if (p.1 ∣ n) then (1 : ℂ) else 0
  set nt : Nat.Primes → ℂ := fun p ↦
    ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)),
      χ ((((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n)⁻¹) * χ (p : ZMod n)

  have hbase : Summable base := by
    simpa [base] using (summable_primes_one_div_cpow_of_one_lt_real (s := s) hs)

  have hind : Summable (fun p : Nat.Primes ↦ ind p * base p) := by
    -- finite support: primes dividing `n`
    have hsubset :
        Function.support (fun p : Nat.Primes ↦ ind p * base p) ⊆ (primesDividing n : Set Nat.Primes) := by
      intro p hp
      have hind0 : ind p ≠ 0 := by
        intro h0
        have : ind p * base p = 0 := by simp [h0]
        exact hp (by simpa [Function.mem_support] using this)
      by_cases hpn : (p.1 ∣ n)
      · exact (mem_primesDividing_iff (n := n) (p := p)).2 hpn
      · simp [ind, hpn] at hind0
    have hfinite : (Function.support (fun p : Nat.Primes ↦ ind p * base p)).Finite :=
      (primesDividing n).finite_toSet.subset hsubset
    exact summable_of_finite_support hfinite

  have hnt : Summable (fun p : Nat.Primes ↦ c * nt p * base p) := by
    -- crude bound: `‖nt p‖ ≤ card`, then compare with `‖base p‖`
    have hR : Summable (fun p : Nat.Primes ↦ ‖c‖ * (({1}ᶜ : Finset (DirichletCharacter ℂ n)).card : ℝ) *
        ‖base p‖) := by
      simpa [mul_assoc] using
        (hbase.norm.mul_left (‖c‖ * (({1}ᶜ : Finset (DirichletCharacter ℂ n)).card : ℝ)))
    refine Summable.of_norm_bounded hR ?_
    intro p
    have hχ :
        ‖nt p‖ ≤ (({1}ᶜ : Finset (DirichletCharacter ℂ n)).card : ℝ) := by
      classical
      -- `‖∑‖ ≤ ∑ ‖‖` and each term has norm ≤ 1
      have htri :
          ‖nt p‖ ≤ ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)),
            ‖χ ((((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n)⁻¹) * χ (p : ZMod n)‖ := by
        simpa [nt] using
          (norm_sum_le ({1}ᶜ : Finset (DirichletCharacter ℂ n))
            (fun χ ↦ χ ((((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n)⁻¹) * χ (p : ZMod n)))
      have hle :
          (∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)),
              ‖χ ((((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n)⁻¹) * χ (p : ZMod n)‖)
            ≤ ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)), (1 : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro χ _
        have h1 : ‖χ ((((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n)⁻¹)‖ ≤ 1 :=
          (DirichletCharacter.norm_le_one (χ := χ) _)
        have h2 : ‖χ (p : ZMod n)‖ ≤ 1 := (DirichletCharacter.norm_le_one (χ := χ) _)
        simpa [norm_mul] using (mul_le_mul h1 h2 (by positivity) zero_le_one)
      have hcard :
          (∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)), (1 : ℝ))
            = (({1}ᶜ : Finset (DirichletCharacter ℂ n)).card : ℝ) := by
        simp
      exact htri.trans (hle.trans_eq hcard)
    calc
      ‖c * nt p * base p‖ = ‖c‖ * ‖nt p‖ * ‖base p‖ := by
        simp [mul_assoc]
      _ ≤ ‖c‖ * (({1}ᶜ : Finset (DirichletCharacter ℂ n)).card : ℝ) * ‖base p‖ := by
        gcongr
      _ = ‖c‖ * (({1}ᶜ : Finset (DirichletCharacter ℂ n)).card : ℝ) * ‖base p‖ := rfl

  -- Rewrite the numerator as `c * tsum base + (tsum(c*nt*base) - c*tsum(ind*base))`.
  have hif : (fun p : Nat.Primes ↦ (if (p.1 ∣ n) then (0 : ℂ) else 1)) =
      fun p : Nat.Primes ↦ (1 : ℂ) - ind p := by
    funext p
    by_cases hp : (p.1 ∣ n) <;> simp [ind, hp]

  -- Convert `h` to the `base`-notation and replace the denominator.
  have h' :
      ratioDefault (frobPrimeSet (n := n) (L := L) σ) s =
        (∑' p : Nat.Primes, (c * ((if (p.1 ∣ n) then (0 : ℂ) else 1) + nt p)) / ((p : ℂ) ^ (s : ℂ))) /
          seriesAll s := by
    -- This is `h`, with `nt` unfolded and the denominator rewritten to `seriesAll s`.
    simpa [nt, hden] using h

  have h'_base :
      ratioDefault (frobPrimeSet (n := n) (L := L) σ) s =
        (∑' p : Nat.Primes, c * ((if (p.1 ∣ n) then (0 : ℂ) else 1) + nt p) * base p) / seriesAll s := by
    have hn :
        (∑' p : Nat.Primes, (c * ((if (p.1 ∣ n) then (0 : ℂ) else 1) + nt p)) / ((p : ℂ) ^ (s : ℂ))) =
          ∑' p : Nat.Primes, c * ((if (p.1 ∣ n) then (0 : ℂ) else 1) + nt p) * base p := by
      refine tsum_congr ?_
      intro p
      simp [base, div_eq_mul_inv, mul_assoc]
    simpa [hn] using h'

  -- Now expand the integrand pointwise (case split on `p ∣ n`) and use `tsum` linearity.
  -- First: `c*((if..)+nt)*base = c*base - c*(ind*base) + c*nt*base`.
  have hterm :
      (fun p : Nat.Primes ↦ c * ((if (p.1 ∣ n) then (0 : ℂ) else 1) + nt p) * base p)
        =
      fun p : Nat.Primes ↦ (c * base p + c * nt p * base p) - c * (ind p * base p) := by
    funext p
    by_cases hp : (p.1 ∣ n)
    · simp [ind, base, hp]
    · simp [ind, base, hp]; ring

  have hsum :
      (∑' p : Nat.Primes, c * ((if (p.1 ∣ n) then (0 : ℂ) else 1) + nt p) * base p)
        =
      (c * (∑' p : Nat.Primes, base p) + (∑' p : Nat.Primes, c * nt p * base p)) -
        (∑' p : Nat.Primes, c * (ind p * base p)) := by
    -- apply `tsum` to the pointwise identity and use `Summable` linearity
    have hsum1 : Summable (fun p : Nat.Primes ↦ c * base p) := hbase.mul_left c
    have hsum2 : Summable (fun p : Nat.Primes ↦ c * nt p * base p) := hnt
    have hsum3 : Summable (fun p : Nat.Primes ↦ c * (ind p * base p)) := (hind.mul_left c)
    -- `tsum (a - b) = tsum a - tsum b`, `tsum (a + b) = tsum a + tsum b`
    calc
      (∑' p : Nat.Primes, c * ((if (p.1 ∣ n) then (0 : ℂ) else 1) + nt p) * base p)
          = ∑' p : Nat.Primes, ((c * base p + c * nt p * base p) - c * (ind p * base p)) := by
              simp [hterm]
      _ = (∑' p : Nat.Primes, (c * base p + c * nt p * base p)) - (∑' p : Nat.Primes, c * (ind p * base p)) := by
              simpa using ( (hsum1.add hsum2).tsum_sub hsum3 )
      _ = (c * (∑' p : Nat.Primes, base p) + (∑' p : Nat.Primes, c * nt p * base p)) -
            (∑' p : Nat.Primes, c * (ind p * base p)) := by
              -- expand the `tsum` of the sum and pull out the constant
              simp [hsum1.tsum_add hsum2, tsum_mul_left]

  have hbase_tsum : (∑' p : Nat.Primes, base p) = seriesAll s := by
    -- by definition of `base` and `hden`
    have : (∑' p : Nat.Primes, (1 : ℂ) / ((p : ℂ) ^ (s : ℂ))) = seriesAll s := hden
    simpa [base] using this

  have hnontriv_def :
      nontrivPrimeError (n := n) (L := L) σ s = (∑' p : Nat.Primes, c * nt p * base p) := by
    simp [nontrivPrimeError, c, nt, base, div_eq_mul_inv, mul_assoc]

  -- Conclude by dividing by `seriesAll s` and simplifying.
  calc
    ratioDefault (frobPrimeSet (n := n) (L := L) σ) s
        = (∑' p : Nat.Primes, c * ((if (p.1 ∣ n) then (0 : ℂ) else 1) + nt p) * base p) / seriesAll s := h'_base
    _ = ((c * (∑' p : Nat.Primes, base p) + (∑' p : Nat.Primes, c * nt p * base p)) -
          (∑' p : Nat.Primes, c * (ind p * base p))) / seriesAll s := by
          simp [hsum]
    _ = c + ( (∑' p : Nat.Primes, c * nt p * base p) - (∑' p : Nat.Primes, c * (ind p * base p)) ) / seriesAll s := by
          -- use `∑ base = seriesAll` and `seriesAll s ≠ 0` to simplify the main term.
          -- We rewrite everything in terms of `div` to avoid accidental simplifications at `seriesAll s = 0`.
          -- Clear denominators using `field_simp`.
          -- First rewrite `∑ base` into `seriesAll`.
          rw [hbase_tsum]
          field_simp [h0]
          ring
    _ = ((1 : ℂ) / (n.totient : ℂ)) +
          (nontrivPrimeError (n := n) (L := L) σ s -
              ((1 : ℂ) / (n.totient : ℂ)) *
                (∑' p : Nat.Primes, (if (p.1 ∣ n) then (1 : ℂ) else 0) / ((p : ℂ) ^ (s : ℂ)))) /
            seriesAll s := by
          -- rewrite the remaining `tsum` pieces
          -- `ind*base` is exactly the finite correction term, and `tsum` is linear for summable series.
          have hind_def :
              (∑' p : Nat.Primes, c * (ind p * base p)) =
                c * (∑' p : Nat.Primes, ind p * base p) := by
            simpa using (hind.tsum_mul_left c)
          have hind_base :
              (∑' p : Nat.Primes, ind p * base p) =
                ∑' p : Nat.Primes, (if (p.1 ∣ n) then (1 : ℂ) else 0) / ((p : ℂ) ^ (s : ℂ)) := by
            refine tsum_congr ?_
            intro p
            simp [ind, base, div_eq_mul_inv]
          have hfinite :
              (∑' p : Nat.Primes, c * (ind p * base p)) =
                c * (∑' p : Nat.Primes, (if (p.1 ∣ n) then (1 : ℂ) else 0) / ((p : ℂ) ^ (s : ℂ))) := by
            simpa [hind_base] using hind_def
          have hnontriv' :
              (∑' p : Nat.Primes, c * nt p * base p) =
                nontrivPrimeError (n := n) (L := L) σ s := by
            simpa using hnontriv_def.symm
          -- finalize without unfolding the big definitions again
          have hfinite' :
              (∑' p : Nat.Primes, c * (ind p * base p)) =
                (↑n.totient : ℂ)⁻¹ *
                  (∑' p : Nat.Primes, (if (p.1 ∣ n) then (1 : ℂ) else 0) / ((p : ℂ) ^ (s : ℂ))) := by
            simpa [c] using hfinite
          have hntsum :
              (∑' p : Nat.Primes, (↑n.totient : ℂ)⁻¹ * nt p * base p) =
                nontrivPrimeError (n := n) (L := L) σ s := by
            have hconv :
                (∑' p : Nat.Primes, (↑n.totient : ℂ)⁻¹ * nt p * base p) =
                  ∑' p : Nat.Primes, c * nt p * base p := by
              refine tsum_congr ?_
              intro p
              simp [c]
            -- rewrite via `hnontriv'`
            simpa [hconv] using hnontriv'

          have hftsum :
              (∑' p : Nat.Primes, (↑n.totient : ℂ)⁻¹ * (ind p * base p)) =
                (↑n.totient : ℂ)⁻¹ *
                  (∑' p : Nat.Primes, (if (p.1 ∣ n) then (1 : ℂ) else 0) / ((p : ℂ) ^ (s : ℂ))) := by
            have hconv :
                (∑' p : Nat.Primes, (↑n.totient : ℂ)⁻¹ * (ind p * base p)) =
                  ∑' p : Nat.Primes, c * (ind p * base p) := by
              refine tsum_congr ?_
              intro p
              simp [c]
            simpa [hconv] using hfinite'

          -- now just rewrite
          simp [c, hntsum, hftsum, sub_eq_add_neg]

theorem hasDensity_frobPrimeSet_of_boundedNontriv (σ : Gal(L/ℚ))
    (hBoundNontriv : ∃ M : ℝ,
      (fun s : ℝ ↦ ‖nontrivPrimeError (n := n) (L := L) σ s‖) ≤ᶠ[nhdsWithin 1 (Set.Ioi 1)]
        fun _ ↦ M) :
    HasDensity (frobPrimeSet (n := n) (L := L) σ) ((1 : ℂ) / (n.totient : ℂ)) := by
  -- expresse into the general criterion.
  -- Set `E(s) = nontrivPrimeError(s) - c * finiteCorrection(s)`.
  let E : ℝ → ℂ :=
    fun s ↦ nontrivPrimeError (n := n) (L := L) σ s -
      ((1 : ℂ) / (n.totient : ℂ)) *
        (∑' p : Nat.Primes, (if (p.1 ∣ n) then (1 : ℂ) else 0) / ((p : ℂ) ^ (s : ℂ)))
  have hEq :
      (fun s : ℝ ↦ ratioDefault (frobPrimeSet (n := n) (L := L) σ) s) =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
        fun s ↦ ((1 : ℂ) / (n.totient : ℂ)) + E s / seriesAll s := by
    have hs_gt : ∀ᶠ s : ℝ in nhdsWithin 1 (Set.Ioi 1), 1 < s := by
      simpa [Set.mem_Ioi] using (self_mem_nhdsWithin : Set.Ioi (1 : ℝ) ∈ nhdsWithin 1 (Set.Ioi 1))
    have h0 : ∀ᶠ s : ℝ in nhdsWithin 1 (Set.Ioi 1), seriesAll s ≠ 0 := by
      have hge : ∀ᶠ s : ℝ in nhdsWithin 1 (Set.Ioi 1), (1 : ℝ) ≤ ‖seriesAll s‖ :=
        (tendsto_atTop.1 PrimeNumberTheoremAnd.DirichletDensity.tendsto_norm_seriesAll_atTop) 1
      filter_upwards [hge] with s hs
      intro hsz
      have : (1 : ℝ) ≤ (0 : ℝ) := by simpa [hsz] using hs
      exact (not_le_of_gt zero_lt_one) this
    filter_upwards [hs_gt, h0] with s hs hs0
    simpa [E] using (ratio_frobPrimeSet_eq_main_add_div (n := n) (L := L) (σ := σ) hs hs0)
  -- boundedness of `E` follows from boundedness of nontrivial term and finite correction bound
  rcases hBoundNontriv with ⟨M1, hM1⟩
  rcases eventually_norm_tsum_primes_dvd_le (n := n) with ⟨M2, hM2⟩
  have hBound : ∃ M : ℝ, (fun s : ℝ ↦ ‖E s‖) ≤ᶠ[nhdsWithin 1 (Set.Ioi 1)] fun _ ↦ M := by
    refine ⟨M1 + ‖(1 : ℂ) / (n.totient : ℂ)‖ * M2, ?_⟩
    filter_upwards [hM1, hM2] with s hs1 hs2
    have hs2' :
        ‖∑' p : Nat.Primes, (if (p.1 ∣ n) then (1 : ℂ) else 0) / ((p : ℂ) ^ (s : ℂ))‖ ≤ M2 := hs2
    -- triangle inequality
    have : ‖E s‖ ≤ ‖nontrivPrimeError (n := n) (L := L) σ s‖ +
        ‖((1 : ℂ) / (n.totient : ℂ)) *
          (∑' p : Nat.Primes, (if (p.1 ∣ n) then (1 : ℂ) else 0) / ((p : ℂ) ^ (s : ℂ)))‖ :=
      (norm_sub_le _ _)
    calc
      ‖E s‖
          ≤ ‖nontrivPrimeError (n := n) (L := L) σ s‖ +
              ‖((1 : ℂ) / (n.totient : ℂ)) *
                (∑' p : Nat.Primes, (if (p.1 ∣ n) then (1 : ℂ) else 0) / ((p : ℂ) ^ (s : ℂ)))‖ := this
      _ ≤ M1 + (‖(1 : ℂ) / (n.totient : ℂ)‖ *
                ‖∑' p : Nat.Primes, (if (p.1 ∣ n) then (1 : ℂ) else 0) / ((p : ℂ) ^ (s : ℂ))‖) := by
            gcongr
            have hnorm :
                ‖((1 : ℂ) / (n.totient : ℂ)) *
                      (∑' p : Nat.Primes,
                        (if (p.1 ∣ n) then (1 : ℂ) else 0) / ((p : ℂ) ^ (s : ℂ)))‖
                  =
                  ‖(1 : ℂ) / (n.totient : ℂ)‖ *
                    ‖∑' p : Nat.Primes,
                        (if (p.1 ∣ n) then (1 : ℂ) else 0) / ((p : ℂ) ^ (s : ℂ))‖ := by
                simp
            exact le_of_eq hnorm
      _ ≤ M1 + ‖(1 : ℂ) / (n.totient : ℂ)‖ * M2 := by
            gcongr
  -- Apply the criterion.
  exact PrimeNumberTheoremAnd.DirichletDensity.hasDensity_of_eq_add_div
    (S := frobPrimeSet (n := n) (L := L) σ)
    (a := (1 : ℂ) / (n.totient : ℂ))
    (E := E)
    (hEq := hEq) (hBound := hBound)
    (hDen := PrimeNumberTheoremAnd.DirichletDensity.tendsto_norm_seriesAll_atTop)

end

end Cyclotomic
end Chebotarev
end PrimeNumberTheoremAnd
