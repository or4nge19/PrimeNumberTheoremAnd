import PrimeNumberTheoremAnd.Chebotarev.Density.DirichletDensity
import PrimeNumberTheoremAnd.Chebotarev.Density.DirichletDensityIdeals
import PrimeNumberTheoremAnd.Chebotarev.Density.DirichletDensityIntBridge
import PrimeNumberTheoremAnd.Chebotarev.Density.DirichletDensityIntSummability
import PrimeNumberTheoremAnd.Chebotarev.Density.DirichletDensityTsumPrimes

import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Ideal-norm density on `ℤ` agrees with rational-prime density

Sharifi Def. 7.1.13 is stated for sets of prime ideals. For `R = ℤ`, this file proves the
equivalence with rational-prime Dirichlet density on the reindexed set `natPrimeImageOf S`:

`HasIdealDensity S δ ↔ HasDensity (natPrimeImageOf S) δ`.

The `(p) ↔ p` infrastructure is in `DirichletDensityIntBridge.lean`.
-/

namespace PrimeNumberTheoremAnd

namespace DirichletDensity

open Complex Filter Ideal Nat

open scoped Topology Real LSeries.notation

section BotTerm

lemma idealSeriesTerm_botPrimeIdeal (S : Set (PrimeIdeal ℤ)) (s : ℝ) :
    idealSeriesTerm S botPrimeIdeal s = 0 := by
  by_cases hs : s = 0
  · simp [hs, idealSeriesTerm, idealCoeff, idealNormTerm, botPrimeIdeal_val, Ideal.absNorm_bot,
      Real.rpow_zero, Complex.ofReal_zero, zero_mul]
  · have hsneg : (-s : ℝ) ≠ 0 := by linarith
    simp [idealSeriesTerm, idealCoeff, idealNormTerm, botPrimeIdeal_val,
      Ideal.absNorm_bot, Real.zero_rpow hsneg]

end BotTerm

section TermComparison

lemma coeff_natPrimeImageOf_prime (S : Set (PrimeIdeal ℤ)) (p : Nat.Primes) :
    coeff (natPrimeImageOf S) p =
      idealCoeff S (primeIdealOfNatPrime p) := by
  classical
  simp [coeff, natPrimeImageOf, primeIdealOfNatPrime, p.2]

lemma seriesTerm_eq_idealSeriesTerm (S : Set (PrimeIdeal ℤ)) (p : Nat.Primes) (s : ℝ) :
    seriesTerm (natPrimeImageOf S) s p = idealSeriesTerm S (primeIdealOfNatPrime p) s := by
  have hp0 : (p.1 : ℕ) ≠ 0 := p.2.ne_zero
  simp [seriesTerm, idealSeriesTerm, coeff_natPrimeImageOf_prime, LSeries.term, p.2, hp0,
    absNorm_primeIdealOfNatPrime, div_eq_mul_inv]

noncomputable def optionSeriesTerm (S : Set (PrimeIdeal ℤ)) (s : ℝ) : Option Nat.Primes → ℂ
  | none => 0
  | some p => idealSeriesTerm S (primeIdealOfNatPrime p) s

lemma idealSeriesTerm_eq_optionSeriesTerm_comp (S : Set (PrimeIdeal ℤ)) (s : ℝ)
    (P : PrimeIdeal ℤ) :
    idealSeriesTerm S P s = optionSeriesTerm S s (primeIdealToOption P) := by
  by_cases h : P.1 = ⊥
  · have hP : P = botPrimeIdeal := Subtype.ext (h.trans botPrimeIdeal_val.symm)
    rw [hP]
    simp [idealSeriesTerm_botPrimeIdeal, optionSeriesTerm, primeIdealToOption, botPrimeIdeal_val]
  · simp [optionSeriesTerm, primeIdealToOption, h, primeIdealOfNatPrime_eq_of_nonZero]

lemma idealSeries_eq_tsum_option (S : Set (PrimeIdeal ℤ)) (s : ℝ)
    (hS : IdealSeriesSummable (R := ℤ) S s) :
    idealSeries S s hS =
      ∑' o : Option Nat.Primes, optionSeriesTerm S s o := by
  classical
  haveI := hS
  rw [idealSeries, ← (Equiv.tsum_eq primeIdealOptionEquiv (f := optionSeriesTerm S s))]
  refine tsum_congr fun P => ?_
  exact (idealSeriesTerm_eq_optionSeriesTerm_comp S s P).symm

lemma summable_optionSeriesTerm (S : Set (PrimeIdeal ℤ)) (s : ℝ)
    (hS : IdealSeriesSummable (R := ℤ) S s) :
    Summable (optionSeriesTerm S s) := by
  rw [← (Equiv.summable_iff primeIdealOptionEquiv)]
  simpa [Function.comp, idealSeriesTerm_eq_optionSeriesTerm_comp] using hS

lemma tsum_optionSeriesTerm_eq_tsum_primes (S : Set (PrimeIdeal ℤ)) (s : ℝ)
    (hS : IdealSeriesSummable (R := ℤ) S s) :
    (∑' o : Option Nat.Primes, optionSeriesTerm S s o) =
      ∑' p : Nat.Primes, idealSeriesTerm S (primeIdealOfNatPrime p) s := by
  classical
  have hf := summable_optionSeriesTerm S s hS
  haveI := hf
  rw [show (∑' o : Option Nat.Primes, optionSeriesTerm S s o) =
      ∑' o : (Set.univ \ {none} : Set (Option Nat.Primes)), optionSeriesTerm S s o from
    (tsum_eq_tsum_diff_singleton (s := Set.univ) (b := none) (hf₀ := rfl)).symm]
  rw [show (Set.univ \ {none} : Set (Option Nat.Primes)) = Set.range Option.some by
    ext o
    cases o <;> simp [Option.some_inj]]
  rw [tsum_range Option.some_injective]
  rfl

theorem idealSeries_int_eq_series_natPrimeImageOf (S : Set (PrimeIdeal ℤ)) (s : ℝ)
    (hS : IdealSeriesSummable (R := ℤ) S s) (hs : 1 < s) :
    idealSeries S s hS = series (natPrimeImageOf S) s := by
  classical
  have hNat : SeriesSummable (natPrimeImageOf S) s := summable_series (natPrimeImageOf S) hs
  haveI : Summable (seriesTerm (natPrimeImageOf S) s) :=
    (seriesSummable_iff_summable_seriesTerm (natPrimeImageOf S) s).1 hNat
  rw [seriesAt_eq_series (natPrimeImageOf S) s hNat, seriesAt, series, LSeries]
  rw [idealSeries_eq_tsum_option S s hS, tsum_optionSeriesTerm_eq_tsum_primes S s hS]
  refine tsum_congr fun p => (seriesTerm_eq_idealSeriesTerm S p s).symm

theorem idealSeriesAll_int_eq_seriesAll {s : ℝ} (hs : 1 < s)
    (hAll : IdealSeriesSummable (R := ℤ) (Set.univ : Set (PrimeIdeal ℤ)) s) :
    idealSeriesAll s hAll = seriesAll s :=
  idealSeries_int_eq_series_natPrimeImageOf (Set.univ : Set (PrimeIdeal ℤ)) s hAll hs

end TermComparison

section RatioBridge

lemma idealRatio_int_eq_ratioDefault (S : Set (PrimeIdeal ℤ)) (s : ℝ)
    (hS : IdealSeriesSummable (R := ℤ) S s)
    (hAll : IdealSeriesSummable (R := ℤ) (Set.univ : Set (PrimeIdeal ℤ)) s) (hs : 1 < s) :
    idealRatio S s hS hAll = ratioDefault (natPrimeImageOf S) s := by
  simp [idealRatio, ratioDefault, ratioAt, ratio, hs,
    idealSeries_int_eq_series_natPrimeImageOf S s hS hs,
    idealSeriesAll_int_eq_seriesAll hs hAll]

lemma idealRatioAt_int_eq_ratioDefault (S : Set (PrimeIdeal ℤ))
    (proof :
      ∀ {s : ℝ}, 1 < s →
        IdealSeriesSummable (R := ℤ) S s ∧
          IdealSeriesSummable (R := ℤ) (Set.univ : Set (PrimeIdeal ℤ)) s) (s : ℝ) :
    idealRatioAt (R := ℤ) S proof s = ratioDefault (natPrimeImageOf S) s := by
  by_cases hs : 1 < s
  · simp [idealRatioAt, ratioDefault, ratioAt, hs,
      idealRatio_int_eq_ratioDefault S s (proof hs).1 (proof hs).2 hs]
  · simp [idealRatioAt, ratioDefault, ratioAt, hs]

theorem hasIdealDensity_iff_hasDensity_natPrimeImageOf
    (S : Set (PrimeIdeal ℤ)) (delta : ℂ) :
    HasIdealDensity (R := ℤ) S delta ↔ HasDensity (natPrimeImageOf S) delta := by
  constructor
  · rintro ⟨proof, hT⟩
    refine ⟨seriesSummableProof (natPrimeImageOf S), hT.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s _hs
    exact (idealRatioAt_int_eq_ratioDefault S proof s).symm
  · rintro ⟨proof, hT⟩
    refine ⟨idealSeriesSummableProof_int S, hT.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s _hs
    exact idealRatioAt_int_eq_ratioDefault S (idealSeriesSummableProof_int S) s

end RatioBridge

end DirichletDensity

end PrimeNumberTheoremAnd
