import PrimeNumberTheoremAnd.Chebotarev.Density.DirichletDensity

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Complex

/-!
# Invariants of rational-prime Dirichlet density

Lemmas showing that density data depends only on prime membership, that a density value is
unique, and that the limit is real when it exists.

See `DirichletDensity.lean` for definitions; Sharifi Def. 7.1.13 for the ideal-level analogue.
-/

namespace PrimeNumberTheoremAnd

namespace DirichletDensity

open Classical Complex Filter

open scoped Topology Real

section PrimeSupport

/--
Two sets of naturals agree on which rational primes they contain.

Only this data affects `coeff`, hence all Dirichlet-density series and limits.
-/
def EqOnPrimes (S T : Set ℕ) : Prop :=
  ∀ {p : ℕ}, p.Prime → (p ∈ S ↔ p ∈ T)

lemma eqOnPrimes.symm {S T : Set ℕ} (h : EqOnPrimes S T) : EqOnPrimes T S :=
  fun {p} hp => (h hp).symm

lemma eqOnPrimes.comm {S T : Set ℕ} : EqOnPrimes S T ↔ EqOnPrimes T S :=
  ⟨eqOnPrimes.symm, eqOnPrimes.symm⟩

lemma coeff_eq_of_eqOnPrimes {S T : Set ℕ} (h : EqOnPrimes S T) (n : ℕ) :
    coeff S n = coeff T n := by
  by_cases hn : n.Prime
  · simp [coeff, hn, h hn]
  · simp [coeff_of_not_prime S hn, coeff_of_not_prime T hn]

lemma seriesTerm_eq_of_eqOnPrimes {S T : Set ℕ} (h : EqOnPrimes S T) (s : ℝ) (n : ℕ) :
    seriesTerm S s n = seriesTerm T s n := by
  simp only [seriesTerm, coeff_eq_of_eqOnPrimes h]
  grind

lemma series_eq_of_eqOnPrimes {S T : Set ℕ} (h : EqOnPrimes S T) (s : ℝ) :
    series S s = series T s := by
  rw [series, series, LSeries_congr (fun {n} hn => coeff_eq_of_eqOnPrimes h n)]

lemma seriesAt_eq_of_eqOnPrimes {S T : Set ℕ} (h : EqOnPrimes S T) (s : ℝ)
    {hS : SeriesSummable S s} {hT : SeriesSummable T s} :
    seriesAt S s hS = seriesAt T s hT := by
  classical
  haveI : Summable (seriesTerm S s) := (seriesSummable_iff_summable_seriesTerm S s).1 hS
  haveI : Summable (seriesTerm T s) := (seriesSummable_iff_summable_seriesTerm T s).1 hT
  simp [seriesAt, seriesTerm_eq_of_eqOnPrimes h]

lemma ratioAt_eq_of_eqOnPrimes {S T : Set ℕ} (h : EqOnPrimes S T)
    {proof :
      ∀ {s : ℝ}, 1 < s → SeriesSummable S s ∧ SeriesSummable (Set.univ : Set ℕ) s}
    {proofT :
      ∀ {s : ℝ}, 1 < s → SeriesSummable T s ∧ SeriesSummable (Set.univ : Set ℕ) s}
    {s : ℝ} :
    ratioAt S proof s = ratioAt T proofT s := by
  by_cases hs : 1 < s
  · rw [ratioAt_of_one_lt S proof hs, ratioAt_of_one_lt T proofT hs, ratio,
      seriesAt_eq_of_eqOnPrimes h, show seriesAllAt s (proof hs).2 = seriesAllAt s (proofT hs).2 from rfl]
  · simp [ratioAt, hs]

end PrimeSupport

section Uniqueness

theorem HasDensity_unique (S : Set ℕ) {δ₁ δ₂ : ℂ}
    (h₁ : HasDensity S δ₁) (h₂ : HasDensity S δ₂) : δ₁ = δ₂ := by
  have h₁' := (hasDensity_iff_tendsto_ratioDefault S δ₁).1 h₁
  have h₂' := (hasDensity_iff_tendsto_ratioDefault S δ₂).1 h₂
  exact tendsto_nhds_unique h₁' h₂'

end Uniqueness

section RealDensity

lemma seriesTerm_im_zero (S : Set ℕ) (s : ℝ) (n : ℕ) : (seriesTerm S s n).im = 0 := by
  classical
  by_cases hn : n = 0
  · subst hn
    simp [seriesTerm, LSeries.term]
  · simp [seriesTerm, LSeries.term, hn, coeff]
    split_ifs <;> simp [Complex.div_im, Complex.ofReal_im, Complex.ofReal_re]

lemma series_im_zero (S : Set ℕ) {s : ℝ} (hS : SeriesSummable S s) : (series S s).im = 0 := by
  haveI : Summable (seriesTerm S s) := (seriesSummable_iff_summable_seriesTerm S s).1 hS
  rw [← seriesAt_eq_series S s hS, seriesAt, Complex.im_tsum]
  exact tsum_zero

lemma ratioAt_im_zero (S : Set ℕ)
    (proof :
      ∀ {s : ℝ}, 1 < s → SeriesSummable S s ∧ SeriesSummable (Set.univ : Set ℕ) s) (s : ℝ)
    (hs : 1 < s) : (ratioAt S proof s).im = 0 := by
  rw [ratioAt_of_one_lt S proof hs, ratio]
  rw [Complex.div_im]
  have hnum := series_im_zero S (proof hs).1
  have hden := series_im_zero (Set.univ : Set ℕ) (proof hs).2
  simp [hnum, hden]

lemma ratioDefault_im_zero (S : Set ℕ) (s : ℝ) : (ratioDefault S s).im = 0 := by
  by_cases hs : 1 < s
  · rw [ratioDefault_of_one_lt S hs]
    rw [Complex.div_im]
    have hnum := series_im_zero S (summable_series S hs)
    have hden := series_im_zero (Set.univ : Set ℕ) (summable_series (Set.univ : Set ℕ) hs)
    simp [hnum, hden]
  · simp [ratioDefault, ratioAt, hs]

theorem HasDensity.delta_im_zero (S : Set ℕ) (δ : ℂ) (h : HasDensity S δ) : δ.im = 0 := by
  have hT := (hasDensity_iff_tendsto_ratioDefault S δ).1 h
  have hEv :
      (fun s : ℝ => (ratioDefault S s).im) =ᶠ[nhdsWithin 1 (Set.Ioi 1)] fun _ => (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with s _hs
    exact ratioDefault_im_zero S s
  have hLimIm := hT.comp continuous_im.continuousAt
  have hZero : Tendsto (fun _ : ℝ => (0 : ℝ)) (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) :=
    tendsto_const_nhds
  have hT0 : Tendsto (fun s => (ratioDefault S s).im) (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) :=
    hZero.congr' hEv.symm
  exact tendsto_nhds_unique hT0 hLimIm

/-- A Dirichlet density value is real: `δ = (δ.re : ℂ)`. -/
theorem HasDensity.delta_eq_ofReal (S : Set ℕ) (δ : ℂ) (h : HasDensity S δ) :
    δ = (δ.re : ℂ) := by
  apply Complex.ext
  · rfl
  · exact HasDensity.delta_im_zero S δ h

end RealDensity

end DirichletDensity

end PrimeNumberTheoremAnd
