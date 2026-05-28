import PrimeNumberTheoremAnd.Chebotarev.Density.DirichletDensity

import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Ideal-norm Dirichlet density (Sharifi Def. 7.1.13)

Sharifi's Dirichlet density for a set of prime ideals uses the absolute norm `N(𝔭) = |R/𝔭|`.
This file mirrors `DirichletDensity.lean` at the ideal level:

* local factors `idealSeriesTerm`, indexed by **prime ideals**;
* `IdealSeriesSummable`, an explicit summability hypothesis (avoids silent `tsum = 0`);
* `HasIdealDensity`, a `Tendsto` limit of the prime-ideal series ratio.

For `R = ℤ`, the reindexing `(p) ↔ p` is in `DirichletDensityIntBridge.lean` and summability
at `s > 1` is proved in `DirichletDensityIntSummability.lean`. The general Dedekind-domain
summability input for general Dedekind domains remains open
(`OpenHypotheses.idealSeriesSummable_of_one_lt`, currently `sorry`).
-/

namespace PrimeNumberTheoremAnd

open scoped Real Topology

namespace DirichletDensity

open Complex Filter

section IdealWeights

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

open Classical

/--
Prime ideals of `R`, as a subtype (Sharifi's index set for Def. 7.1.13).
-/
abbrev PrimeIdeal (R : Type*) [CommRing R] := {P : Ideal R // P.IsPrime}

@[simp]
lemma PrimeIdeal.isPrime (P : PrimeIdeal R) : P.1.IsPrime := P.2

@[simp]
lemma PrimeIdeal.coe_isPrime (P : Ideal R) (hP : P.IsPrime) :
    (⟨P, hP⟩ : PrimeIdeal R).1 = P := rfl

/--
Indicator weight at a prime ideal, for a set `S` of prime ideals of `R`.
-/
noncomputable def idealCoeff (S : Set (PrimeIdeal R)) (P : PrimeIdeal R) : ℂ :=
  if P ∈ S then (1 : ℂ) else 0

lemma idealCoeff_apply (S : Set (PrimeIdeal R)) (P : PrimeIdeal R) :
    idealCoeff S P = if P ∈ S then (1 : ℂ) else 0 := rfl

/--
Ideal-norm monomial `N(P)^{-s}` at a prime ideal `P`.
Uses mathlib's `Ideal.absNorm`.
-/
noncomputable def idealNormTerm [Module.Free ℤ R] (P : PrimeIdeal R) (s : ℝ) : ℂ :=
  (Real.rpow (Ideal.absNorm P.1 : ℝ) (-s) : ℂ)

/--
Weighted Dirichlet term `𝟙_{P ∈ S} · N(P)^{-s}` at a prime ideal.

This is the local factor in Sharifi's numerator for Def. 7.1.13.
-/
noncomputable def idealSeriesTerm [Module.Free ℤ R] (S : Set (PrimeIdeal R)) (P : PrimeIdeal R)
    (s : ℝ) : ℂ :=
  idealCoeff S P * idealNormTerm P s

lemma idealSeriesTerm_eq [Module.Free ℤ R] (S : Set (PrimeIdeal R)) (P : PrimeIdeal R) (s : ℝ) :
    idealSeriesTerm S P s = idealCoeff S P * idealNormTerm P s := rfl

lemma idealSeriesTerm_not_mem [Module.Free ℤ R] {S : Set (PrimeIdeal R)} {P : PrimeIdeal R} (s : ℝ)
    (h : P ∉ S) : idealSeriesTerm S P s = 0 := by
  simp [idealSeriesTerm, idealCoeff, h]

end IdealWeights

section IdealSeries

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R]

open Classical

/--
The prime-ideal Dirichlet series for `S` converges absolutely at `s`.

This predicate is part of the data for `idealSeries`, `idealRatio`, and `HasIdealDensity`.
It prevents using `tsum` when the series diverges.
-/
def IdealSeriesSummable (S : Set (PrimeIdeal R)) (s : ℝ) : Prop :=
  Summable (fun P : PrimeIdeal R => idealSeriesTerm S P s)

noncomputable def idealSeries (S : Set (PrimeIdeal R)) (s : ℝ) (hS : IdealSeriesSummable S s) : ℂ := by
  classical
  haveI := hS
  exact ∑' P : PrimeIdeal R, idealSeriesTerm S P s

noncomputable def idealSeriesAll (s : ℝ) (hAll : IdealSeriesSummable (Set.univ : Set (PrimeIdeal R)) s) :
    ℂ :=
  idealSeries (S := Set.univ) s hAll

noncomputable def idealRatio (S : Set (PrimeIdeal R)) (s : ℝ)
    (hS : IdealSeriesSummable S s) (hAll : IdealSeriesSummable (Set.univ : Set (PrimeIdeal R)) s) :
    ℂ :=
  idealSeries S s hS / idealSeriesAll s hAll

/--
The ideal-level density ratio, bundled with summability proofs.

Defined as `0` for `s ≤ 1`; the `Tendsto` in `HasIdealDensity` only probes `s → 1⁺`.
-/
noncomputable def idealRatioAt (S : Set (PrimeIdeal R))
    (proof :
      ∀ {s : ℝ}, 1 < s →
        IdealSeriesSummable S s ∧ IdealSeriesSummable (Set.univ : Set (PrimeIdeal R)) s) (s : ℝ) :
    ℂ :=
  if hs : 1 < s then
    idealRatio S s (proof hs).1 (proof hs).2
  else 0

/--
Sharifi Def. 7.1.13: Dirichlet density of a set of prime ideals, as a `Tendsto` limit at `s → 1⁺`.

The summability side conditions are part of the data, mirroring the guardrails in
`DirichletDensity.HasDensity` and `DirichletDensity.ratioAt`.
-/
def HasIdealDensity (S : Set (PrimeIdeal R)) (delta : ℂ) : Prop :=
  ∃ (proof :
      ∀ {s : ℝ}, 1 < s →
        IdealSeriesSummable S s ∧ IdealSeriesSummable (Set.univ : Set (PrimeIdeal R)) s),
    Tendsto (idealRatioAt (R := R) (S := S) proof) (nhdsWithin 1 (Set.Ioi 1)) (nhds delta)

lemma idealCoeff_mem {S : Set (PrimeIdeal R)} {P : PrimeIdeal R} (h : P ∈ S) :
    idealCoeff S P = 1 := by
  simp [idealCoeff, h]

lemma idealCoeff_not_mem {S : Set (PrimeIdeal R)} {P : PrimeIdeal R} (h : P ∉ S) :
    idealCoeff S P = 0 := by
  simp [idealCoeff, h]

lemma idealSeriesTerm_mem [Module.Free ℤ R] {S : Set (PrimeIdeal R)} {P : PrimeIdeal R} (s : ℝ)
    (h : P ∈ S) : idealSeriesTerm S P s = idealNormTerm P s := by
  simp [idealSeriesTerm, idealCoeff, h]

end IdealSeries

end DirichletDensity

end PrimeNumberTheoremAnd
