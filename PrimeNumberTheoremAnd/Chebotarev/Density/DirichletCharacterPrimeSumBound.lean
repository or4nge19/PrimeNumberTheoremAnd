import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HolomorphicLogBall

import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Topology.Order.LeftRightNhds

/-!
# Boundedness of prime Dirichlet series for nontrivial characters near `s = 1⁺`

This file provides the analytic input needed in the cyclotomic Chebotarev density argument
(Sharifi Prop. 7.2.1 / orthogonality step): for a nontrivial Dirichlet character `χ`, the prime
series `∑' p, χ p / p^s` is **bounded** as `s → 1⁺` (real).

## Proof strategy

1. Introduce the prime-log series `Hχ(s) = ∑' p, -log(1 - χ(p) p^{-s})`.
2. Show `exp(Hχ(s)) = LFunction χ s` for `1 < re s` via `DirichletCharacter.LSeries_eulerProduct_exp_log`.
3. Use nonvanishing of `LFunction χ` at `s = 1` and continuity to obtain a holomorphic log on a
   small disk around `1` (`Complex.DifferentiableOn.exists_log_of_ball`).
4. Deduce that `Hχ` differs from this holomorphic log by a constant on `(1, 1+ε)`, hence is bounded.
5. Transfer boundedness to `∑' p, χ(p)/p^s` using Taylor bounds for `log(1+z) - z`
   (`ChebotarevDirichletCharacterPrimeSeriesBound`).

## Tags

Dirichlet character, L-series, Chebotarev density, Euler product
-/

namespace PrimeNumberTheoremAnd

open scoped Classical Real Topology

open Filter Complex Metric

namespace Chebotarev

namespace DirichletCharacterPrime

open Nat.Primes

variable {N : ℕ} [NeZero N]

/-!
### Prime Dirichlet series

These are the prime-indexed summands appearing in the Euler product logarithm for Dirichlet
L-series.
-/

/-- The prime-log series `∑' p, -log(1 - χ(p) p^{-s})` from the Euler product. -/
noncomputable abbrev primeLogSeries (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, -Complex.log (1 - χ p * (p : ℂ) ^ (-s))

/-- The prime coefficient series `∑' p, χ(p) p^{-s}`. -/
noncomputable abbrev primeSeries (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, χ p * (p : ℂ) ^ (-s)

lemma exp_primeLogSeries_eq_LSeries (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (primeLogSeries (N := N) χ s) = LSeries ((χ ·) : ℕ → ℂ) s := by
  simpa [primeLogSeries] using
    (DirichletCharacter.LSeries_eulerProduct_exp_log (χ := χ) (s := s) hs)

lemma exp_primeLogSeries_eq_LFunction (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (primeLogSeries (N := N) χ s) = DirichletCharacter.LFunction χ s := by
  simpa [(DirichletCharacter.LFunction_eq_LSeries (χ := χ) hs).symm] using
    exp_primeLogSeries_eq_LSeries (N := N) χ hs

/-!
### A disk where `LFunction χ` is nonzero and admits a holomorphic log
-/

private lemma exists_delta_LFunction_ne_zero_on_ball (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ ball (1 : ℂ) ε, DirichletCharacter.LFunction χ z ≠ 0 := by
  let f : ℂ → ℂ := fun z => DirichletCharacter.LFunction χ z
  have hfcont : Continuous f :=
    (DirichletCharacter.differentiable_LFunction (χ := χ) hχ).continuous
  have hopen : IsOpen {z : ℂ | f z ≠ 0} := isOpen_ne.preimage hfcont
  have h1 : f 1 ≠ 0 := by
    simpa [f] using (DirichletCharacter.LFunction_apply_one_ne_zero (χ := χ) hχ)
  obtain ⟨ε, hεpos, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds (by simpa using h1))
  exact ⟨ε, hεpos, hball⟩

theorem exists_log_LFunction_on_ball (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball (1 : ℂ) ε) ∧
        ∀ z ∈ ball (1 : ℂ) ε, Complex.exp (g z) = DirichletCharacter.LFunction χ z := by
  obtain ⟨ε, hεpos, hne⟩ := exists_delta_LFunction_ne_zero_on_ball (N := N) χ hχ
  have hf : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) (ball (1 : ℂ) ε) :=
    (DirichletCharacter.differentiable_LFunction (χ := χ) hχ).differentiableOn
  obtain ⟨g, hg, hexp⟩ :=
    hf.exists_log_of_ball hεpos (by intro z hz; exact hne z hz)
  exact ⟨ε, hεpos, g, hg, hexp⟩

private lemma mem_ball_of_mem_Icc {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : x ∈ Set.Icc 1 (1 + ε / 2)) :
    (x : ℂ) ∈ ball (1 : ℂ) ε := by
  have habs : |x - 1| ≤ ε / 2 := abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hlt : |x - 1| < ε := lt_of_le_of_lt habs (half_lt_self hε)
  rw [Metric.mem_ball, dist_eq_norm]
  have : (x : ℂ) - (1 : ℂ) = ((x - 1 : ℝ) : ℂ) := by simp
  rw [this, norm_real, Real.norm_eq_abs]
  exact hlt

private lemma mem_ball_of_one_lt_lt {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht1 : 1 < t)
    (ht2 : t < 1 + ε) : (t : ℂ) ∈ ball (1 : ℂ) ε := by
  have hlt : |t - 1| < ε := abs_lt.2 ⟨by linarith, by linarith⟩
  rw [Metric.mem_ball, dist_eq_norm]
  have : (t : ℂ) - (1 : ℂ) = ((t - 1 : ℝ) : ℂ) := by simp
  rw [this, norm_real, Real.norm_eq_abs]
  exact hlt

/-!
### Local constancy and boundedness near `s = 1`

We complete the analytic argument:

* prove `primeLogSeries` is continuous on half-planes `{s | 1 + ε < re s}` using uniform bounds
  and `continuousOn_tsum`;
* on a small interval `(1, 1+ε)` the difference between `primeLogSeries` and a holomorphic log of
  `LFunction` is locally constant (since `exp` is locally injective);
* deduce boundedness of `primeLogSeries` near `1` along the real axis.
-/

section BoundedNearOne

open scoped Topology

private lemma norm_chi_mul_cpow_le {ε : ℝ} (hε : 0 < ε) (χ : DirichletCharacter ℂ N)
    (p : Nat.Primes) {s : ℂ} (hs : 1 + ε < s.re) :
    ‖χ p * (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-(1 + ε)) := by
  have hne : (-s).re ≠ 0 := by
    have : 0 < s.re := lt_trans (by linarith [hε]) hs
    simpa using ne_of_gt this
  have hchi : ‖χ p‖ ≤ (1 : ℝ) := by simpa using (DirichletCharacter.norm_le_one (χ := χ) p)
  have hcpow : ‖(p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-(1 + ε)) := by
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp p.2.pos)
    have hmono : (p : ℝ) ^ ((-s).re) ≤ (p : ℝ) ^ (-(1 + ε)) := by
      apply Real.rpow_le_rpow_of_exponent_le hp1
      have : (-s).re ≤ -(1 + ε) := le_of_lt (neg_lt_neg hs)
      simpa [Complex.neg_re] using this
    calc
      ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ ((-s).re) := by
        simp [norm_natCast_cpow_of_re_ne_zero _ hne]
      _ ≤ (p : ℝ) ^ (-(1 + ε)) := hmono
  calc
    ‖χ p * (p : ℂ) ^ (-s)‖ ≤ ‖χ p‖ * ‖(p : ℂ) ^ (-s)‖ := by simp
    _ ≤ 1 * (p : ℝ) ^ (-(1 + ε)) := by gcongr
    _ = (p : ℝ) ^ (-(1 + ε)) := by simp

private lemma norm_chi_mul_cpow_le_half {ε : ℝ} (hε : 0 < ε) (χ : DirichletCharacter ℂ N)
    (p : Nat.Primes) {s : ℂ} (hs : 1 + ε < s.re) :
    ‖χ p * (p : ℂ) ^ (-s)‖ ≤ (1 / 2 : ℝ) := by
  have h₁ : ‖χ p * (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-(1 + ε)) :=
    norm_chi_mul_cpow_le (N := N) hε χ p hs
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
  have hneg : (-(1 + ε) : ℝ) ≤ 0 := by linarith
  have h₂ : (p : ℝ) ^ (-(1 + ε)) ≤ (2 : ℝ) ^ (-(1 + ε)) := by
    simpa using (Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < (2 : ℝ)) hp2 hneg)
  have h₃ : (2 : ℝ) ^ (-(1 + ε)) < (1 / 2 : ℝ) := by
    have : (-(1 + ε) : ℝ) < (-1 : ℝ) := by linarith
    have h' : (2 : ℝ) ^ (-(1 + ε)) < (2 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) this
    simpa [Real.rpow_neg, Real.rpow_one] using h'
  exact h₁.trans (h₂.trans (le_of_lt h₃))

private lemma norm_primeLogSeries_term_le {ε : ℝ} (hε : 0 < ε) (χ : DirichletCharacter ℂ N)
    (p : Nat.Primes) {s : ℂ} (hs : 1 + ε < s.re) :
    ‖-Complex.log (1 - χ p * (p : ℂ) ^ (-s))‖ ≤ (3 / 2 : ℝ) * (p : ℝ) ^ (-(1 + ε)) := by
  set w : ℂ := χ p * (p : ℂ) ^ (-s)
  have hw : ‖w‖ ≤ (1 / 2 : ℝ) := by simpa [w] using norm_chi_mul_cpow_le_half (N := N) hε χ p hs
  have hlog : ‖Complex.log (1 - w)‖ ≤ (3 / 2 : ℝ) * ‖w‖ := by
    have : ‖Complex.log (1 + (-w))‖ ≤ (3 / 2 : ℝ) * ‖-w‖ :=
      Complex.norm_log_one_add_half_le_self (z := -w) (by simpa [norm_neg] using hw)
    simpa [sub_eq_add_neg, norm_neg] using this
  have hw' : ‖w‖ ≤ (p : ℝ) ^ (-(1 + ε)) := by simpa [w] using norm_chi_mul_cpow_le (N := N) hε χ p hs
  calc
    ‖-Complex.log (1 - w)‖ = ‖Complex.log (1 - w)‖ := by simp
    _ ≤ (3 / 2 : ℝ) * ‖w‖ := hlog
    _ ≤ (3 / 2 : ℝ) * (p : ℝ) ^ (-(1 + ε)) := by gcongr

private lemma continuousOn_primeLogSeries_halfPlane (χ : DirichletCharacter ℂ N) {ε : ℝ}
    (hε : 0 < ε) :
    ContinuousOn (primeLogSeries (N := N) χ) {s : ℂ | 1 + ε < s.re} := by
  classical
  have hsumm : Summable (fun p : Nat.Primes ↦ (3 / 2 : ℝ) * (p : ℝ) ^ (-(1 + ε))) := by
    have : Summable (fun p : Nat.Primes ↦ (p : ℝ) ^ (-(1 + ε))) := by
      have : (-(1 + ε) : ℝ) < (-1 : ℝ) := by linarith
      exact (Nat.Primes.summable_rpow (r := (-(1 + ε) : ℝ))).2 this
    simpa [mul_assoc] using this.mul_left (3 / 2 : ℝ)
  refine continuousOn_tsum
      (u := fun p : Nat.Primes ↦ (3 / 2 : ℝ) * (p : ℝ) ^ (-(1 + ε)))
      (f := fun p s => -Complex.log (1 - χ p * (p : ℂ) ^ (-s)))
      (s := {s : ℂ | 1 + ε < s.re}) ?_ hsumm ?_
  · intro p s hs
    have hs' : 1 + ε < s.re := hs
    have hw_le : ‖χ p * (p : ℂ) ^ (-s)‖ ≤ (1 / 2 : ℝ) :=
      norm_chi_mul_cpow_le_half (N := N) hε χ p hs'
    have hw_lt : ‖-(χ p * (p : ℂ) ^ (-s))‖ < (1 : ℝ) := by
      simpa [norm_neg] using (lt_of_le_of_lt hw_le one_half_lt_one)
    have hslit : (1 - χ p * (p : ℂ) ^ (-s)) ∈ slitPlane := by
      simpa [sub_eq_add_neg] using (mem_slitPlane_of_norm_lt_one hw_lt)
    have hpow : ContinuousWithinAt (fun z : ℂ => (p : ℂ) ^ (-z)) {z : ℂ | 1 + ε < z.re} s := by
      have h1 : ContinuousAt (fun t : ℂ => (p : ℂ) ^ t) (-s) :=
        continuousAt_const_cpow (a := (p : ℂ)) (b := -s) (by exact_mod_cast p.2.ne_zero)
      have h2 : ContinuousWithinAt (fun z : ℂ => -z) {z : ℂ | 1 + ε < z.re} s :=
        continuous_neg.continuousAt.continuousWithinAt
      exact h1.comp_continuousWithinAt h2
    have hinner :
        ContinuousWithinAt (fun z : ℂ => 1 - χ p * (p : ℂ) ^ (-z)) {z : ℂ | 1 + ε < z.re} s := by
      exact continuousWithinAt_const.sub (continuousWithinAt_const.mul hpow)
    have hlog :
        ContinuousWithinAt (fun z : ℂ => Complex.log (1 - χ p * (p : ℂ) ^ (-z)))
          {z : ℂ | 1 + ε < z.re} s := hinner.clog hslit
    simpa using hlog.neg
  · intro p s hs
    exact norm_primeLogSeries_term_le (N := N) hε χ p hs

private lemma continuousAt_primeLogSeries (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    ContinuousAt (primeLogSeries (N := N) χ) s := by
  set ε : ℝ := (s.re - 1) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hs' : 1 + ε < s.re := by dsimp [ε]; linarith
  have hopen : IsOpen {z : ℂ | 1 + ε < z.re} := isOpen_lt continuous_const continuous_re
  have hcontOn : ContinuousOn (primeLogSeries (N := N) χ) {z : ℂ | 1 + ε < z.re} :=
    continuousOn_primeLogSeries_halfPlane (N := N) (χ := χ) hε
  exact hcontOn.continuousAt (hopen.mem_nhds hs')

/-- For a nontrivial Dirichlet character, the prime-log Euler series is bounded as `s → 1⁺`.

We use nonvanishing of `L(χ, 1)` and existence of a holomorphic logarithm of `LFunction χ` on a
disk around `1`. -/
theorem bounded_primeLogSeries_near_one (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∃ M : ℝ,
      (fun s : ℝ => ‖primeLogSeries (N := N) χ (s : ℂ)‖) ≤ᶠ[nhdsWithin 1 (Set.Ioi 1)]
        fun _ => M := by
  obtain ⟨ε, hε, g, hg, hexp⟩ := exists_log_LFunction_on_ball (N := N) χ hχ
  set I : Set ℝ := Set.Ioo 1 (1 + ε / 2)
  have hδ2 : 0 < ε / 2 := by nlinarith
  have hI_mem : I ∈ nhdsWithin 1 (Set.Ioi 1) := by
    simpa [I, nhdsWithin] using Ioo_mem_nhdsGT (by nlinarith [hε])
  have hIpre : IsPreconnected I := isPreconnected_Ioo
  let F : I → ℂ := fun t => primeLogSeries (N := N) χ (t.1 : ℂ) - g (t.1 : ℂ)
  have hExpF : ∀ t : I, Complex.exp (F t) = 1 := by
    intro t
    have ht1 : (1 : ℝ) < t.1 := t.2.1
    have ht2 : t.1 < 1 + ε := by linarith [t.2.2]
    have htball : (t.1 : ℂ) ∈ ball (1 : ℂ) ε :=
      mem_ball_of_one_lt_lt (ε := ε) hε ht1 (by linarith [t.2.2])
    have hA : Complex.exp (primeLogSeries (N := N) χ (t.1 : ℂ)) =
        DirichletCharacter.LFunction χ (t.1 : ℂ) :=
      exp_primeLogSeries_eq_LFunction (N := N) χ (hs := by simpa using ht1)
    have hB : Complex.exp (g (t.1 : ℂ)) = DirichletCharacter.LFunction χ (t.1 : ℂ) :=
      hexp (t.1 : ℂ) htball
    have hne : DirichletCharacter.LFunction χ (t.1 : ℂ) ≠ 0 := by
      simpa [hB] using Complex.exp_ne_zero (g (t.1 : ℂ))
    calc
      Complex.exp (F t) = Complex.exp (primeLogSeries (N := N) χ (t.1 : ℂ)) /
          Complex.exp (g (t.1 : ℂ)) := by simp [F, Complex.exp_sub]
      _ = DirichletCharacter.LFunction χ (t.1 : ℂ) /
          DirichletCharacter.LFunction χ (t.1 : ℂ) := by simp [hA, hB]
      _ = 1 := by simp [hne]
  have hF_loc : IsLocallyConstant F := by
    refine (IsLocallyConstant.iff_eventually_eq (f := F)).2 (fun t0 => ?_)
    have ht0 : (1 : ℝ) < t0.1 := t0.2.1
    have ht0' : t0.1 < 1 + ε := by linarith [t0.2.2]
    have ht0ball : (t0.1 : ℂ) ∈ ball (1 : ℂ) ε :=
      mem_ball_of_one_lt_lt (ε := ε) hε ht0 (by linarith [t0.2.2])
    have hcontAt : ContinuousAt F t0 := by
      have hH : ContinuousAt (fun z : ℂ => primeLogSeries (N := N) χ z) (t0.1 : ℂ) :=
        continuousAt_primeLogSeries (N := N) (χ := χ) (s := (t0.1 : ℂ)) (by simpa using ht0)
      have hG : ContinuousAt g (t0.1 : ℂ) := by
        have hx : ball (1 : ℂ) ε ∈ 𝓝 (t0.1 : ℂ) := isOpen_ball.mem_nhds ht0ball
        exact (hg.continuousOn.continuousAt hx)
      have hval : ContinuousAt (fun t : I => (t.1 : ℂ)) t0 :=
        Complex.continuous_ofReal.continuousAt.comp continuous_subtype_val.continuousAt
      simpa [F, sub_eq_add_neg] using
        (hH.tendsto.comp hval.tendsto).sub (hG.tendsto.comp hval.tendsto)
    have hball : {t : I | ‖F t - F t0‖ < Real.pi} ∈ 𝓝 t0 := by
      have : Metric.ball (F t0) Real.pi ∈ 𝓝 (F t0) := Metric.ball_mem_nhds (x := F t0) Real.pi_pos
      have : {t : I | F t ∈ Metric.ball (F t0) Real.pi} ∈ 𝓝 t0 :=
        hcontAt.preimage_mem_nhds this
      simpa [Metric.mem_ball, dist_eq_norm] using this
    have hball' : ∀ᶠ t in 𝓝 t0, ‖F t - F t0‖ < Real.pi := hball
    refine hball'.mono ?_
    intro t ht
    have hExp : Complex.exp (F t) = Complex.exp (F t0) := by simp [hExpF t, hExpF t0]
    have : F t = F t0 :=
      Complex.eq_of_exp_eq_exp_of_norm_sub_lt_pi hExp (by simpa [sub_eq_add_neg] using ht)
    simp [this]
  haveI : PreconnectedSpace I := Subtype.preconnectedSpace hIpre
  have hInonempty : I.Nonempty := by
    refine ⟨1 + ε / 4, ?_⟩
    have hδ4 : 0 < ε / 4 := by nlinarith
    constructor <;> linarith [hδ4, hδ2]
  let t0 : I := ⟨(hInonempty.choose), hInonempty.choose_spec⟩
  let C : ℂ := F t0
  have hC : ∀ t : I, F t = C := fun t =>
    hF_loc.apply_eq_of_preconnectedSpace t t0
  set K : Set ℝ := Set.Icc 1 (1 + ε / 2)
  have hKcompact : IsCompact K := isCompact_Icc
  have hcontK : ContinuousOn (fun x : ℝ => g (x : ℂ)) K := by
    intro x hx
    have hxball : (x : ℂ) ∈ ball (1 : ℂ) ε := mem_ball_of_mem_Icc (ε := ε) hε hx
    have hxnhds : ball (1 : ℂ) ε ∈ 𝓝 (x : ℂ) := isOpen_ball.mem_nhds hxball
    exact ((hg.continuousOn.continuousAt hxnhds).comp_continuousWithinAt
      Complex.continuous_ofReal.continuousWithinAt)
  have hbdd : Bornology.IsBounded ((fun x : ℝ => g (x : ℂ)) '' K) :=
    (hKcompact.image_of_continuousOn hcontK).isBounded
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hbdd
  refine ⟨R + ‖C‖, ?_⟩
  have hEv : ∀ᶠ s in nhdsWithin 1 (Set.Ioi 1), s ∈ I := hI_mem
  refine hEv.mono ?_
  intro s hsI
  have hsK : s ∈ K := ⟨le_of_lt hsI.1, le_of_lt hsI.2⟩
  have hgs : ‖g (s : ℂ)‖ ≤ R := by
    have : g (s : ℂ) ∈ Metric.closedBall (0 : ℂ) R := hR ⟨s, hsK, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using this
  have hEq : primeLogSeries (N := N) χ (s : ℂ) = g (s : ℂ) + C := by
    have hF : primeLogSeries (N := N) χ (s : ℂ) - g (s : ℂ) = C := by
      simpa [F] using hC ⟨s, hsI⟩
    calc
      primeLogSeries (N := N) χ (s : ℂ) =
          g (s : ℂ) + (primeLogSeries (N := N) χ (s : ℂ) - g (s : ℂ)) := by ring
      _ = g (s : ℂ) + C := by rw [hF]
  calc
    ‖primeLogSeries (N := N) χ (s : ℂ)‖ = ‖g (s : ℂ) + C‖ := by simp [hEq]
    _ ≤ ‖g (s : ℂ)‖ + ‖C‖ := norm_add_le _ _
    _ ≤ R + ‖C‖ := by gcongr

end BoundedNearOne

end DirichletCharacterPrime

end Chebotarev

end PrimeNumberTheoremAnd
