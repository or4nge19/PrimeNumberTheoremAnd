import PrimeNumberTheoremAnd.Chebotarev.Density.DirichletCharacterPrimeSumBound
import PrimeNumberTheoremAnd.Chebotarev.Density.PrimeSeriesSummable

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
## Boundedness of `∑' p, χ p / p^s` near `s = 1⁺`

This file upgrades the boundedness of the *prime-log* series (proved in
`ChebotarevDirichletCharacterPrimeSumBound`) to boundedness of the *prime* series
`∑' p, χ p / p^s`, using the Taylor bound for `log (1+z) - z` and summability of `∑ p⁻²`.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical Real Topology

open Filter Complex

namespace Chebotarev.DirichletCharacterPrime

open Nat.Primes

variable {N : ℕ} [NeZero N]

private lemma norm_dirichletSummand_le_half (χ : _root_.DirichletCharacter ℂ N) {s : ℝ} (hs : 1 < s)
    (p : Nat.Primes) : ‖χ p * (p : ℂ) ^ (-(s : ℂ))‖ ≤ (1 / 2 : ℝ) := by
  -- `‖χ p‖ ≤ 1` and `‖p^{-s}‖ = p^{-s}`, and `p ≥ 2`.
  have hchi : ‖χ p‖ ≤ (1 : ℝ) := by simpa using (_root_.DirichletCharacter.norm_le_one (χ := χ) p)
  have hspos : 0 < s := by linarith
  have hnere : (s : ℂ).re ≠ 0 := by
    simpa using (ne_of_gt hspos)
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
  have hnorm_pows : ‖(p : ℂ) ^ (-(s : ℂ))‖ = (p : ℝ) ^ (-s) := by
    -- `‖p^(-s)‖ = p^(-re s)` and `re(s)=s`.
    have hne' : (-(s : ℂ)).re ≠ 0 := by simpa using hnere
    calc
      ‖(p : ℂ) ^ (-(s : ℂ))‖ = (p : ℝ) ^ ((-(s : ℂ)).re) := by
        simp [norm_natCast_cpow_of_re_ne_zero _ hne']
      _ = (p : ℝ) ^ (-s) := by simp
  have hpow_le : (p : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < (2 : ℝ)) hp2 (by linarith)
  have hpow_lt : (2 : ℝ) ^ (-s) < (1 / 2 : ℝ) := by
    have : (-s : ℝ) < (-1 : ℝ) := by linarith
    have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) this
    simpa [Real.rpow_neg, Real.rpow_one] using this
  calc
    ‖χ p * (p : ℂ) ^ (-(s : ℂ))‖ = ‖χ p‖ * ‖(p : ℂ) ^ (-(s : ℂ))‖ := by simp
    _ ≤ 1 * ‖(p : ℂ) ^ (-(s : ℂ))‖ := by gcongr
    _ = (p : ℝ) ^ (-s) := by simp [hnorm_pows]
    _ ≤ (2 : ℝ) ^ (-s) := hpow_le
    _ ≤ (1 / 2 : ℝ) := le_of_lt hpow_lt

private lemma norm_log_term_sub_self_le_sq {w : ℂ} (hw : ‖w‖ ≤ (1 / 2 : ℝ)) :
    ‖-Complex.log (1 - w) - w‖ ≤ ‖w‖ ^ 2 := by
  have hw' : ‖-w‖ < (1 : ℝ) :=
    (lt_of_le_of_lt (by simpa [norm_neg] using hw) one_half_lt_one)
  have h := Complex.norm_log_one_add_sub_self_le (z := -w) hw'
  -- turn the RHS into `‖w‖^2` using `‖w‖ ≤ 1/2`
  have hle : ‖-w‖ ^ 2 * (1 - ‖-w‖)⁻¹ / 2 ≤ ‖w‖ ^ 2 := by
    have hhalf : (1 / 2 : ℝ) ≤ 1 - ‖-w‖ := by
      have : ‖-w‖ ≤ (1 / 2 : ℝ) := by simpa [norm_neg] using hw
      linarith
    have hinv : (1 - ‖-w‖)⁻¹ ≤ (2 : ℝ) := by
      -- `1 / (1 - ‖-w‖) ≤ 1 / (1/2) = 2`
      have ha : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
      have : (1 : ℝ) / (1 - ‖-w‖) ≤ (1 : ℝ) / (1 / 2 : ℝ) :=
        one_div_le_one_div_of_le ha hhalf
      simpa [one_div] using this
    have hfac : (1 - ‖-w‖)⁻¹ / 2 ≤ (1 : ℝ) := by
      have : (1 - ‖-w‖)⁻¹ / 2 ≤ (2 : ℝ) / 2 := div_le_div_of_nonneg_right hinv (by positivity)
      simpa using this
    calc
      ‖-w‖ ^ 2 * (1 - ‖-w‖)⁻¹ / 2 = ‖-w‖ ^ 2 * ((1 - ‖-w‖)⁻¹ / 2) := by ring
      _ ≤ ‖-w‖ ^ 2 * 1 := by gcongr
      _ = ‖w‖ ^ 2 := by simp [norm_neg]
  have h' : ‖Complex.log (1 - w) + w‖ ≤ ‖w‖ ^ 2 := by
    -- rewrite the left side into the form `log(1+z) - z`.
    have : ‖Complex.log (1 + (-w)) - (-w)‖ ≤ ‖-w‖ ^ 2 * (1 - ‖-w‖)⁻¹ / 2 := h
    have : ‖Complex.log (1 - w) + w‖ ≤ ‖-w‖ ^ 2 * (1 - ‖-w‖)⁻¹ / 2 := by
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this
    exact this.trans hle
  -- finish
  have h'' : ‖-Complex.log (1 - w) - w‖ = ‖Complex.log (1 - w) + w‖ := by
    have hswap : ‖-Complex.log (1 - w) - w‖ = ‖-w + -Complex.log (1 - w)‖ := by
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    have hw' : -w + -Complex.log (1 - w) = -(Complex.log (1 - w) + w) := by ring
    calc
      ‖-Complex.log (1 - w) - w‖ = ‖-w + -Complex.log (1 - w)‖ := hswap
      _ = ‖-(Complex.log (1 - w) + w)‖ := by
            simpa using congrArg (fun z : ℂ => ‖z‖) hw'
      _ = ‖Complex.log (1 - w) + w‖ := by
            simpa using (norm_neg (Complex.log (1 - w) + w))
  simpa [h''] using h'

private lemma norm_dirichletSummand_le_one_div_cpow (χ : _root_.DirichletCharacter ℂ N) {s : ℝ}
    (hs : 1 < s) (p : Nat.Primes) :
    ‖χ p * (p : ℂ) ^ (-(s : ℂ))‖ ≤ ‖(1 : ℂ) / ((p : ℂ) ^ (s : ℂ))‖ := by
  have hchi : ‖χ p‖ ≤ (1 : ℝ) := by
    simpa using (_root_.DirichletCharacter.norm_le_one (χ := χ) p)
  calc
    ‖χ p * (p : ℂ) ^ (-(s : ℂ))‖ = ‖χ p‖ * ‖(p : ℂ) ^ (-(s : ℂ))‖ := by simp [norm_mul]
    _ ≤ 1 * ‖(p : ℂ) ^ (-(s : ℂ))‖ := by gcongr
    _ = ‖(p : ℂ) ^ (-(s : ℂ))‖ := by simp
    _ = ‖((p : ℂ) ^ (s : ℂ))⁻¹‖ := by simp [Complex.cpow_neg]
    _ = ‖(1 : ℂ) / ((p : ℂ) ^ (s : ℂ))‖ := by simp [one_div]

private lemma summable_primeSeries_real (χ : _root_.DirichletCharacter ℂ N) {s : ℝ} (hs : 1 < s) :
    Summable (fun p : Nat.Primes ↦ χ p * (p : ℂ) ^ (-(s : ℂ))) := by
  have hbase :
      Summable (fun p : Nat.Primes ↦ (1 : ℂ) / ((p : ℂ) ^ (s : ℂ))) :=
    PrimeNumberTheoremAnd.summable_primes_one_div_cpow_of_one_lt_real (s := s) hs
  have hbase' : Summable (fun p : Nat.Primes ↦ ‖(1 : ℂ) / ((p : ℂ) ^ (s : ℂ))‖) := hbase.norm
  refine Summable.of_norm_bounded hbase' (fun p => ?_)
  simpa using norm_dirichletSummand_le_one_div_cpow (N := N) (χ := χ) (s := s) hs p

private lemma summable_primeLogSeries_real (χ : _root_.DirichletCharacter ℂ N) {s : ℝ} (hs : 1 < s) :
    Summable (fun p : Nat.Primes ↦ -Complex.log (1 - χ p * (p : ℂ) ^ (-(s : ℂ)))) := by
  have hw : Summable (fun p : Nat.Primes ↦ χ p * (p : ℂ) ^ (-(s : ℂ))) :=
    summable_primeSeries_real (N := N) (χ := χ) hs
  simpa using (hw.clog_one_sub.neg)

private lemma norm_primeLogSeries_sub_primeSeries_le (χ : _root_.DirichletCharacter ℂ N) {s : ℝ}
    (hs : 1 < s) :
    ‖primeLogSeries (N := N) χ (s : ℂ) - primeSeries (N := N) χ (s : ℂ)‖ ≤
      ∑' p : Nat.Primes, (p : ℝ) ^ (-(2 : ℝ)) := by
  -- set up `w` and `err`
  let w : Nat.Primes → ℂ := fun p ↦ χ p * (p : ℂ) ^ (-(s : ℂ))
  let err : Nat.Primes → ℂ := fun p ↦ (-Complex.log (1 - w p)) - w p
  have hw_le : ∀ p, ‖w p‖ ≤ (1 / 2 : ℝ) := fun p => norm_dirichletSummand_le_half (N := N) (χ := χ) hs p
  have herr_le : ∀ p, ‖err p‖ ≤ (p : ℝ) ^ (-(2 : ℝ)) := by
    intro p
    have h1 : ‖err p‖ ≤ ‖w p‖ ^ 2 := by
      simpa [err] using norm_log_term_sub_self_le_sq (w := w p) (hw := hw_le p)
    -- compare `‖w p‖^2` to `p^{-2}` using `‖w p‖ ≤ p^{-s}` and `s > 1`.
    have hws : ‖w p‖ ≤ (p : ℝ) ^ (-s) := by
      -- from `‖w p‖ ≤ ‖1 / p^s‖` and identify the RHS norm
      have hle : ‖w p‖ ≤ ‖(1 : ℂ) / ((p : ℂ) ^ (s : ℂ))‖ := by
        simpa [w] using norm_dirichletSummand_le_one_div_cpow (N := N) (χ := χ) (s := s) hs p
      -- `‖1 / p^s‖ = p^{-s}`
      have hsC : (s : ℂ).re ≠ 0 := by simpa using (ne_of_gt (show 0 < s by linarith))
      have hn :
          ‖(1 : ℂ) / ((p : ℂ) ^ (s : ℂ))‖ = ((p : ℝ) ^ s)⁻¹ := by
        calc
          ‖(1 : ℂ) / ((p : ℂ) ^ (s : ℂ))‖
              = ‖((p : ℂ) ^ (s : ℂ))⁻¹‖ := by simp [one_div]
          _ = ‖(p : ℂ) ^ (s : ℂ)‖⁻¹ := by simp
          _ = ((p : ℝ) ^ ((s : ℂ).re))⁻¹ := by
                simp [norm_natCast_cpow_of_re_ne_zero _ hsC]
          _ = ((p : ℝ) ^ s)⁻¹ := by simp
      have hwsinv : ‖w p‖ ≤ ((p : ℝ) ^ s)⁻¹ := by simpa [hn] using hle
      -- rewrite `(p^s)⁻¹` as `p^(-s)` for the later exponent comparison
      have : ((p : ℝ) ^ s)⁻¹ = (p : ℝ) ^ (-s) := by
        have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
        simpa using (Real.rpow_neg hp0 s).symm
      simpa [this] using hwsinv
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp p.2.pos)
    have hs' : (-2 * s : ℝ) ≤ (-(2 : ℝ)) := by nlinarith [hs.le]
    have hpow : (p : ℝ) ^ (-2 * s) ≤ (p : ℝ) ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hp1 hs'
    have h2 : ‖w p‖ ^ 2 ≤ (p : ℝ) ^ (-(2 : ℝ)) := by
      calc
        ‖w p‖ ^ 2 ≤ ((p : ℝ) ^ (-s)) ^ 2 := by gcongr
        _ = (p : ℝ) ^ (-2 * s) := by
              have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
              -- use `rpow_mul` with exponent `2`, then rewrite `(-s) * 2 = -2 * s`
              have := (Real.rpow_mul hp0 (-s) (2 : ℝ))
              -- `p ^ ((-s) * 2) = (p ^ (-s)) ^ (2:ℝ) = ((p ^ (-s)) ^ 2)`
              have : (p : ℝ) ^ ((-s) * (2 : ℝ)) = ((p : ℝ) ^ (-s)) ^ (2 : ℕ) := by
                simpa using this.trans (by simpa using (Real.rpow_natCast ((p : ℝ) ^ (-s)) 2))
              -- rearrange
              have : ((p : ℝ) ^ (-s)) ^ (2 : ℕ) = (p : ℝ) ^ (-2 * s) := by
                -- `(-s) * 2 = -2 * s`
                simpa [pow_two, mul_assoc, mul_comm, mul_left_comm, mul_add, add_mul] using this.symm
              simpa using this
        _ ≤ (p : ℝ) ^ (-(2 : ℝ)) := hpow
    exact h1.trans (h2)
  have hsumm : Summable (fun p : Nat.Primes ↦ (p : ℝ) ^ (-(2 : ℝ))) :=
    (Nat.Primes.summable_rpow (r := (-(2 : ℝ)))).2 (by norm_num)
  have htsum_err : ‖∑' p : Nat.Primes, err p‖ ≤ ∑' p : Nat.Primes, (p : ℝ) ^ (-(2 : ℝ)) :=
    tsum_of_norm_bounded hsumm.hasSum herr_le
  -- identify `∑' err` with the difference of the two prime sums
  have hsumW : Summable (fun p : Nat.Primes ↦ w p) := by simpa [w] using summable_primeSeries_real (N := N) (χ := χ) hs
  have hsumLog : Summable (fun p : Nat.Primes ↦ -Complex.log (1 - w p)) := by
    simpa [w] using summable_primeLogSeries_real (N := N) (χ := χ) hs
  have hdiff :
      ∑' p : Nat.Primes, err p =
        primeLogSeries (N := N) χ (s : ℂ) - primeSeries (N := N) χ (s : ℂ) := by
    classical
    have hsumNegW : Summable (fun p : Nat.Primes ↦ -(w p)) := hsumW.neg
    calc
      (∑' p : Nat.Primes, err p)
          = ∑' p : Nat.Primes, (-Complex.log (1 - w p) + -(w p)) := by
              simp [err, sub_eq_add_neg, add_assoc]
      _ = (∑' p : Nat.Primes, -Complex.log (1 - w p)) + (∑' p : Nat.Primes, -(w p)) := by
            -- `Summable.tsum_add` gives the forward direction
            simpa using (hsumLog.tsum_add hsumNegW)
      _ = (∑' p : Nat.Primes, -Complex.log (1 - w p)) - (∑' p : Nat.Primes, w p) := by
            simp [sub_eq_add_neg, tsum_neg, hsumW]
      _ = primeLogSeries (N := N) χ (s : ℂ) - primeSeries (N := N) χ (s : ℂ) := by
            simp [primeLogSeries, primeSeries, w]
  -- conclude
  simpa [hdiff] using htsum_err

theorem bounded_primeSeries_near_one (χ : _root_.DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∃ M : ℝ,
      (fun s : ℝ ↦ ‖primeSeries (N := N) χ (s : ℂ)‖) ≤ᶠ[nhdsWithin 1 (Set.Ioi 1)]
        fun _ ↦ M := by
  rcases bounded_primeLogSeries_near_one (N := N) χ hχ with ⟨Mlog, hMlog⟩
  let Merr : ℝ := ∑' p : Nat.Primes, (p : ℝ) ^ (-(2 : ℝ))
  refine ⟨Mlog + Merr, ?_⟩
  have hEv : ∀ᶠ s in nhdsWithin 1 (Set.Ioi 1), (1 : ℝ) < s := by
    have : ∀ᶠ s in nhdsWithin 1 (Set.Ioi 1), s ∈ Set.Ioi (1 : ℝ) := self_mem_nhdsWithin
    exact this.mono (by intro s hs; exact hs)
  refine (hMlog.and hEv).mono ?_
  intro s hs
  rcases hs with ⟨hslog, hs1⟩
  have hdiff : ‖primeLogSeries (N := N) χ (s : ℂ) - primeSeries (N := N) χ (s : ℂ)‖ ≤ Merr := by
    simpa [Merr] using norm_primeLogSeries_sub_primeSeries_le (N := N) (χ := χ) (s := s) hs1
  -- `‖primeSeries‖ ≤ ‖primeLogSeries‖ + ‖primeLogSeries - primeSeries‖`
  have htri :
      ‖primeSeries (N := N) χ (s : ℂ)‖ ≤
        ‖primeLogSeries (N := N) χ (s : ℂ)‖ +
          ‖primeLogSeries (N := N) χ (s : ℂ) - primeSeries (N := N) χ (s : ℂ)‖ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (norm_le_insert (u := primeLogSeries (N := N) χ (s : ℂ)) (v := primeSeries (N := N) χ (s : ℂ)))
  calc
    ‖primeSeries (N := N) χ (s : ℂ)‖
        ≤ ‖primeLogSeries (N := N) χ (s : ℂ)‖ +
            ‖primeLogSeries (N := N) χ (s : ℂ) - primeSeries (N := N) χ (s : ℂ)‖ := htri
    _ ≤ Mlog + Merr := by gcongr

end Chebotarev.DirichletCharacterPrime

end PrimeNumberTheoremAnd
