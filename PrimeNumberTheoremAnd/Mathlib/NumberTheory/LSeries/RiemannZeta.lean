/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Extra Riemann zeta API from the WF branch. -/

@[expose] public section

noncomputable section

open Complex

/-- The Riemann zeta function is analytic on `ℂ \ {1}`. -/
theorem analyticOn_riemannZeta_compl_one : AnalyticOn ℂ riemannZeta ({1} : Set ℂ)ᶜ := by
  have hopen : IsOpen ({1} : Set ℂ)ᶜ := isOpen_compl_singleton
  have hdiff : DifferentiableOn ℂ riemannZeta ({1} : Set ℂ)ᶜ := by
    intro z hz
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using
      (differentiableAt_riemannZeta
        (by simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hz)).differentiableWithinAt
  simpa [Complex.analyticOn_iff_differentiableOn hopen] using hdiff

namespace Nat.Primes

/-- For a prime `p` and `s` with real part `> 1`, `‖p^{-s}‖ < 1`. -/
lemma norm_cpow_neg_lt_one (p : Nat.Primes) (s : ℂ) (hs : 1 < s.re) :
    ‖((p : ℕ) : ℂ) ^ (-s)‖ < 1 := by
  have hx1 : 1 < ((p : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast (p.2.two_le : 2 ≤ (p : ℕ))
    exact lt_of_lt_of_le one_lt_two h2
  have hx0 : 0 < ((p : ℕ) : ℝ) := lt_trans zero_lt_one hx1
  have hnorm : ‖((p : ℕ) : ℂ) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s.re) :=
    Complex.norm_cpow_eq_rpow_re_of_pos hx0 (-s)
  have hz : -s.re < 0 := neg_lt_zero.mpr (lt_trans zero_lt_one hs)
  simpa [hnorm] using Real.rpow_lt_one_of_one_lt_of_neg hx1 hz

/-- `‖p^{-s}‖ = p^{- re s}` for a prime `p`. -/
lemma norm_cpow_neg_eq_rpow_neg_re (p : Nat.Primes) (s : ℂ) :
    ‖((p : ℕ) : ℂ) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s.re) := by
  have hx : 0 < ((p : ℕ) : ℝ) := Nat.cast_pos.mpr p.property.pos
  simpa [Complex.ofReal_natCast, Complex.neg_re] using
    Complex.norm_cpow_eq_rpow_re_of_pos hx (-s)

end Nat.Primes

/-- `1 / (n : ℂ) ^ s` rewrites to `(n : ℂ) ^ (-s)` away from `n = 0`. -/
theorem one_div_natCast_cpow_eq_ite_cpow_neg (s : ℂ) (hs : s ≠ 0) (n : ℕ) :
    1 / (n : ℂ) ^ s = if n = 0 then 0 else (n : ℂ) ^ (-s) := by
  by_cases h : n = 0
  · simp [h, Complex.zero_cpow hs]
  · simp [h, one_div, Complex.cpow_neg]

end
