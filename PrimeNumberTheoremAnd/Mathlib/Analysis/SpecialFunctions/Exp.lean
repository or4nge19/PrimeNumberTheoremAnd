/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Probability.Distributions.Exponential

/-!
# Elementary exponential estimates

Small real exponential inequalities used to absorb polynomial and product factors into
finite-order growth bounds.

The final section records basic complex exponential half-line integrals used for Laplace-transform
normalizations.
-/

@[expose] public section

open MeasureTheory

namespace Real

/-- The elementary inequality `x ≤ exp x`. -/
theorem le_exp_self (x : ℝ) : x ≤ exp x :=
  le_trans (by linarith : x ≤ x + 1) (add_one_le_exp x)

/-- Combine four elementary exponential majorants. -/
lemma mul_four_le_exp_add {a b c d A B C D : ℝ}
    (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d)
    (ha : a ≤ exp A) (hb : b ≤ exp B) (hc : c ≤ exp C) (hd : d ≤ exp D) :
    a * b * c * d ≤ exp (A + B + C + D) := by
  have hab : a * b ≤ exp A * exp B :=
    mul_le_mul ha hb hb0 (exp_pos A).le
  have habc : (a * b) * c ≤ (exp A * exp B) * exp C :=
    mul_le_mul hab hc hc0 (by positivity)
  have hprod : a * b * c * d ≤ exp A * exp B * exp C * exp D :=
    mul_le_mul habc hd hd0 (by positivity)
  calc
    a * b * c * d ≤ exp A * exp B * exp C * exp D := hprod
    _ = exp (A + B + C + D) := by
        rw [← exp_add, ← exp_add, ← exp_add]

/-- Once `x ≤ A` and `1 ≤ A`, the factor `2x` is dominated by `exp (2A²)`. -/
lemma two_mul_le_exp_two_mul_sq {x A : ℝ} (hx : x ≤ A) (hA1 : 1 ≤ A) :
    x * 2 ≤ exp (2 * (A * A)) := by
  have h1 : x * 2 ≤ 2 * A := by linarith [hx]
  have hA0 : 0 ≤ A := zero_le_one.trans hA1
  have hA_le_sq : A ≤ A * A := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hA1 hA0
  have h2 : 2 * A ≤ 2 * (A * A) := by nlinarith [hA_le_sq]
  exact le_trans (le_trans h1 h2) (le_exp_self (2 * (A * A)))

end Real

namespace Complex

/-- Derivative of the one-dimensional complex exponential kernel `exp (-w * y)`. -/
theorem hasDerivAt_exp_neg_mul (w : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ exp (-w * (y : ℂ))) (-w * exp (-w * (x : ℂ))) x := by
  have hofReal : HasDerivAt (fun y : ℝ ↦ (y : ℂ)) (1 : ℂ) x := by
    simpa using (HasDerivAt.ofReal_comp (hasDerivAt_id x))
  have hlin : HasDerivAt (fun y : ℝ ↦ -w * (y : ℂ)) (-w) x := by
    simpa using hofReal.const_mul (-w)
  simpa [mul_comm, mul_left_comm, mul_assoc] using hlin.cexp

/-- A primitive of the Laplace exponential kernel, valid when `w ≠ 0`. -/
theorem hasDerivAt_laplaceKernelPrimitive {w : ℂ} (hw : w ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (-w⁻¹) * exp (-w * (y : ℂ)))
      (exp (-w * (x : ℂ))) x := by
  have h := (hasDerivAt_exp_neg_mul w x).const_mul (-w⁻¹)
  convert h using 1
  field_simp [hw]

section LaplaceKernel

variable {w : ℂ}

/-- Complex exponential decay on a right half-line is integrable when the real part is positive. -/
theorem integrableOn_exp_neg_mul_Ioi (hw : 0 < w.re) :
    IntegrableOn (fun y : ℝ ↦ exp (-w * (y : ℂ))) (Set.Ioi (0 : ℝ)) volume := by
  have hReal : IntegrableOn (fun y : ℝ ↦ Real.exp (-(w.re) * y))
      (Set.Ioi (0 : ℝ)) volume := by
    simpa [neg_mul] using (exp_neg_integrableOn_Ioi (0 : ℝ) (b := w.re) hw)
  refine hReal.mono' ?_ ?_
  · fun_prop
  · filter_upwards with y
    rw [norm_exp]
    simp [mul_re]

/-- The basic half-line Laplace integral of a complex exponential. -/
theorem integral_exp_neg_mul_Ioi (hwre : 0 < w.re) :
    (∫ y in Set.Ioi (0 : ℝ), exp (-w * (y : ℂ)) ∂volume) = 1 / w := by
  have hw : w ≠ 0 := by
    intro h
    simp [h] at hwre
  have hInt : IntegrableOn (fun y : ℝ ↦ exp (-w * (y : ℂ)))
      (Set.Ioi (0 : ℝ)) volume :=
    integrableOn_exp_neg_mul_Ioi hwre
  have hInterval (R : ℝ) :
      (∫ y in (0 : ℝ)..R, exp (-w * (y : ℂ)) ∂volume) =
        (-w⁻¹) * exp (-w * (R : ℂ)) - (-w⁻¹) := by
    have hint : IntervalIntegrable (fun y : ℝ ↦ exp (-w * (y : ℂ))) volume (0 : ℝ) R := by
      have hcont : ContinuousOn (fun y : ℝ ↦ exp (-w * (y : ℂ))) (Set.uIcc (0 : ℝ) R) := by
        fun_prop
      exact hcont.intervalIntegrable
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ ↦ (-w⁻¹) * exp (-w * (y : ℂ)))
      (f' := fun y : ℝ ↦ exp (-w * (y : ℂ)))
      (fun x _hx ↦ hasDerivAt_laplaceKernelPrimitive hw x) hint
    simpa using hFTC
  have hSetLim := intervalIntegral_tendsto_integral_Ioi (a := (0 : ℝ)) hInt Filter.tendsto_id
  have hExp0 : Filter.Tendsto (fun R : ℝ ↦ exp (-w * (R : ℂ))) Filter.atTop (nhds 0) := by
    rw [Complex.tendsto_exp_nhds_zero_iff]
    have hlin : Filter.Tendsto (fun R : ℝ ↦ w.re * R) Filter.atTop Filter.atTop :=
      Filter.tendsto_id.const_mul_atTop hwre
    refine (Filter.tendsto_neg_atBot_iff.mpr hlin).congr' ?_
    filter_upwards with R
    simp [mul_re]
  have hRhs : Filter.Tendsto (fun R : ℝ ↦ (-w⁻¹) * exp (-w * (R : ℂ)) - (-w⁻¹))
      Filter.atTop (nhds (1 / w)) := by
    have hmul := hExp0.const_mul (-w⁻¹)
    have hconst : Filter.Tendsto (fun _ : ℝ ↦ (-w⁻¹ : ℂ)) Filter.atTop (nhds (-w⁻¹)) :=
      tendsto_const_nhds
    have hsub := hmul.sub hconst
    have htarget : (-w⁻¹ * 0 - -w⁻¹) = 1 / w := by
      field_simp [hw]
      ring
    simpa [htarget] using hsub
  exact tendsto_nhds_unique (hSetLim.congr' (Filter.Eventually.of_forall hInterval)) hRhs

end LaplaceKernel

end Complex
