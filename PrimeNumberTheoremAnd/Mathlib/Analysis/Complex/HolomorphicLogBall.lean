import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Holomorphic logarithms on disks

This file shows that a nonvanishing holomorphic function on an open disk in `ℂ` admits a
holomorphic logarithm. The proof uses mathlib's disk primitive theorem
(`DifferentiableOn.isExactOn_ball`) and the logarithmic derivative, avoiding any
project-specific rectangular-convex infrastructure.

## Main results

* `Complex.differentiableOn_logDeriv`: the logarithmic derivative of a nonvanishing holomorphic
  function is holomorphic.
* `Complex.DifferentiableOn.exists_log_of_ball`: existence of a holomorphic branch of the log on a
  disk.
* `Complex.eq_of_exp_eq_exp_of_norm_sub_lt_pi`: if two complex numbers have the same exponential
  and differ by less than `π` in norm, they are equal.
-/

namespace Complex

open Set Metric Filter

/-- The logarithmic derivative of a nonvanishing holomorphic function is holomorphic. -/
theorem differentiableOn_logDeriv {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hf_ne : ∀ z ∈ U, f z ≠ 0) :
    DifferentiableOn ℂ (logDeriv f) U := by
  intro z hz
  have hf_at := hf.differentiableAt (hU.mem_nhds hz)
  have hf_ne_z : f z ≠ 0 := hf_ne z hz
  unfold logDeriv
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.div
  · exact (hf.deriv hU).differentiableAt (hU.mem_nhds hz)
  · exact hf_at
  · exact hf_ne_z

/-- If `exp x = exp y` and `‖x - y‖ < π`, then `x = y`. -/
theorem eq_of_exp_eq_exp_of_norm_sub_lt_pi {x y : ℂ} (hxy : exp x = exp y)
    (hπ : ‖x - y‖ < Real.pi) : x = y := by
  rcases (exp_eq_exp_iff_exists_int).1 hxy with ⟨n, hn⟩
  have hsub : x - y = n * (2 * Real.pi * I) := by
    have hn' : x = n * (2 * Real.pi * I) + y := by
      simpa [add_comm, add_left_comm, add_assoc] using hn
    exact (sub_eq_iff_eq_add).2 hn'
  by_cases hn0 : n = 0
  · simpa [hn0] using hn
  · have hnabs : (1 : ℝ) ≤ ‖(n : ℂ)‖ := by
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
      have hR : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast this
      have : (1 : ℝ) ≤ ‖(n : ℤ)‖ := by simpa [Int.norm_eq_abs] using hR
      simpa [norm_intCast] using this
    have hnorm2pi : ‖(2 * Real.pi * I : ℂ)‖ = 2 * Real.pi := by
      simp [Real.pi_pos.le, mul_assoc]
    have hge : Real.pi ≤ ‖n * (2 * Real.pi * I : ℂ)‖ := by
      calc
        Real.pi ≤ (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
        _ ≤ ‖(n : ℂ)‖ * (2 * Real.pi) := by
              have hpos : (0 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_pos]
              simpa [one_mul] using mul_le_mul_of_nonneg_right hnabs hpos
        _ = ‖(n : ℂ)‖ * ‖(2 * Real.pi * I : ℂ)‖ := by
              simpa using congrArg (fun r : ℝ => ‖(n : ℂ)‖ * r) hnorm2pi.symm
        _ = ‖(n : ℂ) * (2 * Real.pi * I : ℂ)‖ := (norm_mul _ _).symm
        _ = ‖n * (2 * Real.pi * I : ℂ)‖ := by simp
    exact absurd hπ (not_lt_of_ge (by simpa [hsub] using hge))

/-- A nonvanishing holomorphic function on an open disk has a holomorphic logarithm. -/
theorem DifferentiableOn.exists_log_of_ball {c : ℂ} {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball c r)) (hf_ne : ∀ z ∈ ball c r, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c r) ∧ ∀ z ∈ ball c r, exp (g z) = f z := by
  have hU : IsOpen (ball c r) := isOpen_ball
  have hlogDeriv : DifferentiableOn ℂ (logDeriv f) (ball c r) :=
    differentiableOn_logDeriv hU hf hf_ne
  obtain ⟨g₀, hg₀⟩ := hlogDeriv.isExactOn_ball
  have hz₀ : c ∈ ball c r := Metric.mem_ball_self hr
  let h := fun z => f z * exp (-g₀ z)
  have hh_diff : DifferentiableOn ℂ h (ball c r) := by
    apply DifferentiableOn.mul hf
    apply DifferentiableOn.cexp
    apply DifferentiableOn.neg
    intro z hz
    exact (hg₀ z hz).differentiableAt.differentiableWithinAt
  have hh_deriv_zero : ∀ z ∈ ball c r, deriv h z = 0 := by
    intro z hz
    have hf_at := hf.differentiableAt (hU.mem_nhds hz)
    have hg₀_at : HasDerivAt g₀ (logDeriv f z) z := hg₀ z hz
    have hexp_at : DifferentiableAt ℂ (fun w => exp (-g₀ w)) z := by
      apply DifferentiableAt.cexp
      exact hg₀_at.differentiableAt.neg
    rw [show h = f * fun w => exp (-g₀ w) from rfl, deriv_mul hf_at hexp_at]
    have hexp_deriv : deriv (fun w => exp (-g₀ w)) z = -logDeriv f z * exp (-g₀ z) := by
      have h1 : deriv (fun w => exp (-g₀ w)) z = exp (-g₀ z) * deriv (fun w => -g₀ w) z := by
        apply deriv_cexp
        exact hg₀_at.differentiableAt.neg
      have h2 : deriv (fun w => -g₀ w) z = -deriv g₀ z := deriv.neg
      rw [h1, h2, hg₀_at.deriv]
      ring
    rw [hexp_deriv, logDeriv_apply]
    field_simp [hf_ne z hz]
    ring
  have h_const : ∀ z ∈ ball c r, h z = h c := fun z hz =>
    IsOpen.is_const_of_deriv_eq_zero isOpen_ball (convex_ball c r).isPreconnected hh_diff
      (by intro w hw; exact hh_deriv_zero w hw) hz hz₀
  let c₀ := h c
  have hc_ne : c₀ ≠ 0 := mul_ne_zero (hf_ne c hz₀) (exp_ne_zero _)
  let L₀ := log c₀
  have hexp_L₀ : exp L₀ = c₀ := exp_log hc_ne
  refine ⟨fun z => g₀ z + L₀, ?_, ?_⟩
  · apply DifferentiableOn.add
    · intro z hz; exact (hg₀ z hz).differentiableAt.differentiableWithinAt
    · exact differentiableOn_const L₀
  · intro z hz
    have heq : h z = c₀ := h_const z hz
    calc
      exp (g₀ z + L₀) = exp (g₀ z) * exp L₀ := exp_add (g₀ z) L₀
      _ = exp (g₀ z) * c₀ := by rw [hexp_L₀]
      _ = exp (g₀ z) * (f z * exp (-g₀ z)) := by rw [← heq]
      _ = f z * (exp (g₀ z) * exp (-g₀ z)) := by ring
      _ = f z * exp (g₀ z + (-g₀ z)) := by rw [exp_add]
      _ = f z := by simp

end Complex
