import Architect
import PrimeNumberTheoremAnd.Defs
import PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions
import PrimeNumberTheoremAnd.IEANTN.HadamardLogDerivative
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.WeilGuinand
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZeta

blueprint_comment /--
\section{An explicit zero-free region for \texorpdfstring{$\zeta$}{zeta}}\label{kadiri-sec}
-/

blueprint_comment /--
In this section we begin a formalisation of the zero-free region for the Riemann zeta function
of Kadiri \cite{Kadiri2005}, who proved that $\zeta(s)$ has no zeros in the region
$$ \Re s \geq 1 - \frac{1}{5.70176 \log |\Im s|}, \qquad |\Im s| \geq 2. $$

The initial target is the explicit formula \cite[(5)]{Kadiri2005} for
$\Re \sum_{n \geq 1} \frac{\Lambda(n)}{n^s} f(\log n)$ expressed as a sum over the non-trivial
zeros of $\zeta$, where $f$ is a suitable smooth, compactly supported test function and $s$ a
complex parameter.
-/

namespace Kadiri

open MeasureTheory Complex
open ArithmeticFunction hiding log

/-! ## Precursor definitions for Proposition 2.1

`vonMangoldt` (with notation `Λ`), `Complex.Gamma` / `Complex.digamma`, and `riemannZeta`
are all in Mathlib. The set of zeros of `ζ` (and the rect-filtered variant
`riemannZeta.zeroes_rect`) are already defined in `ZetaDefinitions.lean`; the non-trivial zeros
are `riemannZeta.zeroes_rect (Set.Ioo 0 1) Set.univ`. -/

/-- Laplace transform of a real-valued function `f`:
`F(s) = ∫₀^∞ e^{-s · t} f(t) dt`. -/
noncomputable abbrev laplaceTransform (f : ℝ → ℝ) (s : ℂ) : ℂ :=
  RiemannZeta.WeilGuinand.laplaceTransform (fun t : ℝ => (f t : ℂ)) s

/-! ## Helper: finite support of `f ∘ log` -/

private lemma f_log_support_finite {d : ℝ} {f : ℝ → ℝ} (hf_supp : tsupport f ⊆ .Ico 0 d) :
    (Function.support (fun n : ℕ ↦ f (Real.log n))).Finite := by
  apply Set.Finite.subset (Set.finite_Iic ⌊Real.exp d⌋₊)
  intro n hn
  obtain ⟨_, h_lt⟩ := hf_supp (subset_tsupport f hn)
  rw [Set.mem_Iic]
  apply Nat.le_floor
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · exact_mod_cast (Real.exp_pos d).le
  · rw [← Real.exp_log (Nat.cast_pos.mpr hn0), Real.exp_le_exp]
    exact h_lt.le

/-- Corollary: any pointwise product `g n · f (Real.log n)` (in `ℂ`) is summable. -/
private lemma summable_f_log {d : ℝ} {f : ℝ → ℝ} (hf_supp : tsupport f ⊆ .Ico 0 d)
    (g : ℕ → ℂ) : Summable (fun n : ℕ ↦ g n * ((f (Real.log n) : ℝ) : ℂ)) := by
  apply summable_of_hasFiniteSupport
  refine (f_log_support_finite hf_supp).subset fun n hn ↦ ?_
  simp only [Function.mem_support] at hn ⊢
  exact fun h ↦ hn (by rw [h, Complex.ofReal_zero, mul_zero])

/-- A function with topological support contained in `[0, d)` vanishes to the left of `0`. -/
private lemma eq_zero_of_lt_zero {d x : ℝ} {f : ℝ → ℝ}
    (hf_supp : tsupport f ⊆ .Ico 0 d) (hx : x < 0) :
    f x = 0 := by
  by_contra hfx
  have hxmem : x ∈ Set.Ico (0 : ℝ) d := hf_supp (subset_tsupport f hfx)
  exact not_le_of_gt hx hxmem.1

/-- A function with topological support contained in `[0, d)` vanishes on and to the right of `d`. -/
private lemma eq_zero_of_ge_d {d x : ℝ} {f : ℝ → ℝ}
    (hf_supp : tsupport f ⊆ .Ico 0 d) (hx : d ≤ x) :
    f x = 0 := by
  by_contra hfx
  have hxmem : x ∈ Set.Ico (0 : ℝ) d := hf_supp (subset_tsupport f hfx)
  exact not_lt_of_ge hx hxmem.2

/-- The derivative of a compactly supported test function vanishes strictly to the right of `d`. -/
private lemma deriv_eq_zero_of_gt_d {d x : ℝ} {f : ℝ → ℝ}
    (hf_supp : tsupport f ⊆ .Ico 0 d) (hx : d < x) :
    deriv f x = 0 := by
  by_contra hfx
  have hxmem : x ∈ Set.Ico (0 : ℝ) d := hf_supp (support_deriv_subset hfx)
  exact not_lt_of_ge hx.le hxmem.2

/-- The second derivative also vanishes strictly to the right of `d`. -/
private lemma deriv_deriv_eq_zero_of_gt_d {d x : ℝ} {f : ℝ → ℝ}
    (hf_supp : tsupport f ⊆ .Ico 0 d) (hx : d < x) :
    deriv (deriv f) x = 0 := by
  have hEventually : (fun y ↦ deriv f y) =ᶠ[nhds x] (fun _ : ℝ ↦ 0) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact deriv_eq_zero_of_gt_d hf_supp hy
  simpa using hEventually.deriv_eq

/-- The real-valued Laplace integrand vanishes outside the compact support interval. -/
private lemma laplace_integrand_eq_zero_of_ge_d {d x : ℝ} {f : ℝ → ℝ}
    (hf_supp : tsupport f ⊆ .Ico 0 d) (w : ℂ) (hx : d ≤ x) :
    (f x : ℂ) * exp (-w * (x : ℂ)) = 0 := by
  simp [eq_zero_of_ge_d hf_supp hx]

/-- A half-line integral is a compact integral when the integrand vanishes to the right of `d`. -/
private lemma integral_Ioi_eq_integral_Ioc_of_forall_eq_zero_of_lt {d : ℝ} {g : ℝ → ℂ}
    (hg : ∀ x : ℝ, d < x → g x = 0) :
    (∫ x in Set.Ioi (0 : ℝ), g x ∂volume) =
      ∫ x in Set.Ioc (0 : ℝ) d, g x ∂volume := by
  have hEqOn : Set.EqOn g ((Set.Ioc (0 : ℝ) d).indicator g) (Set.Ioi (0 : ℝ)) := by
    intro x hx
    by_cases hxd : x ≤ d
    · exact (Set.indicator_of_mem (show x ∈ Set.Ioc (0 : ℝ) d from ⟨hx, hxd⟩) g).symm
    · have hdx : d < x := lt_of_not_ge hxd
      have hxnot : x ∉ Set.Ioc (0 : ℝ) d := fun hxIoc ↦ hxd hxIoc.2
      rw [Set.indicator_of_notMem hxnot]
      simp [hg x hdx]
  calc
    ∫ x in Set.Ioi (0 : ℝ), g x ∂volume =
        ∫ x in Set.Ioi (0 : ℝ), (Set.Ioc (0 : ℝ) d).indicator g x ∂volume := by
          exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hEqOn
    _ = ∫ x in Set.Ioi (0 : ℝ) ∩ Set.Ioc (0 : ℝ) d, g x ∂volume := by
          rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc]
    _ = ∫ x in Set.Ioc (0 : ℝ) d, g x ∂volume := by
          have hset : Set.Ioi (0 : ℝ) ∩ Set.Ioc (0 : ℝ) d = Set.Ioc (0 : ℝ) d := by
            ext x
            simp
          rw [hset]

/-- Under the compact-support hypothesis, the half-line Laplace integral is a compact integral. -/
private lemma laplaceTransform_eq_integral_Ioc {d : ℝ} {f : ℝ → ℝ}
    (hf_supp : tsupport f ⊆ .Ico 0 d) (w : ℂ) :
    laplaceTransform f w =
      ∫ x in Set.Ioc (0 : ℝ) d, (f x : ℂ) * exp (-w * (x : ℂ)) ∂volume := by
  let g : ℝ → ℂ := fun x ↦ (f x : ℂ) * exp (-w * (x : ℂ))
  exact integral_Ioi_eq_integral_Ioc_of_forall_eq_zero_of_lt fun x hx ↦ by
    simp [eq_zero_of_ge_d hf_supp hx.le]

/-- Interval-integral form of the compactly supported Laplace transform. -/
private lemma laplaceTransform_eq_intervalIntegral {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_supp : tsupport f ⊆ .Ico 0 d) (w : ℂ) :
    laplaceTransform f w =
      ∫ x in (0 : ℝ)..d, (f x : ℂ) * exp (-w * (x : ℂ)) ∂volume := by
  rw [laplaceTransform_eq_integral_Ioc hf_supp w, intervalIntegral.integral_of_le hd.le]

/-- Compact integral form for the Laplace transform of `f''`. -/
private lemma laplaceTransform_deriv_deriv_eq_integral_Ioc {d : ℝ} {f : ℝ → ℝ}
    (hf_supp : tsupport f ⊆ .Ico 0 d) (w : ℂ) :
    laplaceTransform (fun u ↦ deriv (𝕜 := ℝ) (deriv (𝕜 := ℝ) f) u) w =
      ∫ x in Set.Ioc (0 : ℝ) d,
        ((deriv (𝕜 := ℝ) (deriv (𝕜 := ℝ) f) x : ℝ) : ℂ) *
          exp (-w * (x : ℂ)) ∂volume := by
  let g : ℝ → ℂ := fun x ↦
    ((deriv (𝕜 := ℝ) (deriv (𝕜 := ℝ) f) x : ℝ) : ℂ) * exp (-w * (x : ℂ))
  exact integral_Ioi_eq_integral_Ioc_of_forall_eq_zero_of_lt fun x hx ↦ by
    simp [deriv_deriv_eq_zero_of_gt_d hf_supp hx]

/-- Interval-integral form for the Laplace transform of `f''`. -/
private lemma laplaceTransform_deriv_deriv_eq_intervalIntegral {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf_supp : tsupport f ⊆ .Ico 0 d) (w : ℂ) :
    laplaceTransform (fun u ↦ deriv (𝕜 := ℝ) (deriv (𝕜 := ℝ) f) u) w =
      ∫ x in (0 : ℝ)..d,
        ((deriv (𝕜 := ℝ) (deriv (𝕜 := ℝ) f) x : ℝ) : ℂ) *
          exp (-w * (x : ℂ)) ∂volume := by
  rw [laplaceTransform_deriv_deriv_eq_integral_Ioc hf_supp w,
    intervalIntegral.integral_of_le hd.le]

/-- A `C¹` real function on `[0, d]` has interval-integrable complexified derivative. -/
private lemma intervalIntegrable_deriv_complex_of_contDiffOn_Icc {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf_C1 : ContDiffOn ℝ 1 f (Set.Icc 0 d)) :
    IntervalIntegrable (fun x : ℝ ↦ ((deriv f x : ℝ) : ℂ)) volume 0 d := by
  have hcontWithin : ContinuousOn
      (fun x : ℝ ↦ ((derivWithin f (Set.Icc 0 d) x : ℝ) : ℂ)) (Set.Icc 0 d) :=
    continuous_ofReal.comp_continuousOn
      (hf_C1.continuousOn_derivWithin (uniqueDiffOn_Icc hd) (by norm_num))
  have hintWithinIoo : IntegrableOn
      (fun x : ℝ ↦ ((derivWithin f (Set.Icc 0 d) x : ℝ) : ℂ)) (Set.Ioo 0 d) volume :=
    hcontWithin.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
  have hEqOn : Set.EqOn
      (fun x : ℝ ↦ ((derivWithin f (Set.Icc 0 d) x : ℝ) : ℂ))
      (fun x : ℝ ↦ ((deriv f x : ℝ) : ℂ)) (Set.Ioo 0 d) := by
    intro x hx
    change ((derivWithin f (Set.Icc 0 d) x : ℝ) : ℂ) = ((deriv f x : ℝ) : ℂ)
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hd.le]
  exact hintWithinIoo.congr_fun hEqOn measurableSet_Ioo

/-- One integration by parts for the compactly supported Laplace transform. -/
private lemma interval_laplace_ibp_once {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C1 : ContDiffOn ℝ 1 f (Set.Icc 0 d)) (hf_d : f d = 0)
    {w : ℂ} (hw : w ≠ 0) :
    (∫ x in (0 : ℝ)..d, (f x : ℂ) * exp (-w * (x : ℂ)) ∂volume) =
      (f 0 : ℂ) / w +
        w⁻¹ * ∫ x in (0 : ℝ)..d, ((deriv f x : ℝ) : ℂ) *
          exp (-w * (x : ℂ)) ∂volume := by
  let v : ℝ → ℂ := fun x ↦ (-w⁻¹) * exp (-w * (x : ℂ))
  let v' : ℝ → ℂ := fun x ↦ exp (-w * (x : ℂ))
  have hu : ContinuousOn (fun x : ℝ ↦ (f x : ℂ)) (Set.uIcc (0 : ℝ) d) :=
    by simpa [Set.uIcc_of_le hd.le] using
      continuous_ofReal.comp_continuousOn hf_C1.continuousOn
  have hv : ContinuousOn v (Set.uIcc (0 : ℝ) d) := by
    fun_prop
  have hu' : IntervalIntegrable (fun x : ℝ ↦ ((deriv f x : ℝ) : ℂ)) volume 0 d :=
    intervalIntegrable_deriv_complex_of_contDiffOn_Icc hd hf_C1
  have hv' : IntervalIntegrable v' volume 0 d := by
    have hv'cont : ContinuousOn v' (Set.uIcc (0 : ℝ) d) := by
      fun_prop
    exact hv'cont.intervalIntegrable
  have huu' : ∀ x ∈ Set.Ioo (min (0 : ℝ) d) (max (0 : ℝ) d),
      HasDerivAt (fun x : ℝ ↦ (f x : ℂ)) ((deriv f x : ℝ) : ℂ) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) d := by simpa [min_eq_left hd.le, max_eq_right hd.le] using hx
    have hreal : HasDerivAt f (deriv f x) x :=
      (hf_C1.differentiableOn (by norm_num)).hasDerivAt (Icc_mem_nhds hx'.1 hx'.2)
    exact hreal.ofReal_comp
  have hvv' : ∀ x ∈ Set.Ioo (min (0 : ℝ) d) (max (0 : ℝ) d), HasDerivAt v (v' x) x := by
    intro x _hx
    exact hasDerivAt_laplaceKernelPrimitive hw x
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun x : ℝ ↦ (f x : ℂ)) (v := v)
    (u' := fun x : ℝ ↦ ((deriv f x : ℝ) : ℂ)) (v' := v')
    hu hv huu' hvv' hu' hv'
  dsimp [v, v'] at hIBP ⊢
  have hfactor :
      (∫ x in (0 : ℝ)..d, ((deriv f x : ℝ) : ℂ) *
          (-w⁻¹ * exp (-w * (x : ℂ))) ∂volume) =
        -w⁻¹ * ∫ x in (0 : ℝ)..d, ((deriv f x : ℝ) : ℂ) *
          exp (-w * (x : ℂ)) ∂volume := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  rw [hfactor] at hIBP
  simpa [hf_d, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hIBP

/-- Away from one point, almost everywhere. -/
private lemma ae_ne_volume (a : ℝ) : ∀ᵐ x : ℝ ∂volume, x ≠ a := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (measure_singleton a)] with x hx
  exact fun h ↦ hx (by simp [h])

/-- The second integration-by-parts step, applied to the one-sided derivative of `f` on
`[0, d]`.  This is the Kadiri/H1 formulation: endpoint derivatives are derivatives within the
closed interval, while the integrals may still be written with the ordinary derivatives because
the endpoints are null. -/
private lemma interval_laplace_ibp_derivWithin {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_derivWithin_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_derivWithin_d : derivWithin f (Set.Icc 0 d) d = 0)
    {w : ℂ} (hw : w ≠ 0) :
    (∫ x in (0 : ℝ)..d, ((deriv f x : ℝ) : ℂ) * exp (-w * (x : ℂ)) ∂volume) =
      w⁻¹ * ∫ x in (0 : ℝ)..d, ((deriv (deriv f) x : ℝ) : ℂ) *
        exp (-w * (x : ℂ)) ∂volume := by
  let g : ℝ → ℝ := fun x ↦ derivWithin f (Set.Icc 0 d) x
  have hg_C1 : ContDiffOn ℝ 1 g (Set.Icc 0 d) := by
    simpa [g] using
      hf_C2.derivWithin (uniqueDiffOn_Icc hd)
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have hleft :
      (∫ x in (0 : ℝ)..d, ((deriv f x : ℝ) : ℂ) * exp (-w * (x : ℂ)) ∂volume) =
        ∫ x in (0 : ℝ)..d, ((g x : ℝ) : ℂ) * exp (-w * (x : ℂ)) ∂volume := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_ne_volume 0, ae_ne_volume d] with x hx0 hxd hx
    have hxIoc : x ∈ Set.Ioc (0 : ℝ) d := by
      simpa [Set.uIoc_of_le hd.le] using hx
    have hxIoo : x ∈ Set.Ioo (0 : ℝ) d :=
      ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hxd⟩
    change ((deriv f x : ℝ) : ℂ) * exp (-w * (x : ℂ)) =
      ((g x : ℝ) : ℂ) * exp (-w * (x : ℂ))
    rw [show g x = deriv f x by
      dsimp [g]
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds hxIoo.1 hxIoo.2)]]
  have hright :
      (∫ x in (0 : ℝ)..d, ((deriv g x : ℝ) : ℂ) * exp (-w * (x : ℂ)) ∂volume) =
        ∫ x in (0 : ℝ)..d, ((deriv (deriv f) x : ℝ) : ℂ) *
          exp (-w * (x : ℂ)) ∂volume := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_ne_volume 0, ae_ne_volume d] with x hx0 hxd hx
    have hxIoc : x ∈ Set.Ioc (0 : ℝ) d := by
      simpa [Set.uIoc_of_le hd.le] using hx
    have hxIoo : x ∈ Set.Ioo (0 : ℝ) d :=
      ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hxd⟩
    have hg_eventually : g =ᶠ[nhds x] deriv f := by
      refine (Set.EqOn.eventuallyEq_of_mem ?_ (Ioo_mem_nhds hxIoo.1 hxIoo.2))
      intro y hy
      dsimp [g]
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)]
    change ((deriv g x : ℝ) : ℂ) * exp (-w * (x : ℂ)) =
      ((deriv (deriv f) x : ℝ) : ℂ) * exp (-w * (x : ℂ))
    rw [hg_eventually.deriv_eq]
  have hibp := interval_laplace_ibp_once (d := d) (f := g) hd hg_C1 hf_derivWithin_d hw
  calc
    (∫ x in (0 : ℝ)..d, ((deriv f x : ℝ) : ℂ) * exp (-w * (x : ℂ)) ∂volume)
        = ∫ x in (0 : ℝ)..d, ((g x : ℝ) : ℂ) * exp (-w * (x : ℂ)) ∂volume := hleft
    _ = w⁻¹ * ∫ x in (0 : ℝ)..d, ((deriv g x : ℝ) : ℂ) *
          exp (-w * (x : ℂ)) ∂volume := by
      simpa [g, hf_derivWithin_0, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hibp
    _ = w⁻¹ * ∫ x in (0 : ℝ)..d, ((deriv (deriv f) x : ℝ) : ℂ) *
          exp (-w * (x : ℂ)) ∂volume := by
      rw [hright]

/-- Two integrations by parts on the compact interval `[0, d]`. -/
private lemma interval_laplace_ibp_twice {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C1 : ContDiffOn ℝ 1 f (Set.Icc 0 d))
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_d : f d = 0)
    (hf_derivWithin_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_derivWithin_d : derivWithin f (Set.Icc 0 d) d = 0)
    {w : ℂ} (hw : w ≠ 0) :
    (∫ x in (0 : ℝ)..d, (f x : ℂ) * exp (-w * (x : ℂ)) ∂volume) =
      (f 0 : ℂ) / w +
        (∫ x in (0 : ℝ)..d, ((deriv (deriv f) x : ℝ) : ℂ) *
          exp (-w * (x : ℂ)) ∂volume) / w ^ 2 := by
  rw [interval_laplace_ibp_once hd hf_C1 hf_d hw,
    interval_laplace_ibp_derivWithin hd hf_C2 hf_derivWithin_0 hf_derivWithin_d hw]
  field_simp [hw]

/-- Half-line Laplace-transform form of the two-integration-by-parts identity. -/
private lemma laplaceTransform_ibp_of_contDiffOn_two {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C1 : ContDiffOn ℝ 1 f (Set.Icc 0 d))
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_derivWithin_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_derivWithin_d : derivWithin f (Set.Icc 0 d) d = 0)
    {w : ℂ} (hw : w ≠ 0) :
    laplaceTransform f w =
      (f 0 : ℂ) / w + laplaceTransform (fun u ↦ deriv (deriv f) u) w / w ^ 2 := by
  rw [laplaceTransform_eq_intervalIntegral hd hf_supp w,
    laplaceTransform_deriv_deriv_eq_intervalIntegral hd hf_supp w]
  exact interval_laplace_ibp_twice hd hf_C1 hf_C2 hf_d hf_derivWithin_0 hf_derivWithin_d hw

/-! ## Precursor results for Proposition 2.1

Three ingredients of the proof of \ref{kadiri-prop-2-1}: the Hadamard constant $B$
(\ref{kadiri-hadamard-B}), the Hadamard expansion of $-\zeta'/\zeta$
(\ref{kadiri-hadamard-identity}), and the intermediate identity (16) of \cite{Kadiri2005}
obtained by applying the Weil-type explicit formula to a specific test function
(\ref{kadiri-identity-16}). All three are stated below with `sorry` proofs.
\ref{kadiri-prop-2-1} below is stated on the half-plane $\Re s > 1$, which is enough for
Kadiri's zero-free-region argument; the harmonic-extension principle that would
lift it to all of $\mathbb{C}$ is no longer needed and is commented out below
(see \ref{kadiri-re-agree-extension}). -/

blueprint_comment /--
The constant $B \in \mathbb{C}$ is the derivative of the degree-one polynomial in the
genus-one Hadamard product for Riemann's entire xi function:
$$ \xi(s) = e^{A + Bs}
     \prod_{\rho \in Z(\zeta)} \left(1 - \tfrac{s}{\rho}\right) e^{s/\rho}. $$
Here we take an explicit xi Hadamard polynomial `P` and use
`Polynomial.eval 0 P.derivative`. The uniqueness statement below shows that this value is
independent of the chosen no-monomial Hadamard factorisation.

The theorem `existsUnique_hadamardB` below is the canonical formulation: it proves that the
candidate value extracted from any no-monomial xi Hadamard polynomial is unique.
-/

@[blueprint
  "kadiri-hadamard-B"
  (title := "Canonical xi Hadamard constant")
  (statement := /-- There is a unique complex number obtained as the derivative at the origin of
  the degree-one polynomial in a no-monomial genus-one Hadamard factorisation of Riemann's entire
  xi function:
  $$ \xi(s) = e^{P(s)}
       \prod_{\rho} \left(1 - \tfrac{s}{\rho}\right)e^{s/\rho},
  \qquad \deg P \le 1. $$
  This unique value is Kadiri's Hadamard constant $B$. -/)
  (proof := /-- Existence is the genus-one Hadamard factorisation for `riemannXi`, with the origin
  monomial removed by `riemannXi 0 \ne 0`.  Uniqueness follows by taking logarithmic derivatives of
  two such factorisations at `0`: the divisor-indexed zero product has the same logarithmic
  derivative in both identities, and `0` is not among the nonzero divisor indices. -/)
  (latexEnv := "lemma")
  (discussion := 1474)]
theorem existsUnique_hadamardB : ∃! B : ℂ, ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧
    (∀ z : ℂ, riemannXi z = Complex.exp (Polynomial.eval z P) *
      Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) z) ∧
    B = Polynomial.eval 0 P.derivative :=
  existsUnique_riemannXi_hadamard_polynomial_derivative_eval_zero

/-- Kadiri's Hadamard constant `B`: the canonical value `P'(0)`, common to every degree-≤1
no-monomial xi Hadamard polynomial `P` by `existsUnique_hadamardB`. -/
noncomputable def hadamardB : ℂ := existsUnique_hadamardB.exists.choose

/-- The defining property of `hadamardB`: it is `P'(0)` for some degree-≤1 no-monomial xi
Hadamard polynomial `P`. -/
theorem hadamardB_spec :  ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧ (∀ z : ℂ, riemannXi z =
      Complex.exp (Polynomial.eval z P) *
        Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) z) ∧
    hadamardB = Polynomial.eval 0 P.derivative :=
  existsUnique_hadamardB.exists.choose_spec

/-! ## The zeros of `ξ` are exactly the non-trivial zeros of `ζ`

The Hadamard factorisation above is indexed by the divisor zeros of Riemann's entire `ξ`
(`Complex.Hadamard.divisorZeroIndex₀ riemannXi`). Kadiri's explicit formula is phrased over
the non-trivial zeros of `ζ`, i.e.\ `riemannZeta.zeroes_rect (.Ioo 0 1) .univ`.  The classical
fact reconciling the two indexings is that every zero of `ξ` lies in the open critical strip
`0 < \Re s < 1`, and there `ξ(s) = 0 ↔ ζ(s) = 0`.  These lemmas establish that correspondence;
they are the foundation for the (multiplicity-aware) reindexing of the divisor-indexed zero sum
onto `zeroes_rect`. -/

/-- For `\Re s > 0`, the completed zeta function factors as `Λ(s) = Γ_ℝ(s) · ζ(s)`
(valid throughout the right half-plane, not just on `Ω = {\Re s > 1/2}`). -/
private lemma completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta_of_re_pos {s : ℂ}
    (hs : 0 < s.re) : completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hdef : riemannZeta s = completedRiemannZeta s / Gammaℝ s :=
    riemannZeta_def_of_ne_zero hs0
  rw [eq_div_iff hΓ] at hdef
  rw [← hdef]; ring

/-- Inside the open critical strip, `ξ` vanishes exactly where `ζ` does. -/
private lemma riemannXi_eq_zero_iff_riemannZeta_of_mem_strip {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannXi s = 0 ↔ riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at h0
  have hs1 : s ≠ 1 := by rintro rfl; simp at h1
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0
  have hXi : riemannXi s = (s * (s - 1) * Gammaℝ s / 2) * riemannZeta s := by
    rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1,
        completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta_of_re_pos h0]
    ring
  have hpre : s * (s - 1) * Gammaℝ s / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) hΓ) (by norm_num)
  rw [hXi, mul_eq_zero]
  simp [hpre]

/-- `ξ` does not vanish on the closed half-plane `\Re s ≥ 1`. -/
private lemma riemannXi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannXi s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hs1
  · have h10 : riemannXi (1 : ℂ) = riemannXi 0 := by
      have := riemannXi_one_sub (1 : ℂ); simpa using this.symm
    rw [h10, riemannXi_zero]; norm_num
  · have hs0 : s ≠ 0 := by rintro rfl; norm_num [Complex.zero_re] at hs
    have h0 : (0 : ℝ) < s.re := lt_of_lt_of_le one_pos hs
    have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0
    have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs
    rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1,
        completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta_of_re_pos h0]
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) (mul_ne_zero hΓ hζ)) (by norm_num)

/-- `ξ` does not vanish on the closed half-plane `\Re s ≤ 0` (by the functional equation). -/
private lemma riemannXi_ne_zero_of_re_le_zero {s : ℂ} (hs : s.re ≤ 0) : riemannXi s ≠ 0 := by
  rw [← riemannXi_one_sub]
  refine riemannXi_ne_zero_of_one_le_re ?_
  rw [Complex.sub_re, Complex.one_re]; linarith

/-- **ξ–ζ zero correspondence.** Riemann's entire `ξ` vanishes precisely at the non-trivial
zeros of `ζ`: at points of the open critical strip `0 < \Re s < 1` where `ζ` vanishes. -/
theorem riemannXi_eq_zero_iff_mem_nontrivial {s : ℂ} :
    riemannXi s = 0 ↔ (0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0) := by
  constructor
  · intro hXi
    grind only [hadamardB_spec, riemannXi_ne_zero_of_re_le_zero,
      riemannXi_eq_zero_iff_riemannZeta_of_mem_strip, riemannXi_ne_zero_of_one_le_re]
  · rintro ⟨h0, h1, hz⟩
    exact (riemannXi_eq_zero_iff_riemannZeta_of_mem_strip h0 h1).mpr hz

/-- The zero set of `ξ` is exactly `riemannZeta.zeroes_rect (.Ioo 0 1) .univ`. -/
theorem riemannXi_eq_zero_iff_mem_zeroes_rect {s : ℂ} :
    riemannXi s = 0 ↔ s ∈ riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) := by
  rw [riemannXi_eq_zero_iff_mem_nontrivial]
  simp only [riemannZeta.zeroes_rect, riemannZeta.zeroes, Set.mem_setOf_eq, Set.mem_Ioo,
    Set.mem_univ, true_and]
  tauto

/-- At any point where `ζ` is analytic (`z ≠ 1`), Kadiri's integer multiplicity
`riemannZeta.order z` coincides with the analytic (ℕ-valued) order of `ζ`.  This identifies the
order-weighting used in `riemannZeta.zeroes_sum` with the analytic multiplicity that the Hadamard
divisor counts.  (The identity holds even in the vacuous `⊤`/identically-zero case, where both
sides are `0`.) -/
theorem riemannZeta_order_eq_analyticOrderNatAt {z : ℂ} (hz : z ≠ 1) :
    riemannZeta.order z = (analyticOrderNatAt riemannZeta z : ℤ) := by
  have han : AnalyticAt ℂ riemannZeta z :=
    riemannZeta_analyticOn_compl_one z (Set.mem_compl_singleton_iff.mpr hz)
  simp only [riemannZeta.order, analyticOrderNatAt]
  cases h : analyticOrderAt riemannZeta z with
  | top => simp [han.meromorphicOrderAt_eq, h]
  | coe n =>
    rw [han.meromorphicOrderAt_eq, h]
    rfl

/-! ### Order matching: `ξ` and `ζ` have equal multiplicity in the strip

The Hadamard divisor of `ξ` counts each zero with its analytic multiplicity
`analyticOrderNatAt riemannXi`.  In the open critical strip this equals the analytic order of
`ζ`, hence (via `riemannZeta_order_eq_analyticOrderNatAt`) Kadiri's `riemannZeta.order`.  This is
the multiplicity half of the divisor→order-weighted reindexing of the Hadamard zero sum. -/

/-- `Γ_ℝ` is analytic on the right half-plane `0 < Re s`: its reciprocal is entire
(`differentiable_Gammaℝ_inv`) and nonvanishing there. -/
private lemma analyticAt_Gammaℝ_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ Gammaℝ z := by
  have hinv : AnalyticAt ℂ (fun s : ℂ => (Gammaℝ s)⁻¹) z :=
    differentiable_Gammaℝ_inv.analyticAt z
  have hne : (Gammaℝ z)⁻¹ ≠ 0 := inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hz)
  have h2 : AnalyticAt ℂ (fun s : ℂ => ((Gammaℝ s)⁻¹)⁻¹) z := hinv.inv hne
  have heq : (fun s : ℂ => ((Gammaℝ s)⁻¹)⁻¹) = Gammaℝ := by funext s; rw [inv_inv]
  rwa [heq] at h2

/-- In the open critical strip, the analytic (ℕ-valued) order of `ξ` equals that of `ζ`:
near such a point `ξ = (s(s-1)/2 · Γ_ℝ) · ζ`, with the prefactor an analytic non-vanishing
unit (so it contributes order `0`). -/
theorem analyticOrderNatAt_riemannXi_eq_riemannZeta {z : ℂ}
    (h0 : 0 < z.re) (h1 : z.re < 1) :
    analyticOrderNatAt riemannXi z = analyticOrderNatAt riemannZeta z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at h0
  have hz1 : z ≠ 1 := by rintro rfl; simp at h1
  have hΓ_an : AnalyticAt ℂ Gammaℝ z := analyticAt_Gammaℝ_of_re_pos h0
  have hpoly : Differentiable ℂ (fun w : ℂ => w * (w - 1) / 2) := by fun_prop
  have hpoly_an : AnalyticAt ℂ (fun w : ℂ => w * (w - 1) / 2) z := hpoly.analyticAt z
  have hg_an : AnalyticAt ℂ (fun w : ℂ => w * (w - 1) / 2 * Gammaℝ w) z := hpoly_an.mul hΓ_an
  have hζ_an : AnalyticAt ℂ riemannZeta z :=
    riemannZeta_analyticOn_compl_one z (Set.mem_compl_singleton_iff.mpr hz1)
  have hEq : riemannXi =ᶠ[nhds z] (fun w : ℂ => w * (w - 1) / 2 * Gammaℝ w) * riemannZeta := by
    have hV : {w : ℂ | 0 < w.re ∧ w.re < 1} ∈ nhds z :=
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds ⟨h0, h1⟩
    filter_upwards [hV] with w hw
    obtain ⟨hw0, hw1⟩ := hw
    have hwne0 : w ≠ 0 := by rintro rfl; simp at hw0
    have hwne1 : w ≠ 1 := by rintro rfl; simp at hw1
    simp only [Pi.mul_apply]
    rw [riemannXi_eq_mul_completedRiemannZeta hwne0 hwne1,
        completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta_of_re_pos hw0]
    ring
  have hg_ne : (fun w : ℂ => w * (w - 1) / 2 * Gammaℝ w) z ≠ 0 := by
    exact mul_ne_zero
      (div_ne_zero (mul_ne_zero hz0 (sub_ne_zero.mpr hz1)) (by norm_num))
      (Gammaℝ_ne_zero_of_re_pos h0)
  dsimp only [analyticOrderNatAt]
  rw [analyticOrderAt_congr hEq, analyticOrderAt_mul hg_an hζ_an,
      hg_an.analyticOrderAt_eq_zero.mpr hg_ne, zero_add]

/-- In the open critical strip, the analytic multiplicity of `ξ` (what the Hadamard divisor
counts) is exactly Kadiri's integer order weight `riemannZeta.order`.  This is the per-zero
weight identity underlying the divisor→`riemannZeta.zeroes_sum` reindexing. -/
theorem analyticOrderNatAt_riemannXi_eq_order {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    (analyticOrderNatAt riemannXi z : ℤ) = riemannZeta.order z := by
  have hz1 : z ≠ 1 := by rintro rfl; simp at h1
  rw [analyticOrderNatAt_riemannXi_eq_riemannZeta h0 h1,
      riemannZeta_order_eq_analyticOrderNatAt hz1]

@[blueprint
  "kadiri-hadamard-identity"
  (title := "Hadamard expansion of $-\\zeta'/\\zeta$ (after equation (16))")
  (statement := /-- For every $s \in \mathbb{C}$ that is neither $1$ nor a non-trivial zero
  of $\zeta$,
  $$ -\frac{\zeta'}{\zeta}(s) = -B - \tfrac{1}{2} \log \pi + \frac{1}{s - 1}
       + \tfrac{1}{2} \frac{\Gamma'}{\Gamma}\!\left(\tfrac{s}{2} + 1\right)
       - \sum_{\rho \in Z(\zeta)} \left(\frac{1}{\rho} + \frac{1}{s - \rho}\right), $$
  where $B$ is the xi Hadamard constant (\ref{kadiri-hadamard-B}). This is obtained by
  differentiating the genus-one Hadamard factorisation of `riemannXi` and then using
  $\xi(s) = (s - 1)\pi^{-s/2}\Gamma(s/2+1)\zeta(s)$ on $\Re s > 1$
  (\cite[Chapter 12]{Davenport2000}). -/)
  (proof := /-- Differentiate the xi Hadamard product (\ref{kadiri-hadamard-B})
  logarithmically; the derivative of the degree-one Hadamard polynomial is the constant
  $B$. The $\tfrac{1}{s-1}$ term comes from the pole factor in
  $\xi(s) = (s - 1)\pi^{-s/2}\Gamma(s/2+1)\zeta(s)$, and the
  $\tfrac{1}{2} \Gamma'/\Gamma$ term comes from the shifted gamma factor. The identity is derived
  from the Hadamard product for `riemannXi`, not from one for $(s - 1)\zeta(s)`. -/)
  (latexEnv := "lemma")
  (discussion := 1474)]
theorem hadamard_identity (s : ℂ) (hs1 : s ≠ 1)
    (hsZ : s ∉ riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ)) :
    -deriv riemannZeta s / riemannZeta s =
      -hadamardB - (1 / 2 : ℂ) * Real.log Real.pi + 1 / (s - 1) +
      (1 / 2 : ℂ) * digamma (s / 2 + 1) -
      ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
        (1 / (ρ.val : ℂ) + 1 / (s - ρ.val)) := by
  sorry

/-- Version of the Hadamard logarithmic derivative using an explicit degree-one xi Hadamard
polynomial and its derivative at the origin. Translating the divisor-indexed xi zeros to
`riemannZeta.zeroes_rect` gives the zero sum in the blueprint statement `hadamard_identity`. -/
theorem neg_zeta_logDeriv_eq_of_riemannXi_hadamardPolynomial
    {P : Polynomial ℂ}
    (hdeg : P.degree ≤ 1)
    (hfac : ∀ z : ℂ, Complex.riemannXi z =
      Complex.exp (Polynomial.eval z P) *
        Complex.Hadamard.divisorCanonicalProduct 1 Complex.riemannXi (Set.univ : Set ℂ) z)
    (s : ℂ)
    (hs : 1 < s.re)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓ : zetaGammaFactor s ≠ 0)
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ),
      s ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    -deriv riemannZeta s / riemannZeta s =
      -Polynomial.eval 0 P.derivative
      - ∑' p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ),
          (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p)
      + 1 / (s - 1)
      - (1 / 2 : ℂ) * Real.log Real.pi
      + (1 / 2 : ℂ) * digamma (s / 2 + 1) := by
  have h :=
    neg_zeta_logDeriv_eq_of_riemannXi_polynomial_hadamard
      (P := P) s hs hΓdiff hΓ hfac hz
  rw [Polynomial.eval_derivative_eq_eval_derivative_zero_of_degree_le_one hdeg s] at h
  exact h

/-- Structured `q = 1`, trivial-character Weil--Guinand formula. This is the analytic
contour-shift theorem; the displayed equality below is a projection of this structure. -/
theorem kadiri_thm_3_1_q1_QOneFormula_core {φ : ℝ → ℂ} (_hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (_hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (_hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    RiemannZeta.WeilGuinand.QOneFormula φ
      (RiemannZeta.WeilGuinand.laplaceTransform φ)
      (fun n : ℕ => (Λ n : ℂ))
      (fun n : ℕ => (Λ n : ℂ) / (n : ℂ))
      (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) => ρ.val) := by
  sorry

@[blueprint
  "kadiri-thm-3-1-q1"
  (title := "Theorem 3.1 of \\cite{Kadiri2005}, case $q = 1$, $\\chi$ trivial")
  (statement := /-- Let $\varphi \colon \mathbb{R} \to \mathbb{C}$ be $C^1$ and suppose there
  exists $b > 0$ such that both $\varphi(x) e^{x/2}$ and $\varphi'(x) e^{x/2}$ are
  $O(e^{-(1/2 + b)|x|})$ as $|x| \to \infty$. Define the Laplace transform
  $\Phi(z) := \int_0^{\infty} \varphi(y) e^{-zy}\, dy$. Then
  $$ \sum_{n \geq 1} \Lambda(n)\, \varphi(\log n)
     = \Phi(-1) + \Phi(0) - \sum_{\rho \in Z(\zeta)} \Phi(-\rho)
       - \varphi(0)\, \log \pi
       + \sum_{n \geq 1} \tfrac{\Lambda(n)}{n}\, \varphi(-\log n)
       + \tfrac{1}{2 \pi i} \int_{1/2 - i\infty}^{1/2 + i\infty}
           \Re \tfrac{\Gamma'}{\Gamma}\!\left( \tfrac{z}{2} \right) \Phi(-z)\, dz, $$
  where the $\rho$-sum runs over the non-trivial zeros of $\zeta$.

  This is the $q = 1$, $\chi$ trivial case of the Weil-type explicit formula of
  \cite[Theorem 3.1]{Kadiri2005}. The $\Phi(-1)$ term comes from the simple pole of $\zeta$
  at $z = 1$ (and is absent for non-trivial $\chi$); the $\varphi(0)\log\pi$ term and the
  $\Gamma$-integral come from the gamma factor in the functional equation of $\zeta$; the
  $\sum_n \tfrac{\Lambda(n)}{n}\varphi(-\log n)$ term is the contribution from the reflected
  ($z \leftrightarrow 1 - z$) Dirichlet series. -/)
  (proof := /-- Classical Weil-style argument. Write the LHS as a Mellin contour integral
  $\tfrac{1}{2\pi i} \int_{(c)} (-\zeta'/\zeta)(z)\, \Phi(-z)\, dz$ for some $c > 1$, using
  the Dirichlet series $-\zeta'/\zeta(z) = \sum_n \Lambda(n) n^{-z}$ on $\Re z > 1$ together
  with the Mellin inversion $\varphi(\log n) = \tfrac{1}{2\pi i} \int_{(c)} n^z \Phi(-z)\, dz$.
  Contour-shift to $\Re z = -1 - a$ for some $0 < a < b$, picking up residues at: $z = 1$
  (the simple pole of $\zeta$, contributing $\Phi(-1)$); $z = 0$ (contributing $\Phi(0)$ via
  the Laurent expansion of $-\zeta'/\zeta$ at $0$); and each non-trivial zero $z = \rho$
  (contributing $-\Phi(-\rho)$). Then use the functional equation
  $\zeta(z) \Gamma(z/2) \pi^{-z/2} = \zeta(1-z) \Gamma((1-z)/2) \pi^{-(1-z)/2}$
  to rewrite the integral on $\Re z = -1 - a$ as the reflected Dirichlet series
  $\sum_n \tfrac{\Lambda(n)}{n} \varphi(-\log n)$ plus the $\Gamma'/\Gamma$ contour integral
  on $\Re z = 1/2$, with the $\pi^{z/2}$ factor producing $-\varphi(0)\log\pi$. To be
  formalised. -/)
  (latexEnv := "theorem")]
theorem kadiri_thm_3_1_q1 {φ : ℝ → ℂ} (_hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (_hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (_hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    let Φ : ℂ → ℂ := fun z ↦ ∫ y in (.Ioi (0 : ℝ)), φ y * exp (-z * (y : ℂ)) ∂volume
    (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n)) =
      Φ (-1) + Φ 0
        - ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ), Φ (-ρ.val)
        - φ 0 * ((Real.log Real.pi : ℝ) : ℂ)
        + ∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n)
        + (1 / (2 * (Real.pi : ℂ))) *
            ∫ t : ℝ,
              ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
                Φ (-(1 / 2 + (t : ℂ) * I)) := by
  dsimp
  have hQ := kadiri_thm_3_1_q1_QOneFormula_core _hφ _hb _hφ_decay _hφ'_decay
  have hΛ0 : (fun n : ℕ => (Λ n : ℂ)) 0 = 0 := by simp
  have hΛref0 : (fun n : ℕ => (Λ n : ℂ) / (n : ℂ)) 0 = 0 := by simp
  have hformula := hQ.formula
  rw [RiemannZeta.WeilGuinand.primeSum_eq_tsum_nat hΛ0] at hformula
  rw [RiemannZeta.WeilGuinand.qOneRHS] at hformula
  rw [RiemannZeta.WeilGuinand.reflectedPrimeSum_eq_tsum_nat hΛref0] at hformula
  simpa [RiemannZeta.WeilGuinand.zeroSum, RiemannZeta.WeilGuinand.gammaIntegral,
    RiemannZeta.WeilGuinand.gammaIntegrand, RiemannZeta.WeilGuinand.laplaceTransform] using
    hformula

/-- The displayed `q = 1` formula follows from the abstract Weil--Guinand formulation with the
Riemann-zeta coefficients and the standard indexing of non-trivial zeros. -/
theorem kadiri_thm_3_1_q1_of_QOneFormula {φ : ℝ → ℂ}
    (hQ : RiemannZeta.WeilGuinand.QOneFormula φ
      (RiemannZeta.WeilGuinand.laplaceTransform φ)
      (fun n : ℕ => (Λ n : ℂ))
      (fun n : ℕ => (Λ n : ℂ) / (n : ℂ))
      (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) => ρ.val)) :
    let Φ : ℂ → ℂ := fun z ↦ ∫ y in (.Ioi (0 : ℝ)), φ y * exp (-z * (y : ℂ)) ∂volume
    (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n)) =
      Φ (-1) + Φ 0
        - ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ), Φ (-ρ.val)
        - φ 0 * ((Real.log Real.pi : ℝ) : ℂ)
        + ∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n)
        + (1 / (2 * (Real.pi : ℂ))) *
            ∫ t : ℝ,
              ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
                Φ (-(1 / 2 + (t : ℂ) * I)) := by
  dsimp
  have hΛ0 : (fun n : ℕ => (Λ n : ℂ)) 0 = 0 := by simp
  have hΛref0 : (fun n : ℕ => (Λ n : ℂ) / (n : ℂ)) 0 = 0 := by simp
  have hformula := hQ.formula
  rw [RiemannZeta.WeilGuinand.primeSum_eq_tsum_nat hΛ0] at hformula
  rw [RiemannZeta.WeilGuinand.qOneRHS] at hformula
  rw [RiemannZeta.WeilGuinand.reflectedPrimeSum_eq_tsum_nat hΛref0] at hformula
  simpa [RiemannZeta.WeilGuinand.zeroSum, RiemannZeta.WeilGuinand.gammaIntegral,
    RiemannZeta.WeilGuinand.gammaIntegrand, RiemannZeta.WeilGuinand.laplaceTransform] using
    hformula

/-- Structured `q = 1`, trivial-character Weil--Guinand formula. Unlike the displayed theorem
`kadiri_thm_3_1_q1`, this keeps the convergence hypotheses supplied by the contour-shift proof. -/
theorem kadiri_thm_3_1_q1_QOneFormula {φ : ℝ → ℂ} (_hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (_hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (_hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    RiemannZeta.WeilGuinand.QOneFormula φ
      (RiemannZeta.WeilGuinand.laplaceTransform φ)
      (fun n : ℕ => (Λ n : ℂ))
      (fun n : ℕ => (Λ n : ℂ) / (n : ℂ))
      (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) => ρ.val) := by
  exact kadiri_thm_3_1_q1_QOneFormula_core _hφ _hb _hφ_decay _hφ'_decay

theorem kadiri_thm_3_1_q1_zero_summable {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) =>
      RiemannZeta.WeilGuinand.laplaceTransform φ (-ρ.val)) := by
  exact (kadiri_thm_3_1_q1_QOneFormula hφ hb hφ_decay hφ'_decay).zero_summable

/-! ## Machinery for deriving (16) from Theorem 3.1

Three sublemmas (\ref{kadiri-laplace-ibp}, \ref{kadiri-test-fn-contDiff} +
\ref{kadiri-test-fn-decay}, \ref{kadiri-test-fn-laplace}) reduce the proof of
\ref{kadiri-identity-16} (given \ref{kadiri-thm-3-1-q1}) to algebraic identities. The first one
(\ref{kadiri-laplace-ibp}) is also a precursor for \ref{kadiri-laplace-re-decay}. -/

@[blueprint
  "kadiri-laplace-ibp"
  (title := "Two-integration-by-parts form of the Laplace transform")
  (statement := /-- Formal integration-by-parts version of the $F$/$F_2$ relation used in
  \ref{kadiri-prop-2-1}.  For $f$ satisfying the compact-support and endpoint hypotheses of
  $(H_1)$, with endpoint derivatives interpreted within `[0,d]`, for every
  $w \in \mathbb{C}$ with $w \neq 0$,
  $$ F(w) = \frac{f(0)}{w} + \frac{F_2(w)}{w^2}, $$
  where $F_2(w) := \int_0^d e^{-wy} f''(y)\, dy$ is the Laplace transform of $f''$. -/)
  (proof := /-- Two successive integrations by parts on
  $F(w) = \int_0^d e^{-wy} f(y)\, dy$. The first gives
  $F(w) = \tfrac{f(0)}{w} - \tfrac{f(d) e^{-w d}}{w}
        + \tfrac{1}{w} \int_0^d e^{-wy} f'(y)\, dy$;
  using $f(d) = 0$ from $(H_1)$ kills the boundary term, leaving
  $\tfrac{f(0)}{w} + \tfrac{1}{w} \int_0^d e^{-wy} f'(y)\, dy$. The second IBP on the
  remaining integral gives
  $\tfrac{1}{w} \int_0^d e^{-wy} f'(y)\, dy
   = \tfrac{f'(0)}{w^2} - \tfrac{f'(d) e^{-w d}}{w^2}
     + \tfrac{1}{w^2} \int_0^d e^{-wy} f''(y)\, dy$;
  using the one-sided endpoint conditions $f'(0) = f'(d) = 0$ from $(H_1)$ kills both boundary
  terms, leaving
  $F_2(w)/w^2$. To be formalised. -/)
  (latexEnv := "lemma")
  (discussion := 1483)]
theorem laplaceTransform_ibp {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_derivWithin_0 : derivWithin f (.Icc 0 d) 0 = 0)
    (hf_derivWithin_d : derivWithin f (.Icc 0 d) d = 0)
    {w : ℂ} (hw : w ≠ 0) :
    laplaceTransform f w =
      (f 0 : ℂ) / w + laplaceTransform (fun u ↦ deriv (deriv f) u) w / w ^ 2 := by
  have hf_C1 : ContDiffOn ℝ 1 f (.Icc 0 d) := hf_C2.of_le (by norm_num)
  exact laplaceTransform_ibp_of_contDiffOn_two hd hf_C1 hf_C2 hf_supp hf_d hf_derivWithin_0
    hf_derivWithin_d hw

@[blueprint
  "kadiri-test-fn"
  (title := "The Kadiri test function")
  (statement := /-- The $s$-parametrised test function
  $\varphi(y;\, s) := (f(0) - f(y))\, e^{-y s}\, \mathbf{1}_{y \geq 0}$ used to derive
  \ref{kadiri-identity-16} from \ref{kadiri-thm-3-1-q1}. -/)
  (latexEnv := "definition")
  (discussion := 1484)]
noncomputable def kadiriTestFn (f : ℝ → ℝ) (s : ℂ) : ℝ → ℂ := fun y ↦
  if 0 ≤ y then ((f 0 : ℂ) - (f y : ℂ)) * exp (-s * (y : ℂ)) else 0

@[simp]
theorem kadiriTestFn_of_lt_zero {f : ℝ → ℝ} {s : ℂ} {y : ℝ} (hy : y < 0) :
    kadiriTestFn f s y = 0 := by
  simp [kadiriTestFn, not_le_of_gt hy]

theorem kadiriTestFn_of_nonneg {f : ℝ → ℝ} {s : ℂ} {y : ℝ} (hy : 0 ≤ y) :
    kadiriTestFn f s y = ((f 0 : ℂ) - (f y : ℂ)) * exp (-s * (y : ℂ)) := by
  simp [kadiriTestFn, hy]

theorem kadiriTestFn_of_ge_d {d y : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_supp : tsupport f ⊆ .Ico 0 d) (s : ℂ) (hy : d ≤ y) :
    kadiriTestFn f s y = (f 0 : ℂ) * exp (-s * (y : ℂ)) := by
  rw [kadiriTestFn_of_nonneg (le_trans hd.le hy), eq_zero_of_ge_d hf_supp hy]
  simp

theorem kadiriTestFn_mul_exp_of_pos {f : ℝ → ℝ} {s z : ℂ} {y : ℝ} (hy : 0 < y) :
    kadiriTestFn f s y * exp (-z * (y : ℂ)) =
      ((f 0 : ℂ) - (f y : ℂ)) * exp (-(s + z) * (y : ℂ)) := by
  rw [kadiriTestFn_of_nonneg hy.le]
  rw [mul_assoc, ← Complex.exp_add]
  congr 1
  ring_nf

theorem kadiriTestFn_mul_exp_of_lt_zero {f : ℝ → ℝ} {s z : ℂ} {y : ℝ} (hy : y < 0) :
    kadiriTestFn f s y * exp (-z * (y : ℂ)) = 0 := by
  simp [kadiriTestFn_of_lt_zero hy]

theorem kadiriTestFn_mul_exp_of_ge_d {d y : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_supp : tsupport f ⊆ .Ico 0 d) (s z : ℂ) (hy : d ≤ y) :
    kadiriTestFn f s y * exp (-z * (y : ℂ)) =
      (f 0 : ℂ) * exp (-(s + z) * (y : ℂ)) := by
  rw [kadiriTestFn_of_ge_d hd hf_supp s hy]
  rw [mul_assoc, ← Complex.exp_add]
  congr 1
  ring_nf

theorem hasDerivAt_kadiriTestFn_of_lt_zero {f : ℝ → ℝ} {s : ℂ} {y : ℝ}
    (hy : y < 0) :
    HasDerivAt (kadiriTestFn f s) 0 y := by
  have hEq : kadiriTestFn f s =ᶠ[nhds y] fun _ : ℝ ↦ (0 : ℂ) := by
    refine (Set.EqOn.eventuallyEq_of_mem ?_ (Iio_mem_nhds hy))
    intro x hx
    exact kadiriTestFn_of_lt_zero hx
  exact hEq.hasDerivAt_iff.mpr (hasDerivAt_const y (0 : ℂ))

theorem deriv_kadiriTestFn_of_lt_zero {f : ℝ → ℝ} {s : ℂ} {y : ℝ} (hy : y < 0) :
    deriv (kadiriTestFn f s) y = 0 :=
  (hasDerivAt_kadiriTestFn_of_lt_zero hy).deriv

theorem hasDerivAt_kadiriTestFn_of_pos {f : ℝ → ℝ} {s : ℂ} {y : ℝ}
    (hy : 0 < y) (hf : HasDerivAt f (deriv f y) y) :
    HasDerivAt (kadiriTestFn f s)
      ((-((deriv f y : ℝ) : ℂ)) * exp (-s * (y : ℂ)) +
        ((f 0 : ℂ) - (f y : ℂ)) * (-s * exp (-s * (y : ℂ)))) y := by
  have hEq : kadiriTestFn f s =ᶠ[nhds y]
      fun x : ℝ ↦ ((f 0 : ℂ) - (f x : ℂ)) * exp (-s * (x : ℂ)) := by
    refine (Set.EqOn.eventuallyEq_of_mem ?_ (Ioi_mem_nhds hy))
    intro x hx
    exact kadiriTestFn_of_nonneg hx.le
  have hfC : HasDerivAt (fun x : ℝ ↦ (f x : ℂ)) ((deriv f y : ℝ) : ℂ) y :=
    hf.ofReal_comp
  have hleft : HasDerivAt (fun x : ℝ ↦ (f 0 : ℂ) - (f x : ℂ))
      (-((deriv f y : ℝ) : ℂ)) y := by
    simpa using (hasDerivAt_const y (f 0 : ℂ)).sub hfC
  exact hEq.hasDerivAt_iff.mpr (hleft.mul (hasDerivAt_exp_neg_mul s y))

theorem deriv_kadiriTestFn_of_pos {f : ℝ → ℝ} {s : ℂ} {y : ℝ}
    (hy : 0 < y) (hf : HasDerivAt f (deriv f y) y) :
    deriv (kadiriTestFn f s) y =
      (-((deriv f y : ℝ) : ℂ)) * exp (-s * (y : ℂ)) +
        ((f 0 : ℂ) - (f y : ℂ)) * (-s * exp (-s * (y : ℂ))) :=
  (hasDerivAt_kadiriTestFn_of_pos hy hf).deriv

private lemma Icc_mem_nhds_of_mem_Ioo {d y : ℝ} (hy0 : 0 < y) (hyd : y < d) :
    Set.Icc (0 : ℝ) d ∈ nhds y := by
  rw [mem_nhds_iff]
  exact ⟨Set.Ioo (0 : ℝ) d, Set.Ioo_subset_Icc_self, isOpen_Ioo, ⟨hy0, hyd⟩⟩

theorem deriv_kadiriTestFn_of_pos_lt_d {d y : ℝ} {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d)) (s : ℂ) (hy0 : 0 < y) (hyd : y < d) :
    deriv (kadiriTestFn f s) y =
      (-((deriv f y : ℝ) : ℂ)) * exp (-s * (y : ℂ)) +
        ((f 0 : ℂ) - (f y : ℂ)) * (-s * exp (-s * (y : ℂ))) := by
  have hIcc : Set.Icc (0 : ℝ) d ∈ nhds y := Icc_mem_nhds_of_mem_Ioo hy0 hyd
  have hf_at : ContDiffAt ℝ 2 f y := hf_C2.contDiffAt hIcc
  exact deriv_kadiriTestFn_of_pos hy0
    (hf_at.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).hasDerivAt

theorem deriv_kadiriTestFn_of_pos_lt_d_derivWithin {d y : ℝ} {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d)) (s : ℂ) (hy0 : 0 < y) (hyd : y < d) :
    deriv (kadiriTestFn f s) y =
      (-((derivWithin f (Set.Icc 0 d) y : ℝ) : ℂ)) * exp (-s * (y : ℂ)) +
        ((f 0 : ℂ) - (f y : ℂ)) * (-s * exp (-s * (y : ℂ))) := by
  rw [deriv_kadiriTestFn_of_pos_lt_d hf_C2 s hy0 hyd]
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds_of_mem_Ioo hy0 hyd)]

theorem hasDerivAt_kadiriTestFn_of_gt_d {d y : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_supp : tsupport f ⊆ .Ico 0 d) (s : ℂ) (hy : d < y) :
    HasDerivAt (kadiriTestFn f s)
      ((f 0 : ℂ) * (-s * exp (-s * (y : ℂ)))) y := by
  have hEq : kadiriTestFn f s =ᶠ[nhds y]
      fun x : ℝ ↦ (f 0 : ℂ) * exp (-s * (x : ℂ)) := by
    refine (Set.EqOn.eventuallyEq_of_mem ?_ (Ioi_mem_nhds hy))
    intro x hx
    exact kadiriTestFn_of_ge_d hd hf_supp s hx.le
  have hTail := (hasDerivAt_exp_neg_mul s y).const_mul (f 0 : ℂ)
  exact hEq.hasDerivAt_iff.mpr hTail

theorem deriv_kadiriTestFn_of_gt_d {d y : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_supp : tsupport f ⊆ .Ico 0 d) (s : ℂ) (hy : d < y) :
    deriv (kadiriTestFn f s) y = (f 0 : ℂ) * (-s * exp (-s * (y : ℂ))) :=
  (hasDerivAt_kadiriTestFn_of_gt_d hd hf_supp s hy).deriv

theorem hasDerivAt_kadiriTestFn_of_pos_gt_d {d y : ℝ} {f : ℝ → ℝ}
    (hf_supp : tsupport f ⊆ .Ico 0 d) (s : ℂ) (hy0 : 0 < y) (hyd : d < y) :
    HasDerivAt (kadiriTestFn f s)
      ((f 0 : ℂ) * (-s * exp (-s * (y : ℂ)))) y := by
  have htail : max (0 : ℝ) d < y := max_lt hy0 hyd
  have hEq : kadiriTestFn f s =ᶠ[nhds y]
      fun x : ℝ ↦ (f 0 : ℂ) * exp (-s * (x : ℂ)) := by
    refine (Set.EqOn.eventuallyEq_of_mem ?_ (Ioi_mem_nhds htail))
    intro x hx
    have hx0 : 0 ≤ x := le_trans (le_max_left (0 : ℝ) d) hx.le
    have hxd : d ≤ x := le_trans (le_max_right (0 : ℝ) d) hx.le
    rw [kadiriTestFn_of_nonneg hx0, eq_zero_of_ge_d hf_supp hxd]
    simp
  have hTail := (hasDerivAt_exp_neg_mul s y).const_mul (f 0 : ℂ)
  exact hEq.hasDerivAt_iff.mpr hTail

theorem deriv_kadiriTestFn_of_pos_gt_d {d y : ℝ} {f : ℝ → ℝ}
    (hf_supp : tsupport f ⊆ .Ico 0 d) (s : ℂ) (hy0 : 0 < y) (hyd : d < y) :
    deriv (kadiriTestFn f s) y = (f 0 : ℂ) * (-s * exp (-s * (y : ℂ))) :=
  (hasDerivAt_kadiriTestFn_of_pos_gt_d hf_supp s hy0 hyd).deriv

theorem kadiriTestFn_mul_exp_half_of_lt_zero {f : ℝ → ℝ} {s : ℂ} {y : ℝ} (hy : y < 0) :
    kadiriTestFn f s y * exp ((y : ℂ) / 2) = 0 := by
  simp [kadiriTestFn_of_lt_zero hy]

theorem deriv_kadiriTestFn_mul_exp_half_of_lt_zero {f : ℝ → ℝ} {s : ℂ} {y : ℝ}
    (hy : y < 0) :
    deriv (kadiriTestFn f s) y * exp ((y : ℂ) / 2) = 0 := by
  simp [deriv_kadiriTestFn_of_lt_zero hy]

theorem kadiriTestFn_mul_exp_half_of_gt_d {d y : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_supp : tsupport f ⊆ .Ico 0 d) (s : ℂ) (hy : d < y) :
    kadiriTestFn f s y * exp ((y : ℂ) / 2) =
      (f 0 : ℂ) * exp (((1 / 2 : ℂ) - s) * (y : ℂ)) := by
  rw [kadiriTestFn_of_ge_d hd hf_supp s hy.le]
  rw [mul_assoc, ← Complex.exp_add]
  congr 1
  ring_nf

theorem deriv_kadiriTestFn_mul_exp_half_of_gt_d {d y : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_supp : tsupport f ⊆ .Ico 0 d) (s : ℂ) (hy : d < y) :
    deriv (kadiriTestFn f s) y * exp ((y : ℂ) / 2) =
      (f 0 : ℂ) * (-s) * exp (((1 / 2 : ℂ) - s) * (y : ℂ)) := by
  rw [deriv_kadiriTestFn_of_gt_d hd hf_supp s hy]
  rw [mul_assoc, mul_assoc, ← Complex.exp_add]
  ring_nf

private lemma Icc_mem_nhdsWithin_Ici_left {d : ℝ} (hd : 0 < d) :
    Set.Icc (0 : ℝ) d ∈ nhdsWithin (0 : ℝ) (Set.Ici 0) := by
  rw [mem_nhdsWithin]
  refine ⟨Set.Iio d, isOpen_Iio, hd, ?_⟩
  intro x hx
  exact ⟨hx.2, le_of_lt hx.1⟩

private lemma half_Icc_mem_nhdsWithin_Ici_left {d : ℝ} (hd : 0 < d) :
    Set.Icc (0 : ℝ) (d / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ici 0) := by
  rw [mem_nhdsWithin]
  refine ⟨Set.Iio (d / 2), isOpen_Iio, half_pos hd, ?_⟩
  intro x hx
  exact ⟨hx.2, le_of_lt hx.1⟩

private lemma Icc_mem_nhdsWithin_Iic_right {d : ℝ} (hd : 0 < d) :
    Set.Icc (0 : ℝ) d ∈ nhdsWithin d (Set.Iic d) := by
  rw [mem_nhdsWithin]
  refine ⟨Set.Ioi (0 : ℝ), isOpen_Ioi, hd, ?_⟩
  intro x hx
  exact ⟨hx.1.le, hx.2⟩

private lemma half_Icc_mem_nhdsWithin_Iic_right {d : ℝ} (hd : 0 < d) :
    Set.Icc (d / 2) d ∈ nhdsWithin d (Set.Iic d) := by
  rw [mem_nhdsWithin]
  refine ⟨Set.Ioi (d / 2), isOpen_Ioi, half_lt_self hd, ?_⟩
  intro x hx
  exact ⟨hx.1.le, hx.2⟩

private lemma ofReal_contDiffAt {n : WithTop ℕ∞} {f : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun y : ℝ ↦ (f y : ℂ)) x := by
  simpa [Function.comp_def] using (Complex.ofRealCLM.contDiff.comp_contDiffAt x hf)

private lemma toSpanSingleton_sub (z w : ℂ) :
    ContinuousLinearMap.toSpanSingleton ℝ z - ContinuousLinearMap.toSpanSingleton ℝ w =
      ContinuousLinearMap.toSpanSingleton ℝ (z - w) := by
  ext
  simp [ContinuousLinearMap.toSpanSingleton_apply]

private lemma continuous_toSpanSingleton_complex :
    Continuous (fun z : ℂ => ContinuousLinearMap.toSpanSingleton ℝ z) := by
  rw [Metric.continuous_iff]
  intro z ε hε
  refine ⟨ε, hε, ?_⟩
  intro w hw
  rw [dist_eq_norm, toSpanSingleton_sub, ContinuousLinearMap.norm_toSpanSingleton]
  simpa [dist_eq_norm] using hw

private lemma continuousAt_toSpanSingleton_deriv {φ : ℝ → ℂ} {x : ℝ}
    (hφ : ContinuousAt (deriv φ) x) :
    ContinuousAt (fun y : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (deriv φ y)) x :=
  continuous_toSpanSingleton_complex.continuousAt.comp hφ

private lemma exp_neg_mul_contDiffAt {s : ℂ} {x : ℝ} :
    ContDiffAt ℝ 1 (fun y : ℝ ↦ exp (-s * (y : ℂ))) x := by
  have hid : ContDiffAt ℝ 1 (fun y : ℝ ↦ (y : ℂ)) x :=
    ofReal_contDiffAt (f := fun y : ℝ => y) contDiff_id.contDiffAt
  have hmul : ContDiffAt ℝ 1 (fun y : ℝ ↦ s * (y : ℂ)) x := by
    simpa using (contDiffAt_const.mul hid)
  have hlin : ContDiffAt ℝ 1 (fun y : ℝ ↦ -(s * (y : ℂ))) x := hmul.neg
  simpa [neg_mul] using hlin.cexp

private lemma contDiffAt_kadiriTestFn_model {f : ℝ → ℝ} {s : ℂ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) :
    ContDiffAt ℝ 1
      (fun y : ℝ ↦ ((f 0 : ℂ) - (f y : ℂ)) * exp (-s * (y : ℂ))) x := by
  have hf1 : ContDiffAt ℝ 1 f x := hf.of_le (by norm_num)
  have hfC : ContDiffAt ℝ 1 (fun y : ℝ ↦ (f y : ℂ)) x := ofReal_contDiffAt hf1
  have hsub : ContDiffAt ℝ 1 (fun y : ℝ ↦ (f 0 : ℂ) - (f y : ℂ)) x := by
    simpa using (contDiffAt_const.sub hfC)
  exact hsub.mul exp_neg_mul_contDiffAt

private lemma contDiffAt_kadiriTestFn_tail {f : ℝ → ℝ} {s : ℂ} {x : ℝ} :
    ContDiffAt ℝ 1 (fun y : ℝ ↦ (f 0 : ℂ) * exp (-s * (y : ℂ))) x :=
  contDiffAt_const.mul exp_neg_mul_contDiffAt

theorem contDiffAt_kadiriTestFn_of_lt_zero {f : ℝ → ℝ} {s : ℂ} {x : ℝ} (hx : x < 0) :
    ContDiffAt ℝ 1 (kadiriTestFn f s) x := by
  have hEq : kadiriTestFn f s =ᶠ[nhds x] fun _ : ℝ ↦ (0 : ℂ) := by
    refine (Set.EqOn.eventuallyEq_of_mem ?_ (Iio_mem_nhds hx))
    intro y hy
    exact kadiriTestFn_of_lt_zero hy
  exact contDiffAt_const.congr_of_eventuallyEq hEq

theorem contDiffAt_kadiriTestFn_of_pos_lt_d {d x : ℝ} {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d)) (s : ℂ) (hx0 : 0 < x) (hxd : x < d) :
    ContDiffAt ℝ 1 (kadiriTestFn f s) x := by
  have hIcc : Set.Icc (0 : ℝ) d ∈ nhds x := by
    rw [mem_nhds_iff]
    refine ⟨Set.Ioo (0 : ℝ) d, Set.Ioo_subset_Icc_self, isOpen_Ioo, ⟨hx0, hxd⟩⟩
  have hf_at : ContDiffAt ℝ 2 f x := hf_C2.contDiffAt hIcc
  have hmodel := contDiffAt_kadiriTestFn_model (f := f) (s := s) hf_at
  have hEq : kadiriTestFn f s =ᶠ[nhds x]
      fun y : ℝ ↦ ((f 0 : ℂ) - (f y : ℂ)) * exp (-s * (y : ℂ)) := by
    refine (Set.EqOn.eventuallyEq_of_mem ?_ (Ioi_mem_nhds hx0))
    intro y hy
    exact kadiriTestFn_of_nonneg hy.le
  exact hmodel.congr_of_eventuallyEq hEq

theorem contDiffAt_kadiriTestFn_of_gt_d {d x : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_supp : tsupport f ⊆ Set.Ico 0 d) (s : ℂ) (hxd : d < x) :
    ContDiffAt ℝ 1 (kadiriTestFn f s) x := by
  have hmodel := contDiffAt_kadiriTestFn_tail (f := f) (s := s) (x := x)
  have hEq : kadiriTestFn f s =ᶠ[nhds x] fun y : ℝ ↦ (f 0 : ℂ) * exp (-s * (y : ℂ)) := by
    refine (Set.EqOn.eventuallyEq_of_mem ?_ (Ioi_mem_nhds hxd))
    intro y hy
    exact kadiriTestFn_of_ge_d hd hf_supp s hy.le
  exact hmodel.congr_of_eventuallyEq hEq

private lemma continuousWithinAt_kadiriTestFn_compact {d x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) d)
    {f : ℝ → ℝ} (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d)) (s : ℂ) :
    ContinuousWithinAt
      (fun y : ℝ ↦ ((f 0 : ℂ) - (f y : ℂ)) * exp (-s * (y : ℂ)))
      (Set.Icc 0 d) x := by
  have hfc : ContinuousWithinAt f (Set.Icc (0 : ℝ) d) x :=
    hf_C2.continuousOn.continuousWithinAt hx
  have hfcC : ContinuousWithinAt (fun y : ℝ ↦ (f y : ℂ)) (Set.Icc (0 : ℝ) d) x := by
    exact (Complex.continuous_ofReal.tendsto (f x)).comp hfc.tendsto
  have hkernel : ContinuousWithinAt (fun y : ℝ ↦ exp (-s * (y : ℂ)))
      (Set.Icc (0 : ℝ) d) x := by
    fun_prop
  exact ((continuousWithinAt_const.sub hfcC).mul hkernel)

theorem kadiriTestFn_continuousAt_zero {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d)) (s : ℂ) :
    ContinuousAt (kadiriTestFn f s) 0 := by
  have hleft : ContinuousWithinAt (kadiriTestFn f s) (Set.Iic (0 : ℝ)) 0 := by
    refine ContinuousWithinAt.congr
      (show ContinuousWithinAt (fun _ : ℝ => (0 : ℂ)) (Set.Iic (0 : ℝ)) 0 from
        continuousWithinAt_const) ?_ ?_
    · intro y hy
      rw [Set.mem_Iic] at hy
      rcases lt_or_eq_of_le hy with hylt | rfl
      · exact kadiriTestFn_of_lt_zero hylt
      · simp [kadiriTestFn]
    · simp [kadiriTestFn]
  have hright_fun : ContinuousWithinAt
      (fun y : ℝ ↦ ((f 0 : ℂ) - (f y : ℂ)) * exp (-s * (y : ℂ)))
      (Set.Ici (0 : ℝ)) 0 := by
    have hcontIcc :
        ContinuousWithinAt
          (fun y : ℝ ↦ ((f 0 : ℂ) - (f y : ℂ)) * exp (-s * (y : ℂ)))
          (Set.Icc (0 : ℝ) d) 0 :=
      continuousWithinAt_kadiriTestFn_compact ⟨le_rfl, hd.le⟩ hf_C2 s
    rw [ContinuousWithinAt] at hcontIcc ⊢
    exact hcontIcc.mono_left (by
      rw [nhdsWithin_le_iff]
      exact Icc_mem_nhdsWithin_Ici_left hd)
  have hright : ContinuousWithinAt (kadiriTestFn f s) (Set.Ici (0 : ℝ)) 0 := by
    refine ContinuousWithinAt.congr hright_fun ?_ ?_
    · intro y hy
      exact kadiriTestFn_of_nonneg hy
    · simp [kadiriTestFn]
  have hU : ContinuousWithinAt (kadiriTestFn f s) (Set.Iic (0 : ℝ) ∪ Set.Ici 0) 0 :=
    hleft.union hright
  rw [Set.Iic_union_Ici] at hU
  exact hU.continuousAt (by simp)

theorem kadiriTestFn_continuousAt_d {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d)) (hf_supp : tsupport f ⊆ Set.Ico 0 d)
    (hf_d : f d = 0) (s : ℂ) :
    ContinuousAt (kadiriTestFn f s) d := by
  let hfun : ℝ → ℂ := fun y ↦ ((f 0 : ℂ) - (f y : ℂ)) * exp (-s * (y : ℂ))
  have hleft_h : ContinuousWithinAt hfun (Set.Iic d) d := by
    have hcontIcc : ContinuousWithinAt hfun (Set.Icc (0 : ℝ) d) d :=
      continuousWithinAt_kadiriTestFn_compact ⟨hd.le, le_rfl⟩ hf_C2 s
    rw [ContinuousWithinAt] at hcontIcc ⊢
    exact hcontIcc.mono_left (by
      rw [nhdsWithin_le_iff]
      exact Icc_mem_nhdsWithin_Iic_right hd)
  have hleft : ContinuousWithinAt (kadiriTestFn f s) (Set.Iic d) d := by
    refine ContinuousWithinAt.congr_of_eventuallyEq hleft_h ?_ ?_
    · refine (Set.EqOn.eventuallyEq_of_mem ?_ (Icc_mem_nhdsWithin_Iic_right hd))
      intro y hy
      exact kadiriTestFn_of_nonneg hy.1
    · dsimp [hfun]
      rw [kadiriTestFn_of_nonneg hd.le, hf_d]
  have hright_h : ContinuousWithinAt (fun y : ℝ ↦ (f 0 : ℂ) * exp (-s * (y : ℂ)))
      (Set.Ici d) d := by
    fun_prop
  have hright : ContinuousWithinAt (kadiriTestFn f s) (Set.Ici d) d := by
    refine ContinuousWithinAt.congr hright_h ?_ ?_
    · intro y hy
      exact kadiriTestFn_of_ge_d hd hf_supp s hy
    · rw [kadiriTestFn_of_ge_d hd hf_supp s le_rfl]
  have hU : ContinuousWithinAt (kadiriTestFn f s) (Set.Iic d ∪ Set.Ici d) d :=
    hleft.union hright
  rw [Set.Iic_union_Ici] at hU
  exact hU.continuousAt (by simp)

theorem hasDerivAt_kadiriTestFn_zero {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_derivWithin_0 : derivWithin f (Set.Icc 0 d) 0 = 0) (s : ℂ) :
    HasDerivAt (kadiriTestFn f s) 0 0 := by
  let hfun : ℝ → ℂ := fun y ↦ ((f 0 : ℂ) - (f y : ℂ)) * exp (-s * (y : ℂ))
  have hleft : HasDerivWithinAt (kadiriTestFn f s) 0 (Set.Iic (0 : ℝ)) 0 := by
    refine HasDerivWithinAt.congr
      (hasDerivWithinAt_const (0 : ℝ) (Set.Iic (0 : ℝ)) (0 : ℂ)) ?_ ?_
    · intro y hy
      rw [Set.mem_Iic] at hy
      rcases lt_or_eq_of_le hy with hylt | rfl
      · exact kadiriTestFn_of_lt_zero hylt
      · simp [kadiriTestFn]
    · simp [kadiriTestFn]
  have hright_h_Icc : HasDerivWithinAt hfun 0 (Set.Icc (0 : ℝ) d) 0 := by
    have hdiff : DifferentiableWithinAt ℝ f (Set.Icc (0 : ℝ) d) 0 :=
      (hf_C2.differentiableOn (by norm_num : (2 : WithTop ℕ∞) ≠ 0)) 0
        ⟨le_rfl, hd.le⟩
    have hfderiv : HasDerivWithinAt f 0 (Set.Icc (0 : ℝ) d) 0 := by
      simpa [hf_derivWithin_0] using hdiff.hasDerivWithinAt
    have hfC : HasDerivWithinAt (fun y : ℝ ↦ (f y : ℂ)) 0 (Set.Icc (0 : ℝ) d) 0 := by
      simpa using hfderiv.ofReal_comp
    have hsub : HasDerivWithinAt (fun y : ℝ ↦ (f 0 : ℂ) - (f y : ℂ)) 0
        (Set.Icc (0 : ℝ) d) 0 := by
      simpa using hfC.const_sub (f 0 : ℂ)
    have hkernel : HasDerivWithinAt (fun y : ℝ ↦ exp (-s * (y : ℂ)))
        (-s * exp (-s * (0 : ℂ))) (Set.Icc (0 : ℝ) d) 0 :=
      (Complex.hasDerivAt_exp_neg_mul s 0).hasDerivWithinAt
    have hmul := hsub.mul hkernel
    dsimp [hfun] at hmul ⊢
    simpa using hmul
  have hright_h : HasDerivWithinAt hfun 0 (Set.Ici (0 : ℝ)) 0 := by
    rw [HasDerivWithinAt] at hright_h_Icc ⊢
    exact hright_h_Icc.mono (Filter.prod_mono (by
      rw [nhdsWithin_le_iff]
      exact Icc_mem_nhdsWithin_Ici_left hd) le_rfl)
  have hright : HasDerivWithinAt (kadiriTestFn f s) 0 (Set.Ici (0 : ℝ)) 0 := by
    refine HasDerivWithinAt.congr hright_h ?_ ?_
    · intro y hy
      exact kadiriTestFn_of_nonneg hy
    · simp [kadiriTestFn, hfun]
  have hU : HasDerivWithinAt (kadiriTestFn f s) 0 (Set.Iic (0 : ℝ) ∪ Set.Ici 0) 0 :=
    hleft.union hright
  rw [Set.Iic_union_Ici] at hU
  exact hU.hasDerivAt (by simp)

theorem deriv_kadiriTestFn_zero {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_derivWithin_0 : derivWithin f (Set.Icc 0 d) 0 = 0) (s : ℂ) :
    deriv (kadiriTestFn f s) 0 = 0 :=
  (hasDerivAt_kadiriTestFn_zero hd hf_C2 hf_derivWithin_0 s).deriv

theorem hasDerivAt_kadiriTestFn_d {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d)) (hf_supp : tsupport f ⊆ Set.Ico 0 d)
    (hf_d : f d = 0) (hf_derivWithin_d : derivWithin f (Set.Icc 0 d) d = 0) (s : ℂ) :
    HasDerivAt (kadiriTestFn f s) ((f 0 : ℂ) * (-s * exp (-s * (d : ℂ)))) d := by
  let hfun : ℝ → ℂ := fun y ↦ ((f 0 : ℂ) - (f y : ℂ)) * exp (-s * (y : ℂ))
  let hderiv : ℂ := (f 0 : ℂ) * (-s * exp (-s * (d : ℂ)))
  have hleft_h_Icc : HasDerivWithinAt hfun hderiv (Set.Icc (0 : ℝ) d) d := by
    have hdiff : DifferentiableWithinAt ℝ f (Set.Icc (0 : ℝ) d) d :=
      (hf_C2.differentiableOn (by norm_num : (2 : WithTop ℕ∞) ≠ 0)) d
        ⟨hd.le, le_rfl⟩
    have hfderiv : HasDerivWithinAt f 0 (Set.Icc (0 : ℝ) d) d := by
      simpa [hf_derivWithin_d] using hdiff.hasDerivWithinAt
    have hfC : HasDerivWithinAt (fun y : ℝ ↦ (f y : ℂ)) 0 (Set.Icc (0 : ℝ) d) d := by
      simpa using hfderiv.ofReal_comp
    have hsub : HasDerivWithinAt (fun y : ℝ ↦ (f 0 : ℂ) - (f y : ℂ)) 0
        (Set.Icc (0 : ℝ) d) d := by
      simpa using hfC.const_sub (f 0 : ℂ)
    have hkernel : HasDerivWithinAt (fun y : ℝ ↦ exp (-s * (y : ℂ)))
        (-s * exp (-s * (d : ℂ))) (Set.Icc (0 : ℝ) d) d :=
      (Complex.hasDerivAt_exp_neg_mul s d).hasDerivWithinAt
    have hmul := hsub.mul hkernel
    dsimp [hfun, hderiv] at hmul ⊢
    simpa [hf_d] using hmul
  have hleft_h : HasDerivWithinAt hfun hderiv (Set.Iic d) d := by
    rw [HasDerivWithinAt] at hleft_h_Icc ⊢
    exact hleft_h_Icc.mono (Filter.prod_mono (by
      rw [nhdsWithin_le_iff]
      exact Icc_mem_nhdsWithin_Iic_right hd) le_rfl)
  have hleft : HasDerivWithinAt (kadiriTestFn f s) hderiv (Set.Iic d) d := by
    refine HasDerivWithinAt.congr_of_eventuallyEq hleft_h ?_ ?_
    · refine (Set.EqOn.eventuallyEq_of_mem ?_ (Icc_mem_nhdsWithin_Iic_right hd))
      intro y hy
      exact kadiriTestFn_of_nonneg hy.1
    · dsimp [hfun]
      rw [kadiriTestFn_of_nonneg hd.le, hf_d]
  have hright_h : HasDerivWithinAt (fun y : ℝ ↦ (f 0 : ℂ) * exp (-s * (y : ℂ))) hderiv
      (Set.Ici d) d := by
    dsimp [hderiv]
    simpa using ((Complex.hasDerivAt_exp_neg_mul s d).const_mul (f 0 : ℂ)).hasDerivWithinAt
  have hright : HasDerivWithinAt (kadiriTestFn f s) hderiv (Set.Ici d) d := by
    refine HasDerivWithinAt.congr hright_h ?_ ?_
    · intro y hy
      exact kadiriTestFn_of_ge_d hd hf_supp s hy
    · rw [kadiriTestFn_of_ge_d hd hf_supp s le_rfl]
  have hU : HasDerivWithinAt (kadiriTestFn f s) hderiv (Set.Iic d ∪ Set.Ici d) d :=
    hleft.union hright
  rw [Set.Iic_union_Ici] at hU
  simpa [hderiv] using hU.hasDerivAt (by simp)

theorem deriv_kadiriTestFn_d {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d)) (hf_supp : tsupport f ⊆ Set.Ico 0 d)
    (hf_d : f d = 0) (hf_derivWithin_d : derivWithin f (Set.Icc 0 d) d = 0) (s : ℂ) :
    deriv (kadiriTestFn f s) d = (f 0 : ℂ) * (-s * exp (-s * (d : ℂ))) :=
  (hasDerivAt_kadiriTestFn_d hd hf_C2 hf_supp hf_d hf_derivWithin_d s).deriv

private lemma continuousWithinAt_kadiriTestFn_deriv_model_zero {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d)) (s : ℂ) :
    ContinuousWithinAt
      (fun y : ℝ ↦
        (-((derivWithin f (Set.Icc 0 d) y : ℝ) : ℂ)) * exp (-s * (y : ℂ)) +
          ((f 0 : ℂ) - (f y : ℂ)) * (-s * exp (-s * (y : ℂ))))
      (Set.Icc (0 : ℝ) d) 0 := by
  have hUD : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) d) := uniqueDiffOn_Icc hd
  have hg_contOn : ContinuousOn (derivWithin f (Set.Icc (0 : ℝ) d))
      (Set.Icc (0 : ℝ) d) := by
    have hcd : ContDiffOn ℝ 0 (derivWithin f (Set.Icc (0 : ℝ) d))
        (Set.Icc (0 : ℝ) d) :=
      hf_C2.derivWithin hUD (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 2)
    exact hcd.continuousOn
  have hg : ContinuousWithinAt (derivWithin f (Set.Icc (0 : ℝ) d))
      (Set.Icc (0 : ℝ) d) 0 :=
    hg_contOn.continuousWithinAt ⟨le_rfl, hd.le⟩
  have hgC : ContinuousWithinAt
      (fun y : ℝ ↦ ((derivWithin f (Set.Icc (0 : ℝ) d) y : ℝ) : ℂ))
      (Set.Icc (0 : ℝ) d) 0 := by
    exact (Complex.continuous_ofReal.tendsto (derivWithin f (Set.Icc (0 : ℝ) d) 0)).comp
      hg.tendsto
  have hf_cont : ContinuousWithinAt f (Set.Icc (0 : ℝ) d) 0 :=
    hf_C2.continuousOn.continuousWithinAt ⟨le_rfl, hd.le⟩
  have hfC : ContinuousWithinAt (fun y : ℝ ↦ (f y : ℂ)) (Set.Icc (0 : ℝ) d) 0 := by
    exact (Complex.continuous_ofReal.tendsto (f 0)).comp hf_cont.tendsto
  have hkernel : ContinuousWithinAt (fun y : ℝ ↦ exp (-s * (y : ℂ)))
      (Set.Icc (0 : ℝ) d) 0 := by
    fun_prop
  have hkernel' : ContinuousWithinAt (fun y : ℝ ↦ -s * exp (-s * (y : ℂ)))
      (Set.Icc (0 : ℝ) d) 0 :=
    continuousWithinAt_const.mul hkernel
  have hleft : ContinuousWithinAt
      (fun y : ℝ ↦ (-((derivWithin f (Set.Icc 0 d) y : ℝ) : ℂ)) *
        exp (-s * (y : ℂ)))
      (Set.Icc (0 : ℝ) d) 0 :=
    hgC.neg.mul hkernel
  have hright : ContinuousWithinAt
      (fun y : ℝ ↦ ((f 0 : ℂ) - (f y : ℂ)) * (-s * exp (-s * (y : ℂ))))
      (Set.Icc (0 : ℝ) d) 0 :=
    (continuousWithinAt_const.sub hfC).mul hkernel'
  exact hleft.add hright

theorem continuousAt_deriv_kadiriTestFn_zero {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_derivWithin_0 : derivWithin f (Set.Icc 0 d) 0 = 0) (s : ℂ) :
    ContinuousAt (deriv (kadiriTestFn f s)) 0 := by
  let model : ℝ → ℂ := fun y ↦
    (-((derivWithin f (Set.Icc 0 d) y : ℝ) : ℂ)) * exp (-s * (y : ℂ)) +
      ((f 0 : ℂ) - (f y : ℂ)) * (-s * exp (-s * (y : ℂ)))
  have hleft : ContinuousWithinAt (deriv (kadiriTestFn f s)) (Set.Iic (0 : ℝ)) 0 := by
    refine ContinuousWithinAt.congr
      (show ContinuousWithinAt (fun _ : ℝ => (0 : ℂ)) (Set.Iic (0 : ℝ)) 0 from
        continuousWithinAt_const) ?_ ?_
    · intro y hy
      rw [Set.mem_Iic] at hy
      rcases lt_or_eq_of_le hy with hylt | rfl
      · exact deriv_kadiriTestFn_of_lt_zero hylt
      · exact deriv_kadiriTestFn_zero hd hf_C2 hf_derivWithin_0 s
    · exact deriv_kadiriTestFn_zero hd hf_C2 hf_derivWithin_0 s
  have hright_model_Icc := continuousWithinAt_kadiriTestFn_deriv_model_zero hd hf_C2 s
  have hright_model : ContinuousWithinAt model (Set.Ici (0 : ℝ)) 0 := by
    rw [ContinuousWithinAt] at hright_model_Icc ⊢
    exact hright_model_Icc.mono_left (by
      rw [nhdsWithin_le_iff]
      exact Icc_mem_nhdsWithin_Ici_left hd)
  have hright : ContinuousWithinAt (deriv (kadiriTestFn f s)) (Set.Ici (0 : ℝ)) 0 := by
    refine ContinuousWithinAt.congr_of_eventuallyEq hright_model ?_ ?_
    · refine (Set.EqOn.eventuallyEq_of_mem ?_ (half_Icc_mem_nhdsWithin_Ici_left hd))
      intro y hy
      rw [Set.mem_Icc] at hy
      rcases lt_or_eq_of_le hy.1 with hypos | rfl
      · have hyd : y < d := by linarith
        dsimp [model]
        exact deriv_kadiriTestFn_of_pos_lt_d_derivWithin hf_C2 s hypos hyd
      · dsimp [model]
        rw [deriv_kadiriTestFn_zero hd hf_C2 hf_derivWithin_0 s, hf_derivWithin_0]
        simp
    · dsimp [model]
      rw [deriv_kadiriTestFn_zero hd hf_C2 hf_derivWithin_0 s, hf_derivWithin_0]
      simp
  have hU : ContinuousWithinAt (deriv (kadiriTestFn f s))
      (Set.Iic (0 : ℝ) ∪ Set.Ici 0) 0 :=
    hleft.union hright
  rw [Set.Iic_union_Ici] at hU
  exact hU.continuousAt (by simp)

private lemma continuousWithinAt_kadiriTestFn_deriv_model_d {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d)) (s : ℂ) :
    ContinuousWithinAt
      (fun y : ℝ ↦
        (-((derivWithin f (Set.Icc 0 d) y : ℝ) : ℂ)) * exp (-s * (y : ℂ)) +
          ((f 0 : ℂ) - (f y : ℂ)) * (-s * exp (-s * (y : ℂ))))
      (Set.Icc (0 : ℝ) d) d := by
  have hUD : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) d) := uniqueDiffOn_Icc hd
  have hg_contOn : ContinuousOn (derivWithin f (Set.Icc (0 : ℝ) d))
      (Set.Icc (0 : ℝ) d) := by
    have hcd : ContDiffOn ℝ 0 (derivWithin f (Set.Icc (0 : ℝ) d))
        (Set.Icc (0 : ℝ) d) :=
      hf_C2.derivWithin hUD (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 2)
    exact hcd.continuousOn
  have hg : ContinuousWithinAt (derivWithin f (Set.Icc (0 : ℝ) d))
      (Set.Icc (0 : ℝ) d) d :=
    hg_contOn.continuousWithinAt ⟨hd.le, le_rfl⟩
  have hgC : ContinuousWithinAt
      (fun y : ℝ ↦ ((derivWithin f (Set.Icc (0 : ℝ) d) y : ℝ) : ℂ))
      (Set.Icc (0 : ℝ) d) d := by
    exact (Complex.continuous_ofReal.tendsto (derivWithin f (Set.Icc (0 : ℝ) d) d)).comp
      hg.tendsto
  have hf_cont : ContinuousWithinAt f (Set.Icc (0 : ℝ) d) d :=
    hf_C2.continuousOn.continuousWithinAt ⟨hd.le, le_rfl⟩
  have hfC : ContinuousWithinAt (fun y : ℝ ↦ (f y : ℂ)) (Set.Icc (0 : ℝ) d) d := by
    exact (Complex.continuous_ofReal.tendsto (f d)).comp hf_cont.tendsto
  have hkernel : ContinuousWithinAt (fun y : ℝ ↦ exp (-s * (y : ℂ)))
      (Set.Icc (0 : ℝ) d) d := by
    fun_prop
  have hkernel' : ContinuousWithinAt (fun y : ℝ ↦ -s * exp (-s * (y : ℂ)))
      (Set.Icc (0 : ℝ) d) d :=
    continuousWithinAt_const.mul hkernel
  have hleft : ContinuousWithinAt
      (fun y : ℝ ↦ (-((derivWithin f (Set.Icc 0 d) y : ℝ) : ℂ)) *
        exp (-s * (y : ℂ)))
      (Set.Icc (0 : ℝ) d) d :=
    hgC.neg.mul hkernel
  have hright : ContinuousWithinAt
      (fun y : ℝ ↦ ((f 0 : ℂ) - (f y : ℂ)) * (-s * exp (-s * (y : ℂ))))
      (Set.Icc (0 : ℝ) d) d :=
    (continuousWithinAt_const.sub hfC).mul hkernel'
  exact hleft.add hright

theorem continuousAt_deriv_kadiriTestFn_d {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d)) (hf_supp : tsupport f ⊆ Set.Ico 0 d)
    (hf_d : f d = 0) (hf_derivWithin_d : derivWithin f (Set.Icc 0 d) d = 0) (s : ℂ) :
    ContinuousAt (deriv (kadiriTestFn f s)) d := by
  let model : ℝ → ℂ := fun y ↦
    (-((derivWithin f (Set.Icc 0 d) y : ℝ) : ℂ)) * exp (-s * (y : ℂ)) +
      ((f 0 : ℂ) - (f y : ℂ)) * (-s * exp (-s * (y : ℂ)))
  let tail : ℝ → ℂ := fun y ↦ (f 0 : ℂ) * (-s * exp (-s * (y : ℂ)))
  have hleft_model_Icc := continuousWithinAt_kadiriTestFn_deriv_model_d hd hf_C2 s
  have hleft_model : ContinuousWithinAt model (Set.Iic d) d := by
    rw [ContinuousWithinAt] at hleft_model_Icc ⊢
    exact hleft_model_Icc.mono_left (by
      rw [nhdsWithin_le_iff]
      exact Icc_mem_nhdsWithin_Iic_right hd)
  have hleft : ContinuousWithinAt (deriv (kadiriTestFn f s)) (Set.Iic d) d := by
    refine ContinuousWithinAt.congr_of_eventuallyEq hleft_model ?_ ?_
    · refine (Set.EqOn.eventuallyEq_of_mem ?_ (half_Icc_mem_nhdsWithin_Iic_right hd))
      intro y hy
      rw [Set.mem_Icc] at hy
      rcases lt_or_eq_of_le hy.2 with hylt | rfl
      · have hypos : 0 < y := by nlinarith [hd, hy.1]
        dsimp [model]
        exact deriv_kadiriTestFn_of_pos_lt_d_derivWithin hf_C2 s hypos hylt
      · dsimp [model]
        rw [deriv_kadiriTestFn_d hd hf_C2 hf_supp hf_d hf_derivWithin_d s,
          hf_derivWithin_d, hf_d]
        simp
    · dsimp [model]
      rw [deriv_kadiriTestFn_d hd hf_C2 hf_supp hf_d hf_derivWithin_d s,
        hf_derivWithin_d, hf_d]
      simp
  have hright_tail : ContinuousWithinAt tail (Set.Ici d) d := by
    dsimp [tail]
    fun_prop
  have hright : ContinuousWithinAt (deriv (kadiriTestFn f s)) (Set.Ici d) d := by
    refine ContinuousWithinAt.congr hright_tail ?_ ?_
    · intro y hy
      rw [Set.mem_Ici] at hy
      rcases lt_or_eq_of_le hy with hylt | rfl
      · dsimp [tail]
        rw [deriv_kadiriTestFn_of_gt_d hd hf_supp s hylt]
      · dsimp [tail]
        rw [deriv_kadiriTestFn_d hd hf_C2 hf_supp hf_d hf_derivWithin_d s]
    · dsimp [tail]
      rw [deriv_kadiriTestFn_d hd hf_C2 hf_supp hf_d hf_derivWithin_d s]
  have hU : ContinuousWithinAt (deriv (kadiriTestFn f s)) (Set.Iic d ∪ Set.Ici d) d :=
    hleft.union hright
  rw [Set.Iic_union_Ici] at hU
  exact hU.continuousAt (by simp)

private lemma continuousAt_deriv_kadiriTestFn_of_lt_zero {f : ℝ → ℝ} {s : ℂ} {x : ℝ}
    (hx : x < 0) : ContinuousAt (deriv (kadiriTestFn f s)) x := by
  have hEq : deriv (kadiriTestFn f s) =ᶠ[nhds x] fun _ : ℝ ↦ (0 : ℂ) := by
    refine (Set.EqOn.eventuallyEq_of_mem ?_ (Iio_mem_nhds hx))
    intro y hy
    exact deriv_kadiriTestFn_of_lt_zero hy
  exact continuousAt_const.congr_of_eventuallyEq hEq

private lemma continuousAt_deriv_kadiriTestFn_of_pos_lt_d {d x : ℝ} {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d)) (s : ℂ) (hx0 : 0 < x) (hxd : x < d) :
    ContinuousAt (deriv (kadiriTestFn f s)) x := by
  let model : ℝ → ℂ := fun y ↦
    (-((derivWithin f (Set.Icc 0 d) y : ℝ) : ℂ)) * exp (-s * (y : ℂ)) +
      ((f 0 : ℂ) - (f y : ℂ)) * (-s * exp (-s * (y : ℂ)))
  have hd : 0 < d := lt_trans hx0 hxd
  have hUD : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) d) := uniqueDiffOn_Icc hd
  have hg_contOn : ContinuousOn (derivWithin f (Set.Icc (0 : ℝ) d))
      (Set.Icc (0 : ℝ) d) := by
    have hcd : ContDiffOn ℝ 0 (derivWithin f (Set.Icc (0 : ℝ) d))
        (Set.Icc (0 : ℝ) d) :=
      hf_C2.derivWithin hUD (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 2)
    exact hcd.continuousOn
  have hg : ContinuousAt (derivWithin f (Set.Icc (0 : ℝ) d)) x :=
    (hg_contOn.continuousWithinAt ⟨hx0.le, hxd.le⟩).continuousAt
      (Icc_mem_nhds_of_mem_Ioo hx0 hxd)
  have hgC : ContinuousAt
      (fun y : ℝ ↦ ((derivWithin f (Set.Icc (0 : ℝ) d) y : ℝ) : ℂ)) x := by
    exact (Complex.continuous_ofReal.tendsto (derivWithin f (Set.Icc (0 : ℝ) d) x)).comp
      hg.tendsto
  have hf_at : ContDiffAt ℝ 2 f x := hf_C2.contDiffAt (Icc_mem_nhds_of_mem_Ioo hx0 hxd)
  have hf_cont : ContinuousAt f x := hf_at.continuousAt
  have hfC : ContinuousAt (fun y : ℝ ↦ (f y : ℂ)) x := by
    exact (Complex.continuous_ofReal.tendsto (f x)).comp hf_cont.tendsto
  have hkernel : ContinuousAt (fun y : ℝ ↦ exp (-s * (y : ℂ))) x := by
    fun_prop
  have hkernel' : ContinuousAt (fun y : ℝ ↦ -s * exp (-s * (y : ℂ))) x :=
    continuousAt_const.mul hkernel
  have hmodel : ContinuousAt model x := by
    dsimp [model]
    exact (hgC.neg.mul hkernel).add ((continuousAt_const.sub hfC).mul hkernel')
  have hEq : deriv (kadiriTestFn f s) =ᶠ[nhds x] model := by
    refine (Set.EqOn.eventuallyEq_of_mem ?_ (Ioo_mem_nhds hx0 hxd))
    intro y hy
    dsimp [model]
    exact deriv_kadiriTestFn_of_pos_lt_d_derivWithin hf_C2 s hy.1 hy.2
  exact hmodel.congr_of_eventuallyEq hEq

private lemma continuousAt_deriv_kadiriTestFn_of_gt_d {d x : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_supp : tsupport f ⊆ Set.Ico 0 d) (s : ℂ) (hxd : d < x) :
    ContinuousAt (deriv (kadiriTestFn f s)) x := by
  let tail : ℝ → ℂ := fun y ↦ (f 0 : ℂ) * (-s * exp (-s * (y : ℂ)))
  have htail : ContinuousAt tail x := by
    dsimp [tail]
    fun_prop
  have hEq : deriv (kadiriTestFn f s) =ᶠ[nhds x] tail := by
    refine (Set.EqOn.eventuallyEq_of_mem ?_ (Ioi_mem_nhds hxd))
    intro y hy
    dsimp [tail]
    rw [deriv_kadiriTestFn_of_gt_d hd hf_supp s hy]
  exact htail.congr_of_eventuallyEq hEq

theorem contDiffAt_kadiriTestFn_zero {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_derivWithin_0 : derivWithin f (Set.Icc 0 d) 0 = 0) (s : ℂ) :
    ContDiffAt ℝ 1 (kadiriTestFn f s) 0 := by
  rw [contDiffAt_one_iff]
  let φ := kadiriTestFn f s
  let f' : ℝ → ℝ →L[ℝ] ℂ := fun y ↦ ContinuousLinearMap.toSpanSingleton ℝ (deriv φ y)
  refine ⟨f', Set.Ioo (-1 : ℝ) (d / 2), ?_, ?_, ?_⟩
  · exact Ioo_mem_nhds (by norm_num) (half_pos hd)
  · rw [isOpen_Ioo.continuousOn_iff]
    intro y hy
    dsimp [f', φ]
    apply continuousAt_toSpanSingleton_deriv
    rcases lt_trichotomy y 0 with hyneg | hyzero | hypos
    · exact continuousAt_deriv_kadiriTestFn_of_lt_zero hyneg
    · subst y
      exact continuousAt_deriv_kadiriTestFn_zero hd hf_C2 hf_derivWithin_0 s
    · have hyd : y < d := by nlinarith [hd, hy.2]
      exact continuousAt_deriv_kadiriTestFn_of_pos_lt_d hf_C2 s hypos hyd
  · intro y hy
    dsimp [f', φ]
    rcases lt_trichotomy y 0 with hyneg | hyzero | hypos
    · exact ((hasDerivAt_kadiriTestFn_of_lt_zero hyneg).hasFDerivAt).congr_fderiv (by
        rw [deriv_kadiriTestFn_of_lt_zero hyneg])
    · subst y
      exact ((hasDerivAt_kadiriTestFn_zero hd hf_C2 hf_derivWithin_0 s).hasFDerivAt).congr_fderiv
        (by rw [deriv_kadiriTestFn_zero hd hf_C2 hf_derivWithin_0 s])
    · have hyd : y < d := by nlinarith [hd, hy.2]
      have hIcc : Set.Icc (0 : ℝ) d ∈ nhds y := Icc_mem_nhds_of_mem_Ioo hypos hyd
      have hf_at : ContDiffAt ℝ 2 f y := hf_C2.contDiffAt hIcc
      exact ((hasDerivAt_kadiriTestFn_of_pos hypos
        (hf_at.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).hasDerivAt).hasFDerivAt).congr_fderiv
          (by rw [deriv_kadiriTestFn_of_pos_lt_d hf_C2 s hypos hyd])

theorem contDiffAt_kadiriTestFn_d {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d)) (hf_supp : tsupport f ⊆ Set.Ico 0 d)
    (hf_d : f d = 0) (hf_derivWithin_d : derivWithin f (Set.Icc 0 d) d = 0) (s : ℂ) :
    ContDiffAt ℝ 1 (kadiriTestFn f s) d := by
  rw [contDiffAt_one_iff]
  let φ := kadiriTestFn f s
  let f' : ℝ → ℝ →L[ℝ] ℂ := fun y ↦ ContinuousLinearMap.toSpanSingleton ℝ (deriv φ y)
  refine ⟨f', Set.Ioo (d / 2) (d + 1), ?_, ?_, ?_⟩
  · exact Ioo_mem_nhds (half_lt_self hd) (by linarith)
  · rw [isOpen_Ioo.continuousOn_iff]
    intro y hy
    dsimp [f', φ]
    apply continuousAt_toSpanSingleton_deriv
    rcases lt_trichotomy y d with hylt | hyeq | hygt
    · have hypos : 0 < y := by nlinarith [hd, hy.1]
      exact continuousAt_deriv_kadiriTestFn_of_pos_lt_d hf_C2 s hypos hylt
    · subst y
      exact continuousAt_deriv_kadiriTestFn_d hd hf_C2 hf_supp hf_d hf_derivWithin_d s
    · exact continuousAt_deriv_kadiriTestFn_of_gt_d hd hf_supp s hygt
  · intro y hy
    dsimp [f', φ]
    rcases lt_trichotomy y d with hylt | hyeq | hygt
    · have hypos : 0 < y := by nlinarith [hd, hy.1]
      have hIcc : Set.Icc (0 : ℝ) d ∈ nhds y := Icc_mem_nhds_of_mem_Ioo hypos hylt
      have hf_at : ContDiffAt ℝ 2 f y := hf_C2.contDiffAt hIcc
      exact ((hasDerivAt_kadiriTestFn_of_pos hypos
        (hf_at.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).hasDerivAt).hasFDerivAt).congr_fderiv
          (by rw [deriv_kadiriTestFn_of_pos_lt_d hf_C2 s hypos hylt])
    · subst y
      exact ((hasDerivAt_kadiriTestFn_d hd hf_C2 hf_supp hf_d hf_derivWithin_d s).hasFDerivAt).congr_fderiv
        (by rw [deriv_kadiriTestFn_d hd hf_C2 hf_supp hf_d hf_derivWithin_d s])
    · exact ((hasDerivAt_kadiriTestFn_of_gt_d hd hf_supp s hygt).hasFDerivAt).congr_fderiv
        (by rw [deriv_kadiriTestFn_of_gt_d hd hf_supp s hygt])

private lemma lt_abs_mem_cocompact {A : ℝ} :
    {x : ℝ | A < |x|} ∈ Filter.cocompact ℝ := by
  rw [Filter.mem_cocompact]
  refine ⟨Set.Icc (-|A|) |A|, isCompact_Icc, ?_⟩
  intro x hx
  rw [Set.mem_compl_iff, Set.mem_Icc] at hx
  rw [Set.mem_setOf_eq, lt_abs]
  by_cases hxA : |A| < x
  · exact Or.inl (lt_of_le_of_lt (le_abs_self A) hxA)
  · right
    by_contra hAxneg
    have hxleA : x ≤ |A| := le_of_not_gt hxA
    have hneg_leA : -x ≤ |A| := le_trans (le_of_not_gt hAxneg) (le_abs_self A)
    have hle : -|A| ≤ x := by linarith
    exact hx ⟨hle, hxleA⟩

private lemma isBigO_cocompact_of_exp_tail {F : ℝ → ℂ} {d : ℝ} {c s : ℂ}
    (hs : 1 < s.re)
    (hneg : ∀ x : ℝ, x < 0 → F x = 0)
    (hpos : ∀ x : ℝ, 0 < x → d < x →
      F x = c * exp (((1 / 2 : ℂ) - s) * (x : ℂ))) :
    F =O[Filter.cocompact ℝ]
      fun x : ℝ ↦ Real.exp (-(1 / 2 + (s.re - 1) / 2) * |x|) := by
  let A : ℝ := max |d| 1
  refine Asymptotics.IsBigO.of_bound (max 1 ‖c‖) ?_
  filter_upwards [lt_abs_mem_cocompact (A := A)] with x hx
  have hC0 : 0 ≤ max 1 ‖c‖ := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left 1 ‖c‖)
  by_cases hxpos : 0 < x
  · have hxabs : |x| = x := abs_of_pos hxpos
    have hAd : |d| ≤ A := le_max_left |d| 1
    have hdx : d < x := by
      have hAx : A < x := by simpa [hxabs] using hx
      exact lt_of_le_of_lt (le_trans (le_abs_self d) hAd) hAx
    rw [hpos x hxpos hdx]
    rw [norm_mul, Complex.norm_exp]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hnormc : ‖c‖ ≤ max 1 ‖c‖ := le_max_right 1 ‖c‖
    have hexp : Real.exp ((((1 / 2 : ℂ) - s) * (x : ℂ)).re) ≤
        Real.exp (-(1 / 2 + (s.re - 1) / 2) * |x|) := by
      rw [Real.exp_le_exp]
      simp [Complex.mul_re, hxabs]
      nlinarith [hs.le, hxpos.le]
    exact mul_le_mul hnormc hexp (Real.exp_pos _).le hC0
  · have hxneg : x < 0 := by
      have hA_one : (1 : ℝ) ≤ A := le_max_right |d| 1
      have h_abs_gt_one : 1 < |x| := lt_of_le_of_lt hA_one hx
      exact lt_of_not_ge fun hx0 => by
        have hxabs : |x| = x := abs_of_nonneg hx0
        linarith
    rw [hneg x hxneg]
    simpa using
      mul_nonneg hC0
        (norm_nonneg (Real.exp (-(1 / 2 + (s.re - 1) / 2) * |x|)))

private lemma kadiriTestFn_shift_integral_eq {f : ℝ → ℝ} (s z : ℂ) :
    (∫ y in Set.Ioi (0 : ℝ), kadiriTestFn f s y * exp (-z * (y : ℂ)) ∂volume) =
      ∫ y in Set.Ioi (0 : ℝ),
        ((f 0 : ℂ) - (f y : ℂ)) * exp (-(s + z) * (y : ℂ)) ∂volume := by
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  exact kadiriTestFn_mul_exp_of_pos hy

/-- The `f`-part of a compactly supported Laplace integrand is integrable on the half-line. -/
private lemma integrableOn_laplace_f_term_of_contDiffOn_Icc {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf_C1 : ContDiffOn ℝ 1 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d) (w : ℂ) :
    IntegrableOn (fun y : ℝ ↦ (f y : ℂ) * exp (-w * (y : ℂ)))
      (Set.Ioi (0 : ℝ)) volume := by
  have hcont : ContinuousOn (fun y : ℝ ↦ (f y : ℂ) * exp (-w * (y : ℂ)))
      (Set.Icc (0 : ℝ) d) := by
    exact (continuous_ofReal.comp_continuousOn hf_C1.continuousOn).mul (by fun_prop)
  have hIoc : IntegrableOn (fun y : ℝ ↦ (f y : ℂ) * exp (-w * (y : ℂ)))
      (Set.Ioc (0 : ℝ) d) volume :=
    hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have htail : IntegrableOn (fun y : ℝ ↦ (f y : ℂ) * exp (-w * (y : ℂ)))
      (Set.Ioi d) volume := by
    refine (integrableOn_zero : IntegrableOn (fun _ : ℝ ↦ (0 : ℂ)) (Set.Ioi d) volume).congr_fun
      ?_ measurableSet_Ioi
    intro y hy
    simp [eq_zero_of_ge_d hf_supp hy.le]
  simpa [Set.Ioc_union_Ioi_eq_Ioi hd.le] using hIoc.union htail

/-- Given the elementary exponential tail integral, the Kadiri test-function shift identity is
just integral algebra.  This bridge keeps the compact-support part separate from the pure
exponential calculation. -/
private lemma kadiriTestFn_laplaceTransform_of_exp_tail {f : ℝ → ℝ} {s z : ℂ}
    (hExpInt : IntegrableOn (fun y : ℝ ↦ exp (-(s + z) * (y : ℂ)))
      (Set.Ioi (0 : ℝ)) volume)
    {d : ℝ} (hd : 0 < d) (hf_C1 : ContDiffOn ℝ 1 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hExp :
      (∫ y in Set.Ioi (0 : ℝ), exp (-(s + z) * (y : ℂ)) ∂volume) = 1 / (s + z)) :
    (∫ y in Set.Ioi (0 : ℝ), kadiriTestFn f s y * exp (-z * (y : ℂ)) ∂volume) =
      (f 0 : ℂ) / (s + z) - laplaceTransform f (s + z) := by
  rw [kadiriTestFn_shift_integral_eq]
  have hPoint :
      (∫ y in Set.Ioi (0 : ℝ),
        ((f 0 : ℂ) - (f y : ℂ)) * exp (-(s + z) * (y : ℂ)) ∂volume) =
        ∫ y in Set.Ioi (0 : ℝ),
          (f 0 : ℂ) * exp (-(s + z) * (y : ℂ)) -
            (f y : ℂ) * exp (-(s + z) * (y : ℂ)) ∂volume := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro y _hy
    ring
  rw [hPoint]
  have hFInt : IntegrableOn
      (fun y : ℝ ↦ (f y : ℂ) * exp (-(s + z) * (y : ℂ))) (Set.Ioi (0 : ℝ)) volume :=
    integrableOn_laplace_f_term_of_contDiffOn_Icc hd hf_C1 hf_supp (s + z)
  rw [MeasureTheory.integral_sub (hExpInt.const_mul (f 0 : ℂ)) hFInt]
  rw [MeasureTheory.integral_const_mul, hExp]
  have hLap :
      (∫ y in Set.Ioi (0 : ℝ), (f y : ℂ) * exp (-(s + z) * (y : ℂ)) ∂volume) =
        laplaceTransform f (s + z) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro y _hy
    simp [mul_comm]
  rw [hLap]
  ring

@[blueprint
  "kadiri-test-fn-contDiff"
  (title := "The Kadiri test function is $C^1$")
  (statement := /-- For $f$ satisfying $(H_1)$ of \ref{kadiri-prop-2-1} and any
  $s \in \mathbb{C}$, the Kadiri test function $\mathrm{kadiriTestFn}\, f\, s$
  (\ref{kadiri-test-fn}) has the $C^1$ regularity needed for
  \ref{kadiri-thm-3-1-q1}.  Kadiri states the stronger $C^2$ regularity for this
  particular test function; this lemma records the weaker regularity used by the
  present abstract explicit-formula interface. -/)
  (proof := /-- The function $\varphi(\cdot;\, s)$ is smooth on each of the three open pieces:
  on $(-\infty, 0)$ it is $\equiv 0$; on $(0, d)$ it equals $(f(0) - f(y)) e^{-sy}$, $C^2$
  from $f \in C^2$ on $[0, d]$; on $(d, \infty)$ it equals $f(0) e^{-sy}$ (using
  $\mathrm{supp}\, f \subseteq [0, d)$), smooth. At the seam $y = 0$: the right-limits of
  $\varphi$ and $\varphi'$ are $(f(0) - f(0)) \cdot 1 = 0$ and
  $-f'(0) - s(f(0) - f(0)) = 0$ respectively (using the right derivative $f'(0)=0$ from
  $(H_1)$), matching the left-limits $0$. At the seam $y = d$: the left-limits of $\varphi$
  and $\varphi'$ are
  $(f(0) - f(d)) e^{-sd} = f(0) e^{-sd}$ (using $f(d) = 0$) and
  $-f'(d) e^{-sd} - s(f(0) - f(d)) e^{-sd} = -s f(0) e^{-sd}$ (using $f(d)=0$ and the
  left derivative $f'(d)=0$), matching the right-limits. Hence $\varphi$ is at least
  $C^1$ globally, which is the condition required below. To be formalised. -/)
  (latexEnv := "lemma")
  (discussion := 1484)]
theorem kadiriTestFn_contDiff {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_derivWithin_0 : derivWithin f (.Icc 0 d) 0 = 0)
    (hf_derivWithin_d : derivWithin f (.Icc 0 d) d = 0)
    (s : ℂ) :
    ContDiff ℝ 1 (kadiriTestFn f s) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases lt_trichotomy x 0 with hx0 | rfl | hx0
  · exact contDiffAt_kadiriTestFn_of_lt_zero hx0
  · exact contDiffAt_kadiriTestFn_zero hd hf_C2 hf_derivWithin_0 s
  · rcases lt_trichotomy x d with hxd | rfl | hdx
    · exact contDiffAt_kadiriTestFn_of_pos_lt_d hf_C2 s hx0 hxd
    · exact contDiffAt_kadiriTestFn_d hd hf_C2 hf_supp hf_d hf_derivWithin_d s
    · exact contDiffAt_kadiriTestFn_of_gt_d hd hf_supp s hdx

@[blueprint
  "kadiri-test-fn-decay"
  (title := "Decay condition (B) for the Kadiri test function")
  (statement := /-- For $f$ satisfying $(H_1)$ of \ref{kadiri-prop-2-1} and
  $s \in \mathbb{C}$ with $\Re s > 1$, the Kadiri test function
  $\varphi(\cdot;\, s) = \mathrm{kadiriTestFn}\, f\, s$ (\ref{kadiri-test-fn}) satisfies
  decay condition (B) of \ref{kadiri-thm-3-1-q1}: there exists $b > 0$
  (any $0 < b < \Re s - 1$ works) such that both $\varphi(x;\, s) e^{x/2}$ and
  $\varphi'(x;\, s) e^{x/2}$ are $O(e^{-(1/2 + b)|x|})$ as $|x| \to \infty$. -/)
  (proof := /-- For $x < 0$ both $\varphi(x;\, s)$ and $\varphi'(x;\, s)$ are identically
  $0$, so the bound holds trivially at $-\infty$. For $x > d$ (above the support of $f$),
  $\varphi(x;\, s) = f(0)\, e^{-x s}$ and $\varphi'(x;\, s) = -s\, f(0)\, e^{-x s}$, so
  $|\varphi(x;\, s) e^{x/2}| = |f(0)|\, e^{-x(\Re s - 1/2)}$ and similarly for the
  derivative with an extra factor $|s|$; both are $O(e^{-(1/2 + b) x})$ as $x \to +\infty$
  precisely when $\Re s - 1/2 \geq 1/2 + b$, i.e.\ $b \leq \Re s - 1$. Take any
  $0 < b < \Re s - 1$. To be formalised. -/)
  (latexEnv := "lemma")
  (discussion := 1485)]
theorem kadiriTestFn_decay {d : ℝ} {f : ℝ → ℝ} (_hf_supp : tsupport f ⊆ .Ico 0 d)
    {s : ℂ} (_hs : 1 < s.re) :
    ∃ b > 0,
      ((fun x : ℝ ↦ kadiriTestFn f s x * exp ((x : ℂ) / 2))
          =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) ∧
      ((fun x : ℝ ↦ deriv (kadiriTestFn f s) x * exp ((x : ℂ) / 2))
          =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) := by
  refine ⟨(s.re - 1) / 2, by linarith, ?_, ?_⟩
  · exact isBigO_cocompact_of_exp_tail (d := d) (c := (f 0 : ℂ)) _hs
      (fun x hx ↦ kadiriTestFn_mul_exp_half_of_lt_zero hx)
      (fun x hx0 hdx ↦ by
        rw [kadiriTestFn_of_nonneg hx0.le, eq_zero_of_ge_d _hf_supp hdx.le]
        simp only [ofReal_zero, sub_zero, neg_mul, one_div]
        rw [mul_assoc, ← Complex.exp_add]
        congr 1
        ring_nf)
  · exact isBigO_cocompact_of_exp_tail (d := d) (c := (f 0 : ℂ) * (-s)) _hs
      (fun x hx ↦ deriv_kadiriTestFn_mul_exp_half_of_lt_zero hx)
      (fun x hx0 hdx ↦ by
        rw [deriv_kadiriTestFn_of_pos_gt_d _hf_supp s hx0 hdx]
        rw [mul_assoc, mul_assoc, ← Complex.exp_add]
        ring_nf)

@[blueprint
  "kadiri-test-fn-laplace"
  (title := "Laplace transform of the Kadiri test function (shift identity)")
  (statement := /-- For $f$ satisfying $(H_1)$ of \ref{kadiri-prop-2-1} and
  $s, z \in \mathbb{C}$ with $\Re(s + z) > 0$,
  $$ \int_0^{\infty} \varphi(y;\, s)\, e^{-z y}\, dy
     = \frac{f(0)}{s + z} - F(s + z), $$
  where $\varphi(\cdot;\, s) = \mathrm{kadiriTestFn}\, f\, s$ (\ref{kadiri-test-fn}) and
  $F$ is the file's `laplaceTransform` of $f$. -/)
  (proof := /-- Direct expansion of the integrand on $y > 0$:
  $\varphi(y;\, s) e^{-zy} = (f(0) - f(y)) e^{-(s+z) y}$. Split the integral:
  $\int_0^{\infty} f(0)\, e^{-(s+z) y}\, dy = f(0)/(s + z)$ converges by
  $\Re(s + z) > 0$; $\int_0^{\infty} f(y)\, e^{-(s+z) y}\, dy = F(s + z)$ unconditionally
  since $\mathrm{supp}\, f \subseteq [0, d]$ makes the integral compactly-supported. To be
  formalised. -/)
  (latexEnv := "lemma")
  (discussion := 1486)]
theorem kadiriTestFn_laplaceTransform {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (s z : ℂ) (hsz : 0 < (s + z).re) :
    (∫ y in (.Ioi (0 : ℝ)), kadiriTestFn f s y * exp (-z * (y : ℂ)) ∂volume) =
      (f 0 : ℂ) / (s + z) - laplaceTransform f (s + z) := by
  have hf_C1 : ContDiffOn ℝ 1 f (.Icc 0 d) := hf_C2.of_le (by norm_num)
  have hExpInt : IntegrableOn (fun y : ℝ ↦ exp (-(s + z) * (y : ℂ)))
      (Set.Ioi (0 : ℝ)) volume :=
    integrableOn_exp_neg_mul_Ioi hsz
  have hExp :
      (∫ y in Set.Ioi (0 : ℝ), exp (-(s + z) * (y : ℂ)) ∂volume) = 1 / (s + z) :=
    integral_exp_neg_mul_Ioi hsz
  exact kadiriTestFn_laplaceTransform_of_exp_tail hExpInt hd hf_C1 hf_supp hExp

/-! ### Evaluation helpers for `kadiriTestFn`

Pointwise unfoldings of \ref{kadiri-test-fn} used inside the proof of
\ref{kadiri-identity-16} to dispatch the vanishing terms ($\varphi(0;\, s) = 0$,
$\varphi(-\log n;\, s) = 0$) and to rewrite $\varphi(\log n;\, s)$ as
$(f(0) - f(\log n)) / n^s$. Trivial unfoldings of the definition; left non-blueprinted. -/

@[simp]
theorem kadiriTestFn_zero (f : ℝ → ℝ) (s : ℂ) : kadiriTestFn f s 0 = 0 := by
  simp [kadiriTestFn]

theorem kadiriTestFn_neg_log (f : ℝ → ℝ) (s : ℂ) (n : ℕ) :
    kadiriTestFn f s (-Real.log n) = 0 := by
  dsimp only [kadiriTestFn]
  split
  · next h =>
    have hz : Real.log (n : ℝ) = 0 :=
      le_antisymm (by linarith) (Real.log_natCast_nonneg n)
    simp [hz]
  · rfl

theorem kadiriTestFn_log (f : ℝ → ℝ) (s : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    kadiriTestFn f s (Real.log n) =
      ((f 0 : ℂ) - (f (Real.log n) : ℂ)) / (n : ℂ) ^ s := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcpow : (n : ℂ) ^ s = Complex.exp ((Real.log (n : ℝ) : ℂ) * s) := by
    rw [Complex.cpow_def_of_ne_zero hn0, Complex.ofReal_log (Nat.cast_nonneg n),
      Complex.ofReal_natCast]
  have hexp : Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) = ((n : ℂ) ^ s)⁻¹ := by
    rw [hcpow, ← Complex.exp_neg]
    congr 1
    ring
  dsimp only [kadiriTestFn]
  rw [if_pos (Real.log_natCast_nonneg n), hexp, div_eq_mul_inv]

/-- The `q = 1` explicit formula specialized to Kadiri's test function, with its regularity and
decay hypotheses discharged by `kadiriTestFn_contDiff` and `kadiriTestFn_decay`. -/
theorem kadiri_thm_3_1_q1_kadiriTestFn {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_derivWithin_0 : derivWithin f (.Icc 0 d) 0 = 0)
    (hf_derivWithin_d : derivWithin f (.Icc 0 d) d = 0)
    {s : ℂ} (hs : 1 < s.re) :
    let Φ : ℂ → ℂ := fun z ↦
      ∫ y in (.Ioi (0 : ℝ)), kadiriTestFn f s y * exp (-z * (y : ℂ)) ∂volume
    (∑' n : ℕ, (Λ n : ℂ) * kadiriTestFn f s (Real.log n)) =
      Φ (-1) + Φ 0
        - ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ), Φ (-ρ.val)
        - kadiriTestFn f s 0 * ((Real.log Real.pi : ℝ) : ℂ)
        + ∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * kadiriTestFn f s (-Real.log n)
        + (1 / (2 * (Real.pi : ℂ))) *
            ∫ t : ℝ,
              ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
                Φ (-(1 / 2 + (t : ℂ) * I)) := by
  obtain ⟨b, hb, hdec, hderiv_dec⟩ := kadiriTestFn_decay hf_supp hs
  exact kadiri_thm_3_1_q1 (kadiriTestFn_contDiff hd hf_C2 hf_supp hf_d
    hf_derivWithin_0 hf_derivWithin_d s) hb hdec hderiv_dec

private lemma kadiriTestFn_laplaceTransform_at_zero_ibp {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_derivWithin_0 : derivWithin f (.Icc 0 d) 0 = 0)
    (hf_derivWithin_d : derivWithin f (.Icc 0 d) d = 0)
    {s : ℂ} (hs : 1 < s.re) :
    (∫ y in (.Ioi (0 : ℝ)), kadiriTestFn f s y * exp (-(0 : ℂ) * (y : ℂ)) ∂volume) =
      -laplaceTransform (fun u ↦ deriv (deriv f) u) s / s ^ 2 := by
  have hspos : 0 < (s + 0).re := by
    simpa using lt_trans (by norm_num : (0 : ℝ) < 1) hs
  have hsne : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hΦ := kadiriTestFn_laplaceTransform hd hf_C2 hf_supp s 0 hspos
  have hF := laplaceTransform_ibp hd hf_C2 hf_supp hf_d hf_derivWithin_0 hf_derivWithin_d hsne
  have hF0 : laplaceTransform f (s + 0) =
      (f 0 : ℂ) / (s + 0) + laplaceTransform (fun u ↦ deriv (deriv f) u) s / s ^ 2 := by
    simpa using hF
  rw [hΦ, hF0]
  field_simp [hsne]
  ring_nf

private lemma kadiriTestFn_laplaceTransform_at_neg_one {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d) {s : ℂ} (hs : 1 < s.re) :
    (∫ y in (.Ioi (0 : ℝ)), kadiriTestFn f s y * exp (-(-1 : ℂ) * (y : ℂ)) ∂volume) =
      (f 0 : ℂ) / (s - 1) - laplaceTransform f (s - 1) := by
  have hpos : 0 < (s + (-1 : ℂ)).re := by
    simp
    linarith [hs]
  have hΦ := kadiriTestFn_laplaceTransform hd hf_C2 hf_supp s (-1) hpos
  simpa [sub_eq_add_neg] using hΦ

private lemma kadiriTestFn_laplaceTransform_at_zeroIndex {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d) {s : ℂ} (hs : 1 < s.re)
    (ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ)) :
    (∫ y in (.Ioi (0 : ℝ)), kadiriTestFn f s y * exp (-(-ρ.val) * (y : ℂ)) ∂volume) =
      (f 0 : ℂ) / (s - ρ.val) - laplaceTransform f (s - ρ.val) := by
  have hρlt : ρ.val.re < 1 := ρ.property.1.2
  have hpos : 0 < (s + -ρ.val).re := by
    simp
    linarith [hs, hρlt]
  have hΦ := kadiriTestFn_laplaceTransform hd hf_C2 hf_supp s (-ρ.val) hpos
  simpa [sub_eq_add_neg] using hΦ

private lemma kadiriTestFn_zero_summable {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_derivWithin_0 : derivWithin f (.Icc 0 d) 0 = 0)
    (hf_derivWithin_d : derivWithin f (.Icc 0 d) d = 0)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) =>
      (f 0 : ℂ) / (s - ρ.val) - laplaceTransform f (s - ρ.val)) := by
  obtain ⟨b, hb, hdec, hderiv_dec⟩ := kadiriTestFn_decay hf_supp hs
  have hzero := kadiri_thm_3_1_q1_zero_summable
    (kadiriTestFn_contDiff hd hf_C2 hf_supp hf_d hf_derivWithin_0 hf_derivWithin_d s)
    hb hdec hderiv_dec
  refine hzero.congr ?_
  intro ρ
  exact kadiriTestFn_laplaceTransform_at_zeroIndex hd hf_C2 hf_supp hs ρ

private lemma kadiriTestFn_laplaceTransform_gammaLine_ibp {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_derivWithin_0 : derivWithin f (.Icc 0 d) 0 = 0)
    (hf_derivWithin_d : derivWithin f (.Icc 0 d) d = 0)
    {s : ℂ} (hs : 1 < s.re) (t : ℝ) :
    (∫ y in (.Ioi (0 : ℝ)),
        kadiriTestFn f s y * exp (- (-(1 / 2 + (t : ℂ) * I)) * (y : ℂ)) ∂volume) =
      -laplaceTransform (fun u ↦ deriv (deriv f) u) (s - (1 / 2 + (t : ℂ) * I)) /
        (s - (1 / 2 + (t : ℂ) * I)) ^ 2 := by
  let z : ℂ := 1 / 2 + (t : ℂ) * I
  have hwpos : 0 < (s + -z).re := by
    dsimp [z]
    simp [Complex.mul_re]
    linarith [hs]
  have hwne : s - z ≠ 0 := by
    intro h
    have hre : (s - z).re = 0 := by
      rw [h]
      simp
    dsimp [z] at hre
    simp [Complex.mul_re] at hre
    linarith [hs]
  have hΦ := kadiriTestFn_laplaceTransform hd hf_C2 hf_supp s (-z) hwpos
  have hF := laplaceTransform_ibp hd hf_C2 hf_supp hf_d hf_derivWithin_0 hf_derivWithin_d hwne
  have hFz : laplaceTransform f (s + -z) =
      (f 0 : ℂ) / (s + -z) +
        laplaceTransform (fun u ↦ deriv (deriv f) u) (s + -z) / (s + -z) ^ 2 := by
    simpa [sub_eq_add_neg] using hF
  rw [hΦ, hFz]
  dsimp [z]
  field_simp [hwne]
  ring_nf

private lemma kadiriTestFn_reflectedPrimeSum_zero (f : ℝ → ℝ) (s : ℂ) :
    (∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * kadiriTestFn f s (-Real.log n)) = 0 := by
  simp [kadiriTestFn_neg_log]

private lemma kadiriTestFn_primeSide_pointwise (f : ℝ → ℝ) (s : ℂ) (n : ℕ) :
    (Λ n : ℂ) * kadiriTestFn f s (Real.log n) =
      (f 0 : ℂ) * ((Λ n : ℂ) / (n : ℂ) ^ s) -
        ((Λ n : ℂ) / (n : ℂ) ^ s) * (f (Real.log n) : ℂ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · simp [kadiriTestFn]
  · have hn : 1 ≤ n := Nat.succ_le_iff.mpr hnpos
    rw [kadiriTestFn_log f s hn]
    ring

private lemma kadiriTestFn_primeSide_tsum_congr (f : ℝ → ℝ) (s : ℂ) :
    (∑' n : ℕ, (Λ n : ℂ) * kadiriTestFn f s (Real.log n)) =
      (∑' n : ℕ, (
        (f 0 : ℂ) * ((Λ n : ℂ) / (n : ℂ) ^ s) -
          ((Λ n : ℂ) / (n : ℂ) ^ s) * (f (Real.log n) : ℂ))) := by
  apply tsum_congr
  intro n
  exact kadiriTestFn_primeSide_pointwise f s n

private lemma summable_vonMangoldt_div_cpow_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (Λ n : ℂ) / (n : ℂ) ^ s) := by
  have hL : LSeriesSummable (fun n : ℕ => (Λ n : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  rw [LSeriesSummable] at hL
  refine hL.congr ?_
  intro n
  by_cases hn : n = 0
  · simp [LSeries.term, hn]
  · simp [LSeries.term, hn]

private lemma kadiriTestFn_primeSide_tsum_split {d : ℝ} {f : ℝ → ℝ}
    (hf_supp : tsupport f ⊆ .Ico 0 d) {s : ℂ}
    (hΛs : Summable (fun n : ℕ => (Λ n : ℂ) / (n : ℂ) ^ s)) :
    (∑' n : ℕ, (Λ n : ℂ) * kadiriTestFn f s (Real.log n)) =
      (f 0 : ℂ) * (∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s) -
        (∑' n : ℕ, (((Λ n : ℂ) / (n : ℂ) ^ s) * (f (Real.log n) : ℂ))) := by
  rw [kadiriTestFn_primeSide_tsum_congr]
  have hf_log : Summable
      (fun n : ℕ => ((Λ n : ℂ) / (n : ℂ) ^ s) * (f (Real.log n) : ℂ)) :=
    summable_f_log hf_supp (fun n : ℕ => (Λ n : ℂ) / (n : ℂ) ^ s)
  rw [Summable.tsum_sub (Summable.mul_left (f 0 : ℂ) hΛs) hf_log]
  rw [tsum_mul_left]

private lemma kadiriTestFn_primeSide_tsum_split_of_one_lt_re {d : ℝ} {f : ℝ → ℝ}
    (hf_supp : tsupport f ⊆ .Ico 0 d) {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, (Λ n : ℂ) * kadiriTestFn f s (Real.log n)) =
      (f 0 : ℂ) * (∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s) -
        (∑' n : ℕ, (((Λ n : ℂ) / (n : ℂ) ^ s) * (f (Real.log n) : ℂ))) :=
  kadiriTestFn_primeSide_tsum_split hf_supp (summable_vonMangoldt_div_cpow_of_one_lt_re hs)

private lemma kadiri_zero_sum_re_split {f : ℝ → ℝ} {s : ℂ}
    (hComb : Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) =>
      (f 0 : ℂ) / (s - ρ.val) - laplaceTransform f (s - ρ.val)))
    (hRecipRe : Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) =>
      (1 / (s - ρ.val)).re))
    (hLapRe : Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) =>
      (laplaceTransform f (s - ρ.val)).re)) :
    (∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
        ((f 0 : ℂ) / (s - ρ.val) - laplaceTransform f (s - ρ.val))).re =
      f 0 * (∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
        (1 / (s - ρ.val)).re) -
      ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
        (laplaceTransform f (s - ρ.val)).re := by
  rw [RiemannZeta.WeilGuinand.re_tsum hComb]
  have hsplit := Summable.tsum_sub (Summable.mul_left (f 0) hRecipRe) hLapRe
  have hsplit' :
      (∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
          (f 0 * (1 / (s - ρ.val)).re - (laplaceTransform f (s - ρ.val)).re)) =
        f 0 * (∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
          (1 / (s - ρ.val)).re) -
        ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
          (laplaceTransform f (s - ρ.val)).re := by
    simpa [tsum_mul_left] using hsplit
  rw [← hsplit']
  apply tsum_congr
  intro ρ
  simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, div_eq_mul_inv]

private lemma kadiriTestFn_gammaLine_eq_neg_F2 {d : ℝ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_derivWithin_0 : derivWithin f (.Icc 0 d) 0 = 0)
    (hf_derivWithin_d : derivWithin f (.Icc 0 d) d = 0)
    {s : ℂ} (hs : 1 < s.re) :
    (1 / (2 * (Real.pi : ℂ))) *
        (∫ t : ℝ,
          ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
            (∫ y in (.Ioi (0 : ℝ)),
              kadiriTestFn f s y * exp (- (-(1 / 2 + (t : ℂ) * I)) * (y : ℂ)) ∂volume)) =
      (1 / (2 * (Real.pi : ℂ))) *
        (∫ t : ℝ,
          -(((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
            (laplaceTransform (fun u ↦ deriv (deriv f) u) (s - (1 / 2 + (t : ℂ) * I)) /
              (s - (1 / 2 + (t : ℂ) * I)) ^ 2))) := by
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [kadiriTestFn_laplaceTransform_gammaLine_ibp hd hf_C2 hf_supp hf_d hf_derivWithin_0
    hf_derivWithin_d hs t]
  ring

private lemma gammaLine_neg_F2_neg_eq_pos {f : ℝ → ℝ} {s : ℂ} :
    -((1 / (2 * (Real.pi : ℂ))) *
        (∫ t : ℝ,
          -(((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
            (laplaceTransform (fun u ↦ deriv (deriv f) u) (s - (1 / 2 + (t : ℂ) * I)) /
              (s - (1 / 2 + (t : ℂ) * I)) ^ 2)))) =
      (1 / (2 * (Real.pi : ℂ))) *
        (∫ t : ℝ,
          ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
            laplaceTransform (fun u ↦ deriv (deriv f) u) (s - (1 / 2 + (t : ℂ) * I)) /
            (s - (1 / 2 + (t : ℂ) * I)) ^ 2) := by
  let G : ℝ → ℂ := fun t => ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ)
  let H : ℝ → ℂ := fun t =>
    laplaceTransform (fun u ↦ deriv (deriv f) u) (s - (1 / 2 + (t : ℂ) * I)) /
      (s - (1 / 2 + (t : ℂ) * I)) ^ 2
  have hInt : (∫ t : ℝ, G t * H t) =
      ∫ t : ℝ,
        ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
          laplaceTransform (fun u ↦ deriv (deriv f) u) (s - (1 / 2 + (t : ℂ) * I)) /
          (s - (1 / 2 + (t : ℂ) * I)) ^ 2 := by
    apply integral_congr_ae
    filter_upwards with t
    dsimp [G, H]
    ring
  change -((1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ, -(G t * H t))) =
      (1 / (2 * (Real.pi : ℂ))) *
        (∫ t : ℝ,
          ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
            laplaceTransform (fun u ↦ deriv (deriv f) u) (s - (1 / 2 + (t : ℂ) * I)) /
            (s - (1 / 2 + (t : ℂ) * I)) ^ 2)
  rw [integral_neg, hInt]
  ring

private theorem kadiriTestFn_q1_substituted {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_derivWithin_0 : derivWithin f (.Icc 0 d) 0 = 0)
    (hf_derivWithin_d : derivWithin f (.Icc 0 d) d = 0)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, (Λ n : ℂ) * kadiriTestFn f s (Real.log n)) =
      ((f 0 : ℂ) / (s - 1) - laplaceTransform f (s - 1))
        - laplaceTransform (fun u ↦ deriv (deriv f) u) s / s ^ 2
        - ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
            ((f 0 : ℂ) / (s - ρ.val) - laplaceTransform f (s - ρ.val))
        + (1 / (2 * (Real.pi : ℂ))) *
            (∫ t : ℝ,
              -(((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
                (laplaceTransform (fun u ↦ deriv (deriv f) u)
                  (s - (1 / 2 + (t : ℂ) * I)) /
                  (s - (1 / 2 + (t : ℂ) * I)) ^ 2))) := by
  have h := kadiri_thm_3_1_q1_kadiriTestFn hd hf_C2 hf_supp hf_d hf_derivWithin_0
    hf_derivWithin_d hs
  dsimp only at h
  have hzero :
      (∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
          ∫ y in Set.Ioi (0 : ℝ),
            kadiriTestFn f s y * exp (-(-↑ρ) * (y : ℂ)) ∂volume) =
        ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
          ((f 0 : ℂ) / (s - ρ.val) - laplaceTransform f (s - ρ.val)) := by
    apply tsum_congr
    intro ρ
    exact kadiriTestFn_laplaceTransform_at_zeroIndex hd hf_C2 hf_supp hs ρ
  rw [kadiriTestFn_laplaceTransform_at_neg_one hd hf_C2 hf_supp hs,
    kadiriTestFn_laplaceTransform_at_zero_ibp hd hf_C2 hf_supp hf_d hf_derivWithin_0
      hf_derivWithin_d hs,
    hzero, kadiriTestFn_zero, zero_mul, kadiriTestFn_reflectedPrimeSum_zero,
    kadiriTestFn_gammaLine_eq_neg_F2 hd hf_C2 hf_supp hf_d hf_derivWithin_0
      hf_derivWithin_d hs] at h
  simpa [sub_eq_add_neg, add_assoc, neg_div] using h

/-! ### Auxiliary: real zero-sum form of equation (16)

Kadiri writes the reciprocal zero contribution as
`Re (∑ρ 1 / (s - ρ))`. In Lean we keep the convergent object explicit as the real sum
`∑ρ Re (1 / (s - ρ))`; the raw complex reciprocal series is not the right unconditionally
summable object. -/

private theorem identity_16_real_of_zero_re_summable {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_derivWithin_0 : derivWithin f (.Icc 0 d) 0 = 0)
    (hf_derivWithin_d : derivWithin f (.Icc 0 d) d = 0)
    {s : ℂ} (hs : 1 < s.re)
    (hComb : Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) =>
      (f 0 : ℂ) / (s - ρ.val) - laplaceTransform f (s - ρ.val)))
    (hRecipRe : Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) =>
      (1 / (s - ρ.val)).re))
    (hLapRe : Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) =>
      (laplaceTransform f (s - ρ.val)).re)) :
    (∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s * ((f (Real.log n) : ℝ) : ℂ)).re =
      f 0 * (((∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s) - 1 / (s - 1)).re +
        ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
          (1 / (s - ρ.val)).re)
        + (laplaceTransform f (s - 1)).re
        - ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) .univ,
            (laplaceTransform f (s - ρ.val)).re
        + ((1 / (2 * (Real.pi : ℂ))) *
            (∫ t : ℝ,
              ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
                laplaceTransform (fun u ↦ deriv (deriv f) u)
                  (s - (1 / 2 + (t : ℂ) * I))
                / (s - (1 / 2 + (t : ℂ) * I)) ^ 2)
            + laplaceTransform (fun u ↦ deriv (deriv f) u) s / s ^ 2).re := by
  have hQ := kadiriTestFn_q1_substituted hd hf_C2 hf_supp hf_d hf_derivWithin_0
    hf_derivWithin_d hs
  rw [kadiriTestFn_primeSide_tsum_split_of_one_lt_re hf_supp hs] at hQ
  have hz := kadiri_zero_sum_re_split hComb hRecipRe hLapRe
  rw [← gammaLine_neg_F2_neg_eq_pos (f := f) (s := s)]
  have hmain := congrArg Complex.re hQ
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hmain ⊢
  rw [hz] at hmain
  simp [div_eq_mul_inv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] at hmain ⊢
  linear_combination -hmain

@[blueprint
  "kadiri-summable-recip-re-at-zeros"
  (title := "Summability of the real reciprocal zero sum")
  (statement := /-- For every $s$ with $\Re s > 1$, the real reciprocal zero sum
  $\sum_{\rho \in Z(\zeta)} \Re \frac{1}{s-\rho}$ is convergent. -/)
  (proof := /-- Write $\rho = \beta+i\gamma$. Since $0 < \beta < 1$ and $\Re s > 1$,
  $\Re(s-\rho)$ stays in a bounded positive interval and
  $$\Re\frac{1}{s-\rho}
    = \frac{\Re s-\beta}{(\Re s-\beta)^2 + (\Im s-\gamma)^2}.$$
  Away from the finitely many zeros with $|\Im s-\gamma| < 1$, this is
  $O(1/(\Im s-\gamma)^2)$. Combine this with Backlund/Riemann--von Mangoldt zero counting
  to sum the tail by Abel summation. To be formalised. -/)
  (latexEnv := "lemma")
  (discussion := 1478)]
theorem summable_recip_re_at_zeros {s : ℂ} (hs : 1 < s.re) :
    Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) =>
      (1 / (s - ρ.val)).re) := by
  sorry

@[blueprint
  "kadiri-identity-16"
  (title := "Equation (16) of \\cite{Kadiri2005}: intermediate identity")
  (statement := /-- Under the hypotheses of \ref{kadiri-prop-2-1}: for every
  $s \in \mathbb{C}$ with $\Re s > 1$,
  $$ \Re \sum_{n \geq 1} \frac{\Lambda(n)}{n^s} f(\log n)
   = f(0) \left( \Re \Bigl( \sum_{n \geq 1} \frac{\Lambda(n)}{n^s}
                     - \frac{1}{s - 1} \Bigr)
                     + \sum_{\rho \in Z(\zeta)} \Re \frac{1}{s - \rho} \right)
   + \Re F(s - 1) - \sum_{\rho \in Z(\zeta)} \Re F(s - \rho)
   + \Re \Bigl( \frac{1}{2\pi i} \int_{1/2 - i\infty}^{1/2 + i\infty}
       \Re \tfrac{\Gamma'}{\Gamma}\!\left(\tfrac{z}{2}\right) \frac{F_2(s - z)}{(s - z)^2}\, dz
       + \frac{F_2(s)}{s^2} \Bigr). $$
  This is the form obtained from \ref{kadiri-thm-3-1-q1} (the Weil-type explicit formula,
  specialized to $q = 1$, $\chi$ trivial) by taking the parametrised test function
  $\varphi(y) = (f(0) - f(y)) e^{-y s} \mathbf{1}_{y \geq 0}$. The restriction $\Re s > 1$
  is where the Dirichlet series for $-\zeta'/\zeta(s)$ converges absolutely; this is also
  the range needed for Kadiri's zero-free-region argument. -/)
  (proof := /-- Apply \ref{kadiri-thm-3-1-q1} to the Kadiri test function
  $\varphi(\cdot;\, s) = \mathrm{kadiriTestFn}\, f\, s$ (\ref{kadiri-test-fn}); its hypotheses
  are discharged by \ref{kadiri-test-fn-contDiff} ($\varphi$ is $C^1$) and
  \ref{kadiri-test-fn-decay} (decay (B) with any $0 < b < \Re s - 1$, requiring
  $\Re s > 1$). The Laplace transform of $\varphi$ is computed by
  \ref{kadiri-test-fn-laplace}: $\Phi(z;\, s) = f(0)/(s+z) - F(s+z)$. In particular
  $\Phi(-1) = f(0)/(s-1) - F(s-1)$, $\Phi(-\rho) = f(0)/(s-\rho) - F(s-\rho)$,
  $\Phi(0) = f(0)/s - F(s)$, and $\Phi(-z) = f(0)/(s-z) - F(s-z)$ at $z = 1/2 + it$.
  Rewriting $F(s) = f(0)/s + F_2(s)/s^2$ via \ref{kadiri-laplace-ibp} (and likewise at
  $w = s - z$) collapses $\Phi(0) = -F_2(s)/s^2$ and $\Phi(-z) = -F_2(s-z)/(s-z)^2$ used
  inside the contour integral. Three terms of \ref{kadiri-thm-3-1-q1}'s conclusion vanish
  for this $\varphi$: $\varphi(0;\, s) = 0$ kills the $\varphi(0) \log \pi$ term, and
  $\varphi(-\log n;\, s) = 0$ for every $n \geq 1$ kills the reflected discrete sum.
  Unfolding the LHS as
  $\sum_n \Lambda(n) \varphi(\log n;\, s) = f(0) \sum_n \Lambda(n)/n^s
                                            - \sum_n \Lambda(n) f(\log n)/n^s$, solving for
  $\sum_n \Lambda(n) f(\log n)/n^s$, substituting the $\Phi$ values, and taking real parts,
  yields the right-hand side of (16), with the reciprocal zero contribution represented as
  the real convergent series $\sum_\rho \Re(1/(s-\rho))$. To be formalised. -/)
  (latexEnv := "lemma")
  (discussion := 1488)]
theorem identity_16 {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_nonneg : ∀ t, 0 ≤ f t)
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_derivWithin_0 : derivWithin f (.Icc 0 d) 0 = 0)
    (hf_derivWithin_d : derivWithin f (.Icc 0 d) d = 0)
    (hf_secondWithin_d :
      derivWithin (fun x ↦ derivWithin f (.Icc 0 d) x) (.Icc 0 d) d = 0)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s * ((f (Real.log n) : ℝ) : ℂ)).re =
      f 0 * (((∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s) - 1 / (s - 1)).re +
        ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
          (1 / (s - ρ.val)).re)
        + (laplaceTransform f (s - 1)).re
        - ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) .univ,
            (laplaceTransform f (s - ρ.val)).re
        + ((1 / (2 * (Real.pi : ℂ))) *
            (∫ t : ℝ,
              ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
                laplaceTransform (fun u ↦ deriv (deriv f) u)
                  (s - (1 / 2 + (t : ℂ) * I))
                / (s - (1 / 2 + (t : ℂ) * I)) ^ 2)
            + laplaceTransform (fun u ↦ deriv (deriv f) u) s / s ^ 2).re := by
  have hComb : Summable
      (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) =>
        (f 0 : ℂ) / (s - ρ.val) - laplaceTransform f (s - ρ.val)) :=
    kadiriTestFn_zero_summable hd hf_C2 hf_supp hf_d hf_derivWithin_0 hf_derivWithin_d hs
  have hRecipRe : Summable
      (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) =>
        (1 / (s - ρ.val)).re) :=
    summable_recip_re_at_zeros hs
  have hLapRe : Summable
      (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) =>
        (laplaceTransform f (s - ρ.val)).re) := by
    -- TODO: supplied later as `summable_lap_re_at_zeros`; this theorem precedes that named
    -- analytic auxiliary so that the section follows Kadiri's derivation order.
    sorry
  exact identity_16_real_of_zero_re_summable hd hf_C2 hf_supp hf_d hf_derivWithin_0
    hf_derivWithin_d hs hComb hRecipRe hLapRe

-- Kept (commented out) as a stub for potential future use. The current Kadiri argument
-- (`identity_16`, `re_inner_eq`, `prop_2_1`, `eq_5`) is stated and proved on the
-- half-plane $\Re s > 1$, which is enough for the zero-free-region argument
-- and avoids the meromorphic-extension subtlety: the RHS of `prop_2_1` has poles at the
-- trivial zeros $s = -2, -4, \ldots$ (digamma factor) and at $s = 1$ (the $1/(s-1)$
-- term), so the "entire" hypothesis below cannot be discharged directly in those
-- formulations.
/-
@[blueprint
  "kadiri-re-agree-extension"
  (title := "Real-part agreement on a half-plane extends to $\\mathbb{C}$")
  (statement := /-- If $F, G \colon \mathbb{C} \to \mathbb{C}$ are entire and
  $\Re F(s) = \Re G(s)$ for every $s$ with $\Re s > 1$, then $\Re F(s) = \Re G(s)$ for all
  $s \in \mathbb{C}$. -/)
  (proof := /-- Let $H = F - G$. Then $H$ is entire and $\Re H \equiv 0$ on the open
  half-plane $\{\Re s > 1\}$. The function $\Re H$ is harmonic on $\mathbb{C}$, and
  vanishes on a non-empty open set; by the identity principle for real-analytic (or
  harmonic) functions on the connected domain $\mathbb{C}$, $\Re H \equiv 0$ everywhere.
  (Equivalently: $H$ is locally constant on the half-plane via Cauchy-Riemann, hence
  $H$ is a purely imaginary constant, hence $\Re H = 0$ everywhere.) -/)
  (latexEnv := "lemma")
  (discussion := 1475)]
theorem re_eq_of_entire_agree_on_halfplane {F G : ℂ → ℂ}
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (hagree : ∀ s : ℂ, 1 < s.re → (F s).re = (G s).re) :
    ∀ s : ℂ, (F s).re = (G s).re := by
  sorry
-/

/-! ## Auxiliaries combining the three precursors to Proposition 2.1

Two facts not in the three precursors above are needed: \ref{kadiri-re-hadamardB-eq} (the
closed form $\Re B = -\sum_\rho \Re(1/\rho)$, conjectured from the Hadamard product) and
\ref{kadiri-summable-lap-at-zeros} (summability of the residue sum at the non-trivial zeros).
They combine with \ref{kadiri-hadamard-identity} to give \ref{kadiri-re-inner-eq}
(collapsing the $f(0)$-coefficient of equation (16) into the $T_1$ form on the half-plane
$\Re s > 1$). After that, \ref{kadiri-prop-2-1} is a two-line `rw` chain combining
\ref{kadiri-identity-16} with \ref{kadiri-re-inner-eq} on the same half-plane.
All three are stated below with `sorry` proofs. The summability auxiliary in turn rests on
two further inputs, also stated below: Backlund's explicit Riemann--von Mangoldt bound
(\ref{kadiri-backlund-bound}), giving $N(T) \ll T \log T$, and the $1/y^2$ decay of $\Re F$
on vertical strips (\ref{kadiri-laplace-re-decay}), giving the per-term bound
$|\Re F(s - \rho)| \ll 1/\gamma^2$. -/

@[blueprint
  "kadiri-re-hadamardB-eq"
  (title := "Real part of the Hadamard constant")
  (statement := /-- $\Re B = -\sum_{\rho \in Z(\zeta)} \Re \tfrac{1}{\rho}$, where $B$ is the
  Hadamard constant (\ref{kadiri-hadamard-B}). -/)
  (proof := /-- Subtract $\tfrac{1}{s-1}$ from \ref{kadiri-hadamard-identity}, take $s \to 1$
  using the Laurent expansion $-\zeta'/\zeta(s) = \tfrac{1}{s-1} - \gamma + O(s - 1)$ near $s = 1$
  and the value $\Gamma'/\Gamma(3/2)$, then symmetrise the resulting sum
  $\sum_\rho (1/\rho + 1/(1-\rho))$ using $\rho \leftrightarrow 1 - \bar\rho$ to relate
  $\sum_\rho 1/\rho$ to $\Re B$. To be formalised. -/)
  (latexEnv := "lemma")
  (discussion := 1476)]
theorem re_hadamardB_eq :
    hadamardB.re =
    -∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
        (1 / (ρ.val : ℂ)).re := by
  sorry

@[blueprint
  "kadiri-hadamard-zero-log-sum-re-split"
  (title := "Real-part split of the Hadamard zero log-derivative sum")
  (statement := /-- For $\Re s > 1$, the real part of the genus-one Hadamard zero sum splits as
  $$\Re\sum_\rho\left(\frac1\rho+\frac1{s-\rho}\right)
      = \sum_\rho \Re\frac1\rho + \sum_\rho \Re\frac1{s-\rho}.$$ -/)
  (proof := /-- Use the genus-one zero-term summability from the xi Hadamard product, transported
  from the divisor-zero index to `riemannZeta.zeroes_rect`, together with
  \ref{kadiri-summable-recip-re-at-zeros} and the corresponding real summability of
  $\Re(1/\rho)$ encoded in \ref{kadiri-re-hadamardB-eq}. Then apply `Complex.reCLM.map_tsum`
  and `Summable.tsum_add`. To be formalised. -/)
  (latexEnv := "lemma")
  (discussion := 1478)]
theorem hadamard_zero_log_sum_re_split {s : ℂ} (hs : 1 < s.re) :
    ((∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
        (1 / (ρ.val : ℂ) + 1 / (s - ρ.val))).re) =
      (∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
        (1 / (ρ.val : ℂ)).re) +
      ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
        (1 / (s - ρ.val)).re := by
  sorry

@[blueprint
  "kadiri-backlund-bound"
  (title := "Backlund's explicit Riemann--von Mangoldt bound")
  (statement := /-- Backlund's explicit zero-counting bound (\cite{Backlund1918}, cited in
  \cite[page 24]{Kadiri2005}): the constants $(b_1, b_2, b_3) = (0.137, 0.443, 6.1)$ satisfy
  the project's \ref{Riemann-von-Mangoldt-estimate}, i.e.\ for every $T \geq 2$,
  $$ \bigl| N(T) - \bigl( \tfrac{T}{2\pi} \log \tfrac{T}{2\pi} - \tfrac{T}{2\pi}
                          + \tfrac{7}{8} \bigr) \bigr|
     \leq 0.137 \log T + 0.443 \log \log T + 6.1. $$
  Backlund's original (\cite[page 24]{Kadiri2005}) bounds the difference from the simpler
  main term $\tfrac{T}{2\pi} \log \tfrac{T}{2\pi e}$ by
  $0.137 \log T + 0.443 \log \log T + 5.225$; absorbing the $\tfrac{7}{8}$ offset between the
  two main-term conventions gives the project-form constant $5.225 + \tfrac{7}{8} = 6.1$.
  For $T \in [2, t_1)$ (below the first non-trivial zero $t_1 \approx 14.1347$) the LHS reduces
  to the main-term absolute value, which is well within the (loose) RHS bound. -/)
  (proof := /-- Classical Backlund 1918 (\cite{Backlund1918}). The
  \cite[Theorem of Backlund]{Backlund1918} variant is the form cited at
  \cite[page 24]{Kadiri2005} as the starting point for the explicit estimates
  $N_1(u), N_2(u)$ of (34)-(35) there. To be formalised. -/)
  (latexEnv := "lemma")]
theorem backlund_bound : riemannZeta.Riemann_vonMangoldt_bound 0.137 0.443 6.1 := by
  sorry

@[blueprint
  "kadiri-laplace-re-decay"
  (title := "$1/y^2$ decay of $\\Re F$ on a vertical strip")
  (statement := /-- Under the hypotheses of \ref{kadiri-prop-2-1}: for every closed vertical
  strip $\sigma_0 \leq \Re s \leq \sigma_1$ there is a constant
  $C = C(\sigma_0, \sigma_1, f)$ such that for every $s \in \mathbb{C}$ with
  $\sigma_0 \leq \Re s \leq \sigma_1$ and $|\Im s| \geq 1$,
  $$ |\Re F(s)| \leq \frac{C}{(\Im s)^2}. $$
  Note that this is sharper than the elementary $|F(s)| = O(1/|s|)$ from a single integration
  by parts: the cancellation $\Re(1/s) = \sigma/(\sigma^2 + y^2) = O(1/y^2)$ for bounded
  $\sigma$ saves one power of $|y|$ once the real part is taken. -/)
  (proof := /-- Apply \ref{kadiri-laplace-ibp} to get
  $F(s) = f(0)/s + F_2(s)/s^2$, where $F_2$ is the Laplace transform of $f''$. Taking real
  parts at $s = \sigma + iy$:
  $\Re F(s) = \dfrac{f(0)\, \sigma}{\sigma^2 + y^2}
              + \Re \dfrac{F_2(s)}{s^2}$. The first summand is bounded by
  $|f(0)| \cdot \max(|\sigma_0|, |\sigma_1|) / y^2$; the second by absolute values is at most
  $\dfrac{1}{y^2} \cdot d \cdot \max(1, e^{-\sigma_0 d}) \cdot \|f''\|_\infty$ (using
  $\mathrm{supp}\, f'' \subseteq [0, d]$). Both depend only on $\sigma_0, \sigma_1, d, f$;
  take $C$ to be their sum. To be formalised. -/)
  (latexEnv := "lemma")
  (discussion := 1487)]
theorem laplaceTransform_re_decay {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_nonneg : ∀ t, 0 ≤ f t)
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_derivWithin_0 : derivWithin f (.Icc 0 d) 0 = 0)
    (hf_derivWithin_d : derivWithin f (.Icc 0 d) d = 0)
    (hf_secondWithin_d :
      derivWithin (fun x ↦ derivWithin f (.Icc 0 d) x) (.Icc 0 d) d = 0)
    (σ₀ σ₁ : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → 1 ≤ |s.im| →
      |(laplaceTransform f s).re| ≤ C / s.im ^ 2 := by
  sorry

@[blueprint
  "kadiri-summable-lap-at-zeros"
  (title := "Summability of $\\sum_\\rho \\Re F(s - \\rho)$")
  (statement := /-- Under the hypotheses of \ref{kadiri-prop-2-1}, the sum
  $\sum_{\rho \in Z(\zeta)} \Re F(s - \rho)$ over the non-trivial zeros of $\zeta$ is
  convergent (Lean: `Summable`). -/)
  (proof := /-- Combine \ref{kadiri-laplace-re-decay} (giving $|\Re F(s-\rho)| \leq
  C/|\Im(s-\rho)|^2 = C/(\Im s - \gamma)^2$ for $|\gamma|$ large, since the real part
  $\Re(s-\rho) = \Re s - \beta$ stays in the bounded strip $[\Re s - 1, \Re s]$) with
  \ref{kadiri-backlund-bound} (giving $N(T) \ll T \log T$, hence by Abel summation
  $\sum_{|\gamma| \geq 1} 1/|\gamma|^2 < \infty$). Bound finitely many small-$|\gamma|$
  terms by hand. To be formalised. -/)
  (latexEnv := "lemma")
  (discussion := 1477)]
theorem summable_lap_re_at_zeros {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_nonneg : ∀ t, 0 ≤ f t)
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_derivWithin_0 : derivWithin f (.Icc 0 d) 0 = 0)
    (hf_derivWithin_d : derivWithin f (.Icc 0 d) d = 0)
    (hf_secondWithin_d :
      derivWithin (fun x ↦ derivWithin f (.Icc 0 d) x) (.Icc 0 d) d = 0)
    (s : ℂ) :
    Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) ↦
                (laplaceTransform f (s - ρ.val)).re) := by
  sorry

@[blueprint
  "kadiri-re-inner-eq"
  (title := "Inner real-part identity: collapsing to $T_1$")
  (statement := /-- For every $s \in \mathbb{C}$ with $\Re s > 1$,
  $$ \Re \Bigl( \sum_{n \geq 1} \frac{\Lambda(n)}{n^s} - \frac{1}{s - 1} \Bigr)
     + \sum_{\rho \in Z(\zeta)} \Re \frac{1}{s - \rho}
   = -\tfrac{1}{2} \log \pi
     + \tfrac{1}{2} \Re \tfrac{\Gamma'}{\Gamma}\!\left(\tfrac{s}{2}+1\right). $$
  This is the identity that turns the $f(0)$-coefficient of equation (16) into the $T_1$
  form of \ref{kadiri-prop-2-1}. -/)
  (proof := /-- For $\Re s > 1$ the Dirichlet series gives
  $\sum \Lambda(n)/n^s = -\zeta'/\zeta(s)$; apply \ref{kadiri-hadamard-identity} to rewrite
  the LHS (treating the equation as one in $\mathbb{C}$, not yet taking $\Re$). The
  $1/(s-1)$ and $\sum_\rho 1/(s-\rho)$ terms cancel, leaving
  $-B - \tfrac{1}{2}\log\pi + \tfrac{1}{2}\Gamma'/\Gamma(s/2+1) - \sum_\rho 1/\rho$.
  Taking real parts and applying \ref{kadiri-re-hadamardB-eq} cancels
  $\Re B + \sum_\rho \Re(1/\rho)$, leaving the claim. -/)
  (latexEnv := "lemma")
  (discussion := 1478)]
theorem re_inner_eq {s : ℂ} (hs : 1 < s.re) :
    ((∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s) - 1 / (s - 1)).re +
       (∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
         (1 / (s - ρ.val)).re) =
    -(1 / 2 : ℝ) * Real.log Real.pi +
      (1 / 2 : ℝ) * (digamma (s / 2 + 1)).re := by
  have hs1 : s ≠ 1 := by
    intro h
    norm_num [h] at hs
  have hsZ : s ∉ riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) := by
    intro hz
    have hlt : s.re < 1 := hz.1.2
    linarith
  have hD : -deriv riemannZeta s / riemannZeta s =
      ∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s := by
    rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
    dsimp [LSeries, LSeries.term]
    apply tsum_congr
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn, div_eq_mul_inv]
  have hH := hadamard_identity s hs1 hsZ
  rw [hD] at hH
  have hR := congrArg Complex.re hH
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im] at hR ⊢
  rw [hadamard_zero_log_sum_re_split hs, re_hadamardB_eq] at hR
  norm_num at hR ⊢
  linear_combination hR

/-! ## Named terms from Kadiri's explicit formula

The "gamma" term `T₁`, the "remainder" term `T₂`, and the difference operators `D`, `Δ₁`, `Δ₂`
are introduced in \cite[§2.1]{Kadiri2005} to package the RHS of (4) for use in the trigonometric
positivity argument. These are real-valued functions of a complex parameter. -/

/-- $T_1(s) := -\tfrac{1}{2} \log \pi + \tfrac{1}{2} \Re(\Gamma'/\Gamma)(s/2 + 1)$ — the "gamma"
contribution to the RHS of \cite[(4)]{Kadiri2005} (the term multiplied by $f(0)$ there). -/
noncomputable def T1 (s : ℂ) : ℝ :=
  -(1 / 2 : ℝ) * Real.log Real.pi + (1 / 2 : ℝ) * (digamma (s / 2 + 1)).re

/-- $T_2(s)$ — the contour-integral and boundary contributions to the RHS of
\cite[(4)]{Kadiri2005}, expressed via $F_2$, the Laplace transform of $f''$. -/
noncomputable def T2 (f : ℝ → ℝ) (s : ℂ) : ℝ :=
  ((1 / (2 * (Real.pi : ℂ))) *
    (∫ t : ℝ,
      ((digamma ((1 / 2 + (t : ℂ) * I) / 2)).re : ℂ) *
        laplaceTransform (fun u ↦ deriv (deriv f) u) (s - (1 / 2 + (t : ℂ) * I))
        / (s - (1 / 2 + (t : ℂ) * I)) ^ 2)
    + laplaceTransform (fun u ↦ deriv (deriv f) u) s / s ^ 2).re

/-- $D_{\kappa, \delta}(s) := \Re F(s) - \kappa \Re F(s + \delta)$ — the difference operator
applied to $\Re F$ from \cite[§2.1]{Kadiri2005}. -/
noncomputable def D (f : ℝ → ℝ) (κ δ : ℝ) (s : ℂ) : ℝ :=
  (laplaceTransform f s).re - κ * (laplaceTransform f (s + (δ : ℂ))).re

/-- $\Delta_1(s) := T_1(s) - \kappa T_1(s + \delta)$ — the difference operator applied to $T_1$. -/
noncomputable def Δ1 (κ δ : ℝ) (s : ℂ) : ℝ :=
  T1 s - κ * T1 (s + (δ : ℂ))

/-- $\Delta_2(s) := T_2(s) - \kappa T_2(s + \delta)$ — the difference operator applied to $T_2$. -/
noncomputable def Δ2 (f : ℝ → ℝ) (κ δ : ℝ) (s : ℂ) : ℝ :=
  T2 f s - κ * T2 f (s + (δ : ℂ))

/-! ## Proposition 2.1 of `Kadiri2005` (the explicit formula)

Assembled from \ref{kadiri-identity-16}, \ref{kadiri-re-inner-eq}, and
\ref{kadiri-summable-lap-at-zeros}. -/

@[blueprint
  "kadiri-prop-2-1"
  (title := "Explicit formula (Kadiri 2005, Prop.~2.1)")
  (statement := /-- Let $d > 0$ and let $f \colon [0, d] \to \mathbb{R}$ be a non-negative
  function of class $C^2$ on $[0, d]$, compactly supported in $[0, d)$, satisfying the
  one-sided boundary conditions $f(d) = f'(0) = f'(d) = f''(d) = 0$ (hypothesis $(H_1)$ of
  \cite{Kadiri2005}).
  Let $F$ denote its Laplace transform $F(s) = \int_0^d e^{-s t} f(t)\, dt$, and let $F_2$
  denote the Laplace transform of $f''$. Then for every $s \in \mathbb{C}$ with $\Re s > 1$,
  the sum $\sum_{\rho \in Z(\zeta)} \Re F(s - \rho)$ over the non-trivial zeros is convergent,
  and
  $$ \Re \sum_{n \geq 1} \frac{\Lambda(n)}{n^s} f(\log n)
    = f(0) \left( -\tfrac{1}{2} \log \pi
        + \tfrac{1}{2} \Re \tfrac{\Gamma'}{\Gamma}\!\left(\tfrac{s}{2} + 1\right) \right)
    + \Re F(s - 1) - \sum_{\rho \in Z(\zeta)} \Re F(s - \rho)
    + \Re \left( \frac{1}{2 \pi i} \int_{1/2 - i \infty}^{1/2 + i \infty}
        \Re \tfrac{\Gamma'}{\Gamma}\!\left(\tfrac{z}{2}\right) \frac{F_2(s - z)}{(s - z)^2}\, dz
        + \frac{F_2(s)}{s^2} \right), $$
  where $Z(\zeta)$ is the set of non-trivial zeros of $\zeta$ (those in the open critical strip
  $0 < \Re \rho < 1$). The half-plane $\Re s > 1$ is the range used in Kadiri's
  zero-free-region argument; the harmonic-extension step that would lift the identity to all
  of $\mathbb{C}$ is not needed for that application. -/)
  (proof := /-- The `Summable` conjunct is \ref{kadiri-summable-lap-at-zeros}.
  For the identity, combine \ref{kadiri-identity-16} (the (16)-form on $\Re s > 1$) with
  \ref{kadiri-re-inner-eq} (which substitutes the $T_1$ form for the $f(0)$-coefficient
  $\Re$-expression, also on $\Re s > 1$). The result is a two-line `rw` chain. -/)
  (latexEnv := "proposition")
  (discussion := 1478)]
theorem prop_2_1 {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hf_nonneg : ∀ t, 0 ≤ f t)
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d))
    (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0)
    (hf_derivWithin_0 : derivWithin f (.Icc 0 d) 0 = 0)
    (hf_derivWithin_d : derivWithin f (.Icc 0 d) d = 0)
    (hf_secondWithin_d :
      derivWithin (fun x ↦ derivWithin f (.Icc 0 d) x) (.Icc 0 d) d = 0)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) ↦
                (laplaceTransform f (s - ρ.val)).re) ∧
    (∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s * ((f (Real.log n) : ℝ) : ℂ)).re =
      f 0 * T1 s
        + (laplaceTransform f (s - 1)).re
        - ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) .univ,
            (laplaceTransform f (s - ρ.val)).re
        + T2 f s := by
  refine ⟨summable_lap_re_at_zeros hd hf_nonneg hf_C2 hf_supp hf_d hf_derivWithin_0
      hf_derivWithin_d hf_secondWithin_d s, ?_⟩
  rw [identity_16 hd hf_nonneg hf_C2 hf_supp hf_d hf_derivWithin_0 hf_derivWithin_d
      hf_secondWithin_d hs, re_inner_eq hs]
  simp [T1, T2]

/-! ## Equation (5) of `Kadiri2005`: the "damped" explicit formula -/

@[blueprint
  "kadiri-eq-5"
  (title := "Damped explicit formula (Kadiri 2005, eq.~(5))")
  (statement := /-- For $f$ as in \ref{kadiri-prop-2-1}, real parameters $\kappa, \delta$, and
  $s \in \mathbb{C}$, set
  $$ \Delta_1(s) := T_1(s) - \kappa T_1(s + \delta), \qquad
     \Delta_2(s) := T_2(s) - \kappa T_2(s + \delta), \qquad
     D(s) := \Re F(s) - \kappa \Re F(s + \delta), $$
  where $T_1, T_2$ are the "gamma" and "remainder" contributions to the RHS of
  \ref{kadiri-prop-2-1}. Then
  $$ \Re \sum_{n \geq 1} \frac{\Lambda(n)}{n^s} f(\log n) \left( 1 - \frac{\kappa}{n^\delta} \right)
       = f(0) \Delta_1(s) + D(s - 1) - \sum_{\rho \in Z(\zeta)} D(s - \rho) + \Delta_2(s). $$
  -/)
  (proof := /-- Direct substitution: apply \ref{kadiri-prop-2-1} at $s$ and at $s + \delta$,
  multiply the latter by $\kappa$, subtract, and use the identity
  $n^{-s} - \kappa n^{-(s + \delta)} = n^{-s} (1 - \kappa n^{-\delta})$ to combine the LHS,
  while the definitions of $\Delta_1, \Delta_2, D$ combine the corresponding RHS terms. -/)
  (latexEnv := "lemma")
  (discussion := 1478)]
theorem eq_5 {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ} (hf_nonneg : ∀ t, 0 ≤ f t)
    (hf_C2 : ContDiffOn ℝ 2 f (.Icc 0 d)) (hf_supp : tsupport f ⊆ .Ico 0 d)
    (hf_d : f d = 0) (hf_derivWithin_0 : derivWithin f (.Icc 0 d) 0 = 0)
    (hf_derivWithin_d : derivWithin f (.Icc 0 d) d = 0)
    (hf_secondWithin_d :
      derivWithin (fun x ↦ derivWithin f (.Icc 0 d) x) (.Icc 0 d) d = 0)
    (κ : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, Λ n / n ^ s * f (Real.log n) * ((1 : ℂ) - κ / n ^ (δ : ℂ))).re =
      f 0 * Δ1 κ δ s + D f κ δ (s - 1)
        - ∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) .univ, D f κ δ (s - ρ.val) + Δ2 f κ δ s := by
  have hsδ : 1 < (s + δ).re := by
    simp only [Complex.add_re, Complex.ofReal_re]; linarith
  have h1 := prop_2_1 hd hf_nonneg hf_C2 hf_supp hf_d hf_derivWithin_0
    hf_derivWithin_d hf_secondWithin_d hs
  have h2 := prop_2_1 hd hf_nonneg hf_C2 hf_supp hf_d hf_derivWithin_0
    hf_derivWithin_d hf_secondWithin_d hsδ
  have hLHS :
      (∑' n : ℕ, Λ n / n ^ s * f (Real.log n) * ((1 : ℂ) - κ / n ^ (δ : ℂ))).re =
      (∑' n : ℕ, Λ n / (n : ℂ) ^ s * f (Real.log n)).re
        - κ * (∑' n : ℕ, Λ n / (n : ℂ) ^ (s + δ) * f (Real.log n)).re := by
    have hpoint (n : ℕ) :
        Λ n / n ^ s * f (Real.log n) * ((1 : ℂ) - κ / n ^ (δ : ℂ)) =
        Λ n / n ^ s * f (Real.log n) - κ * (Λ n / n ^ (s + δ) * f (Real.log n)) := by
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · rw [cpow_add s (δ : ℂ) (Nat.cast_ne_zero.mpr hn)]
        field_simp
    have h_complex :
        (∑' n : ℕ, Λ n / n ^ s * f (Real.log n) * ((1 : ℂ) - κ / n ^ (δ : ℂ))) =
        (∑' n : ℕ, Λ n / (n : ℂ) ^ s * f (Real.log n)) -
        (κ : ℂ) * (∑' n : ℕ, Λ n/ (n : ℂ) ^ (s + δ) * f (Real.log n)) := by
      simp_rw [hpoint]
      rw [((summable_f_log hf_supp _).hasSum.sub ((summable_f_log hf_supp _).mul_left
        (κ : ℂ)).hasSum).tsum_eq, tsum_mul_left]
    rw [h_complex, Complex.sub_re, Complex.re_ofReal_mul]
  have hZeros :
      (∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) .univ, D f κ δ (s - ρ.val)) =
      (∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) .univ,
          (laplaceTransform f (s - ρ.val)).re)
        - κ * (∑' ρ : riemannZeta.zeroes_rect (.Ioo 0 1) .univ,
                 (laplaceTransform f ((s + δ) - ρ.val)).re) := by
    have harg : ∀ ρ : riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ),
        (s - ρ.val) + δ = s + δ - ρ.val := fun _ ↦ by ring
    simp_rw [D, harg, (h1.1.hasSum.sub (h2.1.mul_left κ).hasSum).tsum_eq, tsum_mul_left]
  rw [hLHS, h1.2, h2.2, hZeros]
  simp only [Δ1, Δ2, D]
  ring_nf

end Kadiri
