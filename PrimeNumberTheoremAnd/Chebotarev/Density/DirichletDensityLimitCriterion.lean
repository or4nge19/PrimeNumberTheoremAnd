import PrimeNumberTheoremAnd.Chebotarev.Density.DirichletDensity
import Mathlib.Analysis.SpecificLimits.Normed

/-!
## A safe limit criterion for Dirichlet density ratios

This file provides a small analytic lemma that is used repeatedly in Chebotarev/Dirichlet
arguments:

If for `s → 1⁺` we can write

`ratioDefault S s = a + E s / seriesAll s`

with `‖E s‖` bounded and `‖seriesAll s‖ → ∞`,
then `ratioDefault S s → a`, i.e. `HasDensity S a`.

This isolates the *pure filter/normed-field* reasoning from the number-theoretic input.
-/

namespace PrimeNumberTheoremAnd
namespace DirichletDensity

open scoped Topology

open Filter

open Complex

theorem hasDensity_of_eq_add_div
    (S : Set ℕ) (a : ℂ) (E : ℝ → ℂ)
    (hEq :
      (fun s : ℝ ↦ ratioDefault S s) =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
        fun s ↦ a + E s / seriesAll s)
    (hBound : ∃ M : ℝ, (fun s : ℝ ↦ ‖E s‖) ≤ᶠ[nhdsWithin 1 (Set.Ioi 1)] fun _ ↦ M)
    (hDen : Tendsto (fun s : ℝ ↦ ‖seriesAll s‖) (nhdsWithin 1 (Set.Ioi 1)) atTop) :
    HasDensity S a := by
  rcases hBound with ⟨M, hM⟩
  -- It suffices to show `E s / seriesAll s → 0`.
  have hdiv :
      Tendsto (fun s : ℝ ↦ E s / seriesAll s) (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
    -- bound the norm by `M / ‖seriesAll s‖`
    have hle :
        (fun s : ℝ ↦ ‖E s / seriesAll s‖) ≤ᶠ[nhdsWithin 1 (Set.Ioi 1)]
          fun s ↦ M / ‖seriesAll s‖ := by
      filter_upwards [hM] with s hs
      -- `‖x / y‖ = ‖x‖ / ‖y‖` in a normed field
      have : ‖E s / seriesAll s‖ = ‖E s‖ / ‖seriesAll s‖ := by
        simp [div_eq_mul_inv, norm_inv]
      -- combine
      simpa [this, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (div_le_div_of_nonneg_right hs (by positivity : (0 : ℝ) ≤ ‖seriesAll s‖))
    -- `M / ‖seriesAll s‖ → 0` since `‖seriesAll s‖ → ∞`
    have hM0 : Tendsto (fun s : ℝ ↦ M / ‖seriesAll s‖) (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) :=
      (Filter.Tendsto.const_div_atTop hDen M)
    -- conclude by squeeze
    have hnorm0 :
        Tendsto (fun s : ℝ ↦ ‖E s / seriesAll s‖) (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hM0
        (Filter.Eventually.of_forall (fun s ↦ (norm_nonneg (E s / seriesAll s))))
        hle
    -- back to `E/seriesAll`
    simpa [tendsto_zero_iff_norm_tendsto_zero] using hnorm0
  -- Now `ratioDefault s → a` by adding a vanishing term.
  have hT :
      Tendsto (fun s : ℝ ↦ a + E s / seriesAll s) (nhdsWithin 1 (Set.Ioi 1)) (nhds a) := by
    simpa using (tendsto_const_nhds.add hdiv)
  exact hasDensity_of_tendsto_ratioDefault S a (hT.congr' hEq.symm)

end DirichletDensity
end PrimeNumberTheoremAnd
