import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.CanonicalProduct
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Data.Set.Countable
import Mathlib.Topology.LocallyFinsupp
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Order.Filter.Cofinite
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Complex.RemovableSingularity
import PrimeNumberTheoremAnd.Mathlib.Analysis.FromCarleson.Annulus
import Mathlib.Analysis.Complex.ValueDistribution.CountingFunction

/-!
# Hadamard factorization

This file is the start of the  refactor along the below guidelines:

- The final theorem should take intrinsic hypotheses on an entire function `f`, e.g.
  `EntireOfFiniteOrder ρ f`, and should **not** require a user-supplied `ZeroData`.
- The proof should internally obtain an enumeration of zeros (or an appropriate divisor) and
  then apply canonical product machinery.
-/

noncomputable section

namespace Complex.Hadamard

/-!
## Nonvanishing helpers for Weierstrass factors
-/

lemma weierstrassFactor_ne_zero_iff (m : ℕ) (z : ℂ) :
    weierstrassFactor m z ≠ 0 ↔ z ≠ 1 := by
  simpa [ne_eq] using (not_congr (weierstrassFactor_eq_zero_iff (m := m) (z := z)))

lemma weierstrassFactor_ne_zero_of_ne_one (m : ℕ) {z : ℂ} (hz : z ≠ 1) :
    weierstrassFactor m z ≠ 0 :=
  (weierstrassFactor_ne_zero_iff (m := m) (z := z)).2 hz

/-!
## Intrinsic divisor support: discreteness and countability

This is the first step needed to remove any external "zero enumeration" input:
for a meromorphic function, its divisor is a `Function.locallyFinsuppWithin`, hence has
discrete support; in a second-countable space (like `ℂ`), discrete sets are countable.
-/

open scoped Topology
open Set

/-!
## Divisor values vs analytic order (holomorphic functions)

For a holomorphic function, the intrinsic divisor multiplicity at `z`
agrees with `analyticOrderNatAt`.

This lets us recover multiplicities from `MeromorphicOn.divisor`, and is a prerequisite for removing
`ZeroData` from the API.
-/

lemma divisor_univ_eq_analyticOrderNatAt_int {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    MeromorphicOn.divisor f (Set.univ : Set ℂ) z = (analyticOrderNatAt f z : ℤ) := by
  -- `f` is meromorphic on `univ`
  have hmero : MeromorphicOn f (Set.univ : Set ℂ) := by
    intro w hw
    exact (Differentiable.analyticAt (f := f) hf w).meromorphicAt
  -- unfold divisor via `meromorphicOrderAt`
  simp [MeromorphicOn.divisor_apply hmero (by simp : z ∈ (Set.univ : Set ℂ)),
    analyticOrderNatAt]
  -- relate `meromorphicOrderAt` to `analyticOrderAt` for analytic functions
  have han : AnalyticAt ℂ f z := Differentiable.analyticAt (f := f) hf z
  -- case-split on `analyticOrderAt`
  cases h : analyticOrderAt f z with
  | top =>
      -- both sides are `0` by convention (`untop₀ ⊤ = 0`, `ENat.toNat ⊤ = 0`)
      simp [han.meromorphicOrderAt_eq, h]
  | coe n =>
      -- finite order: divisor is `n` (as an integer), and `analyticOrderNatAt` is `n`
      simp [han.meromorphicOrderAt_eq, h]

lemma divisor_support_countable {f : ℂ → ℂ} {U : Set ℂ} :
    (MeromorphicOn.divisor f U).support.Countable := by
  classical
  -- `support` is discrete within `U` (hence discrete as a subset of `ℂ`)
  have hdisc : IsDiscrete (MeromorphicOn.divisor f U).support := by
    simpa [MeromorphicOn.divisor] using
      (Function.locallyFinsuppWithin.discreteSupport (D := MeromorphicOn.divisor f U))
  -- In `ℂ` (second countable), every set is Lindelöf; discrete + Lindelöf ⇒ countable.
  have hlin : IsLindelof (MeromorphicOn.divisor f U).support :=
    HereditarilyLindelof_LindelofSets _
  exact hlin.countable_of_isDiscrete hdisc

lemma divisor_support_discrete {f : ℂ → ℂ} {U : Set ℂ} :
    IsDiscrete (MeromorphicOn.divisor f U).support := by
  classical
  simpa [MeromorphicOn.divisor] using
    (Function.locallyFinsuppWithin.discreteSupport (D := MeromorphicOn.divisor f U))

lemma exists_ball_inter_divisor_support_eq_singleton {f : ℂ → ℂ} (z₀ : ℂ)
    (hz₀ : z₀ ∈ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support) :
    ∃ ε > 0, Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀} := by
  simpa using
    Metric.exists_ball_inter_eq_singleton_of_mem_discrete
      (hs := divisor_support_discrete (f := f) (U := (Set.univ : Set ℂ))) hz₀

/-!
## Local finiteness on compacts (the cofinite-tail lemma)

For `D : Function.locallyFinsuppWithin U ℤ`, the support is *locally finite within `U`*.
Hence any compact `K ⊆ U` meets `D.support` only finitely often.

This is the main hypothesis we need later to obtain “eventually in `cofinite`” bounds for
divisor-indexed products.
-/

lemma divisor_support_inter_compact_finite {f : ℂ → ℂ} {U K : Set ℂ}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    (K ∩ (MeromorphicOn.divisor f U).support).Finite := by
  classical
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  -- For each `x ∈ K`, choose a neighborhood meeting `D.support` finitely.
  have hloc :
      ∀ x ∈ K, ∃ V : Set ℂ, V ∈ 𝓝 x ∧ Set.Finite (V ∩ D.support) := by
    intro x hxK
    rcases D.supportLocallyFiniteWithinDomain x (hKU hxK) with ⟨V, hV, hfin⟩
    exact ⟨V, hV, hfin⟩
  classical
  choose V hVnhds hVfin using hloc
  -- Extract a finite subcover of `K` by these neighborhoods.
  rcases hK.elim_nhds_subcover' (U := fun x hx => V x hx) (hU := fun x hx => hVnhds x hx) with ⟨t, ht⟩
  -- Reduce to a finite union of finite sets.
  have hsub :
      K ∩ D.support ⊆ ⋃ x ∈ t, (V (x : ℂ) x.2 ∩ D.support) := by
    intro y hy
    rcases hy with ⟨hyK, hyS⟩
    have hycov : y ∈ ⋃ x ∈ t, V (x : ℂ) x.2 := ht hyK
    rcases Set.mem_iUnion.1 hycov with ⟨x, hycov'⟩
    rcases Set.mem_iUnion.1 hycov' with ⟨hxT, hyV⟩
    refine Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ?_⟩
    exact ⟨hxT, ⟨hyV, hyS⟩⟩
  have hfinU :
      Set.Finite (⋃ x ∈ t, (V (x : ℂ) x.2 ∩ D.support)) := by
    -- finite union over a `Finset`
    classical
    refine (t.finite_toSet).biUnion ?_
    intro x hx
    -- `hVfin x x.2 : Set.Finite (V x x.2 ∩ D.support)`
    simpa using (hVfin (x : ℂ) x.2)
  exact hfinU.subset hsub

lemma exists_seq_eq_range_divisor_support {f : ℂ → ℂ} {U : Set ℂ}
    (hne : (MeromorphicOn.divisor f U).support.Nonempty) :
    ∃ a : ℕ → ℂ, (MeromorphicOn.divisor f U).support = Set.range a :=
  (divisor_support_countable (f := f) (U := U)).exists_eq_range hne

/-!
## A nonzero enumeration of the nonzero divisor support

For canonical products we want a sequence of *nonzero* points.  We therefore enumerate the set
`(divisor f U).support \ {0}`.  If this set is empty, we return the constant sequence `1`.
-/

lemma exists_nonzero_seq_divisor_support_diff_zero {f : ℂ → ℂ} {U : Set ℂ} :
    ∃ a : ℕ → ℂ,
      (∀ n, a n ≠ 0) ∧ (MeromorphicOn.divisor f U).support \ {0} ⊆ Set.range a := by
  classical
  set s : Set ℂ := (MeromorphicOn.divisor f U).support \ {0}
  by_cases hs : s.Nonempty
  · -- countable + nonempty ⇒ `s = range a`
    have hs_count : s.Countable := by
      have hsup : (MeromorphicOn.divisor f U).support.Countable :=
        divisor_support_countable (f := f) (U := U)
      refine hsup.mono ?_
      intro x hx
      exact hx.1
    rcases hs_count.exists_eq_range hs with ⟨a, ha⟩
    refine ⟨a, ?_, ?_⟩
    · intro n
      have : a n ∈ s := by
        have : a n ∈ Set.range a := ⟨n, rfl⟩
        simp [ha]
      exact fun h0 => this.2 (by simpa [Set.mem_singleton_iff] using h0)
    · simp [ha]
  · -- empty case
    refine ⟨fun _ => (1 : ℂ), ?_, ?_⟩
    · intro _; simp
    · have : s = ∅ := Set.not_nonempty_iff_eq_empty.1 hs
      simp [this]

/-!
## Canonical product indexed by the divisor (no external enumeration)

To reflect **multiplicities** without introducing a bespoke `ZeroData` structure, we use a sigma-type
index:

`Σ z : ℂ, Fin (Int.toNat ((divisor f U) z))`

This has exactly `Int.toNat ((divisor f U) z)` many “copies” of each point `z`.

We also exclude `z = 0` so that the origin can be split off as the `z^ord₀` factor in the final
Hadamard theorem.
-/

/-- Index type enumerating zeros (with multiplicity) via the divisor. -/
def divisorZeroIndex (f : ℂ → ℂ) (U : Set ℂ) : Type :=
  Σ z : ℂ, Fin (Int.toNat (MeromorphicOn.divisor f U z))

/-- The nonzero part of `divisorZeroIndex`. -/
abbrev divisorZeroIndex₀ (f : ℂ → ℂ) (U : Set ℂ) : Type :=
  {p : divisorZeroIndex f U // p.1 ≠ 0}

/-- The underlying point of a (nonzero) divisor index. -/
abbrev divisorZeroIndex₀_val {f : ℂ → ℂ} {U : Set ℂ} (p : divisorZeroIndex₀ f U) : ℂ :=
  p.1.1

@[simp] lemma divisorZeroIndex₀_val_ne_zero {f : ℂ → ℂ} {U : Set ℂ} (p : divisorZeroIndex₀ f U) :
    divisorZeroIndex₀_val p ≠ 0 := p.2

@[simp] lemma divisorZeroIndex₀_val_mem_divisor_support {f : ℂ → ℂ} {U : Set ℂ}
    (p : divisorZeroIndex₀ f U) :
    divisorZeroIndex₀_val p ∈ (MeromorphicOn.divisor f U).support := by
  classical
  -- if `Int.toNat (divisor ...) = 0`, then `Fin 0` is empty, contradiction
  have hn :
      Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀_val p)) ≠ 0 := by
    intro h0
    have q0 : Fin 0 := by
      -- `p.1.2 : Fin (Int.toNat ...)`
      simpa [divisorZeroIndex₀_val, h0] using p.1.2
    exact Fin.elim0 q0
  have hne :
      MeromorphicOn.divisor f U (divisorZeroIndex₀_val p) ≠ 0 := by
    intro hdiv
    have : Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀_val p)) = 0 := by
      simp [hdiv]
    exact hn this
  -- `support` is the set where the locally-finsupp function is nonzero
  simpa [Function.locallyFinsuppWithin.support, Function.support, divisorZeroIndex₀_val] using hne

lemma exists_ball_inter_divisor_support_eq_singleton_of_index
    {f : ℂ → ℂ} (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    ∃ ε > 0,
      Metric.ball (divisorZeroIndex₀_val p) ε ∩
          (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support =
        {divisorZeroIndex₀_val p} :=
  exists_ball_inter_divisor_support_eq_singleton (f := f) (z₀ := divisorZeroIndex₀_val p)
    (divisorZeroIndex₀_val_mem_divisor_support (p := p))

/-- The canonical product attached to the (nonzero) divisor of `f` on `U`. -/
def divisorCanonicalProduct (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) (z : ℂ) : ℂ :=
  ∏' p : divisorZeroIndex₀ f U, weierstrassFactor m (z / divisorZeroIndex₀_val p)

@[simp] lemma divisorCanonicalProduct_zero (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) :
    divisorCanonicalProduct m f U 0 = 1 := by
  classical
  -- each factor is `weierstrassFactor m 0 = 1`
  simp [divisorCanonicalProduct]

lemma divisorCanonicalProduct_ne_zero_at_zero (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) :
    divisorCanonicalProduct m f U 0 ≠ 0 := by
  simp [divisorCanonicalProduct_zero]

/-!
## Entire functions are never locally zero (under a global nontriviality witness)

If `f` is differentiable on `ℂ` and not identically zero, then it is not locally zero anywhere,
hence `analyticOrderAt f z ≠ ⊤` for all `z`.
-/

lemma analyticOrderAt_ne_top_of_exists_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0) :
    ∀ z : ℂ, analyticOrderAt f z ≠ ⊤ := by
  classical
  rcases hnot with ⟨z1, hz1⟩
  have hf_an : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) := by
    intro z hz
    exact (Differentiable.analyticAt (f := f) hf z)
  have hz1_not_top : analyticOrderAt f z1 ≠ ⊤ := by
    have : analyticOrderAt f z1 = 0 :=
      (hf.analyticAt z1).analyticOrderAt_eq_zero.2 hz1
    simp [this]
  intro z
  exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (hf := hf_an)
    (U := (Set.univ : Set ℂ)) (x := z1) (y := z) (by simpa using isPreconnected_univ)
    (by simp) (by simp) hz1_not_top

lemma divisorZeroIndex₀_val_eq_of_mem_ball
    {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ))
    (hp : divisorZeroIndex₀_val p ∈ Metric.ball z₀ ε) :
    divisorZeroIndex₀_val p = z₀ := by
  have hsupp : divisorZeroIndex₀_val p ∈ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support :=
    divisorZeroIndex₀_val_mem_divisor_support (p := p)
  have : divisorZeroIndex₀_val p ∈
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support := ⟨hp, hsupp⟩
  simpa [hball] using this

lemma weierstrassFactor_div_ne_zero_on_ball_of_val_ne
    (m : ℕ) {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (hp : divisorZeroIndex₀_val p ≠ z₀) :
    ∀ z ∈ Metric.ball z₀ ε, weierstrassFactor m (z / divisorZeroIndex₀_val p) ≠ 0 := by
  intro z hzball h0
  have hz_eq : z = divisorZeroIndex₀_val p := by
    have hdiv1 : z / divisorZeroIndex₀_val p = 1 := by
      simpa [weierstrassFactor_eq_zero_iff (m := m)] using h0
    have ha : divisorZeroIndex₀_val p ≠ 0 := divisorZeroIndex₀_val_ne_zero p
    exact (div_eq_one_iff_eq ha).1 hdiv1
  have hz_support :
      z ∈ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support := by
    simpa [hz_eq] using (divisorZeroIndex₀_val_mem_divisor_support (p := p))
  have hz0 : z = z₀ := by
    have : z ∈ Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support :=
      ⟨hzball, hz_support⟩
    simpa [hball] using this
  have : divisorZeroIndex₀_val p = z₀ := by
    calc
      divisorZeroIndex₀_val p = z := by simp [hz_eq]
      _ = z₀ := hz0
  exact hp this

lemma weierstrassFactor_div_ne_zero_on_ball_punctured
    (m : ℕ) {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀}) :
    ∀ z ∈ Metric.ball z₀ ε, z ≠ z₀ →
      ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        weierstrassFactor m (z / divisorZeroIndex₀_val p) ≠ 0 := by
  intro z hz hz0 p
  by_cases hp : divisorZeroIndex₀_val p = z₀
  · -- fiber case: `z / z₀ ≠ 1` since `z ≠ z₀`
    have hz1 : z / divisorZeroIndex₀_val p ≠ (1 : ℂ) := by
      -- `z / a = 1 ↔ z = a`
      have ha : divisorZeroIndex₀_val p ≠ 0 := divisorZeroIndex₀_val_ne_zero p
      simpa [hp] using (mt (div_eq_one_iff_eq ha).1 (by simpa [hp] using hz0))
    exact weierstrassFactor_ne_zero_of_ne_one (m := m) hz1
  · exact weierstrassFactor_div_ne_zero_on_ball_of_val_ne (m := m) (f := f) (z₀ := z₀)
        (ε := ε) hball p (by simpa using hp) z hz

/-!
## Units-valued factors on a punctured isolating ball

On a punctured ball around `z₀` whose intersection with the divisor support is `{z₀}`, every
Weierstrass factor `weierstrassFactor m (z / a)` is nonzero, hence can be viewed as a unit.

This is the entry-point for applying `tprod` splitting lemmas that require a **group** target.
-/

noncomputable def weierstrassFactorUnits
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) (ε : ℝ)
    (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (z : ℂ) (hz : z ∈ Metric.ball z₀ ε) (hz0 : z ≠ z₀) :
    divisorZeroIndex₀ f (Set.univ : Set ℂ) → Units ℂ :=
  fun p =>
    Units.mk0 (weierstrassFactor m (z / divisorZeroIndex₀_val p))
      (weierstrassFactor_div_ne_zero_on_ball_punctured (m := m) (f := f) (z₀ := z₀)
        (ε := ε) hball z hz hz0 p)

@[simp] lemma weierstrassFactorUnits_coe
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) (ε : ℝ)
    (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (z : ℂ) (hz : z ∈ Metric.ball z₀ ε) (hz0 : z ≠ z₀)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    ((weierstrassFactorUnits (m := m) (f := f) (z₀ := z₀) (ε := ε) hball z hz hz0 p : Units ℂ) : ℂ) =
      weierstrassFactor m (z / divisorZeroIndex₀_val p) := by
  simp [weierstrassFactorUnits]

/-!
## Finiteness of “small” divisor indices

Fix `B` and assume `closedBall 0 B ⊆ U`. Then only finitely many divisor indices have
`‖val‖ ≤ B`. This is the key step for producing “eventually in `cofinite`” statements on the
divisor-index type.
-/

lemma finite_divisorZeroIndex₀_subtype_norm_le {f : ℂ → ℂ} {U : Set ℂ} (B : ℝ)
    (hBU : Metric.closedBall (0 : ℂ) B ⊆ U) :
    Finite {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ B} := by
  classical
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have hK : IsCompact (Metric.closedBall (0 : ℂ) B) := isCompact_closedBall _ _
  have hpts0 : ((Metric.closedBall (0 : ℂ) B) ∩ D.support).Finite :=
    divisor_support_inter_compact_finite (f := f) (U := U) (K := Metric.closedBall (0 : ℂ) B) hK hBU
  -- restrict to nonzero points (so it matches `divisorZeroIndex₀`)
  set pts : Set ℂ := ((Metric.closedBall (0 : ℂ) B) ∩ D.support) \ {0}
  have hpts : pts.Finite := hpts0.diff
  -- `pts` is a finite type
  letI : Fintype pts := hpts.fintype
  -- A finite ambient type to inject into
  let T : Type := Σ z : pts, Fin (Int.toNat (D z.1))
  haveI : Finite T := by infer_instance

  -- Define the injection `S → T` explicitly.
  let F :
      {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ B} → T := fun p =>
    ⟨⟨divisorZeroIndex₀_val p.1, by
        -- membership proof: `val ∈ pts`
        have hball : divisorZeroIndex₀_val p.1 ∈ Metric.closedBall (0 : ℂ) B := by
          simpa [Metric.mem_closedBall, dist_zero_right] using p.2
        have hsupport : divisorZeroIndex₀_val p.1 ∈ D.support := by
          have hne_toNat :
              Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀_val p.1)) ≠ 0 := by
            intro h0
            -- rewrite the `Fin`-index using `h0`
            have hpfin :
                Fin (Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀_val p.1))) := by
              -- definitional change of notation: `D = divisor f U`
              simpa [D] using p.1.1.2
            have : Fin 0 := by simpa [h0] using hpfin
            exact Fin.elim0 this
          have hne_D : D (divisorZeroIndex₀_val p.1) ≠ 0 := by
            intro hD0
            apply hne_toNat
            simp [D, hD0]
          simpa [D, Function.locallyFinsuppWithin.support, Function.support] using hne_D
        have hne0 : divisorZeroIndex₀_val p.1 ≠ 0 := divisorZeroIndex₀_val_ne_zero p.1
        exact ⟨⟨hball, hsupport⟩, by simp [Set.mem_singleton_iff]⟩⟩,
      p.1.1.2⟩

  refine Finite.of_injective F ?_
  intro p q hpq
  apply Subtype.ext
  apply Subtype.ext
  have h' := (Sigma.mk.inj_iff.1 hpq)
  -- first components equal in `pts`, hence the underlying points are equal
  have hz : divisorZeroIndex₀_val p.1 = divisorZeroIndex₀_val q.1 :=
    congrArg Subtype.val h'.1
  -- now rebuild equality in the underlying sigma `divisorZeroIndex`
  apply (Sigma.mk.inj_iff).2
  refine ⟨hz, ?_⟩
  exact h'.2

lemma divisorZeroIndex₀_norm_le_finite {f : ℂ → ℂ} {U : Set ℂ} (B : ℝ)
    (hBU : Metric.closedBall (0 : ℂ) B ⊆ U) :
    ({p : divisorZeroIndex₀ f U | ‖divisorZeroIndex₀_val p‖ ≤ B} : Set _).Finite := by
  classical
  let s : Set (divisorZeroIndex₀ f U) := {p | ‖divisorZeroIndex₀_val p‖ ≤ B}
  haveI : Finite (↥s) := by
    simpa [s] using (finite_divisorZeroIndex₀_subtype_norm_le (f := f) (U := U) B hBU)
  exact Set.toFinite s

/-!
## Uniform convergence on compacts (Filters-first)

This is the “next PR step”: show uniform convergence of the divisor-indexed canonical product on
compacts under the standard summability hypothesis.

We state it for `U = univ` (the entire-function case), so no domain side-conditions are needed.
-/

theorem hasProdUniformlyOn_divisorCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ) {K : Set ℂ} (hK : IsCompact K)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    HasProdUniformlyOn
      (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
        weierstrassFactor m (z / divisorZeroIndex₀_val p))
      (divisorCanonicalProduct m f (Set.univ : Set ℂ)) K := by
  classical
  -- Bound `K` by a radius `R ≥ 1`.
  rcases (isBounded_iff_forall_norm_le.1 hK.isBounded) with ⟨R0, hR0⟩
  set R : ℝ := max R0 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hnormK : ∀ z ∈ K, ‖z‖ ≤ R := fun z hzK => le_trans (hR0 z hzK) (le_max_left _ _)

  -- Use the product M-test for `1 + (E_m(z/a) - 1)`.
  let g : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ :=
    fun p z => weierstrassFactor m (z / divisorZeroIndex₀_val p) - 1
  let u : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
    fun p => (4 * R ^ (m + 1)) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))
  have hu : Summable u := h_sum.mul_left (4 * R ^ (m + 1))

  -- Eventually (cofinitely), `‖val p‖ > 2R`, hence `‖z/val p‖ ≤ 1/2` for all `z ∈ K`.
  have h_big :
      ∀ᶠ p : divisorZeroIndex₀ f (Set.univ : Set ℂ) in Filter.cofinite,
        (2 * R : ℝ) < ‖divisorZeroIndex₀_val p‖ := by
    -- complement `{p | ‖val p‖ ≤ 2R}` is finite
    have hfin :
        ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ 2 * R} : Set _).Finite := by
      -- `closedBall ⊆ univ` is trivial
      have : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
      exact divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ)) (B := 2 * R) this
    -- translate “not ≤” into “<”
    have := hfin.eventually_cofinite_notMem
    -- `p ∉ {p | ‖val p‖ ≤ 2R}` means `¬ ‖val p‖ ≤ 2R`, i.e. `2R < ‖val p‖`
    filter_upwards [this] with p hp
    have : ¬ ‖divisorZeroIndex₀_val p‖ ≤ 2 * R := by simpa using hp
    exact lt_of_not_ge this

  have hBound :
      ∀ᶠ p in Filter.cofinite, ∀ z ∈ K, ‖g p z‖ ≤ u p := by
    filter_upwards [h_big] with p hp z hzK
    have hzle : ‖z‖ ≤ R := hnormK z hzK
    have ha_pos : 0 < ‖divisorZeroIndex₀_val p‖ := lt_trans (by nlinarith [hRpos]) hp
    have hz_div : ‖z / divisorZeroIndex₀_val p‖ ≤ (1 / 2 : ℝ) := by
      have ha_pos : 0 < ‖divisorZeroIndex₀_val p‖ := lt_trans (by nlinarith [hRpos]) hp
      have h2R_pos : 0 < (2 * R : ℝ) := by nlinarith [hRpos]
      have hinv : ‖divisorZeroIndex₀_val p‖⁻¹ < (2 * R)⁻¹ := by
        -- `2R < ‖a‖` ⇒ `‖a‖⁻¹ < (2R)⁻¹`
        simpa [one_div] using (one_div_lt_one_div_of_lt h2R_pos hp)
      have hmul_le : ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ ≤ R * ‖divisorZeroIndex₀_val p‖⁻¹ := by
        refine mul_le_mul_of_nonneg_right hzle ?_
        exact inv_nonneg.2 (norm_nonneg _)
      have hmul_lt : R * ‖divisorZeroIndex₀_val p‖⁻¹ < R * (2 * R)⁻¹ :=
        mul_lt_mul_of_pos_left hinv hRpos
      have hlt : ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ < R * (2 * R)⁻¹ :=
        lt_of_le_of_lt hmul_le hmul_lt
      have hRhalf : R * (2 * R)⁻¹ = (1 / 2 : ℝ) := by
        have hRne : (R : ℝ) ≠ 0 := hRpos.ne'
        -- rewrite as a division and clear denominators
        have : R * (2 * R)⁻¹ = R / (2 * R) := by simp [div_eq_mul_inv]
        rw [this]
        field_simp [hRne]
      -- `‖z / a‖ = ‖z‖ * ‖a‖⁻¹`
      have hnorm : ‖z / divisorZeroIndex₀_val p‖ = ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := by
        simp [div_eq_mul_inv]
      -- conclude
      have hzlt : ‖z / divisorZeroIndex₀_val p‖ < (1 / 2 : ℝ) := by
        calc
          ‖z / divisorZeroIndex₀_val p‖ = ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := hnorm
          _ < R * (2 * R)⁻¹ := hlt
          _ = (1 / 2 : ℝ) := hRhalf
      exact le_of_lt hzlt
    -- Apply the PR1 bound.
    have hE :
        ‖weierstrassFactor m (z / divisorZeroIndex₀_val p) - 1‖ ≤
          4 * ‖z / divisorZeroIndex₀_val p‖ ^ (m + 1) :=
      weierstrassFactor_sub_one_pow_bound (m := m) (z := z / divisorZeroIndex₀_val p) hz_div
    -- Bound `‖z/a‖^(m+1)` by `R^(m+1) * ‖a‖⁻¹^(m+1)`.
    have hz_pow :
        ‖z / divisorZeroIndex₀_val p‖ ^ (m + 1) ≤
          (R ^ (m + 1)) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
      have : ‖z / divisorZeroIndex₀_val p‖ = ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := by
        simp [div_eq_mul_inv]
      rw [this]
      -- expand power of a product and bound `‖z‖^(m+1) ≤ R^(m+1)`
      have : (‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹) ^ (m + 1) =
          ‖z‖ ^ (m + 1) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
        simp [mul_pow]
      rw [this]
      have hzle_pow : ‖z‖ ^ (m + 1) ≤ R ^ (m + 1) :=
        pow_le_pow_left₀ (norm_nonneg z) hzle (m + 1)
      gcongr
    -- finish
    dsimp [g, u]
    nlinarith [hE, hz_pow]

  have hcts : ∀ p, ContinuousOn (g p) K := by
    intro p
    -- First: `weierstrassFactor m` is continuous.
    have hcontE : Continuous (fun z : ℂ => weierstrassFactor m z) := by
      -- prove continuity of `partialLogSum` explicitly (finite sum of continuous terms)
      have hcontPL : Continuous (fun z : ℂ => partialLogSum m z) := by
        classical
        unfold partialLogSum
        refine continuous_finset_sum _ ?_
        intro k hk
        -- `z ↦ z^(k+1) / (k+1)` is continuous
        have hpow : Continuous fun z : ℂ => z ^ (k + 1) := continuous_pow (k + 1)
        -- multiply by the constant `(k+1)⁻¹`
        simpa [div_eq_mul_inv] using hpow.mul continuous_const
      -- now `weierstrassFactor` is built from continuous operations
      have hsub : Continuous fun z : ℂ => (1 : ℂ) - z := continuous_const.sub continuous_id
      have hexp : Continuous fun z : ℂ => Complex.exp (partialLogSum m z) :=
        Complex.continuous_exp.comp hcontPL
      simpa [weierstrassFactor] using hsub.mul hexp
    -- Then: `z ↦ z / a` is continuous for constant `a`.
    have hdiv : Continuous fun z : ℂ => z / divisorZeroIndex₀_val p := by
      -- `z / a = z * a⁻¹`
      simpa [div_eq_mul_inv] using (continuous_id.mul continuous_const)
    have hcont : Continuous fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p) :=
      hcontE.comp hdiv
    simpa [g] using hcont.continuousOn.sub continuous_const.continuousOn

  -- Apply the uniform product M-test (Filters API).
  have hprod :
      HasProdUniformlyOn (fun p z ↦ 1 + g p z) (fun z ↦ ∏' p, (1 + g p z)) K := by
    simpa using Summable.hasProdUniformlyOn_one_add (f := g) (u := u) (K := K) hK hu hBound hcts
  -- Rewrite `1 + g` and the limit back to `weierstrassFactor` / `divisorCanonicalProduct`.
  simpa [g, divisorCanonicalProduct, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    using hprod

/-!
## Entire-ness (holomorphy) of the divisor-indexed canonical product

We now upgrade the uniform-on-compacts convergence to **locally uniform on `univ`** and apply the
standard theorem that a locally uniform limit of holomorphic functions is holomorphic.
-/

theorem hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    HasProdLocallyUniformlyOn
      (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
        weierstrassFactor m (z / divisorZeroIndex₀_val p))
      (divisorCanonicalProduct m f (Set.univ : Set ℂ))
      (Set.univ : Set ℂ) := by
  classical
  -- locally uniform convergence follows from uniform convergence on every compact
  refine hasProdLocallyUniformlyOn_of_forall_compact (f := fun p z => weierstrassFactor m (z / divisorZeroIndex₀_val p))
      (g := divisorCanonicalProduct m f (Set.univ : Set ℂ)) (s := (Set.univ : Set ℂ))
      isOpen_univ ?_
  intro K hKU hK
  simpa using
    (hasProdUniformlyOn_divisorCanonicalProduct_univ (m := m) (f := f) (K := K) hK h_sum)

theorem differentiableOn_divisorCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    DifferentiableOn ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) := by
  classical
  -- Write convergence as a `TendstoLocallyUniformlyOn` of the finite partial products.
  have hloc :
      TendstoLocallyUniformlyOn
        (fun (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) =>
          ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p))
        (divisorCanonicalProduct m f (Set.univ : Set ℂ))
        Filter.atTop
        (Set.univ : Set ℂ) := by
    simpa [HasProdLocallyUniformlyOn] using
      (hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum)

  -- Each finite partial product is entire.
  have hF :
      ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in Filter.atTop,
        DifferentiableOn ℂ
          (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p))
          (Set.univ : Set ℂ) := by
    refine Filter.Eventually.of_forall ?_
    intro s
    have hdiff :
        Differentiable ℂ
          (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p)) := by
      -- Help typeclass inference by naming the factor function.
      let F : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ :=
        fun p z => weierstrassFactor m (z / divisorZeroIndex₀_val p)
      have hF' : ∀ p ∈ s, Differentiable ℂ (F p) := by
        intro p hp
        -- `z ↦ weierstrassFactor m z` is differentiable (PR1), and `z ↦ z / a` is affine.
        have hdiv : Differentiable ℂ (fun z : ℂ => z / divisorZeroIndex₀_val p) := by
          have : Differentiable ℂ (fun z : ℂ => z * ((divisorZeroIndex₀_val p)⁻¹)) :=
            (differentiable_id : Differentiable ℂ (fun z : ℂ => z)).mul_const ((divisorZeroIndex₀_val p)⁻¹)
          simp [div_eq_mul_inv]
        exact (differentiable_weierstrassFactor m).comp hdiv
      -- Apply the finite-product rule.
      simpa [F] using (Differentiable.fun_finset_prod (𝕜 := ℂ) (f := F) (u := s) hF')
    simpa using hdiff.differentiableOn

  -- Holomorphy of the limit.
  haveI : (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))).NeBot :=
    Filter.atTop_neBot
  exact hloc.differentiableOn hF isOpen_univ

/-!
## Basic correctness: the divisor canonical product vanishes at indexed zeros

This is an important sanity check for the intrinsic construction: if one of the factors is `0` at
`z`, then the whole infinite product is `0`.
-/

theorem divisorCanonicalProduct_eq_zero_of_exists
    (m : ℕ) (f : ℂ → ℂ) (z : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (h0 : ∃ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
      weierstrassFactor m (z / divisorZeroIndex₀_val p) = 0) :
    divisorCanonicalProduct m f (Set.univ : Set ℂ) z = 0 := by
  classical
  -- Get pointwise `HasProd` from locally uniform convergence.
  have hloc :
      HasProdLocallyUniformlyOn
        (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (w : ℂ) =>
          weierstrassFactor m (w / divisorZeroIndex₀_val p))
        (divisorCanonicalProduct m f (Set.univ : Set ℂ))
        (Set.univ : Set ℂ) :=
    hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
  have hprod :
      HasProd (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
          weierstrassFactor m (z / divisorZeroIndex₀_val p))
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) :=
    hloc.hasProd (by simp : z ∈ (Set.univ : Set ℂ))
  -- If any factor is zero, then the whole product is zero.
  have hzero :
      HasProd (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
          weierstrassFactor m (z / divisorZeroIndex₀_val p))
        0 := by
    -- Use the general lemma for products in a commutative monoid-with-zero (`ℂ`).
    refine hasProd_zero_of_exists_eq_zero (L := (SummationFilter.unconditional
      (divisorZeroIndex₀ f (Set.univ : Set ℂ)))) ?_
    rcases h0 with ⟨p, hp⟩
    exact ⟨p, hp⟩
  -- Uniqueness of limits in a `T2Space` gives the result.
  exact (hprod.unique hzero)

theorem divisorCanonicalProduct_eq_zero_at_index
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    divisorCanonicalProduct m f (Set.univ : Set ℂ) (divisorZeroIndex₀_val p) = 0 := by
  classical
  refine divisorCanonicalProduct_eq_zero_of_exists (m := m) (f := f) (z := divisorZeroIndex₀_val p) h_sum ?_
  refine ⟨p, ?_⟩
  -- At `z = ρ`, the factor becomes `weierstrassFactor m 1 = 0`.
  have hp0 : divisorZeroIndex₀_val p ≠ 0 := p.property
  -- We unfold `weierstrassFactor` to avoid depending on simp-normal-form details.
  simp [hp0, weierstrassFactor]

/-!
## Atomic order lemma: a single factor has a simple zero at its prescribed point

This is a key input for the eventual multiplicity statement for the full canonical product:
the factor indexed by a nonzero `a` has analytic order exactly `1` at `z = a`.
-/

theorem analyticOrderAt_weierstrassFactor_div_self (m : ℕ) {a : ℂ} (ha : a ≠ 0) :
    analyticOrderAt (fun z : ℂ => weierstrassFactor m (z / a)) a = (1 : ℕ∞) := by
  set F : ℂ → ℂ := fun z => weierstrassFactor m (z / a)
  have hF : AnalyticAt ℂ F a := by
    have hdiv : Differentiable ℂ (fun z : ℂ => z / a) := by
      simp [div_eq_mul_inv]
    have hdiff : Differentiable ℂ F := (differentiable_weierstrassFactor m).comp hdiv
    exact Differentiable.analyticAt (f := F) hdiff a
  -- Identify the order via an explicit local factorization `F(z) = (z-a) * g(z)` with `g(a) ≠ 0`.
  -- Choose `g(z) := (-a⁻¹) * exp (partialLogSum m (z / a))`.
  let g : ℂ → ℂ := fun z => (-a⁻¹) * Complex.exp (partialLogSum m (z / a))
  have hg : AnalyticAt ℂ g a := by
    have hdiv : Differentiable ℂ (fun z : ℂ => z / a) := by
      simp [div_eq_mul_inv]
    have hpls : Differentiable ℂ (fun z : ℂ => partialLogSum m (z / a)) :=
      (differentiable_partialLogSum m).comp hdiv
    have hexp : Differentiable ℂ (fun z : ℂ => Complex.exp (partialLogSum m (z / a))) :=
      (Complex.differentiable_exp).comp hpls
    have hdiffg : Differentiable ℂ g := by
      simpa [g] using hexp.const_mul (-a⁻¹ : ℂ)
    exact Differentiable.analyticAt (f := g) hdiffg a
  have hg0 : g a ≠ 0 := by
    have hconst : (-a⁻¹ : ℂ) ≠ 0 := by simp [ha]
    have hexp0 : Complex.exp (partialLogSum m (a / a)) ≠ 0 :=
      Complex.exp_ne_zero (partialLogSum m (a / a))
    simpa [g] using mul_ne_zero hconst hexp0
  refine (hF.analyticOrderAt_eq_natCast (n := 1)).2 ?_
  refine ⟨g, hg, hg0, ?_⟩
  refine Filter.Eventually.of_forall ?_
  intro z
  have hlin : (1 - z / a) = (z - a) * (-a⁻¹) := by
    have h1 : (1 : ℂ) = a * a⁻¹ := by simp [ha]
    simp [div_eq_mul_inv, h1]
    ring
  simp [F, weierstrassFactor, g, pow_one, hlin, mul_assoc]

theorem analyticOrderNatAt_weierstrassFactor_div_self (m : ℕ) {a : ℂ} (ha : a ≠ 0) :
    analyticOrderNatAt (fun z : ℂ => weierstrassFactor m (z / a)) a = 1 := by
  simp [analyticOrderNatAt, analyticOrderAt_weierstrassFactor_div_self (m := m) ha]

/-!
## Finite product multiplicity at a point

For a finite product of elementary factors indexed by divisor-indices, the analytic order at `z₀`
equals the number of indices whose value is exactly `z₀`.

This is the finite (combinatorial) core that we will later combine with locally-uniform convergence
to reason about the infinite divisor-indexed product.
-/

theorem analyticOrderAt_finset_prod_weierstrassFactor_divisorZeroIndex₀
    (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z₀ : ℂ) :
    analyticOrderAt
        (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p))
        z₀
      =
      ((s.filter (fun p => divisorZeroIndex₀_val p = z₀)).card : ℕ∞) := by
  classical
  -- Finset induction
  refine Finset.induction_on s ?base ?step
  · -- empty: constant 1, order 0, filter card 0
    simp [analyticOrderAt_eq_zero]
  · intro p s hp hs
    -- split according to whether this new factor vanishes at `z₀`
    by_cases hEq : divisorZeroIndex₀_val p = z₀
    · -- contributes +1 to the order
      have hp0 : divisorZeroIndex₀_val p ≠ 0 := p.property
      -- use multiplicativity of analytic order for products
      -- write product as `fac * rest`
      have han_fac :
          AnalyticAt ℂ (fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p)) z₀ := by
        have hdiv : Differentiable ℂ (fun z : ℂ => z / divisorZeroIndex₀_val p) := by
          simp [div_eq_mul_inv]
        have hdiff :
            Differentiable ℂ (fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p)) :=
          (differentiable_weierstrassFactor m).comp hdiv
        exact Differentiable.analyticAt (f := fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p)) hdiff z₀
      have han_rest :
          AnalyticAt ℂ (fun z : ℂ => ∏ q ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val q)) z₀ := by
        -- finite product of analytic functions is analytic
        have hdiff :
            Differentiable ℂ (fun z : ℂ => ∏ q ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val q)) := by
          let F : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ :=
            fun q z => weierstrassFactor m (z / divisorZeroIndex₀_val q)
          have hF : ∀ q ∈ s, Differentiable ℂ (F q) := by
            intro q hq
            have hdiv : Differentiable ℂ (fun z : ℂ => z / divisorZeroIndex₀_val q) := by
              simp [div_eq_mul_inv]
            exact (differentiable_weierstrassFactor m).comp hdiv
          simpa [F] using (Differentiable.fun_finset_prod (𝕜 := ℂ) (f := F) (u := s) hF)
        exact Differentiable.analyticAt (f := fun z : ℂ => ∏ q ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val q)) hdiff z₀
      -- now compute the order of the product
      let fac : ℂ → ℂ := fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p)
      let rest : ℂ → ℂ := fun z : ℂ => ∏ q ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val q)
      have hmul :
          analyticOrderAt (fac * rest) z₀ =
            analyticOrderAt fac z₀ + analyticOrderAt rest z₀ := by
        simpa [fac, rest] using (analyticOrderAt_mul (z₀ := z₀) han_fac han_rest)
      -- finish by simp-rewriting the finset product and filter-card update
      -- LHS product is exactly the inserted-product
      -- RHS card adds 1 when `p` matches `z₀`
      have hcard :
          (Finset.filter (fun q => divisorZeroIndex₀_val q = z₀) (insert p s)).card =
            (Finset.filter (fun q => divisorZeroIndex₀_val q = z₀) s).card + 1 := by
        -- `p` is not in `s` and it satisfies the predicate.
        simp [hEq, hp, Finset.filter_insert]
      have hfac : analyticOrderAt fac z₀ = (1 : ℕ∞) := by
        simpa [fac, hEq] using
          (analyticOrderAt_weierstrassFactor_div_self (m := m) (a := divisorZeroIndex₀_val p) hp0)
      have hrest : analyticOrderAt rest z₀ = ((s.filter (fun q => divisorZeroIndex₀_val q = z₀)).card : ℕ∞) := by
        simpa [rest] using hs
      have hcongr :
          (fun z : ℂ => ∏ q ∈ insert p s, weierstrassFactor m (z / divisorZeroIndex₀_val q))
            =ᶠ[𝓝 z₀] (fac * rest) := by
        refine Filter.Eventually.of_forall ?_
        intro z
        -- `Finset.prod_insert` gives the factor times the rest, and `(*)` on functions is pointwise.
        simp [fac, rest, Finset.prod_insert, hp, Pi.mul_apply]
      calc
        analyticOrderAt (fun z : ℂ => ∏ q ∈ insert p s, weierstrassFactor m (z / divisorZeroIndex₀_val q)) z₀
            =
            analyticOrderAt (fac * rest) z₀ := by
              simpa using (analyticOrderAt_congr hcongr)
        _ = analyticOrderAt fac z₀ + analyticOrderAt rest z₀ := hmul
        _ = (1 : ℕ∞) + ((s.filter (fun q => divisorZeroIndex₀_val q = z₀)).card : ℕ∞) := by
              simp [hfac, hrest]
        _ = (((insert p s).filter (fun q => divisorZeroIndex₀_val q = z₀)).card : ℕ∞) := by
              -- use the card update lemma
              simp [hcard, Nat.add_comm]
    · -- factor is nonzero at `z₀`, contributes 0 to order; card unchanged
      have han_fac :
          AnalyticAt ℂ (fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p)) z₀ := by
        have hdiv : Differentiable ℂ (fun z : ℂ => z / divisorZeroIndex₀_val p) := by
          simp [div_eq_mul_inv]
        have hdiff :
            Differentiable ℂ (fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p)) :=
          (differentiable_weierstrassFactor m).comp hdiv
        exact Differentiable.analyticAt (f := fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p)) hdiff z₀
      have hfac0 :
          analyticOrderAt (fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p)) z₀ = 0 := by
        have hp0 : divisorZeroIndex₀_val p ≠ 0 := p.property
        have hval : weierstrassFactor m (z₀ / divisorZeroIndex₀_val p) ≠ 0 := by
          have : (z₀ / divisorZeroIndex₀_val p) ≠ 1 := by
            intro h1
            have : z₀ = divisorZeroIndex₀_val p := by
              have : z₀ = (z₀ / divisorZeroIndex₀_val p) * (divisorZeroIndex₀_val p) := by
                simp [div_eq_mul_inv]
              simpa [h1, div_eq_mul_inv, hp0] using this
            exact hEq (this.symm)
          -- `weierstrassFactor m w = (1 - w) * exp (...)` and `exp` never vanishes.
          have h1w : (1 - (z₀ / divisorZeroIndex₀_val p)) ≠ 0 := by
            -- `w ≠ 1` implies `1 - w ≠ 0`
            simpa [sub_eq_zero] using this.symm
          have hexp : Complex.exp (partialLogSum m (z₀ / divisorZeroIndex₀_val p)) ≠ 0 :=
            Complex.exp_ne_zero _
          -- finish
          simpa [weierstrassFactor] using mul_ne_zero h1w hexp
        simpa using (han_fac.analyticOrderAt_eq_zero).2 (by simpa using hval)
      -- card unchanged when predicate false
      have hcard :
          (Finset.filter (fun q => divisorZeroIndex₀_val q = z₀) (insert p s)).card =
            (Finset.filter (fun q => divisorZeroIndex₀_val q = z₀) s).card := by
        simp [hEq, Finset.filter_insert]
      -- now finish: order is same as rest
      have han_rest :
          AnalyticAt ℂ (fun z : ℂ => ∏ q ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val q)) z₀ := by
        have hdiff :
            Differentiable ℂ (fun z : ℂ => ∏ q ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val q)) := by
          let F : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ :=
            fun q z => weierstrassFactor m (z / divisorZeroIndex₀_val q)
          have hF : ∀ q ∈ s, Differentiable ℂ (F q) := by
            intro q hq
            have hdiv : Differentiable ℂ (fun z : ℂ => z / divisorZeroIndex₀_val q) := by
              simp [div_eq_mul_inv]
            exact (differentiable_weierstrassFactor m).comp hdiv
          simpa [F] using (Differentiable.fun_finset_prod (𝕜 := ℂ) (f := F) (u := s) hF)
        exact Differentiable.analyticAt (f := fun z : ℂ => ∏ q ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val q)) hdiff z₀
      let fac : ℂ → ℂ := fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p)
      let rest : ℂ → ℂ := fun z : ℂ => ∏ q ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val q)
      have hmul :
          analyticOrderAt (fac * rest) z₀ =
            analyticOrderAt fac z₀ + analyticOrderAt rest z₀ := by
        simpa [fac, rest] using (analyticOrderAt_mul (z₀ := z₀) han_fac han_rest)
      have hcongr :
          (fun z : ℂ => ∏ q ∈ insert p s, weierstrassFactor m (z / divisorZeroIndex₀_val q))
            =ᶠ[𝓝 z₀] (fac * rest) := by
        refine Filter.Eventually.of_forall ?_
        intro z
        simp [fac, rest, Finset.prod_insert, hp, Pi.mul_apply]
      calc
        analyticOrderAt (fun z : ℂ => ∏ q ∈ insert p s, weierstrassFactor m (z / divisorZeroIndex₀_val q)) z₀
            =
            analyticOrderAt (fac * rest) z₀ := by
              simpa using (analyticOrderAt_congr hcongr)
        _ = analyticOrderAt rest z₀ := by
              calc
                analyticOrderAt (fac * rest) z₀ = analyticOrderAt fac z₀ + analyticOrderAt rest z₀ := hmul
                _ = analyticOrderAt rest z₀ := by
                      have hfac0' : analyticOrderAt fac z₀ = 0 := by
                        simpa [fac] using hfac0
                      simp [hfac0']
        _ = ((s.filter (fun q => divisorZeroIndex₀_val q = z₀)).card : ℕ∞) := by
              simpa [rest] using hs
        _ = (((insert p s).filter (fun q => divisorZeroIndex₀_val q = z₀)).card : ℕ∞) := by
              simpa using congrArg (fun n : ℕ => (n : ℕ∞)) hcard.symm

theorem analyticOrderNatAt_finset_prod_weierstrassFactor_divisorZeroIndex₀
    (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z₀ : ℂ) :
    analyticOrderNatAt
        (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p))
        z₀
      =
      (s.filter (fun p => divisorZeroIndex₀_val p = z₀)).card := by
  simpa [analyticOrderNatAt] using
    (congrArg ENat.toNat
      (analyticOrderAt_finset_prod_weierstrassFactor_divisorZeroIndex₀ (m := m) (f := f) (s := s) (z₀ := z₀)))

/-!
## The multiplicity fiber `{p | divisorZeroIndex₀_val p = z₀}` is finite

This is the intrinsic replacement for “multiplicity is finite”: it is literally a subtype of
`Fin (Int.toNat (divisor f z₀))`, hence finite, but we can also obtain it as a subset of a norm-bounded
set (and we already proved norm-bounded sets are finite).
-/

theorem divisorZeroIndex₀_fiber_finite (f : ℂ → ℂ) (z₀ : ℂ) :
    ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | divisorZeroIndex₀_val p = z₀} : Set _).Finite := by
  classical
  -- the fiber is contained in the norm-bounded set `{p | ‖val p‖ ≤ ‖z₀‖}`
  have hsub :
      ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | divisorZeroIndex₀_val p = z₀} : Set _)
        ⊆
        ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ ‖z₀‖} : Set _) := by
    intro p hp
    have : divisorZeroIndex₀_val p = z₀ := hp
    simp [this]
  -- norm-bounded sets are finite (proved earlier)
  have hfin :
      ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ ‖z₀‖} : Set _).Finite := by
    have : Metric.closedBall (0 : ℂ) ‖z₀‖ ⊆ (Set.univ : Set ℂ) := by simp
    simpa using (divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ)) (B := ‖z₀‖) this)
  exact hfin.subset hsub

noncomputable def divisorZeroIndex₀_fiberFinset (f : ℂ → ℂ) (z₀ : ℂ) :
    Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
  (divisorZeroIndex₀_fiber_finite (f := f) z₀).toFinset

@[simp] lemma mem_divisorZeroIndex₀_fiberFinset (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ ↔ divisorZeroIndex₀_val p = z₀ := by
  classical
  simp [divisorZeroIndex₀_fiberFinset]

/-!
## Fiber cardinality equals divisor multiplicity

The type `divisorZeroIndex₀ f U` is `Σ z, Fin (Int.toNat (divisor z))` with `z ≠ 0`.
Hence the fiber over a nonzero `z₀` has exactly `Int.toNat (divisor z₀)` elements.

This is the intrinsic replacement for any “multiplicity counting” done via `ZeroData`.
-/

lemma divisorZeroIndex₀_fiberFinset_card_eq_toNat_divisor (f : ℂ → ℂ) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    (divisorZeroIndex₀_fiberFinset (f := f) z₀).card
      =
      Int.toNat (MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀) := by
  classical
  -- abbreviate the fiber set
  let S : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := {p | divisorZeroIndex₀_val p = z₀}
  have hS : S.Finite := divisorZeroIndex₀_fiber_finite (f := f) z₀
  -- compute the cardinality of the fiber via an explicit equivalence to `Fin n`
  set n : ℕ := Int.toNat (MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀)
  have hcard : Nat.card S = n := by
    classical
    haveI : Fintype S := hS.fintype
    -- `S` (the fiber over `z₀`) is equivalent to `Fin n`
    let e : S ≃ Fin n :=
      { toFun := fun x =>
          cast
              (congrArg Fin <| by
                -- the index depends only on the first coordinate, and `x.2` says it is `z₀`
                have hx : divisorZeroIndex₀_val x.1 = z₀ := x.2
                simpa [n] using
                  congrArg (fun z => Int.toNat (MeromorphicOn.divisor f (Set.univ : Set ℂ) z)) hx
              )
              x.1.1.2
        invFun := fun q => ⟨⟨⟨z₀, q⟩, hz₀⟩, rfl⟩
        left_inv := by
          -- do the dependent bookkeeping by explicit cases, then use `Subtype.ext`.
          rintro ⟨p, hp⟩
          rcases p with ⟨⟨z, q⟩, hz⟩
          have hzEq : z = z₀ := by simpa [divisorZeroIndex₀_val] using hp
          subst hzEq
          -- equalities in subtypes ignore proof fields
          apply Subtype.ext
          apply Subtype.ext
          rfl
        right_inv := by
          intro q
          rfl }
    -- `Nat.card (Fin n) = n`
    have h := Nat.card_congr (α := S) (β := Fin n) e
    simpa using (h.trans (by simp))
  -- turn the `Nat.card` computation into the `Finset.card` computation
  have hSncard : S.ncard = n := by
    -- `Nat.card S = S.ncard`
    simpa [Nat.card_coe_set_eq] using hcard
  -- `fiberFinset` is `hS.toFinset`
  have hto : hS.toFinset = divisorZeroIndex₀_fiberFinset (f := f) z₀ := by
    rfl
  -- `S.ncard = card (toFinset)`
  have htoFinset : S.ncard = (divisorZeroIndex₀_fiberFinset (f := f) z₀).card := by
    -- avoid aggressive simp unfolding (it can hit recursion limits)
    have h' : S.ncard = hS.toFinset.card := Set.ncard_eq_toFinset_card S hS
    simpa [hto] using h'
  -- conclude
  exact htoFinset.symm.trans hSncard

lemma divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    (divisorZeroIndex₀_fiberFinset (f := f) z₀).card = analyticOrderNatAt f z₀ := by
  classical
  have hdiv :
      MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀ = (analyticOrderNatAt f z₀ : ℤ) :=
    divisor_univ_eq_analyticOrderNatAt_int (f := f) hf z₀
  -- `analyticOrderNatAt` is a natural number; rewrite the divisor via `Int.toNat`
  have htoNat : Int.toNat (MeromorphicOn.divisor f (Set.univ : Set ℂ) z₀) = analyticOrderNatAt f z₀ := by
    simp [hdiv]
  exact (divisorZeroIndex₀_fiberFinset_card_eq_toNat_divisor (f := f) (z₀ := z₀) hz₀).trans htoNat

lemma mem_divisorZeroIndex₀_fiberFinset_of_val_mem_ball
    {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ))
    (hp : divisorZeroIndex₀_val p ∈ Metric.ball z₀ ε) :
    p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ := by
  classical
  -- any divisor index whose value lies in the ball must equal `z₀`
  have : divisorZeroIndex₀_val p = z₀ :=
    divisorZeroIndex₀_val_eq_of_mem_ball (f := f) (z₀ := z₀) (ε := ε) hball p hp
  exact (mem_divisorZeroIndex₀_fiberFinset (f := f) (z₀ := z₀) p).2 this

lemma mem_divisorZeroIndex₀_fiberFinset_iff_val_mem_ball
    {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hε : 0 < ε)
    (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ ↔ divisorZeroIndex₀_val p ∈ Metric.ball z₀ ε := by
  classical
  constructor
  · intro hp
    have : divisorZeroIndex₀_val p = z₀ :=
      (mem_divisorZeroIndex₀_fiberFinset (f := f) (z₀ := z₀) p).1 hp
    simpa [this] using (Metric.mem_ball_self hε : z₀ ∈ Metric.ball z₀ ε)
  · intro hp
    exact mem_divisorZeroIndex₀_fiberFinset_of_val_mem_ball (f := f) (z₀ := z₀) (ε := ε) hball p hp

lemma not_mem_divisorZeroIndex₀_fiberFinset_iff_val_ne
    {f : ℂ → ℂ} (z₀ : ℂ) (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    p ∉ divisorZeroIndex₀_fiberFinset (f := f) z₀ ↔ divisorZeroIndex₀_val p ≠ z₀ := by
  classical
  simp [mem_divisorZeroIndex₀_fiberFinset]

lemma val_not_mem_ball_of_not_mem_fiberFinset
    {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hε : 0 < ε)
    (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ))
    (hp : p ∉ divisorZeroIndex₀_fiberFinset (f := f) z₀) :
    divisorZeroIndex₀_val p ∉ Metric.ball z₀ ε := by
  -- contrapositive using the `fiberFinset ↔ val ∈ ball` lemma
  intro hpball
  exact hp ((mem_divisorZeroIndex₀_fiberFinset_iff_val_mem_ball (f := f) (z₀ := z₀) (ε := ε) hε hball p).2 hpball)

lemma weierstrassFactor_div_ne_zero_on_ball_of_not_mem_fiberFinset
    (m : ℕ) {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ))
    (hp : p ∉ divisorZeroIndex₀_fiberFinset (f := f) z₀) :
    ∀ z ∈ Metric.ball z₀ ε, weierstrassFactor m (z / divisorZeroIndex₀_val p) ≠ 0 := by
  have hp' : divisorZeroIndex₀_val p ≠ z₀ :=
    (not_mem_divisorZeroIndex₀_fiberFinset_iff_val_ne (f := f) z₀ p).1 hp
  exact weierstrassFactor_div_ne_zero_on_ball_of_val_ne (m := m) (f := f) (z₀ := z₀) (ε := ε) hball p hp'

/-!
## The fiber finite product has the expected order at `z₀`

This expresses the finite multiplicity calculation for the specific finset corresponding to the fiber
`{p | divisorZeroIndex₀_val p = z₀}`.
-/

theorem analyticOrderAt_prod_fiberFinset
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) :
    analyticOrderAt
        (fun z : ℂ =>
          ∏ p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀,
            weierstrassFactor m (z / divisorZeroIndex₀_val p))
        z₀
      =
      ((divisorZeroIndex₀_fiberFinset (f := f) z₀).card : ℕ∞) := by
  classical
  -- Start from the general finset order lemma.
  have h :=
    analyticOrderAt_finset_prod_weierstrassFactor_divisorZeroIndex₀
      (m := m) (f := f) (s := divisorZeroIndex₀_fiberFinset (f := f) z₀) (z₀ := z₀)
  -- The filter on `val = z₀` is the whole finset, by definition of `fiberFinset`.
  have hfilter :
      (divisorZeroIndex₀_fiberFinset (f := f) z₀).filter (fun p => divisorZeroIndex₀_val p = z₀) =
        divisorZeroIndex₀_fiberFinset (f := f) z₀ := by
    ext p
    simp
  simpa [hfilter] using h

theorem analyticOrderNatAt_prod_fiberFinset
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) :
    analyticOrderNatAt
        (fun z : ℂ =>
          ∏ p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀,
            weierstrassFactor m (z / divisorZeroIndex₀_val p))
        z₀
      =
      (divisorZeroIndex₀_fiberFinset (f := f) z₀).card := by
  -- Convert from the `ℕ∞` statement using `toNat`.
  simpa [analyticOrderNatAt] using
    congrArg ENat.toNat (analyticOrderAt_prod_fiberFinset (m := m) (f := f) (z₀ := z₀))

/-!
## Partial products eventually contain the full fiber (and thus have the right order)

This is the first “finite → infinite” bridge: along the `atTop` filter on `Finset`, any fixed finite
subset is eventually contained in the running finset.
-/

theorem analyticOrderAt_partialProduct_eq_fiberCard_of_subset
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hs : divisorZeroIndex₀_fiberFinset (f := f) z₀ ⊆ s) :
    analyticOrderAt
        (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p))
        z₀
      =
      ((divisorZeroIndex₀_fiberFinset (f := f) z₀).card : ℕ∞) := by
  classical
  -- Start from the general `Finset` formula.
  have h :=
    analyticOrderAt_finset_prod_weierstrassFactor_divisorZeroIndex₀
      (m := m) (f := f) (s := s) (z₀ := z₀)
  -- Identify the filtered finset `{p ∈ s | val p = z₀}` with the fiber finset.
  have hfilter :
      s.filter (fun p => divisorZeroIndex₀_val p = z₀) =
        divisorZeroIndex₀_fiberFinset (f := f) z₀ := by
    ext p
    constructor
    · intro hp'
      have hpv : divisorZeroIndex₀_val p = z₀ := (Finset.mem_filter.mp hp').2
      -- membership in fiber finset follows from `hpv`
      simpa [mem_divisorZeroIndex₀_fiberFinset] using hpv
    · intro hp_fiber
      have hpv : divisorZeroIndex₀_val p = z₀ := (mem_divisorZeroIndex₀_fiberFinset (f := f) (z₀ := z₀) p).1 hp_fiber
      have hps : p ∈ s := hs (by simpa [mem_divisorZeroIndex₀_fiberFinset] using hpv)
      exact Finset.mem_filter.2 ⟨hps, hpv⟩
  -- Substitute into the order formula.
  simpa [hfilter] using h

theorem eventually_atTop_subset_fiberFinset
    (f : ℂ → ℂ) (z₀ : ℂ) :
    ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      divisorZeroIndex₀_fiberFinset (f := f) z₀ ⊆ s := by
  -- On `atTop`, all sufficiently large finsets contain a fixed finset.
  refine (Filter.eventually_atTop.2 ?_)
  refine ⟨divisorZeroIndex₀_fiberFinset (f := f) z₀, ?_⟩
  intro s hs
  exact hs

/-!
## Local factorization of partial products at `z₀`

If a partial product finset `s` contains the full fiber over `z₀`, then the partial product has
analytic order exactly `k = (fiberFinset.card)` at `z₀`, hence it factors locally as
`(z - z₀)^k • g z` with `g z₀ ≠ 0`.

This is the right interface for feeding into a future “infinite product has at least this order”
argument via locally uniform convergence and removable singularity.
-/

theorem exists_analyticAt_eq_pow_smul_of_partialProduct_contains_fiber
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hs : divisorZeroIndex₀_fiberFinset (f := f) z₀ ⊆ s) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
        (fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p))
          =ᶠ[𝓝 z₀]
          fun z : ℂ => (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card • g z := by
  classical
  -- Let `F` be the partial product.
  let F : ℂ → ℂ := fun z : ℂ => ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p)
  have hF_ana : AnalyticAt ℂ F z₀ := by
    -- finite product of analytic functions is analytic
    have hdiff : Differentiable ℂ F := by
      let Φ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ :=
        fun p z => weierstrassFactor m (z / divisorZeroIndex₀_val p)
      have hΦ : ∀ p ∈ s, Differentiable ℂ (Φ p) := by
        intro p hp
        have hdiv : Differentiable ℂ (fun z : ℂ => z / divisorZeroIndex₀_val p) := by
          simp [div_eq_mul_inv]
        exact (differentiable_weierstrassFactor m).comp hdiv
      simpa [F, Φ] using (Differentiable.fun_finset_prod (𝕜 := ℂ) (f := Φ) (u := s) hΦ)
    exact Differentiable.analyticAt (f := F) hdiff z₀
  -- We know the order is exactly the fiber card.
  have hOrder :
      analyticOrderAt F z₀ =
        ((divisorZeroIndex₀_fiberFinset (f := f) z₀).card : ℕ∞) := by
    -- use the computed order for finsets containing the fiber
    simpa [F] using
      (analyticOrderAt_partialProduct_eq_fiberCard_of_subset (m := m) (f := f) (z₀ := z₀) (s := s) hs)
  -- Use the `analyticOrderAt_eq_natCast` characterization at `n = card`.
  refine (hF_ana.analyticOrderAt_eq_natCast (n := (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)).1 ?_
  -- Rewrite `analyticOrderAt` as `n` using `hOrder`.
  -- `((card : ℕ) : ℕ∞)` is definitional `ENat` coercion.
  simp [hOrder]

/-!
## Partial products as a named function + their locally uniform convergence

This is a convenience API: many later arguments about multiplicities/quotients are easier to write
using a named partial product function rather than repeating `∏ p ∈ s, ...`.
-/

noncomputable def divisorPartialProduct (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) : ℂ :=
  ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p)

@[simp] lemma divisorPartialProduct_def (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) :
    divisorPartialProduct m f s z = ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p) :=
  rfl

/-!
## Splitting finite partial products into fiber vs complement

This is the finitary version of the “fiber × complement” split that will later be passed to the
limit in the infinite product.
-/

noncomputable def divisorComplementPartialProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) : ℂ :=
  by
    classical
    -- product over the complement, implemented by inserting `1` on the fiber indices
    exact
      ∏ p ∈ s,
        if p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ then (1 : ℂ)
        else weierstrassFactor m (z / divisorZeroIndex₀_val p)

@[simp] lemma divisorComplementPartialProduct_def
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) :
    divisorComplementPartialProduct m f z₀ s z =
      ∏ p ∈ s,
        if divisorZeroIndex₀_val p = z₀ then (1 : ℂ)
        else weierstrassFactor m (z / divisorZeroIndex₀_val p) := by
  classical
  simp [divisorComplementPartialProduct, mem_divisorZeroIndex₀_fiberFinset]

/-!
## Complement canonical product (fiber factors removed)

For a fixed point `z₀`, we often want to split the infinite product into a finite “fiber part”
(`val = z₀`, accounting for the multiplicity) and an infinite “complement part” (all other indices).

To keep the definition total and Mathlib-idiomatic, we implement the complement part by inserting
the neutral element `1` on the fiber indices.
-/

noncomputable def divisorComplementCanonicalProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) (z : ℂ) : ℂ :=
  by
    classical
    exact
      ∏' p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        if p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ then (1 : ℂ)
        else weierstrassFactor m (z / divisorZeroIndex₀_val p)

noncomputable def divisorComplementFactor
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) : ℂ :=
  by
    classical
    exact
      if p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ then (1 : ℂ)
      else weierstrassFactor m (z / divisorZeroIndex₀_val p)

/-!
## Convergence/holomorphy of the complement canonical product

This is the same M-test argument as for `divisorCanonicalProduct`, but with finitely many factors
replaced by `1`. We keep the same summability hypothesis.
-/

theorem hasProdUniformlyOn_divisorComplementCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) {K : Set ℂ} (hK : IsCompact K)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    HasProdUniformlyOn
      (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
        divisorComplementFactor m f z₀ p z)
      (divisorComplementCanonicalProduct m f z₀)
      K := by
  classical
  -- Bound `K` by a radius `R ≥ 1`.
  rcases (isBounded_iff_forall_norm_le.1 hK.isBounded) with ⟨R0, hR0⟩
  set R : ℝ := max R0 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hnormK : ∀ z ∈ K, ‖z‖ ≤ R := fun z hzK => le_trans (hR0 z hzK) (le_max_left _ _)

  -- Apply the product M-test for `1 + g`.
  let term : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ := fun p z =>
    divisorComplementFactor m f z₀ p z
  let g : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ := fun p z => term p z - 1
  let u : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
    fun p => (4 * R ^ (m + 1)) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))
  have hu : Summable u := h_sum.mul_left (4 * R ^ (m + 1))

  -- Cofinitely, `‖val p‖ > 2R`.
  have h_big :
      ∀ᶠ p : divisorZeroIndex₀ f (Set.univ : Set ℂ) in Filter.cofinite,
        (2 * R : ℝ) < ‖divisorZeroIndex₀_val p‖ := by
    have hfin :
        ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ 2 * R} : Set _).Finite := by
      have : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
      exact divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ)) (B := 2 * R) this
    have := hfin.eventually_cofinite_notMem
    filter_upwards [this] with p hp
    have : ¬ ‖divisorZeroIndex₀_val p‖ ≤ 2 * R := by simpa using hp
    exact lt_of_not_ge this

  have hBound :
      ∀ᶠ p in Filter.cofinite, ∀ z ∈ K, ‖g p z‖ ≤ u p := by
    filter_upwards [h_big] with p hp z hzK
    by_cases hpF : p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀
    · -- fiber indices contribute `term = 1`, hence `g = 0`.
      have hval : divisorZeroIndex₀_val p = z₀ :=
        (mem_divisorZeroIndex₀_fiberFinset (f := f) (z₀ := z₀) p).1 hpF
      have hu0 : 0 ≤ u p := by
        dsimp [u]
        refine mul_nonneg ?_ ?_
        · nlinarith [pow_nonneg (show 0 ≤ R from le_of_lt hRpos) (m + 1)]
        · exact pow_nonneg (inv_nonneg.2 (norm_nonneg _)) (m + 1)
      -- after rewriting `p ∈ fiberFinset` as `val p = z₀`, the integrand is constantly `0`
      simp [g, term, divisorComplementFactor, hval, hu0, sub_eq_add_neg,
        add_comm]
    · -- non-fiber: reuse the PR1 bound.
      have hzle : ‖z‖ ≤ R := hnormK z hzK
      have hz_div : ‖z / divisorZeroIndex₀_val p‖ ≤ (1 / 2 : ℝ) := by
        have h2R_pos : 0 < (2 * R : ℝ) := by nlinarith [hRpos]
        have hinv : ‖divisorZeroIndex₀_val p‖⁻¹ < (2 * R)⁻¹ := by
          simpa [one_div] using (one_div_lt_one_div_of_lt h2R_pos hp)
        have hmul_le : ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ ≤ R * ‖divisorZeroIndex₀_val p‖⁻¹ := by
          refine mul_le_mul_of_nonneg_right hzle ?_
          exact inv_nonneg.2 (norm_nonneg _)
        have hmul_lt : R * ‖divisorZeroIndex₀_val p‖⁻¹ < R * (2 * R)⁻¹ :=
          mul_lt_mul_of_pos_left hinv hRpos
        have hlt : ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ < R * (2 * R)⁻¹ :=
          lt_of_le_of_lt hmul_le hmul_lt
        have hRhalf : R * (2 * R)⁻¹ = (1 / 2 : ℝ) := by
          have hRne : (R : ℝ) ≠ 0 := hRpos.ne'
          have : R * (2 * R)⁻¹ = R / (2 * R) := by simp [div_eq_mul_inv]
          rw [this]
          field_simp [hRne]
        have hnorm : ‖z / divisorZeroIndex₀_val p‖ = ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := by
          simp [div_eq_mul_inv]
        have hzlt : ‖z / divisorZeroIndex₀_val p‖ < (1 / 2 : ℝ) := by
          calc
            ‖z / divisorZeroIndex₀_val p‖ = ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := hnorm
            _ < R * (2 * R)⁻¹ := hlt
            _ = (1 / 2 : ℝ) := hRhalf
        exact le_of_lt hzlt
      have hE :
          ‖weierstrassFactor m (z / divisorZeroIndex₀_val p) - 1‖ ≤
            4 * ‖z / divisorZeroIndex₀_val p‖ ^ (m + 1) :=
        weierstrassFactor_sub_one_pow_bound (m := m) (z := z / divisorZeroIndex₀_val p) hz_div
      have hz_pow :
          ‖z / divisorZeroIndex₀_val p‖ ^ (m + 1) ≤
            (R ^ (m + 1)) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
        have : ‖z / divisorZeroIndex₀_val p‖ = ‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := by
          simp [div_eq_mul_inv]
        rw [this]
        have : (‖z‖ * ‖divisorZeroIndex₀_val p‖⁻¹) ^ (m + 1) =
            ‖z‖ ^ (m + 1) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
          simp [mul_pow]
        rw [this]
        have hzle_pow : ‖z‖ ^ (m + 1) ≤ R ^ (m + 1) :=
          pow_le_pow_left₀ (norm_nonneg z) hzle (m + 1)
        gcongr
      dsimp [g, term, u]
      simp [divisorComplementFactor, hpF] at *
      nlinarith [hE, hz_pow]

  have hcts : ∀ p, ContinuousOn (g p) K := by
    intro p
    by_cases hpF : p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀
    · -- constant zero function
      have hval : divisorZeroIndex₀_val p = z₀ :=
        (mem_divisorZeroIndex₀_fiberFinset (f := f) (z₀ := z₀) p).1 hpF
      simpa [g, term, divisorComplementFactor, hval, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm] using
        (continuousOn_const : ContinuousOn (fun _ : ℂ => (0 : ℂ)) K)
    · -- same continuity argument as in the full product
      have hvalne : divisorZeroIndex₀_val p ≠ z₀ :=
        (not_mem_divisorZeroIndex₀_fiberFinset_iff_val_ne (f := f) z₀ p).1 hpF
      have hcontE : Continuous (fun z : ℂ => weierstrassFactor m z) := by
        have hcontPL : Continuous (fun z : ℂ => partialLogSum m z) := by
          classical
          unfold partialLogSum
          refine continuous_finset_sum _ ?_
          intro k hk
          have hpow : Continuous fun z : ℂ => z ^ (k + 1) := continuous_pow (k + 1)
          simpa [div_eq_mul_inv] using hpow.mul continuous_const
        have hsub : Continuous fun z : ℂ => (1 : ℂ) - z := continuous_const.sub continuous_id
        have hexp : Continuous fun z : ℂ => Complex.exp (partialLogSum m z) :=
          Complex.continuous_exp.comp hcontPL
        simpa [weierstrassFactor] using hsub.mul hexp
      have hdiv : Continuous fun z : ℂ => z / divisorZeroIndex₀_val p := by
        simpa [div_eq_mul_inv] using (continuous_id.mul continuous_const)
      have hcont : Continuous fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p) :=
        hcontE.comp hdiv
      have : ContinuousOn (fun z : ℂ => weierstrassFactor m (z / divisorZeroIndex₀_val p) - 1) K :=
        (hcont.continuousOn.sub continuous_const.continuousOn)
      -- rewrite `p ∈ fiberFinset` as `val p = z₀`, then simplify the `if` using `hvalne`
      simpa [g, term, divisorComplementFactor, mem_divisorZeroIndex₀_fiberFinset, hvalne] using this

  have hprod :
      HasProdUniformlyOn (fun p z ↦ 1 + g p z) (fun z ↦ ∏' p, (1 + g p z)) K := by
    simpa using
      Summable.hasProdUniformlyOn_one_add (f := g) (u := u) (K := K) hK hu hBound hcts

  -- Rewrite `1 + g` as `term`, then change the limit function to `divisorComplementCanonicalProduct`.
  have hterm :
      HasProdUniformlyOn (fun p z ↦ term p z) (fun z ↦ ∏' p, term p z) K := by
    simpa [g, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hprod
  refine hterm.congr_right ?_
  intro z hz
  classical
  simp [term, divisorComplementCanonicalProduct, divisorComplementFactor]

theorem hasProdLocallyUniformlyOn_divisorComplementCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    HasProdLocallyUniformlyOn
      (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
        divisorComplementFactor m f z₀ p z)
      (divisorComplementCanonicalProduct m f z₀)
      (Set.univ : Set ℂ) := by
  classical
  refine hasProdLocallyUniformlyOn_of_forall_compact
      (f := fun p z => divisorComplementFactor m f z₀ p z)
      (g := divisorComplementCanonicalProduct m f z₀) (s := (Set.univ : Set ℂ))
      isOpen_univ ?_
  intro K hKU hK
  simpa using
    (hasProdUniformlyOn_divisorComplementCanonicalProduct_univ (m := m) (f := f) (z₀ := z₀)
      (K := K) hK h_sum)

theorem tendstoLocallyUniformlyOn_divisorComplementPartialProduct_univ
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    TendstoLocallyUniformlyOn
      (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
        divisorComplementPartialProduct m f z₀ s)
      (divisorComplementCanonicalProduct m f z₀)
      Filter.atTop
      (Set.univ : Set ℂ) := by
  classical
  have hprod :
      HasProdLocallyUniformlyOn
        (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
          divisorComplementFactor m f z₀ p z)
        (divisorComplementCanonicalProduct m f z₀)
        (Set.univ : Set ℂ) :=
    hasProdLocallyUniformlyOn_divisorComplementCanonicalProduct_univ (m := m) (f := f) (z₀ := z₀) h_sum
  -- Unfold `HasProdLocallyUniformlyOn` to a `TendstoLocallyUniformlyOn` statement about finset products,
  -- then rewrite those products as `divisorComplementPartialProduct`.
  have h :
      TendstoLocallyUniformlyOn
        (fun (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) =>
          ∏ p ∈ s,
            if divisorZeroIndex₀_val p = z₀ then (1 : ℂ)
            else weierstrassFactor m (z / divisorZeroIndex₀_val p))
        (divisorComplementCanonicalProduct m f z₀)
        Filter.atTop
        (Set.univ : Set ℂ) := by
    simpa [HasProdLocallyUniformlyOn, divisorComplementFactor, mem_divisorZeroIndex₀_fiberFinset]
      using hprod
  refine h.congr (G := fun s z => divisorComplementPartialProduct m f z₀ s z) ?_
  intro s z hz
  simp [divisorComplementPartialProduct_def]

theorem differentiableOn_divisorComplementCanonicalProduct_univ
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    DifferentiableOn ℂ (divisorComplementCanonicalProduct m f z₀) (Set.univ : Set ℂ) := by
  classical
  have hloc :
      TendstoLocallyUniformlyOn
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          divisorComplementPartialProduct m f z₀ s)
        (divisorComplementCanonicalProduct m f z₀)
        Filter.atTop
        (Set.univ : Set ℂ) :=
    tendstoLocallyUniformlyOn_divisorComplementPartialProduct_univ (m := m) (f := f) (z₀ := z₀) h_sum
  have hF :
      ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in Filter.atTop,
        DifferentiableOn ℂ (divisorComplementPartialProduct m f z₀ s) (Set.univ : Set ℂ) := by
    refine Filter.Eventually.of_forall ?_
    intro s
    -- finite product of differentiable functions is differentiable
    have hdiff : Differentiable ℂ (divisorComplementPartialProduct m f z₀ s) := by
      let Φ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ :=
        fun p z =>
          if divisorZeroIndex₀_val p = z₀ then (1 : ℂ)
          else weierstrassFactor m (z / divisorZeroIndex₀_val p)
      have hΦ : ∀ p ∈ s, Differentiable ℂ (Φ p) := by
        intro p hp
        classical
        by_cases hval : divisorZeroIndex₀_val p = z₀
        · simp [Φ, hval]
        · have hdiv : Differentiable ℂ (fun z : ℂ => z / divisorZeroIndex₀_val p) := by
            simp [div_eq_mul_inv]
          simpa [Φ, hval] using (differentiable_weierstrassFactor m).comp hdiv
      have hEq : (fun z : ℂ => ∏ p ∈ s, Φ p z) = divisorComplementPartialProduct m f z₀ s := by
        ext z
        simp [Φ, divisorComplementPartialProduct_def]
      -- apply the finite-product differentiability lemma, then rewrite by `hEq`
      have : Differentiable ℂ (fun z : ℂ => ∏ p ∈ s, Φ p z) := by
        simpa using (Differentiable.fun_finset_prod (𝕜 := ℂ) (f := Φ) (u := s) hΦ)
      simpa [hEq] using this
    simpa using hdiff.differentiableOn
  haveI : (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))).NeBot :=
    Filter.atTop_neBot
  exact hloc.differentiableOn hF isOpen_univ

lemma divisorPartialProduct_eq_fiber_mul_complement_of_subset
    (m : ℕ) (f : ℂ → ℂ) (z₀ z : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))
    (hs : divisorZeroIndex₀_fiberFinset (f := f) z₀ ⊆ s) :
    divisorPartialProduct m f s z =
      divisorPartialProduct m f (divisorZeroIndex₀_fiberFinset (f := f) z₀) z *
        divisorComplementPartialProduct m f z₀ s z := by
  classical
  let fiber : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
    divisorZeroIndex₀_fiberFinset (f := f) z₀
  let P : divisorZeroIndex₀ f (Set.univ : Set ℂ) → Prop := fun p => p ∈ fiber
  let term : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ :=
    fun p => weierstrassFactor m (z / divisorZeroIndex₀_val p)

  have hfilter : s.filter P = fiber := by
    ext p
    constructor
    · intro hp
      exact (Finset.mem_filter.mp hp).2
    · intro hp
      exact Finset.mem_filter.mpr ⟨hs hp, hp⟩

  -- Split the total product over `s` into `P` and `¬P`.
  have hsplit :
      (∏ p ∈ s with P p, term p) * (∏ p ∈ s with ¬ P p, term p) = ∏ p ∈ s, term p := by
    simpa [term] using
      (Finset.prod_filter_mul_prod_filter_not (s := s) (p := P) (f := term))

  -- Rewrite the `P`-part as the product over `fiber`.
  have hP :
      (∏ p ∈ s with P p, term p) = divisorPartialProduct m f fiber z := by
    -- `∏ p ∈ s with P p, term p` is a product with `if P p then term p else 1`.
    -- Since `fiber ⊆ s`, this is exactly the product over `fiber`.
    -- Use `prod_subset_one_on_sdiff` to drop the `1`s.
    have hg :
        ∀ x ∈ s \ fiber, (if x ∈ fiber then term x else (1 : ℂ)) = 1 := by
      intro x hx
      have hxnot : x ∉ fiber := (Finset.mem_sdiff.mp hx).2
      simp [hxnot]
    have hfg :
        ∀ x ∈ fiber, term x = (if x ∈ fiber then term x else (1 : ℂ)) := by
      intro x hx
      simp [hx]
    -- `∏_{fiber} term = ∏_{s} (if x∈fiber then term x else 1)`
    have hsub :=
      (Finset.prod_subset_one_on_sdiff (s₁ := fiber) (s₂ := s)
        (f := term) (g := fun x => if x ∈ fiber then term x else (1 : ℂ)) hs hg hfg)
    -- rewrite the RHS as the `with P`-filtered product and conclude
    -- `∏ p ∈ s with P p, term p` rewrites to a product with `if P p then term p else 1`
    simpa [divisorPartialProduct, term, P, fiber, Finset.prod_filter] using hsub.symm

  -- Rewrite the `¬P`-part as the named complement partial product.
  have hnotP :
      (∏ p ∈ s with ¬ P p, term p) = divisorComplementPartialProduct m f z₀ s z := by
    -- by definition, `divisorComplementPartialProduct` inserts `1` on the fiber indices
    simp [divisorComplementPartialProduct, term, P, fiber, Finset.prod_filter]

  -- Now assemble, using `hsplit.symm` and the rewrites.
  have hsplit' :
      ∏ p ∈ s, term p =
        (∏ p ∈ s with P p, term p) * (∏ p ∈ s with ¬ P p, term p) := hsplit.symm

  calc
    divisorPartialProduct m f s z
        = ∏ p ∈ s, term p := by simp [divisorPartialProduct, term]
    _ = (∏ p ∈ s with P p, term p) * (∏ p ∈ s with ¬ P p, term p) := hsplit'
    _ = divisorPartialProduct m f fiber z * divisorComplementPartialProduct m f z₀ s z := by
      simp [hP, hnotP, fiber]

lemma divisorComplementPartialProduct_ne_zero_on_ball
    (m : ℕ) {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) :
    ∀ z ∈ Metric.ball z₀ ε,
      divisorComplementPartialProduct m f z₀ s z ≠ 0 := by
  classical
  intro z hz
  have hfac :
      ∀ p ∈ s,
        (if p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ then (1 : ℂ)
          else weierstrassFactor m (z / divisorZeroIndex₀_val p)) ≠ 0 := by
    intro p hp
    by_cases hpF : p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀
    · simp [hpF]
    · have : weierstrassFactor m (z / divisorZeroIndex₀_val p) ≠ 0 :=
        weierstrassFactor_div_ne_zero_on_ball_of_not_mem_fiberFinset
          (m := m) (f := f) (z₀ := z₀) (ε := ε) hball p hpF z hz
      simp [hpF, this]
  -- product of nonzero factors is nonzero
  simpa [divisorComplementPartialProduct, Finset.prod_ne_zero_iff] using hfac

theorem eventually_eq_fiber_mul_divisorComplementPartialProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) :
    ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      ∀ z : ℂ,
        divisorPartialProduct m f s z =
          divisorPartialProduct m f (divisorZeroIndex₀_fiberFinset (f := f) z₀) z *
            divisorComplementPartialProduct m f z₀ s z := by
  classical
  refine (eventually_atTop_subset_fiberFinset (f := f) z₀).mono ?_
  intro s hs z
  simpa using
    (divisorPartialProduct_eq_fiber_mul_complement_of_subset (m := m) (f := f) (z₀ := z₀)
      (z := z) (s := s) hs)

/-!
## Refining the factorization: factoring out `(z - z₀)^k` using the fiber-only product

When `s` contains the fiber finset, we can write the partial product as

`divisorPartialProduct s = (z - z₀)^k • (divisorComplementPartialProduct s * u)`

where `u` is the analytic quotient coming from the fiber-only product.
-/

theorem eventually_exists_analyticAt_eq_pow_smul_divisorComplementPartialProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) :
    ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      ∃ u : ℂ → ℂ,
        AnalyticAt ℂ u z₀ ∧ u z₀ ≠ 0 ∧
          (fun z : ℂ => divisorPartialProduct m f s z)
            =ᶠ[𝓝 z₀]
            fun z : ℂ =>
              (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card •
                (divisorComplementPartialProduct m f z₀ s z * u z) := by
  classical
  -- choose the fixed fiber-only quotient `u`
  let fiber : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
    divisorZeroIndex₀_fiberFinset (f := f) z₀
  have hfib :
      ∃ u : ℂ → ℂ, AnalyticAt ℂ u z₀ ∧ u z₀ ≠ 0 ∧
        (fun z : ℂ => divisorPartialProduct m f fiber z)
          =ᶠ[𝓝 z₀]
          fun z : ℂ =>
            (z - z₀) ^ fiber.card • u z := by
    -- apply the existing factorization lemma to `s = fiber`
    simpa [fiber, divisorPartialProduct] using
      (exists_analyticAt_eq_pow_smul_of_partialProduct_contains_fiber (m := m) (f := f) (z₀ := z₀)
        (s := fiber) (by rfl : fiber ⊆ fiber))
  rcases hfib with ⟨u, huA, hu0, huEq⟩
  -- now use that eventually `fiber ⊆ s` and multiply by the complement partial product
  refine (eventually_atTop_subset_fiberFinset (f := f) z₀).mono ?_
  intro s hs
  refine ⟨u, huA, hu0, ?_⟩
  -- factor `divisorPartialProduct s` into `fiber * complement`
  have hmul : ∀ z : ℂ,
      divisorPartialProduct m f s z =
        divisorPartialProduct m f fiber z * divisorComplementPartialProduct m f z₀ s z := by
    intro z
    simpa [fiber] using
      (divisorPartialProduct_eq_fiber_mul_complement_of_subset (m := m) (f := f) (z₀ := z₀)
        (z := z) (s := s) hs)
  -- combine with the fiber factorization near `z₀`
  have hmul_ev :
      (fun z : ℂ => divisorPartialProduct m f s z)
        =ᶠ[𝓝 z₀]
          fun z : ℂ => ((z - z₀) ^ fiber.card • u z) * divisorComplementPartialProduct m f z₀ s z := by
    filter_upwards [huEq] with z hz
    -- start from the finitary split `hmul` and rewrite the fiber part using `hz`
    have hsplit_z :
        divisorPartialProduct m f s z =
          divisorPartialProduct m f fiber z * divisorComplementPartialProduct m f z₀ s z :=
      hmul z
    -- rewrite and re-associate
    calc
      divisorPartialProduct m f s z
          = divisorPartialProduct m f fiber z * divisorComplementPartialProduct m f z₀ s z := hsplit_z
      _ = (((z - z₀) ^ fiber.card • u z) * divisorComplementPartialProduct m f z₀ s z) := by
            -- multiply the fiber identity `hz` by the complement factor
            simpa [mul_assoc] using congrArg (fun t => t * divisorComplementPartialProduct m f z₀ s z) hz
  -- rearrange into the requested form: `(z-z₀)^k • (complement * u)`
  filter_upwards [hmul_ev] with z hz
  -- scalar multiplication in `ℂ` is multiplication
  -- and commute `u` with the complement factor
  simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm, fiber] using hz

lemma divisorPartialProduct_ne_zero_on_ball_punctured
    (m : ℕ) {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) :
    ∀ z ∈ Metric.ball z₀ ε, z ≠ z₀ → divisorPartialProduct m f s z ≠ 0 := by
  classical
  intro z hz hz0
  -- every factor in the finite product is nonzero on the punctured ball
  have hfac :
      ∀ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p) ≠ 0 := by
    intro p hp
    exact weierstrassFactor_div_ne_zero_on_ball_punctured
      (m := m) (f := f) (z₀ := z₀) (ε := ε) hball z hz hz0 p
  -- hence the product is nonzero
  simpa [divisorPartialProduct, Finset.prod_ne_zero_iff] using hfac

theorem tendstoLocallyUniformlyOn_divisorPartialProduct_univ
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    TendstoLocallyUniformlyOn
      (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) => divisorPartialProduct m f s)
      (divisorCanonicalProduct m f (Set.univ : Set ℂ))
      Filter.atTop
      (Set.univ : Set ℂ) := by
  classical
  -- Unfold `HasProdLocallyUniformlyOn` for the existing theorem.
  have hprod :
      HasProdLocallyUniformlyOn
        (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) =>
          weierstrassFactor m (z / divisorZeroIndex₀_val p))
        (divisorCanonicalProduct m f (Set.univ : Set ℂ))
        (Set.univ : Set ℂ) :=
    hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
  simpa [HasProdLocallyUniformlyOn, divisorPartialProduct] using hprod

/-!
## Transport uniform convergence through multiplication by a bounded function

On a fixed set `K`, if `Fₙ → f` uniformly and `h` is bounded on `K`, then `h * Fₙ → h * f` uniformly.
We will use this on compacts avoiding `z₀` with `h(z) = ((z - z₀)^k)⁻¹`.
-/

theorem TendstoUniformlyOn.mul_left_bounded
    {ι : Type*} {p : Filter ι} {K : Set ℂ}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {h : ℂ → ℂ}
    (hF : TendstoUniformlyOn F f p K)
    (hh : ∃ C, ∀ z ∈ K, ‖h z‖ ≤ C) :
    TendstoUniformlyOn (fun n z => h z * F n z) (fun z => h z * f z) p K := by
  classical
  intro u hu
  rcases Metric.mem_uniformity_dist.1 hu with ⟨ε, hεpos, hεu⟩
  rcases hh with ⟨C, hC⟩
  -- Use `C' := max C 1` to avoid division-by-zero.
  set C' : ℝ := max C 1
  have hC'pos : 0 < C' := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hC' : ∀ z ∈ K, ‖h z‖ ≤ C' := fun z hz => le_trans (hC z hz) (le_max_left _ _)
  -- Apply uniform convergence with tolerance `ε / C'`.
  have hv : {p : ℂ × ℂ | dist p.1 p.2 < ε / C'} ∈ uniformity ℂ := by
    exact Metric.mem_uniformity_dist.2 ⟨ε / C', div_pos hεpos hC'pos, by intro a b hab; exact hab⟩
  have hF' : ∀ᶠ n in p, ∀ z : ℂ, z ∈ K → dist (f z) (F n z) < ε / C' :=
    (hF _ hv)
  filter_upwards [hF'] with n hn z hzK
  have hdist : dist (h z * f z) (h z * F n z) < ε := by
    -- `dist` is norm for `ℂ`
    have hn' : ‖f z - F n z‖ < ε / C' := by
      simpa [dist_eq_norm] using hn z hzK
    -- bound the multiplier on `K`
    have hle :
        ‖h z‖ * ‖f z - F n z‖ ≤ C' * ‖f z - F n z‖ :=
      mul_le_mul_of_nonneg_right (hC' z hzK) (norm_nonneg _)
    have hlt : C' * ‖f z - F n z‖ < C' * (ε / C') :=
      mul_lt_mul_of_pos_left hn' hC'pos
    -- finish
    have : ‖h z * f z - h z * F n z‖ = ‖h z‖ * ‖f z - F n z‖ := by
      -- `a*b - a*c = a*(b-c)` and `‖a*b‖ = ‖a‖*‖b‖`
      calc
        ‖h z * f z - h z * F n z‖ = ‖h z * (f z - F n z)‖ := by simp [mul_sub]
        _ = ‖h z‖ * ‖f z - F n z‖ := by simp
    -- back to `dist`
    simp [dist_eq_norm]
    calc
      ‖h z * f z - h z * F n z‖
          = ‖h z‖ * ‖f z - F n z‖ := this
      _ < C' * (ε / C') := lt_of_le_of_lt hle hlt
      _ = ε := by field_simp [hC'pos.ne']
  exact hεu hdist

/-!
## Quotient convergence on compacts avoiding `z₀`

If `K` is compact and avoids `z₀`, then multiplying by `((z - z₀)^k)⁻¹` preserves uniform convergence
on `K`. This is the key tool for the eventual removable-singularity argument for multiplicities.
-/

theorem tendstoUniformlyOn_divisorPartialProduct_div_pow_sub
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) (k : ℕ) {K : Set ℂ} (hK : IsCompact K) (hKz : ∀ z ∈ K, z ≠ z₀) :
    TendstoUniformlyOn
      (fun s z => (divisorPartialProduct m f s z) / (z - z₀) ^ k)
      (fun z => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k)
      (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))))
      K := by
  classical
  -- First: uniform convergence of partial products on `K`.
  have hloc :
      TendstoLocallyUniformlyOn
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) => divisorPartialProduct m f s)
        (divisorCanonicalProduct m f (Set.univ : Set ℂ))
        Filter.atTop
        K :=
    (tendstoLocallyUniformlyOn_divisorPartialProduct_univ (m := m) (f := f) h_sum).mono
      (by intro z hz; simp)
  have hunif :
      TendstoUniformlyOn
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) => divisorPartialProduct m f s)
        (divisorCanonicalProduct m f (Set.univ : Set ℂ))
        Filter.atTop
        K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1 hloc

  -- Define the bounded multiplier `h(z) = ((z - z₀)^k)⁻¹` on `K`.
  let h : ℂ → ℂ := fun z => ((z - z₀) ^ k)⁻¹
  have hh : ∃ C, ∀ z ∈ K, ‖h z‖ ≤ C := by
    -- `h` is continuous on `K` (since `K` avoids `z₀`), hence bounded on compact `K`.
    have hcont : ContinuousOn h K := by
      have hpow : ContinuousOn (fun z : ℂ => (z - z₀) ^ k) K := by
        fun_prop
      refine hpow.inv₀ ?_
      intro z hz
      have hz0 : z - z₀ ≠ 0 := sub_ne_zero.mpr (hKz z hz)
      exact pow_ne_zero k hz0
    have hKimg : IsCompact (h '' K) := hK.image_of_continuousOn hcont
    rcases (isBounded_iff_forall_norm_le.1 hKimg.isBounded) with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro z hz
    exact hC (h z) ⟨z, hz, rfl⟩

  -- Multiply uniform convergence by `h` and rewrite as division.
  have hunif' :=
    (TendstoUniformlyOn.mul_left_bounded (p := (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)))))
        (K := K)
        (F := fun s z => divisorPartialProduct m f s z)
        (f := fun z => divisorCanonicalProduct m f (Set.univ : Set ℂ) z)
        (h := h)
        hunif hh)
  -- Convert `h z * F n z` to `F n z / (z - z₀)^k`.
  simpa [h, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hunif'

/-!
## Quotient locally uniform convergence on the punctured plane `ℂ \ {z₀}`
-/

theorem tendstoLocallyUniformlyOn_divisorPartialProduct_div_pow_sub
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) (k : ℕ) :
    TendstoLocallyUniformlyOn
      (fun s z => (divisorPartialProduct m f s z) / (z - z₀) ^ k)
      (fun z => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k)
      (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))))
      ((Set.univ : Set ℂ) \ {z₀}) := by
  -- Use the `forall isCompact` characterization on the open set `univ \ {z₀}`.
  have hopen : IsOpen ((Set.univ : Set ℂ) \ {z₀}) := by
    have hset : ((Set.univ : Set ℂ) \ {z₀}) = ({z₀} : Set ℂ)ᶜ := by
      ext z
      simp
    simp [hset]
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hopen).2 ?_
  intro K hKsub hK
  -- `K` avoids `z₀` (since `K ⊆ univ \ {z₀}`)
  have hKz : ∀ z ∈ K, z ≠ z₀ := by
    intro z hzK
    have : z ∈ (Set.univ : Set ℂ) \ {z₀} := hKsub hzK
    exact by simpa [Set.mem_diff, Set.mem_singleton_iff] using this.2
  -- Convert locally uniform convergence of partial products to uniform convergence on compact `K`.
  exact tendstoUniformlyOn_divisorPartialProduct_div_pow_sub
    (m := m) (f := f) h_sum (z₀ := z₀) (k := k) (hK := hK) hKz

/-!
## Passing the fiber/complement factorization to the infinite product (punctured neighborhood)

This is the core “removable singularity” input: near `z₀`, the quotient
`divisorCanonicalProduct / (z - z₀)^k` agrees (on a punctured ball) with the product of
`divisorComplementCanonicalProduct` and the analytic factor `u` coming from the fiber-only product.
-/

open Filter

set_option maxHeartbeats 800000 in
theorem exists_ball_eq_divisorCanonicalProduct_div_pow_eq
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    ∃ ε > 0, ∃ u : ℂ → ℂ,
      AnalyticAt ℂ u z₀ ∧ u z₀ ≠ 0 ∧
      ∀ z : ℂ, z ∈ Metric.ball z₀ ε → z ≠ z₀ →
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
            (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card
          =
          (divisorComplementCanonicalProduct m f z₀ z) * u z := by
  classical
  let fiber : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
    divisorZeroIndex₀_fiberFinset (f := f) z₀
  -- First, factor the fiber-only finite product as `(z-z₀)^k * u(z)` near `z₀`.
  have hfib :
      ∃ u : ℂ → ℂ,
        AnalyticAt ℂ u z₀ ∧ u z₀ ≠ 0 ∧
          (fun z : ℂ => divisorPartialProduct m f fiber z)
            =ᶠ[𝓝 z₀]
            fun z : ℂ => (z - z₀) ^ fiber.card • u z := by
    simpa [fiber, divisorPartialProduct] using
      (exists_analyticAt_eq_pow_smul_of_partialProduct_contains_fiber (m := m) (f := f) (z₀ := z₀)
        (s := fiber) (by rfl : fiber ⊆ fiber))
  rcases hfib with ⟨u, huA, hu0, huEq⟩

  -- Extract a ball on which the factorization of the fiber product holds.
  have hmem : {z : ℂ | divisorPartialProduct m f fiber z =
      (z - z₀) ^ fiber.card • u z} ∈ 𝓝 z₀ := huEq
  rcases Metric.mem_nhds_iff.1 hmem with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, u, huA, hu0, ?_⟩

  -- Convergence of the (full) quotient partial products to the quotient canonical product, on `univ \ {z₀}`.
  have hq :
      TendstoLocallyUniformlyOn
        (fun s z =>
          (divisorPartialProduct m f s z) /
            (z - z₀) ^ fiber.card)
        (fun z =>
          (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
            (z - z₀) ^ fiber.card)
        (Filter.atTop : Filter (Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))))
        ((Set.univ : Set ℂ) \ {z₀}) :=
    tendstoLocallyUniformlyOn_divisorPartialProduct_div_pow_sub
      (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀) (k := fiber.card)

  -- Convergence of the complement partial products to the complement canonical product, pointwise.
  have hcomp :
      TendstoLocallyUniformlyOn
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          divisorComplementPartialProduct m f z₀ s)
        (divisorComplementCanonicalProduct m f z₀)
        Filter.atTop
        (Set.univ : Set ℂ) :=
    tendstoLocallyUniformlyOn_divisorComplementPartialProduct_univ (m := m) (f := f) (z₀ := z₀) h_sum

  -- For each `z` in the chosen punctured ball, show the desired equality by identifying both limits.
  intro z hz hzne
  have hz' : z ∈ ((Set.univ : Set ℂ) \ {z₀}) := by
    refine ⟨by simp, ?_⟩
    simpa [Set.mem_singleton_iff] using hzne

  -- `F_s(z)` tends to the quotient canonical product.
  have hF :
      Tendsto
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card)
        (Filter.atTop : Filter _)
        (𝓝 ((divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ fiber.card)) :=
    hq.tendsto_at hz'

  -- `G_s(z)` tends to `divisorComplementCanonicalProduct z * u z`.
  have hG0 :
      Tendsto
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          divisorComplementPartialProduct m f z₀ s z)
        (Filter.atTop : Filter _)
        (𝓝 (divisorComplementCanonicalProduct m f z₀ z)) :=
    hcomp.tendsto_at (by simp : z ∈ (Set.univ : Set ℂ))
  have hG :
      Tendsto
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          (divisorComplementPartialProduct m f z₀ s z) * u z)
        (Filter.atTop : Filter _)
        (𝓝 ((divisorComplementCanonicalProduct m f z₀ z) * u z)) :=
    (hG0.mul tendsto_const_nhds)

  -- Eventually, `fiber ⊆ s`, hence we can use the finitary split and the fiber factorization on the fixed ball.
  have hsub : ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      fiber ⊆ s := eventually_atTop_subset_fiberFinset (f := f) z₀
  have heq_eventually :
      ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
        (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card
          = (divisorComplementPartialProduct m f z₀ s z) * u z := by
    filter_upwards [hsub] with s hs
    have hsplit :
        divisorPartialProduct m f s z =
          divisorPartialProduct m f fiber z * divisorComplementPartialProduct m f z₀ s z := by
      -- specialize the finitary split lemma
      simpa [fiber] using
        (divisorPartialProduct_eq_fiber_mul_complement_of_subset (m := m) (f := f) (z₀ := z₀)
          (z := z) (s := s) hs)
    have hfibz :
        divisorPartialProduct m f fiber z = (z - z₀) ^ fiber.card • u z := by
      exact hball hz
    have hzpow : (z - z₀) ^ fiber.card ≠ 0 :=
      pow_ne_zero _ (sub_ne_zero.mpr hzne)
    -- combine and divide by the nonzero factor
    set a : ℂ := (z - z₀) ^ fiber.card
    have ha : a ≠ 0 := by simpa [a] using hzpow
    -- Name the complement partial product at `z` to keep expressions stable.
    set c : ℂ := divisorComplementPartialProduct m f z₀ s z with hc
    -- Rewrite using the finitary split and the fiber factorization on the fixed ball.
    rw [hsplit, hfibz, smul_eq_mul]
    -- Now cancel `a` and commute.
    calc
      ((a * u z) * c) / a
          = (a * (u z * c)) / a := by simp [mul_assoc]
      _ = u z * c := by
            simpa [mul_assoc] using (mul_div_cancel_left₀ (u z * c) ha)
      _ = c * u z := by ac_rfl
      _ = (divisorComplementPartialProduct m f z₀ s z) * u z := by
            simp [c]

  -- Conclude by uniqueness of limits (transfer `hG` along the eventual equality).
  have hG' :
      Tendsto
        (fun s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) =>
          (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card)
        (Filter.atTop : Filter _)
        (𝓝 ((divisorComplementCanonicalProduct m f z₀ z) * u z)) := by
    have heq' :
        ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
          (divisorComplementPartialProduct m f z₀ s z) * u z
            = (divisorPartialProduct m f s z) / (z - z₀) ^ fiber.card := by
      filter_upwards [heq_eventually] with s hs
      exact hs.symm
    exact (hG.congr' heq')
  exact tendsto_nhds_unique hF hG'

/-!
## Boundedness of the quotient on a punctured ball

We only need boundedness of the analytic factor `u` near `z₀`, so `ContinuousAt` at `z₀` suffices.
-/

theorem bddAbove_norm_divisorCanonicalProduct_div_pow_puncturedBall
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    ∃ r > 0,
      BddAbove
        (norm ∘
          (fun z : ℂ =>
            (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card) ''
            ((Metric.ball z₀ r) \ {z₀})) := by
  classical
  rcases exists_ball_eq_divisorCanonicalProduct_div_pow_eq (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀) with
    ⟨ε, hε, u, huA, hu0, hEq⟩
  -- Bound `u` on a smaller ball using continuity at `z₀`.
  have huC : ContinuousAt u z₀ := huA.continuousAt
  have hpre : {z : ℂ | ‖u z - u z₀‖ < 1} ∈ 𝓝 z₀ := by
    -- preimage of the metric ball around `u z₀`
    have : u ⁻¹' Metric.ball (u z₀) (1 : ℝ) ∈ 𝓝 z₀ :=
      huC.preimage_mem_nhds (Metric.ball_mem_nhds (u z₀) (by norm_num))
    simpa [Metric.ball, dist_eq_norm, Set.preimage] using this
  rcases Metric.mem_nhds_iff.1 hpre with ⟨r0, hr0pos, hr0sub⟩
  set r : ℝ := min (ε / 2) r0
  have hrpos : 0 < r := lt_min (by nlinarith [hε]) hr0pos
  have hr_lt_ε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by nlinarith [hε])

  have huBound : ∀ z ∈ Metric.ball z₀ r, ‖u z‖ ≤ ‖u z₀‖ + 1 := by
    intro z hz
    have hz0 : z ∈ Metric.ball z₀ r0 := by
      have : r ≤ r0 := min_le_right _ _
      exact Metric.ball_subset_ball this hz
    have hdiff : ‖u z - u z₀‖ < 1 := hr0sub hz0
    have htri : ‖u z‖ ≤ ‖u z - u z₀‖ + ‖u z₀‖ := by
      simpa [sub_eq_add_neg, add_assoc] using
        (norm_add_le (u z - u z₀) (u z₀))
    have : ‖u z‖ ≤ 1 + ‖u z₀‖ := le_trans htri (by nlinarith [le_of_lt hdiff])
    nlinarith [this]

  have hdiffC :
      DifferentiableOn ℂ (divisorComplementCanonicalProduct m f z₀) (Set.univ : Set ℂ) :=
    differentiableOn_divisorComplementCanonicalProduct_univ (m := m) (f := f) (z₀ := z₀) h_sum
  have hcontC : ContinuousOn (divisorComplementCanonicalProduct m f z₀) (Metric.closedBall z₀ r) :=
    (hdiffC.continuousOn).mono (by intro z hz; simp)
  have hK : IsCompact (Metric.closedBall z₀ r) := isCompact_closedBall _ _
  rcases (isBounded_iff_forall_norm_le.1 (hK.image_of_continuousOn hcontC).isBounded) with ⟨C, hC⟩

  refine ⟨r, hrpos, ⟨C * (‖u z₀‖ + 1), ?_⟩⟩
  rintro _ ⟨z, hzset, rfl⟩
  rcases hzset with ⟨hzr, hzne⟩
  have hz_in_ε : z ∈ Metric.ball z₀ ε := Metric.ball_subset_ball hr_lt_ε.le hzr
  have hz_ne : z ≠ z₀ := by simpa [Set.mem_singleton_iff] using hzne
  have hq :
      (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card
        = divisorComplementCanonicalProduct m f z₀ z * u z :=
    hEq z hz_in_ε hz_ne
  have hCz : ‖divisorComplementCanonicalProduct m f z₀ z‖ ≤ C := by
    have hzK : z ∈ Metric.closedBall z₀ r := Metric.mem_closedBall.2 (le_of_lt hzr)
    exact hC _ ⟨z, hzK, rfl⟩
  have huZ : ‖u z‖ ≤ ‖u z₀‖ + 1 := huBound z hzr
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) hCz
  have hmul : ‖divisorComplementCanonicalProduct m f z₀ z * u z‖ ≤ C * (‖u z₀‖ + 1) := by
    calc
      ‖divisorComplementCanonicalProduct m f z₀ z * u z‖
          = ‖divisorComplementCanonicalProduct m f z₀ z‖ * ‖u z‖ := by simp
      _ ≤ C * (‖u z₀‖ + 1) := by
            exact mul_le_mul hCz huZ (norm_nonneg _) hCnonneg
  simpa [Function.comp, hq] using hmul

/-!
## Nonvanishing of the complement canonical product near `z₀`

Pointwise, the complement canonical product is an infinite product of factors of the form `1 + aₚ`
with `∑ ‖aₚ‖` summable, hence the product is nonzero.
-/

theorem divisorComplementCanonicalProduct_ne_zero_at
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    divisorComplementCanonicalProduct m f z₀ z₀ ≠ 0 := by
  classical
  let Φ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ :=
    fun p => if divisorZeroIndex₀_val p = z₀ then (1 : ℂ)
      else weierstrassFactor m (z₀ / divisorZeroIndex₀_val p)
  let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ := fun p => Φ p - 1

  have hΦ_ne : ∀ p, Φ p ≠ 0 := by
    intro p
    by_cases hp : divisorZeroIndex₀_val p = z₀
    · simp [Φ, hp]
    · have hval : divisorZeroIndex₀_val p ≠ z₀ := hp
      have hz : z₀ / divisorZeroIndex₀_val p ≠ (1 : ℂ) := by
        intro h
        by_cases hp0 : divisorZeroIndex₀_val p = 0
        · -- `z₀ / 0 = 0`
          have : z₀ / divisorZeroIndex₀_val p = (0 : ℂ) := by simp [hp0]
          have h01 := h
          -- rewrite the left-hand side using `this : z₀ / divisorZeroIndex₀_val p = 0`
          rw [this] at h01
          exact (show False from (by simpa using (show (0 : ℂ) ≠ (1 : ℂ) from by simp) h01))
        · have : z₀ = divisorZeroIndex₀_val p := (div_eq_one_iff_eq hp0).1 h
          exact hval this.symm
      have hE : weierstrassFactor m (z₀ / divisorZeroIndex₀_val p) ≠ 0 := by
        -- `weierstrassFactor m z = 0 ↔ z = 1`
        intro h0
        have : z₀ / divisorZeroIndex₀_val p = (1 : ℂ) :=
          (weierstrassFactor_eq_zero_iff (m := m) (z := z₀ / divisorZeroIndex₀_val p)).1 h0
        exact hz this
      simp [Φ, hp, hE]

  -- Summability of `‖a p‖`.
  -- This is the same bound as in the product M-test proofs, specialized to the singleton `{z₀}`.
  have hz0_le : ‖z₀‖ ≤ max ‖z₀‖ 1 := le_max_left _ _
  set R : ℝ := max ‖z₀‖ 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  let u : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
    fun p => (4 * R ^ (m + 1)) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))
  have hu : Summable u := h_sum.mul_left (4 * R ^ (m + 1))

  have h_big :
      ∀ᶠ p : divisorZeroIndex₀ f (Set.univ : Set ℂ) in Filter.cofinite,
        (2 * R : ℝ) < ‖divisorZeroIndex₀_val p‖ := by
    have hfin :
        ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ 2 * R} : Set _).Finite := by
      have : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
      exact divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ)) (B := 2 * R) this
    have := hfin.eventually_cofinite_notMem
    filter_upwards [this] with p hp
    have : ¬ ‖divisorZeroIndex₀_val p‖ ≤ 2 * R := by simpa using hp
    exact lt_of_not_ge this

  have hBound :
      ∀ᶠ p in Filter.cofinite, ‖a p‖ ≤ u p := by
    filter_upwards [h_big] with p hp
    have ha_pos : 0 < ‖divisorZeroIndex₀_val p‖ := lt_trans (by nlinarith [hRpos]) hp
    have hz_div : ‖z₀ / divisorZeroIndex₀_val p‖ ≤ (1 / 2 : ℝ) := by
      have h2R_pos : 0 < (2 * R : ℝ) := by nlinarith [hRpos]
      have hinv : ‖divisorZeroIndex₀_val p‖⁻¹ < (2 * R)⁻¹ := by
        simpa [one_div] using (one_div_lt_one_div_of_lt h2R_pos hp)
      have hmul_le : ‖z₀‖ * ‖divisorZeroIndex₀_val p‖⁻¹ ≤ R * ‖divisorZeroIndex₀_val p‖⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 (norm_nonneg _))
        exact hz0_le
      have hmul_lt : R * ‖divisorZeroIndex₀_val p‖⁻¹ < R * (2 * R)⁻¹ :=
        mul_lt_mul_of_pos_left hinv hRpos
      have hlt : ‖z₀‖ * ‖divisorZeroIndex₀_val p‖⁻¹ < R * (2 * R)⁻¹ :=
        lt_of_le_of_lt hmul_le hmul_lt
      have hRhalf : R * (2 * R)⁻¹ = (1 / 2 : ℝ) := by
        have hRne : (R : ℝ) ≠ 0 := hRpos.ne'
        have : R * (2 * R)⁻¹ = R / (2 * R) := by simp [div_eq_mul_inv]
        rw [this]
        field_simp [hRne]
      have hnorm : ‖z₀ / divisorZeroIndex₀_val p‖ = ‖z₀‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := by
        simp [div_eq_mul_inv]
      have hzlt : ‖z₀ / divisorZeroIndex₀_val p‖ < (1 / 2 : ℝ) := by
        calc
          ‖z₀ / divisorZeroIndex₀_val p‖ = ‖z₀‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := hnorm
          _ < R * (2 * R)⁻¹ := hlt
          _ = (1 / 2 : ℝ) := hRhalf
      exact le_of_lt hzlt
    have hE :
        ‖weierstrassFactor m (z₀ / divisorZeroIndex₀_val p) - 1‖ ≤
          4 * ‖z₀ / divisorZeroIndex₀_val p‖ ^ (m + 1) :=
      weierstrassFactor_sub_one_pow_bound (m := m) (z := z₀ / divisorZeroIndex₀_val p) hz_div
    have hz_pow :
        ‖z₀ / divisorZeroIndex₀_val p‖ ^ (m + 1) ≤
          (R ^ (m + 1)) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
      have : ‖z₀ / divisorZeroIndex₀_val p‖ = ‖z₀‖ * ‖divisorZeroIndex₀_val p‖⁻¹ := by
        simp [div_eq_mul_inv]
      rw [this]
      have : (‖z₀‖ * ‖divisorZeroIndex₀_val p‖⁻¹) ^ (m + 1) =
          ‖z₀‖ ^ (m + 1) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
        simp [mul_pow]
      rw [this]
      have hzle_pow : ‖z₀‖ ^ (m + 1) ≤ R ^ (m + 1) :=
        pow_le_pow_left₀ (norm_nonneg z₀) hz0_le (m + 1)
      gcongr
    have hp_ne : divisorZeroIndex₀_val p ≠ z₀ := by
      intro h
      have : ‖divisorZeroIndex₀_val p‖ ≤ R := by
        simp [h, R]  -- `‖z₀‖ ≤ max ‖z₀‖ 1`
      exact (not_lt_of_ge this) (lt_trans (by nlinarith [hRpos]) hp)
    -- conclude: on this cofinite set, `Φ p = weierstrassFactor ...`
    have ha : ‖a p‖ = ‖weierstrassFactor m (z₀ / divisorZeroIndex₀_val p) - 1‖ := by
      simp [a, Φ, hp_ne, sub_eq_add_neg, add_comm]
    -- combine bounds
    calc
      ‖a p‖ = ‖weierstrassFactor m (z₀ / divisorZeroIndex₀_val p) - 1‖ := ha
      _ ≤ 4 * ‖z₀ / divisorZeroIndex₀_val p‖ ^ (m + 1) := by
            simpa [sub_eq_add_neg, add_comm] using hE
      _ ≤ 4 * (R ^ (m + 1) * (‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) := by
            gcongr
      _ = u p := by
            simp [u, mul_assoc, mul_comm]

  have hsum_norm : Summable (fun p => ‖a p‖) := by
    -- direct comparison on `cofinite`
    -- (use the summable bound `u`)
    refine (Summable.of_norm_bounded_eventually (E := ℝ) (f := fun p => ‖a p‖) (g := u) hu ?_)
    -- `‖‖a p‖‖ = ‖a p‖`
    filter_upwards [hBound] with p hp
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (a p))] using hp

  -- Apply the nonzero lemma for products of `1 + a p`.
  have htprod_ne :
      (∏' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (1 + a p)) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable (R := ℂ) (f := a) (hf := fun p => by
      -- `1 + (Φ p - 1) = Φ p`
      simpa [a, Φ, add_sub_cancel] using hΦ_ne p) hsum_norm

  -- `∏' p, (1 + a p) = ∏' p, Φ p = divisorComplementCanonicalProduct ... z₀`
  have : (∏' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), (1 + a p)) =
      divisorComplementCanonicalProduct m f z₀ z₀ := by
    -- simplify `1 + (Φ-1)` to `Φ`, then unfold the complement canonical product at `z₀`
    simp [a, Φ, divisorComplementCanonicalProduct, mem_divisorZeroIndex₀_fiberFinset]
  exact by
    intro h0
    exact htprod_ne (by simpa [this] using h0)

theorem exists_ball_divisorComplementCanonicalProduct_ne_zero
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    ∃ r > 0, ∀ z ∈ Metric.ball z₀ r, divisorComplementCanonicalProduct m f z₀ z ≠ 0 := by
  classical
  have hdiff :
      DifferentiableOn ℂ (divisorComplementCanonicalProduct m f z₀) (Set.univ : Set ℂ) :=
    differentiableOn_divisorComplementCanonicalProduct_univ (m := m) (f := f) (z₀ := z₀) h_sum
  have hdiffAt : DifferentiableAt ℂ (divisorComplementCanonicalProduct m f z₀) z₀ := by
    -- `univ ∈ 𝓝 z₀`, so `DifferentiableWithinAt` upgrades to `DifferentiableAt`
    exact (hdiff z₀ (by simp)).differentiableAt (by simp)
  have hcont : ContinuousAt (divisorComplementCanonicalProduct m f z₀) z₀ :=
    hdiffAt.continuousAt
  have h0 : divisorComplementCanonicalProduct m f z₀ z₀ ≠ 0 :=
    divisorComplementCanonicalProduct_ne_zero_at (m := m) (f := f) (z₀ := z₀) h_sum
  have hopen : IsOpen (({0} : Set ℂ)ᶜ) := isClosed_singleton.isOpen_compl
  have hmem : divisorComplementCanonicalProduct m f z₀ z₀ ∈ (({0} : Set ℂ)ᶜ) := by
    simp [h0]
  rcases (Metric.mem_nhds_iff.1 (hcont (hopen.mem_nhds hmem))) with ⟨r, hrpos, hr⟩
  refine ⟨r, hrpos, ?_⟩
  intro z hz
  have : divisorComplementCanonicalProduct m f z₀ z ∈ ({0} : Set ℂ)ᶜ := hr hz
  simpa using this

/-!
## Eventually: partial products factor at `z₀` with the fiber multiplicity

This is the key “asymptotic divisibility” statement: along `atTop`, all sufficiently large partial
products contain the fiber, hence each such partial product is locally divisible by `(z - z₀)^k`
where `k` is the intrinsic multiplicity fiber cardinality.
-/

theorem eventually_exists_analyticAt_eq_pow_smul_divisorPartialProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) :
    ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      ∃ g : ℂ → ℂ,
        AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
          (fun z : ℂ => divisorPartialProduct m f s z)
            =ᶠ[𝓝 z₀]
            fun z : ℂ =>
              (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card • g z := by
  classical
  refine (eventually_atTop_subset_fiberFinset (f := f) z₀).mono ?_
  intro s hs
  -- reuse the previously proved factorization lemma for the explicit `∏ p ∈ s` expression
  rcases
      exists_analyticAt_eq_pow_smul_of_partialProduct_contains_fiber
        (m := m) (f := f) (z₀ := z₀) (s := s) hs with
    ⟨g, hg, hg0, hEq⟩
  refine ⟨g, hg, hg0, ?_⟩
  simpa [divisorPartialProduct] using hEq

/-!
## On `𝓝[≠] z₀`, large partial product quotients agree with an analytic function

This is the punctured-neighborhood version of `eventually_exists_analyticAt_eq_pow_smul_divisorPartialProduct`,
obtained by dividing the factorization by `(z - z₀)^k` away from `z₀`.
-/

theorem eventually_eq_punctured_quotient_of_factorization
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) :
    ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      ∃ g : ℂ → ℂ,
        AnalyticAt ℂ g z₀ ∧
          (fun z : ℂ => (divisorPartialProduct m f s z) /
            (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
            =ᶠ[𝓝[≠] z₀] g := by
  classical
  refine (eventually_exists_analyticAt_eq_pow_smul_divisorPartialProduct (m := m) (f := f) z₀).mono ?_
  intro s hs
  rcases hs with ⟨g, hg, hg0, hEq⟩
  refine ⟨g, hg, ?_⟩
  -- restrict factorization to the punctured neighborhood
  have hEq' :
      (fun z : ℂ => divisorPartialProduct m f s z) =ᶠ[𝓝[≠] z₀]
        fun z : ℂ =>
          (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card • g z :=
    hEq.filter_mono nhdsWithin_le_nhds
  have hne : ∀ᶠ z : ℂ in 𝓝[≠] z₀, z ≠ z₀ := by
    -- by definition, `𝓝[≠] z₀` is a neighborhood within `{z | z ≠ z₀}`
    simpa [Filter.Eventually] using (self_mem_nhdsWithin : {z : ℂ | z ≠ z₀} ∈ 𝓝[≠] z₀)
  filter_upwards [hEq', hne] with z hz hzne
  have hz0 : (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card ≠ 0 :=
    pow_ne_zero _ (sub_ne_zero.mpr hzne)
  -- divide the factorization by `(z - z₀)^k`
  -- (`•` is multiplication in `ℂ`)
  -- start from `hz` and cancel
  have : (divisorPartialProduct m f s z) / (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card = g z := by
    -- rewrite using the factorization
    rw [hz]
    -- cancel the nonzero factor
    simpa [smul_eq_mul] using (mul_div_cancel_left₀ (g z) hz0)
  simpa [divisorPartialProduct] using this

theorem eventually_exists_ball_eq_punctured_quotient_of_factorization
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) :
    ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      ∃ ε > 0, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧
        ∀ z : ℂ, z ∈ Metric.ball z₀ ε → z ≠ z₀ →
          (divisorPartialProduct m f s z) /
              (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card
            = g z := by
  classical
  refine (eventually_eq_punctured_quotient_of_factorization (m := m) (f := f) z₀).mono ?_
  intro s hs
  rcases hs with ⟨g, hg, hEq⟩
  -- unpack the `=ᶠ[𝓝[≠] z₀]` as a ball witness
  rcases (Metric.nhdsWithin_basis_ball (x := z₀) (s := {z : ℂ | z ≠ z₀})).mem_iff.1 hEq with
    ⟨ε, hε, hball⟩
  refine ⟨ε, hε, g, hg, ?_⟩
  intro z hz hz0
  have hz' : z ∈ Metric.ball z₀ ε ∩ {z : ℂ | z ≠ z₀} := ⟨hz, hz0⟩
  exact hball hz'

/-!
## Differentiability of the quotient on `ℂ \ {z₀}`

This is the “analytic part” of the removable-singularity setup: the quotient of the infinite product
by `(z - z₀)^k` is holomorphic on the punctured plane.
-/

theorem differentiableOn_divisorPartialProduct_div_pow_sub
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) (k : ℕ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) :
    DifferentiableOn ℂ
      (fun z : ℂ => (divisorPartialProduct m f s z) / (z - z₀) ^ k)
      ((Set.univ : Set ℂ) \ {z₀}) := by
  classical
  -- `divisorPartialProduct` is entire (finite product of entire functions).
  have hdiff_prod : DifferentiableOn ℂ (divisorPartialProduct m f s) (Set.univ : Set ℂ) := by
    -- from global differentiability
    have hdiff : Differentiable ℂ (divisorPartialProduct m f s) := by
      -- reuse the same finset product differentiability proof pattern
      let Φ : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ :=
        fun p z => weierstrassFactor m (z / divisorZeroIndex₀_val p)
      have hΦ : ∀ p ∈ s, Differentiable ℂ (Φ p) := by
        intro p hp
        have hdiv : Differentiable ℂ (fun z : ℂ => z / divisorZeroIndex₀_val p) := by
          simp [div_eq_mul_inv]
        exact (differentiable_weierstrassFactor m).comp hdiv
      simpa [divisorPartialProduct, Φ] using
        (Differentiable.fun_finset_prod (𝕜 := ℂ) (f := Φ) (u := s) hΦ)
    simpa using hdiff.differentiableOn
  -- The denominator is differentiable on `univ \ {z₀}`.
  have hdiff_den : DifferentiableOn ℂ (fun z : ℂ => (z - z₀) ^ k) ((Set.univ : Set ℂ) \ {z₀}) := by
    -- polynomial map, differentiable everywhere
    have : Differentiable ℂ (fun z : ℂ => (z - z₀) ^ k) := by
      fun_prop
    exact this.differentiableOn
  -- Division by a nonzero differentiable function is differentiable; on `univ \ {z₀}`, `(z-z₀)^k ≠ 0` for `k>0`,
  -- and for `k=0` it's constant `1` anyway.
  by_cases hk : k = 0
  · subst hk
    -- then the quotient is just the numerator
    simpa [pow_zero] using (hdiff_prod.mono (by intro z hz; exact hz.1))
  · have hne : ∀ z ∈ ((Set.univ : Set ℂ) \ {z₀}), (fun z : ℂ => (z - z₀) ^ k) z ≠ 0 := by
      intro z hz
      have hz' : z ≠ z₀ := by
        simpa [Set.mem_diff, Set.mem_singleton_iff] using hz.2
      exact pow_ne_zero _ (sub_ne_zero.mpr hz')
    -- use `DifferentiableOn.div` via `mul` with `inv`.
    -- `a / b = a * b⁻¹`
    have hdiff_inv :
        DifferentiableOn ℂ (fun z : ℂ => ((z - z₀) ^ k)⁻¹) ((Set.univ : Set ℂ) \ {z₀}) :=
      hdiff_den.inv hne
    simpa [div_eq_mul_inv] using (hdiff_prod.mono (by intro z hz; exact hz.1)).mul hdiff_inv

theorem differentiableOn_divisorCanonicalProduct_div_pow_sub
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) (k : ℕ) :
    DifferentiableOn ℂ
      (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k)
      ((Set.univ : Set ℂ) \ {z₀}) := by
  classical
  have hopen : IsOpen ((Set.univ : Set ℂ) \ {z₀}) := by
    -- `univ \ {z₀} = {z₀}ᶜ`
    have hset : ((Set.univ : Set ℂ) \ {z₀}) = ({z₀} : Set ℂ)ᶜ := by
      ext z; simp
    simp [hset]
  have hconv :=
    tendstoLocallyUniformlyOn_divisorPartialProduct_div_pow_sub
      (m := m) (f := f) h_sum (z₀ := z₀) (k := k)
  -- apply holomorphy of locally uniform limit
  refine hconv.differentiableOn ?_ hopen
  refine Filter.Eventually.of_forall ?_
  intro s
  exact differentiableOn_divisorPartialProduct_div_pow_sub (m := m) (f := f) (z₀ := z₀) (k := k) s

/-!
## Removable singularity for the quotient at `z₀`

Using punctured-ball boundedness and punctured differentiability, we obtain a holomorphic extension
of the quotient at `z₀` via `Mathlib.Analysis.Complex.RemovableSingularity`.
-/

theorem differentiableOn_update_limUnder_divisorCanonicalProduct_div_pow
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    ∃ r > 0,
      DifferentiableOn ℂ
        (Function.update
          (fun z : ℂ =>
            (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
          z₀
          (limUnder (𝓝[≠] z₀)
            (fun z : ℂ =>
              (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
                (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)))
        (Metric.ball z₀ r) := by
  classical
  rcases bddAbove_norm_divisorCanonicalProduct_div_pow_puncturedBall (m := m) (f := f)
      (h_sum := h_sum) (z₀ := z₀) with ⟨r, hrpos, hbdd⟩
  refine ⟨r, hrpos, ?_⟩
  have hnhds : Metric.ball z₀ r ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hrpos
  have hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ =>
          (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
            (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
        ((Metric.ball z₀ r) \ {z₀}) := by
    have hglob :=
      differentiableOn_divisorCanonicalProduct_div_pow_sub
        (m := m) (f := f) h_sum (z₀ := z₀)
        (k := (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
    refine hglob.mono ?_
    intro z hz
    exact ⟨by simp, hz.2⟩
  have hb :
      BddAbove
        (norm ∘
          (fun z : ℂ =>
            (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card) ''
            ((Metric.ball z₀ r) \ {z₀})) := hbdd
  simpa using
    (Complex.differentiableOn_update_limUnder_of_bddAbove (f := fun z : ℂ =>
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
      (s := Metric.ball z₀ r) (c := z₀) hnhds hdiff hb)

theorem analyticAt_update_limUnder_divisorCanonicalProduct_div_pow
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    AnalyticAt ℂ
      (Function.update
        (fun z : ℂ =>
          (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
            (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
        z₀
        (limUnder (𝓝[≠] z₀)
          (fun z : ℂ =>
            (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
              (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)))
      z₀ := by
  classical
  rcases
      differentiableOn_update_limUnder_divisorCanonicalProduct_div_pow
        (m := m) (f := f) h_sum (z₀ := z₀) with ⟨r, hrpos, hdiff⟩
  -- analytic at `z₀` follows from differentiability on a punctured neighborhood + continuity at `z₀`
  let g : ℂ → ℂ :=
    Function.update
      (fun z : ℂ =>
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
      z₀
      (limUnder (𝓝[≠] z₀) fun z : ℂ =>
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) /
          (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card)
  have hcont : ContinuousAt g z₀ := (hdiff.differentiableAt (Metric.ball_mem_nhds z₀ hrpos)).continuousAt
  have hd :
      ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ g z := by
    -- points in a punctured neighborhood are eventually in the open ball where `hdiff` gives differentiability
    have hballWithin : Metric.ball z₀ r ∈ 𝓝[≠] z₀ := by
      refine mem_nhdsWithin_iff_exists_mem_nhds_inter.2 ?_
      refine ⟨Metric.ball z₀ r, Metric.ball_mem_nhds z₀ hrpos, ?_⟩
      intro z hz
      exact hz.1
    filter_upwards [hballWithin] with z hz
    exact (hdiff z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
  -- now apply the complex analytic criterion
  simpa [g] using Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd hcont

/-!
## Exact multiplicity of the divisor canonical product

At each `z₀`, the zero multiplicity of `divisorCanonicalProduct` equals the intrinsic fiber
cardinality `card (divisorZeroIndex₀_fiberFinset z₀)`.
-/

theorem analyticOrderNatAt_divisorCanonicalProduct_eq_fiber_card
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) :
    analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z₀ =
      (divisorZeroIndex₀_fiberFinset (f := f) z₀).card := by
  classical
  set k : ℕ := (divisorZeroIndex₀_fiberFinset (f := f) z₀).card
  let F : ℂ → ℂ := divisorCanonicalProduct m f (Set.univ : Set ℂ)
  let q0 : ℂ → ℂ := fun z => F z / (z - z₀) ^ k
  let q : ℂ → ℂ := Function.update q0 z₀ (limUnder (𝓝[≠] z₀) q0)

  -- `F` is analytic at `z₀` since it is differentiable everywhere.
  have hdiff_univ : DifferentiableOn ℂ F (Set.univ : Set ℂ) :=
    differentiableOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
  have han : AnalyticAt ℂ F z₀ := by
    refine (Complex.analyticAt_iff_eventually_differentiableAt).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro z
    have : DifferentiableWithinAt ℂ F (Set.univ : Set ℂ) z := hdiff_univ z (by simp)
    exact this.differentiableAt (by simp)

  have hqA : AnalyticAt ℂ q z₀ := by
    simpa [q, q0, F, k] using
      (analyticAt_update_limUnder_divisorCanonicalProduct_div_pow (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀))

  -- Identify the punctured limit of `q0` using the punctured-ball quotient identity.
  rcases
      exists_ball_eq_divisorCanonicalProduct_div_pow_eq (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀)
    with ⟨ε, hε, u, huA, hu0, hEq⟩
  let g : ℂ → ℂ := fun z => (divisorComplementCanonicalProduct m f z₀ z) * u z

  have hcompDiff : DifferentiableOn ℂ (divisorComplementCanonicalProduct m f z₀) (Set.univ : Set ℂ) :=
    differentiableOn_divisorComplementCanonicalProduct_univ (m := m) (f := f) (z₀ := z₀) h_sum
  have hcompCont : ContinuousAt (divisorComplementCanonicalProduct m f z₀) z₀ :=
    (hcompDiff z₀ (by simp)).differentiableAt (by simp) |>.continuousAt
  have hgCont : ContinuousAt g z₀ := (hcompCont.mul huA.continuousAt)
  have hg0 : g z₀ ≠ 0 := by
    have hcomp0 : divisorComplementCanonicalProduct m f z₀ z₀ ≠ 0 :=
      divisorComplementCanonicalProduct_ne_zero_at (m := m) (f := f) (z₀ := z₀) h_sum
    exact mul_ne_zero hcomp0 hu0

  have hne_mem : ∀ᶠ z in 𝓝[≠] z₀, z ∈ (({z₀} : Set ℂ)ᶜ) :=
    Filter.eventually_of_mem
      (self_mem_nhdsWithin : (({z₀} : Set ℂ)ᶜ) ∈ 𝓝[≠] z₀) (fun _ hz => hz)
  have hne : ∀ᶠ z in 𝓝[≠] z₀, z ≠ z₀ := by
    filter_upwards [hne_mem] with z hz
    simpa [Set.mem_compl_singleton_iff] using hz

  have ht_q0 : Tendsto q0 (𝓝[≠] z₀) (𝓝 (g z₀)) := by
    have hball : ∀ᶠ z in 𝓝[≠] z₀, z ∈ Metric.ball z₀ ε :=
      Filter.eventually_of_mem
        (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z₀ hε)) (fun _ hz => hz)
    have heq : q0 =ᶠ[𝓝[≠] z₀] g := by
      filter_upwards [hball, hne] with z hz hzne
      have hq := hEq z hz hzne
      simpa [q0, F, k, g, smul_eq_mul] using hq
    exact (hgCont.continuousWithinAt.tendsto.congr' heq.symm)

  have hlim : limUnder (𝓝[≠] z₀) q0 = g z₀ := ht_q0.limUnder_eq
  have hq0 : q z₀ ≠ 0 := by
    have : q z₀ = g z₀ := by simp [q, Function.update_self, hlim]
    exact this.symm ▸ hg0

  -- Punctured equality `F z = (z-z₀)^k • q z` (needed to get the value at `z₀` by limits).
  have heq_punct : (fun z : ℂ => F z) =ᶠ[𝓝[≠] z₀] fun z : ℂ => (z - z₀) ^ k • q z := by
    filter_upwards [hne] with z hz
    have hzpow : (z - z₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz)
    have hq : q z = q0 z := by simp [q, Function.update_of_ne hz]
    have hmul : (z - z₀) ^ k * q0 z = F z := by
      calc
        (z - z₀) ^ k * q0 z
            = (((z - z₀) ^ k) * F z) / ((z - z₀) ^ k) := by
                simp [q0, div_eq_mul_inv, mul_assoc]
        _ = F z := by
              simpa [mul_assoc] using (mul_div_cancel_left₀ (F z) hzpow)
    have : F z = (z - z₀) ^ k * q z := by
      calc
        F z = (z - z₀) ^ k * q0 z := hmul.symm
        _ = (z - z₀) ^ k * q z := by simp [hq]
    simpa [smul_eq_mul] using this

  have hcontF : ContinuousAt F z₀ :=
    (hdiff_univ z₀ (by simp)).differentiableAt (by simp) |>.continuousAt
  have hcontq : ContinuousAt q z₀ := hqA.continuousAt

  -- equality at the point `z₀` by taking limits of the punctured equality
  have h_at_z0 : F z₀ = (z₀ - z₀) ^ k • q z₀ := by
    have ht1 : Tendsto F (𝓝[≠] z₀) (𝓝 (F z₀)) := hcontF.continuousWithinAt.tendsto
    have hpow :
        Tendsto (fun z : ℂ => (z - z₀) ^ k) (𝓝[≠] z₀) (𝓝 ((z₀ - z₀) ^ k)) :=
      ((continuousAt_id.sub continuousAt_const).pow k).continuousWithinAt.tendsto
    have ht2 :
        Tendsto (fun z : ℂ => (z - z₀) ^ k • q z) (𝓝[≠] z₀)
          (𝓝 ((z₀ - z₀) ^ k • q z₀)) :=
      hpow.mul (hcontq.continuousWithinAt.tendsto)
    have ht2' : Tendsto F (𝓝[≠] z₀) (𝓝 ((z₀ - z₀) ^ k • q z₀)) :=
      ht2.congr' heq_punct.symm
    exact tendsto_nhds_unique ht1 ht2'

  -- expresse as `∀ᶠ z in 𝓝 z₀, ...` using a ball neighborhood
  have hfac : ∀ᶠ z in 𝓝 z₀, F z = (z - z₀) ^ k • q z := by
    have hball1 : Metric.ball z₀ 1 ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ (by norm_num)
    have hball1' : ∀ᶠ z in 𝓝 z₀, z ∈ Metric.ball z₀ 1 :=
      Filter.eventually_of_mem hball1 (fun _ hz => hz)
    filter_upwards [hball1'] with z _hz
    by_cases hz0 : z = z₀
    · subst hz0
      simpa using h_at_z0
    · have hzpow : (z - z₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz0)
      have hq : q z = q0 z := by simp [q, Function.update_of_ne hz0]
      have hmul : (z - z₀) ^ k * q0 z = F z := by
        calc
          (z - z₀) ^ k * q0 z
              = (((z - z₀) ^ k) * F z) / ((z - z₀) ^ k) := by
                  simp [q0, div_eq_mul_inv, mul_assoc]
          _ = F z := by
                simpa [mul_assoc] using (mul_div_cancel_left₀ (F z) hzpow)
      have : F z = (z - z₀) ^ k * q z := by
        calc
          F z = (z - z₀) ^ k * q0 z := hmul.symm
          _ = (z - z₀) ^ k * q z := by simp [hq]
      simpa [smul_eq_mul] using this

  -- Conclude by the analytic-order characterization.
  have hk' : analyticOrderAt F z₀ = k :=
    (han.analyticOrderAt_eq_natCast (n := k)).2 ⟨q, hqA, hq0, hfac⟩
  have hkNat : analyticOrderNatAt F z₀ = k := by
    simp [analyticOrderNatAt, hk']
  simpa [F, k] using hkNat

/-!
## Canonical product has the same analytic order as `f` away from the origin

Once the divisor-indexed canonical product is known to converge (the summability hypothesis),
we already proved that its analytic order at `z₀` is the fiber cardinality. The fiber cardinality
itself equals `analyticOrderNatAt f z₀` for holomorphic `f`. Hence the canonical product matches
`f`'s zero multiplicities at every `z₀ ≠ 0`.
-/

theorem analyticOrderNatAt_divisorCanonicalProduct_eq_analyticOrderNatAt
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z₀ =
      analyticOrderNatAt f z₀ := by
  classical
  have hcp :
      analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z₀ =
        (divisorZeroIndex₀_fiberFinset (f := f) z₀).card :=
    analyticOrderNatAt_divisorCanonicalProduct_eq_fiber_card (m := m) (f := f) (h_sum := h_sum) (z₀ := z₀)
  have hfib :
      (divisorZeroIndex₀_fiberFinset (f := f) z₀).card = analyticOrderNatAt f z₀ :=
    divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt (hf := hf) (z₀ := z₀) hz₀
  simpa [hfib] using hcp
