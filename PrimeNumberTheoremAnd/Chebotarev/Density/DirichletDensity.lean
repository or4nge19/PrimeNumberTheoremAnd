import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Dirichlet density of sets of rational primes

Sharifi's Dirichlet density for a set of rational primes, in the form used in Chebotarev
arguments (Sharifi, *Arithmetic of Number Fields*, Def. 7.1.13 in the ideal form; this file
is the `ℤ` / rational-prime specialization).

**Upstream target:** `Mathlib.NumberTheory.DirichletDensity` (this module is the staging area).

### Index-set convention

`HasDensity` is stated for `S : Set ℕ`, but only **prime** membership affects the Dirichlet
series: `coeff S n` is nonzero only when `n` is prime and `n ∈ S`. Composites are invisible.
Two sets with the same prime elements have the same density data (`coeff`, `series`, `ratioAt`,
`HasDensity`).

Mathematically one often indexes by `Nat.Primes`; the `Set ℕ` formulation avoids a separate
prime index type while keeping the same weights. The ideal-level analogue indexes prime ideals
in `DirichletDensityIdeals`.

### Public API contract

* **Primary (guarded):** `seriesAt`, `seriesAllAt`, `ratio`, `ratioAt`, `ratioDefault`, `HasDensity`.
  These require explicit summability data (or the bundled `seriesSummableProof` witness).
* **Secondary (unguarded):** `series`, `seriesAll`. These are `LSeries` values and are **only
  valid inputs when `SeriesSummable` holds**; otherwise `LSeries` silently returns `0`.
  Use `seriesAt_eq_series` / `ratioDefault_of_one_lt` (which assume `1 < s`) to unfold to them.

### Design principles

* Dirichlet series via mathlib's `LSeries` API.
* Summability on `s > 1` from `LSeriesSummable_of_bounded_of_one_lt_real`.
* `ratioAt` is summability-guarded (mirroring `idealRatioAt`) and is `0` for `s ≤ 1`.
* `HasDensity` is `Tendsto (ratioAt …)` along `nhdsWithin 1 (Set.Ioi 1)`.
-/

namespace PrimeNumberTheoremAnd

open scoped Topology Real
open scoped LSeries.notation

open Filter

namespace DirichletDensity

open Classical
open Complex

section Coeff

variable (S : Set ℕ)

/--
The Dirichlet coefficient sequence of a set of primes `S`.

Only prime indices contribute: for composite `n`, `coeff S n = 0`.
-/
noncomputable def coeff (S : Set ℕ) : ℕ → ℂ := by
  classical
  exact fun n ↦ if n.Prime ∧ n ∈ S then 1 else 0

lemma coeff_apply (S : Set ℕ) (n : ℕ) :
    coeff S n = if n.Prime ∧ n ∈ S then 1 else 0 := by
  classical
  rfl

@[simp]
lemma coeff_zero (S : Set ℕ) : coeff S 0 = 0 := by
  classical
  rw [coeff]
  simp [Nat.not_prime_zero]

@[simp]
lemma coeff_of_not_prime (S : Set ℕ) {n : ℕ} (hn : ¬ n.Prime) : coeff S n = 0 := by
  rw [coeff]
  simp [hn]

@[simp]
lemma coeff_mem (S : Set ℕ) {n : ℕ} (hn : n.Prime) (h : n ∈ S) : coeff S n = 1 := by
  rw [coeff]
  simp [hn, h]

@[simp]
lemma coeff_not_mem (S : Set ℕ) {n : ℕ} (hn : n.Prime) (h : n ∉ S) : coeff S n = 0 := by
  classical
  rw [coeff]
  simp [hn, h]

@[simp]
lemma coeff_of_prime (S : Set ℕ) {n : ℕ} (hn : n.Prime) :
    coeff S n = if n ∈ S then 1 else 0 := by
  by_cases h : n ∈ S
  · rw [coeff_mem S hn h, if_pos h]
  · rw [coeff_not_mem S hn h, if_neg h]

lemma norm_coeff_le_one (S : Set ℕ) (n : ℕ) : ‖coeff S n‖ ≤ (1 : ℝ) := by
  classical
  by_cases h : n.Prime ∧ n ∈ S
  · simp [coeff, h]
  · simp [coeff, h]

end Coeff

section Series

variable (S : Set ℕ)

/--
The prime Dirichlet series attached to `S` (as a function of a real variable `s`).

**Unguarded:** this is `LSeries (coeff S) s`, which is `0` when the series diverges.
Prefer `seriesAt` when a summability witness is available.
-/
noncomputable def series (S : Set ℕ) (s : ℝ) : ℂ :=
  LSeries (coeff S) (s : ℂ)

/-- A single term of the prime Dirichlet series at `s`. -/
noncomputable def seriesTerm (S : Set ℕ) (s : ℝ) (n : ℕ) : ℂ :=
  LSeries.term (coeff S) (s : ℂ) n

/-- Absolute convergence of the prime Dirichlet series at `s`. -/
def SeriesSummable (S : Set ℕ) (s : ℝ) : Prop :=
  LSeriesSummable (coeff S) (s : ℂ)

lemma summable_series (S : Set ℕ) {s : ℝ} (hs : 1 < s) : SeriesSummable S s := by
  dsimp [SeriesSummable]
  refine LSeriesSummable_of_bounded_of_one_lt_real (f := coeff S) (m := (1 : ℝ))
    (fun n _ ↦ norm_coeff_le_one S n) hs

lemma seriesSummable_iff_summable_seriesTerm (S : Set ℕ) (s : ℝ) :
    SeriesSummable S s ↔ Summable (seriesTerm S s) := by
  simp only [SeriesSummable, LSeriesSummable]
  exact summable_congr (by funext; simp [seriesTerm])

theorem seriesSummable_of_one_lt (S : Set ℕ) {s : ℝ} (hs : 1 < s) :
    SeriesSummable S s ∧ SeriesSummable (Set.univ : Set ℕ) s :=
  ⟨summable_series S hs, summable_series (Set.univ : Set ℕ) hs⟩

theorem seriesSummableProof (S : Set ℕ) :
    ∀ {s : ℝ}, 1 < s → SeriesSummable S s ∧ SeriesSummable (Set.univ : Set ℕ) s :=
  fun {_} hs => seriesSummable_of_one_lt S hs

/-- The denominator series: sum over all primes. -/
noncomputable abbrev seriesAll (s : ℝ) : ℂ :=
  series (S := (Set.univ : Set ℕ)) s

/--
The prime Dirichlet series at `s`, guarded by a summability proof.

This is the **primary** series API: the value is the unconditional sum `∑' n, seriesTerm S s n`.
When summable, `seriesAt_eq_series` rewrites to the unguarded `series`.
-/
noncomputable def seriesAt (S : Set ℕ) (s : ℝ) (hS : SeriesSummable S s) : ℂ := by
  classical
  haveI : Summable (seriesTerm S s) := (seriesSummable_iff_summable_seriesTerm S s).1 hS
  exact ∑' n, seriesTerm S s n

/-- Denominator series at `s`, guarded by a summability proof. -/
noncomputable def seriesAllAt (s : ℝ) (hAll : SeriesSummable (Set.univ : Set ℕ) s) : ℂ :=
  seriesAt (Set.univ : Set ℕ) s hAll

@[simp]
lemma seriesAt_eq_series (S : Set ℕ) (s : ℝ) (hS : SeriesSummable S s) :
    seriesAt S s hS = series S s := by
  classical
  haveI : Summable (seriesTerm S s) := (seriesSummable_iff_summable_seriesTerm S s).1 hS
  simp [seriesAt, series, seriesTerm, LSeries]

@[simp]
lemma seriesAllAt_eq_seriesAll (s : ℝ) (hAll : SeriesSummable (Set.univ : Set ℕ) s) :
    seriesAllAt s hAll = seriesAll s :=
  seriesAt_eq_series _ s hAll

end Series

section Ratio

variable (S : Set ℕ)

/--
The Dirichlet-density ratio at `s`, with explicit summability hypotheses.

Use `ratioAt` for the bundled version used in `HasDensity`.
-/
noncomputable def ratio (S : Set ℕ) (s : ℝ)
    (hS : SeriesSummable S s) (hAll : SeriesSummable (Set.univ : Set ℕ) s) : ℂ :=
  seriesAt S s hS / seriesAllAt s hAll

/--
Summability-guarded density ratio: the series quotient for `s > 1`, and `0` otherwise.

Mirrors `idealRatioAt` in `DirichletDensityIdeals.lean`.
-/
noncomputable def ratioAt (S : Set ℕ)
    (proof :
      ∀ {s : ℝ}, 1 < s → SeriesSummable S s ∧ SeriesSummable (Set.univ : Set ℕ) s) (s : ℝ) :
    ℂ :=
  if hs : 1 < s then
    ratio S s (proof hs).1 (proof hs).2
  else 0

/-- Canonical density ratio using `seriesSummableProof`. -/
noncomputable def ratioDefault (S : Set ℕ) (s : ℝ) : ℂ :=
  ratioAt S (seriesSummableProof S) s

lemma ratioAt_of_one_lt (S : Set ℕ)
    (proof : ∀ {s : ℝ}, 1 < s → SeriesSummable S s ∧ SeriesSummable (Set.univ : Set ℕ) s)
    {s : ℝ} (hs : 1 < s) :
    ratioAt S proof s = ratio S s (proof hs).1 (proof hs).2 := by
  simp [ratioAt, hs]

/--
At `s > 1`, the ratio unfolds to `series S s / seriesAll s`. The denominator is nonzero
(`seriesAll_ne_zero_of_one_lt` in `SeriesAllDivergesNearOne.lean`).
-/
lemma ratioDefault_of_one_lt (S : Set ℕ) {s : ℝ} (hs : 1 < s) :
    ratioDefault S s = series S s / seriesAll s := by
  simp [ratioDefault, ratioAt, ratio, hs]

lemma ratioAt_eq_ratioAt_of_proof (S : Set ℕ)
    {proof proof' : ∀ {s : ℝ}, 1 < s → SeriesSummable S s ∧ SeriesSummable (Set.univ : Set ℕ) s}
    {s : ℝ} (hs : 1 < s) :
    ratioAt S proof s = ratioAt S proof' s := by
  simp [ratioAt, ratio, hs]

end Ratio

section HasDensity

variable (S : Set ℕ)

/--
`HasDensity S δ` means that the Dirichlet density of `S` exists and equals `δ`, defined as a
limit as `s → 1⁺` of the summability-guarded ratio `ratioAt`.

We take values in `ℂ` because `LSeries` is `ℂ`-valued; later developments can show the value is
real when `S` is a set of primes.

See `hasDensity_iff_tendsto_ratioDefault` for the canonical summability witness.
-/
def HasDensity (S : Set ℕ) (delta : ℂ) : Prop :=
  ∃ (proof : ∀ {s : ℝ}, 1 < s → SeriesSummable S s ∧ SeriesSummable (Set.univ : Set ℕ) s),
    Tendsto (ratioAt S proof) (nhdsWithin 1 (Set.Ioi 1)) (nhds delta)

lemma hasDensity_iff_tendsto_ratioDefault (S : Set ℕ) (delta : ℂ) :
    HasDensity S delta ↔
      Tendsto (ratioDefault S) (nhdsWithin 1 (Set.Ioi 1)) (nhds delta) := by
  constructor
  · rintro ⟨proof, h⟩
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    change ratioDefault S s = ratioAt S proof s
    simp [ratioDefault]
  · intro h
    exact ⟨seriesSummableProof S, h⟩

theorem hasDensity_of_tendsto_ratioDefault (S : Set ℕ) (delta : ℂ)
    (h : Tendsto (ratioDefault S) (nhdsWithin 1 (Set.Ioi 1)) (nhds delta)) :
    HasDensity S delta :=
  (hasDensity_iff_tendsto_ratioDefault S delta).2 h

end HasDensity

end DirichletDensity

end PrimeNumberTheoremAnd
