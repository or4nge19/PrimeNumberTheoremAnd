module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# A Weil--Guinand explicit-formula interface

This file isolates the formal shape of the `q = 1` Weil--Guinand explicit formula used in
Kadiri's zero-free-region argument.  The analytic contour-shift theorem is represented by
`QOneFormula`; this file records the common terms and proves the real-part consequences that only
use summability and algebra.  The regularity assumptions from Kadiri's conditions (A) and (B) are
not bundled into `QOneFormula`: condition (A) allows finitely many first-kind discontinuities, so
those hypotheses belong to the later analytic theorem that proves this abstract formula.

The definitions are indexed by an abstract zero type.  In applications to the Riemann zeta
function, the zero index is usually `riemannZeta.zeroes_rect (.Ioo 0 1) .univ`, with multiplicity
encoded in the index or the coefficients.  Prime sums are indexed by `ℕ+`, so the term `log n`
never has to be interpreted at `n = 0`.
-/

@[expose] public section

open scoped Topology

open Complex MeasureTheory

namespace RiemannZeta
namespace WeilGuinand

/-- The Laplace transform on the positive half-line, in the normalization used by
Weil--Guinand formulas. -/
noncomputable def laplaceTransform (φ : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ y in Set.Ioi (0 : ℝ), φ y * Complex.exp (-s * (y : ℂ)) ∂volume

@[simp]
theorem laplaceTransform_zero (s : ℂ) :
    laplaceTransform (fun _ : ℝ => 0) s = 0 := by
  simp [laplaceTransform]

theorem laplaceTransform_congr {φ ψ : ℝ → ℂ} (h : ∀ y, φ y = ψ y) (s : ℂ) :
    laplaceTransform φ s = laplaceTransform ψ s := by
  simp [laplaceTransform, h]

/-- The prime-side sum in a Weil--Guinand formula, parametrized by its arithmetic coefficients. -/
noncomputable def primeSum (a : ℕ → ℂ) (φ : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ+, a n * φ (Real.log (n : ℕ))

@[simp]
theorem primeSum_zero_coeff (φ : ℝ → ℂ) :
    primeSum (fun _ : ℕ => 0) φ = 0 := by
  simp [primeSum]

@[simp]
theorem primeSum_zero_test (a : ℕ → ℂ) :
    primeSum a (fun _ : ℝ => 0) = 0 := by
  simp [primeSum]

theorem primeSum_congr {a b : ℕ → ℂ} {φ ψ : ℝ → ℂ}
    (ha : ∀ n : ℕ+, a n = b n)
    (hφ : ∀ n : ℕ+, φ (Real.log (n : ℕ)) = ψ (Real.log (n : ℕ))) :
    primeSum a φ = primeSum b ψ := by
  apply tsum_congr
  intro n
  simp [ha n, hφ n]

/-- The reflected prime-side sum in a Weil--Guinand formula. -/
noncomputable def reflectedPrimeSum (a : ℕ → ℂ) (φ : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ+, a n * φ (-Real.log (n : ℕ))

@[simp]
theorem reflectedPrimeSum_zero_coeff (φ : ℝ → ℂ) :
    reflectedPrimeSum (fun _ : ℕ => 0) φ = 0 := by
  simp [reflectedPrimeSum]

@[simp]
theorem reflectedPrimeSum_zero_test (a : ℕ → ℂ) :
    reflectedPrimeSum a (fun _ : ℝ => 0) = 0 := by
  simp [reflectedPrimeSum]

theorem reflectedPrimeSum_congr {a b : ℕ → ℂ} {φ ψ : ℝ → ℂ}
    (ha : ∀ n : ℕ+, a n = b n)
    (hφ : ∀ n : ℕ+, φ (-Real.log (n : ℕ)) = ψ (-Real.log (n : ℕ))) :
    reflectedPrimeSum a φ = reflectedPrimeSum b ψ := by
  apply tsum_congr
  intro n
  simp [ha n, hφ n]

/-- The zero contribution in a Weil--Guinand formula. -/
noncomputable def zeroSum {ι : Type*} (zero : ι → ℂ) (Φ : ℂ → ℂ) : ℂ :=
  ∑' ρ : ι, Φ (-zero ρ)

@[simp]
theorem zeroSum_zero_transform {ι : Type*} (zero : ι → ℂ) :
    zeroSum zero (fun _ : ℂ => 0) = 0 := by
  simp [zeroSum]

@[simp]
theorem zeroSum_empty {ι : Type*} [IsEmpty ι] (zero : ι → ℂ) (Φ : ℂ → ℂ) :
    zeroSum zero Φ = 0 := by
  simp [zeroSum]

theorem zeroSum_congr {ι : Type*} {zero₁ zero₂ : ι → ℂ} {Φ Ψ : ℂ → ℂ}
    (h : ∀ ρ, Φ (-zero₁ ρ) = Ψ (-zero₂ ρ)) :
    zeroSum zero₁ Φ = zeroSum zero₂ Ψ := by
  apply tsum_congr
  intro ρ
  exact h ρ

/-- The integrand in the gamma-line term of the `q = 1` Weil--Guinand formula. -/
noncomputable def gammaIntegrand (Φ : ℂ → ℂ) (t : ℝ) : ℂ :=
  ((Complex.digamma ((1 / 2 + (t : ℂ) * Complex.I) / 2)).re : ℂ) *
    Φ (-(1 / 2 + (t : ℂ) * Complex.I))

@[simp]
theorem gammaIntegrand_zero (t : ℝ) :
    gammaIntegrand (fun _ : ℂ => 0) t = 0 := by
  simp [gammaIntegrand]

theorem gammaIntegrand_congr {Φ Ψ : ℂ → ℂ} (h : ∀ z, Φ z = Ψ z) :
    gammaIntegrand Φ = gammaIntegrand Ψ := by
  funext t
  simp [gammaIntegrand, h]

/-- The gamma-line integral in the `q = 1`, trivial-character Weil--Guinand formula,
parametrized by `z = 1/2 + it`.  The factor is `1 / (2π)` after substituting
`dz = i dt` in the contour integral. -/
noncomputable def gammaIntegral (Φ : ℂ → ℂ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, gammaIntegrand Φ t

@[simp]
theorem gammaIntegral_zero :
    gammaIntegral (fun _ : ℂ => 0) = 0 := by
  simp [gammaIntegral]

theorem gammaIntegral_congr {Φ Ψ : ℂ → ℂ} (h : ∀ z, Φ z = Ψ z) :
    gammaIntegral Φ = gammaIntegral Ψ := by
  rw [gammaIntegral, gammaIntegral, gammaIntegrand_congr h]

/-- The right-hand side of the `q = 1`, trivial-character Weil--Guinand formula. -/
noncomputable def qOneRHS {ι : Type*} (φ : ℝ → ℂ) (Φ : ℂ → ℂ)
    (reflectedCoeff : ℕ → ℂ) (zero : ι → ℂ) : ℂ :=
  Φ (-1) + Φ 0 - zeroSum zero Φ - φ 0 * (Real.log Real.pi : ℂ) +
    reflectedPrimeSum reflectedCoeff φ + gammaIntegral Φ

@[simp]
theorem qOneRHS_zero {ι : Type*} (zero : ι → ℂ) :
    qOneRHS (fun _ : ℝ => 0) (fun _ : ℂ => 0) (fun _ : ℕ => 0) zero = 0 := by
  simp [qOneRHS]

/-- The assertion that the `q = 1`, trivial-character Weil--Guinand explicit formula holds for
the supplied coefficients and zero indexing. -/
structure QOneFormula {ι : Type*} (φ : ℝ → ℂ) (Φ : ℂ → ℂ)
    (primeCoeff reflectedCoeff : ℕ → ℂ) (zero : ι → ℂ) : Prop where
  transform_eq_laplace : ∀ z : ℂ, Φ z = laplaceTransform φ z
  prime_summable :
    Summable (fun n : ℕ+ => primeCoeff n * φ (Real.log (n : ℕ)))
  reflected_prime_summable :
    Summable (fun n : ℕ+ => reflectedCoeff n * φ (-Real.log (n : ℕ)))
  zero_summable : Summable (fun ρ : ι => Φ (-zero ρ))
  gamma_integrable : Integrable (gammaIntegrand Φ)
  formula : primeSum primeCoeff φ = qOneRHS φ Φ reflectedCoeff zero

/-- The abstract formula with its auxiliary transform replaced by the actual Laplace transform. -/
theorem QOneFormula.formula_laplace {ι : Type*} {φ : ℝ → ℂ} {Φ : ℂ → ℂ}
    {primeCoeff reflectedCoeff : ℕ → ℂ} {zero : ι → ℂ}
    (h : QOneFormula φ Φ primeCoeff reflectedCoeff zero) :
    primeSum primeCoeff φ = qOneRHS φ (laplaceTransform φ) reflectedCoeff zero := by
  rw [h.formula]
  simp [qOneRHS, zeroSum, gammaIntegral, gammaIntegrand, h.transform_eq_laplace]

/-- Real part commutes with a summable infinite sum. -/
theorem re_tsum {ι : Type*} {f : ι → ℂ} (hf : Summable f) :
    (∑' i : ι, f i).re = ∑' i : ι, (f i).re := by
  simpa using ContinuousLinearMap.map_tsum Complex.reCLM hf

/-- A sum over positive naturals agrees with the corresponding sum over naturals when the
zero term is zero. -/
theorem tsum_nat_eq_tsum_pnat_of_zero {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    {f : ℕ → α} (hf0 : f 0 = 0) :
    (∑' n : ℕ, f n) = ∑' n : ℕ+, f n := by
  have hsupport : Function.support f ⊆ Set.range ((↑) : ℕ+ → ℕ) := by
    intro n hn
    rw [Function.mem_support] at hn
    by_cases hn0 : n = 0
    · exact (hn (hn0.symm ▸ hf0)).elim
    · exact ⟨⟨n, Nat.pos_of_ne_zero hn0⟩, rfl⟩
  rw [← tsum_subtype_eq_of_support_subset hsupport]
  rw [← (Equiv.ofInjective PNat.val PNat.coe_injective).tsum_eq]
  rfl

/-- Rewrite the prime-side sum as a natural-number sum when the coefficient at zero vanishes. -/
theorem primeSum_eq_tsum_nat {a : ℕ → ℂ} {φ : ℝ → ℂ} (ha0 : a 0 = 0) :
    primeSum a φ = ∑' n : ℕ, a n * φ (Real.log n) := by
  have h0 : (fun n : ℕ => a n * φ (Real.log n)) 0 = 0 := by simp [ha0]
  simpa [primeSum] using
    (tsum_nat_eq_tsum_pnat_of_zero (f := fun n : ℕ => a n * φ (Real.log n)) h0).symm

/-- Rewrite the reflected prime-side sum as a natural-number sum when the coefficient at zero
vanishes. -/
theorem reflectedPrimeSum_eq_tsum_nat {a : ℕ → ℂ} {φ : ℝ → ℂ} (ha0 : a 0 = 0) :
    reflectedPrimeSum a φ = ∑' n : ℕ, a n * φ (-Real.log n) := by
  have h0 : (fun n : ℕ => a n * φ (-Real.log n)) 0 = 0 := by simp [ha0]
  simpa [reflectedPrimeSum] using
    (tsum_nat_eq_tsum_pnat_of_zero (f := fun n : ℕ => a n * φ (-Real.log n)) h0).symm

/-- Real part of the zero contribution. -/
theorem zeroSum_re {ι : Type*} {zero : ι → ℂ} {Φ : ℂ → ℂ}
    (hΦ : Summable (fun ρ : ι => Φ (-zero ρ))) :
    (zeroSum zero Φ).re = ∑' ρ : ι, (Φ (-zero ρ)).re := by
  simpa [zeroSum] using re_tsum hΦ

theorem QOneFormula.zeroSum_re {ι : Type*} {φ : ℝ → ℂ} {Φ : ℂ → ℂ}
    {primeCoeff reflectedCoeff : ℕ → ℂ} {zero : ι → ℂ}
    (h : QOneFormula φ Φ primeCoeff reflectedCoeff zero) :
    (zeroSum zero Φ).re = ∑' ρ : ι, (Φ (-zero ρ)).re :=
  RiemannZeta.WeilGuinand.zeroSum_re h.zero_summable

theorem QOneFormula.zero_summable_laplace {ι : Type*} {φ : ℝ → ℂ} {Φ : ℂ → ℂ}
    {primeCoeff reflectedCoeff : ℕ → ℂ} {zero : ι → ℂ}
    (h : QOneFormula φ Φ primeCoeff reflectedCoeff zero) :
    Summable (fun ρ : ι => laplaceTransform φ (-zero ρ)) := by
  simpa [h.transform_eq_laplace] using h.zero_summable

/-- The real form of an abstract `q = 1` Weil--Guinand formula. -/
theorem QOneFormula.real_formula {ι : Type*} {φ : ℝ → ℂ} {Φ : ℂ → ℂ}
    {primeCoeff reflectedCoeff : ℕ → ℂ} {zero : ι → ℂ}
    (h : QOneFormula φ Φ primeCoeff reflectedCoeff zero) :
    (primeSum primeCoeff φ).re =
      (Φ (-1)).re + (Φ 0).re - ∑' ρ : ι, (Φ (-zero ρ)).re -
        (φ 0 * (Real.log Real.pi : ℂ)).re +
        (reflectedPrimeSum reflectedCoeff φ).re + (gammaIntegral Φ).re := by
  rw [h.formula]
  simp [qOneRHS, RiemannZeta.WeilGuinand.zeroSum_re h.zero_summable, add_assoc]

/-- The real form after replacing the auxiliary transform by its Laplace-transform definition. -/
theorem QOneFormula.real_formula_laplace {ι : Type*} {φ : ℝ → ℂ} {Φ : ℂ → ℂ}
    {primeCoeff reflectedCoeff : ℕ → ℂ} {zero : ι → ℂ}
    (h : QOneFormula φ Φ primeCoeff reflectedCoeff zero) :
    (primeSum primeCoeff φ).re =
      (laplaceTransform φ (-1)).re + (laplaceTransform φ 0).re -
        ∑' ρ : ι, (laplaceTransform φ (-zero ρ)).re -
        (φ 0 * (Real.log Real.pi : ℂ)).re +
        (reflectedPrimeSum reflectedCoeff φ).re +
        (gammaIntegral (laplaceTransform φ)).re := by
  rw [h.real_formula]
  simp [h.transform_eq_laplace, gammaIntegral, gammaIntegrand]

end WeilGuinand
end RiemannZeta
