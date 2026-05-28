import PrimeNumberTheoremAnd.Chebotarev.Density.DirichletDensityIntBridge
import PrimeNumberTheoremAnd.Chebotarev.Density.PrimeSeriesSummable

import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Ideal-norm series summability for `ℤ`

Proves `IdealSeriesSummable` at `s > 1` for sets of prime ideals of `ℤ`.

The bijection `(p) ↔ p` and norm identities are in `DirichletDensityIntBridge.lean`.
This file compares `‖idealSeriesTerm S P s‖` with the rational prime series `∑ p^{-s}`.
-/

namespace PrimeNumberTheoremAnd

open scoped Real Topology

namespace DirichletDensity

open Complex Filter Ideal Nat

section IntIdealNormBounds

lemma norm_idealNormTerm_eq (P : PrimeIdeal ℤ) {s : ℝ} :
    ‖idealNormTerm P s‖ = (Ideal.absNorm P.1 : ℝ) ^ (-s) := by
  simp [idealNormTerm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg,
    Real.rpow_nonneg (Nat.cast_nonneg _)]

lemma norm_idealSeriesTerm_le (S : Set (PrimeIdeal ℤ)) (P : PrimeIdeal ℤ) {s : ℝ} (hs : 1 < s) :
    ‖idealSeriesTerm S P s‖ ≤ (Ideal.absNorm P.1 : ℝ) ^ (-s) := by
  by_cases hmem : P ∈ S
  · rw [← norm_idealNormTerm_eq P]
    simp [idealSeriesTerm, idealCoeff, hmem]
  · simp [idealSeriesTerm, idealCoeff, hmem, Real.rpow_nonneg (Nat.cast_nonneg _)]

end IntIdealNormBounds

section IntIdealSummability

open Nat.Primes

noncomputable def absNormPowNeg (s : ℝ) : PrimeIdeal ℤ → ℝ :=
  fun P => (Ideal.absNorm P.1 : ℝ) ^ (-s)

noncomputable def optionAbsNormPowNeg (s : ℝ) : Option Nat.Primes → ℝ
  | none => 0
  | some p => (p : ℝ) ^ (-s)

noncomputable def sumNormTerm (s : ℝ) : Nat.Primes ⊕ Unit → ℝ
  | Sum.inl p => (p : ℝ) ^ (-s)
  | Sum.inr _ => 0

noncomputable def primeOptionEquiv : Option Nat.Primes ≃ Nat.Primes ⊕ Unit where
  toFun
  | none => Sum.inr ()
  | some p => Sum.inl p
  invFun
  | Sum.inl p => some p
  | Sum.inr _ => none
  left_inv o := by cases o <;> rfl
  right_inv u := by cases u <;> rfl

private lemma absNormPowNeg_eq_optionAbsNormPowNeg {s : ℝ} (hs : 0 < s) (P : PrimeIdeal ℤ) :
    absNormPowNeg s P = optionAbsNormPowNeg s (primeIdealToOption P) := by
  by_cases h : P.1 = ⊥
  · have hsneg : (-s : ℝ) ≠ 0 := by linarith
    simp [absNormPowNeg, optionAbsNormPowNeg, primeIdealToOption, h,
      Ideal.absNorm_bot, Real.zero_rpow hsneg]
  · simp [absNormPowNeg, optionAbsNormPowNeg, primeIdealToOption, h,
      absNorm_pow_eq_natPrime_pow ⟨P, h⟩ s]

private lemma summable_optionAbsNormPowNeg (s : ℝ) (hs : 1 < s) :
    Summable (optionAbsNormPowNeg s) := by
  have hprimes : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-s)) :=
    (Nat.Primes.summable_rpow (r := (-s : ℝ))).2 (by linarith)
  have hOnSum : Summable (sumNormTerm s) :=
    Summable.sum (sumNormTerm s) hprimes summable_zero
  convert (Equiv.summable_iff primeOptionEquiv).mpr hOnSum using 1
  funext o
  cases o <;> simp [optionAbsNormPowNeg, sumNormTerm, primeOptionEquiv, Function.comp]

private lemma summable_absNormPowNeg (s : ℝ) (hs : 1 < s) :
    Summable (absNormPowNeg s) := by
  have hEq : absNormPowNeg s = optionAbsNormPowNeg s ∘ primeIdealOptionEquiv :=
    funext fun P => by
      simp [primeIdealOptionEquiv, absNormPowNeg_eq_optionAbsNormPowNeg (by linarith)]
  rw [hEq]
  refine (Equiv.summable_iff primeIdealOptionEquiv).mpr ?_
  exact summable_optionAbsNormPowNeg s hs

/--
The prime-ideal Dirichlet series for `S` converges absolutely at `s > 1` when `R = ℤ`.

See `DirichletDensityIdeals.IdealSeriesSummable`.
-/
theorem IdealSeriesSummable_int {S : Set (PrimeIdeal ℤ)} {s : ℝ} (hs : 1 < s) :
    IdealSeriesSummable (R := ℤ) S s := by
  refine Summable.of_norm_bounded (g := absNormPowNeg s) (summable_absNormPowNeg s hs)
    (fun P => norm_idealSeriesTerm_le S P hs)

/--
The full prime-ideal series over `Set.univ` converges absolutely at `s > 1` when `R = ℤ`.
-/
theorem idealSeriesSummable_all_int {s : ℝ} (hs : 1 < s) :
    IdealSeriesSummable (R := ℤ) (Set.univ : Set (PrimeIdeal ℤ)) s :=
  IdealSeriesSummable_int (S := Set.univ) hs

/--
Bundled summability proofs for `idealRatioAt` at `s > 1` when `R = ℤ`.

This is the canonical input for `HasIdealDensity` in the `ℤ` case.
-/
noncomputable def idealSeriesSummableProof_int (S : Set (PrimeIdeal ℤ)) :
    ∀ {s : ℝ}, 1 < s →
      IdealSeriesSummable (R := ℤ) S s ∧
        IdealSeriesSummable (R := ℤ) (Set.univ : Set (PrimeIdeal ℤ)) s :=
  fun hs => ⟨IdealSeriesSummable_int (S := S) hs, idealSeriesSummable_all_int hs⟩

end IntIdealSummability

end DirichletDensity

end PrimeNumberTheoremAnd
