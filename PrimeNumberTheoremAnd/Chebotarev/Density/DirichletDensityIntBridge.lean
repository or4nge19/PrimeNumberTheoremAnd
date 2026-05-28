import PrimeNumberTheoremAnd.Chebotarev.Density.DirichletDensityIdeals

import Mathlib.RingTheory.Ideal.NatInt
import Mathlib.RingTheory.Ideal.Int

/-!
# Dirichlet density bridge for `ℤ`

Rational-prime Dirichlet density (`HasDensity` on `Set ℕ`) and ideal-norm density
(`HasIdealDensity` on `Set (PrimeIdeal ℤ)`) use the same local weights once prime ideals
are identified with rational primes via `(p) ↦ p`.

## Index-set convention

Mathlib's `Ideal.isPrime_int_iff` treats `⊥` as a prime ideal of `ℤ`. Accordingly,
`PrimeIdeal ℤ` has one extra point beyond the usual prime ideals `(p)`.
The subtype `NonZeroPrimeIdeal ℤ` is the mathematically standard index set; the equiv
`primeIdealOptionEquiv : PrimeIdeal ℤ ≃ Option Nat.Primes` records the decomposition
into `{⊥}` and the prime-indexed part.

Summability at `s > 1` is proved in `DirichletDensityIntSummability.lean`.
The density transfer `HasIdealDensity S δ ↔ HasDensity (natPrimeImageOf S) δ` is tracked in
`OpenHypotheses.hasIdealDensity_iff_hasDensity_natPrimeImageOf` (`sorry`).
-/

namespace PrimeNumberTheoremAnd

namespace DirichletDensity

open Complex Ideal Nat

open scoped Real

section NonZeroPrimeIdeal

variable {R : Type*} [CommRing R]

/--
Prime ideals of `R` whose underlying ideal is not `⊥`.

For `R = ℤ` this is the index set of genuine prime ideals `(p)`.
-/
abbrev NonZeroPrimeIdeal (R : Type*) [CommRing R] :=
  {P : PrimeIdeal R // P.1 ≠ ⊥}

@[simp] lemma NonZeroPrimeIdeal.coe_val (P : NonZeroPrimeIdeal R) : P.val = P.1 := rfl

lemma NonZeroPrimeIdeal.ne_bot (P : NonZeroPrimeIdeal R) : P.1.1 ≠ ⊥ := P.2

end NonZeroPrimeIdeal

section IntPrimeBridge

/--
The prime ideal `(p)` in `ℤ`, for `p` a rational prime.

See `coe_primeIdealOfNatPrime`.
-/
noncomputable def primeIdealOfNatPrime (p : Nat.Primes) : PrimeIdeal ℤ :=
  ⟨Ideal.span {(p : ℤ)}, by
    rw [Ideal.isPrime_int_iff]
    exact Or.inr ⟨p.1, p.2, rfl⟩⟩

@[simp]
lemma coe_primeIdealOfNatPrime (p : Nat.Primes) :
    (primeIdealOfNatPrime p).1 = Ideal.span {(p : ℤ)} := rfl

@[simp]
lemma absNorm_primeIdealOfNatPrime (p : Nat.Primes) :
    Ideal.absNorm (primeIdealOfNatPrime p).1 = p.1 := by
  simp [primeIdealOfNatPrime]

lemma primeIdealOfNatPrime_ne_bot (p : Nat.Primes) : (primeIdealOfNatPrime p).1 ≠ ⊥ := by
  rw [coe_primeIdealOfNatPrime]
  exact Ideal.span_singleton_eq_bot.not.mpr (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero p.2))

lemma absNorm_eq_of_eq_span (p q : Nat.Primes)
    (h : (primeIdealOfNatPrime p).1 = (primeIdealOfNatPrime q).1) : (p : ℕ) = (q : ℕ) := by
  have := congrArg Ideal.absNorm h
  simpa [absNorm_primeIdealOfNatPrime] using this

lemma primeIdealOfNatPrime_injective :
    Function.Injective (fun p : Nat.Primes => primeIdealOfNatPrime p) := by
  intro p q h
  apply Subtype.ext
  exact absNorm_eq_of_eq_span p q (congrArg Subtype.val h)

lemma exists_span_singleton_of_nonZeroPrimeIdeal (P : NonZeroPrimeIdeal ℤ) :
    ∃ p : Nat.Primes, P.1.1 = Ideal.span {(p : ℤ)} := by
  rcases (Ideal.isPrime_int_iff.mp P.1.2) with hbot | ⟨p, hp, hP⟩
  · exact (P.2 hbot).elim
  · exact ⟨⟨p, hp⟩, hP⟩

/--
The rational prime attached to a nonzero prime ideal of `ℤ`.

Defined as the absolute norm of the underlying ideal; see `natPrimeOf_eq_absNorm`.
-/
noncomputable def natPrimeOfNonZeroPrimeIdeal (P : NonZeroPrimeIdeal ℤ) : Nat.Primes :=
  have h := exists_span_singleton_of_nonZeroPrimeIdeal P
  have hn : Nat.Prime (Ideal.absNorm P.1.1) := by
    obtain ⟨p, hP⟩ := h
    have : Ideal.absNorm P.1.1 = p.1 := by simp [hP]
    rw [this]
    exact p.2
  ⟨Ideal.absNorm P.1.1, hn⟩

@[simp]
lemma natPrimeOf_eq_absNorm (P : NonZeroPrimeIdeal ℤ) :
    (natPrimeOfNonZeroPrimeIdeal P : ℕ) = Ideal.absNorm P.1.1 := rfl

lemma span_eq_of_natPrimeOfNonZeroPrimeIdeal (P : NonZeroPrimeIdeal ℤ) :
    P.1.1 = Ideal.span {(natPrimeOfNonZeroPrimeIdeal P : ℤ)} := by
  obtain ⟨p, hP⟩ := exists_span_singleton_of_nonZeroPrimeIdeal P
  have hp_eq : (p : ℕ) = natPrimeOfNonZeroPrimeIdeal P := by
    have : Ideal.absNorm P.1.1 = (p : ℕ) := by
      simp [hP]
    exact this.symm.trans (natPrimeOf_eq_absNorm P)
  rw [hP]
  congr 1
  rw [hp_eq]

lemma primeIdealOfNatPrime_eq_of_nonZero (P : NonZeroPrimeIdeal ℤ) :
    (primeIdealOfNatPrime (natPrimeOfNonZeroPrimeIdeal P)).1 = P.1.1 := by
  rw [coe_primeIdealOfNatPrime, span_eq_of_natPrimeOfNonZeroPrimeIdeal P]

lemma natPrimeOf_span (p : Nat.Primes) :
    natPrimeOfNonZeroPrimeIdeal ⟨primeIdealOfNatPrime p, primeIdealOfNatPrime_ne_bot p⟩ = p := by
  apply Subtype.ext
  simp [natPrimeOf_eq_absNorm]

/-- Equivalence between rational primes and nonzero prime ideals of `ℤ`. -/
noncomputable def primeIdealNatEquiv : Nat.Primes ≃ NonZeroPrimeIdeal ℤ where
  toFun p := ⟨primeIdealOfNatPrime p, primeIdealOfNatPrime_ne_bot p⟩
  invFun := natPrimeOfNonZeroPrimeIdeal
  left_inv := natPrimeOf_span
  right_inv P := by
    apply Subtype.ext
    apply Subtype.ext
    exact primeIdealOfNatPrime_eq_of_nonZero P

/--
The prime ideal `⊥` expressed as a `PrimeIdeal ℤ`.

This is the extra point in `PrimeIdeal ℤ` coming from `Ideal.isPrime_int_iff`.
See `botPrimeIdeal_val`.
-/
noncomputable def botPrimeIdeal : PrimeIdeal ℤ :=
  ⟨Ideal.span {(0 : ℤ)}, by
    rw [Ideal.isPrime_int_iff]
    exact Or.inl (by simp)⟩

@[simp]
lemma botPrimeIdeal_val : botPrimeIdeal.1 = ⊥ := by
  simp [botPrimeIdeal]

lemma botPrimeIdeal_ne_of_nonZero (P : NonZeroPrimeIdeal ℤ) : P.1 ≠ botPrimeIdeal := by
  intro h
  have : P.1.1 = ⊥ := by simpa [botPrimeIdeal_val] using congrArg Subtype.val h
  exact P.2 this

noncomputable def primeIdealToOption (P : PrimeIdeal ℤ) : Option Nat.Primes :=
  if h : P.1 = ⊥ then none
  else some (natPrimeOfNonZeroPrimeIdeal ⟨P, h⟩)

noncomputable def optionToPrimeIdeal : Option Nat.Primes → PrimeIdeal ℤ
  | none => botPrimeIdeal
  | some p => primeIdealOfNatPrime p

lemma optionToPrimeIdeal_toOption (P : PrimeIdeal ℤ) :
    optionToPrimeIdeal (primeIdealToOption P) = P := by
  by_cases h : P.1 = ⊥
  · have hP : P = botPrimeIdeal := Subtype.ext (h.trans botPrimeIdeal_val.symm)
    subst hP
    simp [optionToPrimeIdeal, primeIdealToOption, botPrimeIdeal_val]
  · dsimp [optionToPrimeIdeal, primeIdealToOption]
    simp only [h]
    exact Subtype.ext (primeIdealOfNatPrime_eq_of_nonZero ⟨P, h⟩)

lemma primeIdealToOption_toPrime (p : Option Nat.Primes) :
    primeIdealToOption (optionToPrimeIdeal p) = p := by
  cases p with
  | none => simp [primeIdealToOption, optionToPrimeIdeal, botPrimeIdeal_val]
  | some p =>
    have hnb := primeIdealOfNatPrime_ne_bot p
    dsimp [primeIdealToOption, optionToPrimeIdeal]
    split_ifs with hb
    · exact (hnb hb).elim
    · exact congrArg some (natPrimeOf_span p)

/-- Equivalence between `PrimeIdeal ℤ` and `Option Nat.Primes` (bot vs `(p)`). -/
noncomputable def primeIdealOptionEquiv : PrimeIdeal ℤ ≃ Option Nat.Primes where
  toFun := primeIdealToOption
  invFun := optionToPrimeIdeal
  left_inv := optionToPrimeIdeal_toOption
  right_inv := primeIdealToOption_toPrime

@[simp]
lemma primeIdealToOption_bot : primeIdealToOption botPrimeIdeal = none := by
  simp [primeIdealToOption, botPrimeIdeal_val]

@[simp]
lemma primeIdealToOption_some (p : Nat.Primes) :
    primeIdealToOption (primeIdealOfNatPrime p) = some p := by
  dsimp [primeIdealToOption]
  split_ifs with hb
  · exact (primeIdealOfNatPrime_ne_bot p hb).elim
  · exact congrArg some (natPrimeOf_span p)

@[simp]
lemma optionToPrimeIdeal_none : optionToPrimeIdeal none = botPrimeIdeal := rfl

@[simp]
lemma optionToPrimeIdeal_some (p : Nat.Primes) :
    optionToPrimeIdeal (some p) = primeIdealOfNatPrime p := rfl

lemma absNorm_pow_eq_natPrime_pow (P : NonZeroPrimeIdeal ℤ) (s : ℝ) :
    (Ideal.absNorm P.1.1 : ℝ) ^ (-s) = (natPrimeOfNonZeroPrimeIdeal P : ℝ) ^ (-s) := by
  rw [show Ideal.absNorm P.1.1 = (natPrimeOfNonZeroPrimeIdeal P : ℕ) from by
    rw [← absNorm_primeIdealOfNatPrime, span_eq_of_natPrimeOfNonZeroPrimeIdeal P,
      coe_primeIdealOfNatPrime]]

/--
Reindex a set of prime ideals of `ℤ` as a set of rational primes.

Only primes `(p)` with `p` rational prime appear in the image; `⊥` is discarded.
See `mem_natPrimeImageOf_iff`.
-/
def natPrimeImageOf (S : Set (PrimeIdeal ℤ)) : Set ℕ :=
  {n | ∃ (hn : n.Prime), primeIdealOfNatPrime ⟨n, hn⟩ ∈ S}

lemma mem_natPrimeImageOf_iff {S : Set (PrimeIdeal ℤ)} {n : ℕ} (hn : n.Prime) :
    n ∈ natPrimeImageOf S ↔ primeIdealOfNatPrime ⟨n, hn⟩ ∈ S := by
  simp [natPrimeImageOf, hn]

lemma mem_natPrimeImageOf_primeIdealOfNatPrime {S : Set (PrimeIdeal ℤ)} (p : Nat.Primes) :
    (p : ℕ) ∈ natPrimeImageOf S ↔ primeIdealOfNatPrime p ∈ S :=
  mem_natPrimeImageOf_iff (S := S) (n := p) p.2

lemma natPrimeImageOf_singleton (p : Nat.Primes) :
    natPrimeImageOf {primeIdealOfNatPrime p} = {(p : ℕ)} := by
  ext n
  constructor
  · rintro ⟨hn, hmem⟩
    rw [Set.mem_singleton_iff] at hmem
    have heq := congrArg Subtype.val (primeIdealOfNatPrime_injective hmem)
    rw [Set.mem_singleton_iff]
    exact heq
  · intro hn
    rw [Set.mem_singleton_iff] at hn
    subst hn
    exact ⟨p.2, Set.mem_singleton _⟩

lemma norm_idealCoeff_le_one (S : Set (PrimeIdeal ℤ)) (P : PrimeIdeal ℤ) :
    ‖idealCoeff S P‖ ≤ (1 : ℝ) := by
  by_cases h : P ∈ S
  · simp [idealCoeff, h]
  · simp [idealCoeff, h]

end IntPrimeBridge

end DirichletDensity

end PrimeNumberTheoremAnd
