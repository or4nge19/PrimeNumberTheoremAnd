import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.NumberTheory.Divisors

/-!
## “Artin-like” L-series from local Euler factors (foundational)

Mathlib does not currently define Artin L-functions. However, one can already formalize a large
piece of the *algebraic* infrastructure behind their Euler products:

* specify **local coefficients** `aₚ(e)` for each prime `p` and exponent `e ≥ 0`, with `aₚ(0) = 1`;
* build a global arithmetic function `a(n)` by multiplicative assembly over the prime factorization;
* define the corresponding naive Dirichlet series as `LSeries a s`;
* prove (under explicit summability hypotheses) the **Euler product identity**
  \[
    \prod_p \left(\sum_{e\ge 0} \frac{a(p^e)}{p^{e s}}\right) = \sum_{n\ge 1} \frac{a(n)}{n^s}.
  \]

This file does exactly that, using the existing `EulerProduct` and `LSeries` APIs.

No analytic continuation or nonvanishing statements are included here; these are genuinely deeper.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical BigOperators
open scoped LSeries.notation

open Complex Nat Finset Filter

namespace ArtinLike

/-! ### Local coefficients and the induced global arithmetic function -/

/--
Local data: coefficients for prime powers.

In an Artin L-function one would take `aₚ(e)` to be the `e`th coefficient of the inverse
characteristic polynomial of a Frobenius matrix at `p`, but this file stays abstract.
-/
structure LocalCoeffs where
  a : Nat.Primes → ℕ → ℂ
  a_zero : ∀ p, a p 0 = 1

namespace LocalCoeffs

@[ext] lemma ext {A B : LocalCoeffs} (h : ∀ p e, A.a p e = B.a p e) : A = B := by
  cases A; cases B
  congr 1
  funext p e
  exact h p e

/--
The induced global arithmetic function `coeff` built from the prime factorization:

* `coeff 0 = 0`;
* for `n ≠ 0`, `coeff n = ∏ p, a p (n.factorization p)`.
-/
noncomputable def coeff (A : LocalCoeffs) (n : ℕ) : ℂ :=
  if _hn : n = 0 then 0 else
    n.factorization.prod fun p e =>
      if hp : p.Prime then A.a ⟨p, hp⟩ e else 1

@[simp] lemma coeff_zero (A : LocalCoeffs) : A.coeff 0 = 0 := by
  simp [coeff]

@[simp] lemma coeff_one (A : LocalCoeffs) : A.coeff 1 = 1 := by
  classical
  simp [coeff]

lemma coeff_eq_prod_factorization (A : LocalCoeffs) {n : ℕ} (hn : n ≠ 0) :
    A.coeff n = n.factorization.prod (fun p e => if hp : p.Prime then A.a ⟨p, hp⟩ e else 1) := by
  simp [coeff, hn]

lemma coeff_mul_of_coprime (A : LocalCoeffs) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hcop : Nat.Coprime m n) :
    A.coeff (m * n) = A.coeff m * A.coeff n := by
  classical
  -- For coprime `m`, `n`, the prime supports of the two factorizations are disjoint,
  -- and `factorization (m*n) = factorization m + factorization n`.
  have hdis :
      Disjoint m.factorization.support n.factorization.support := by
    -- `support_factorization` identifies the support with `primeFactors`.
    simpa [Nat.support_factorization] using hcop.disjoint_primeFactors
  -- Use `prod_add_index_of_disjoint` on the sum of factorizations.
  simp [coeff_eq_prod_factorization A (mul_ne_zero hm hn), coeff_eq_prod_factorization A hm,
    coeff_eq_prod_factorization A hn, Nat.factorization_mul_of_coprime hcop,
    Finsupp.prod_add_index_of_disjoint hdis]

/-- Local coefficients that are constantly `1` (zeta-like local factors). -/
def constOne : LocalCoeffs where
  a _ _ := 1
  a_zero _ := rfl

@[simp] lemma coeff_constOne {n : ℕ} (hn : n ≠ 0) : constOne.coeff n = 1 := by
  rw [coeff_eq_prod_factorization constOne hn]
  refine Finset.prod_eq_one fun p _ => by
    by_cases hp : p.Prime
    · simp [hp, constOne]
    · simp [hp]

/-- The arithmetic function associated to `A.coeff`. -/
noncomputable def toArithmeticFunction (A : LocalCoeffs) : ArithmeticFunction ℂ :=
  _root_.toArithmeticFunction A.coeff

@[simp] lemma toArithmeticFunction_apply (A : LocalCoeffs) {n : ℕ} (hn : n ≠ 0) :
    A.toArithmeticFunction n = A.coeff n := by
  simp [toArithmeticFunction, _root_.toArithmeticFunction, if_neg hn]

lemma isMultiplicative_toArithmeticFunction (A : LocalCoeffs) :
    A.toArithmeticFunction.IsMultiplicative := by
  classical
  refine (ArithmeticFunction.IsMultiplicative.iff_ne_zero).2 ?_
  refine ⟨?_, ?_⟩
  · simp [toArithmeticFunction_apply A one_ne_zero, coeff_one]
  · intro m n hm hn hcop
    simp only [toArithmeticFunction_apply A (mul_ne_zero hm hn),
      toArithmeticFunction_apply A hm, toArithmeticFunction_apply A hn]
    exact A.coeff_mul_of_coprime hm hn hcop

lemma coeff_prime_pow (A : LocalCoeffs) {p k : ℕ} (hp : p.Prime) :
    A.coeff (p ^ k) = A.a ⟨p, hp⟩ k := by
  classical
  have hn : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
  -- Expand using `factorization` and use `factorization_pow` for primes.
  rw [coeff_eq_prod_factorization (A := A) hn, hp.factorization_pow]
  -- Evaluate the product over the single support point.
  let h : ℕ → ℕ → ℂ := fun q e => if hq : q.Prime then A.a ⟨q, hq⟩ e else 1
  have h0 : h p 0 = 1 := by
    simp [h, A.a_zero, hp]
  have hs : (Finsupp.single p k).prod h = h p k :=
    Finsupp.prod_single_index (a := p) (b := k) (h := h) h0
  simpa [h, hp] using hs

/-! ### Multiplying local Euler factors -/

/--
Pointwise multiplication of local Euler factors.

If `A` and `B` are local coefficient systems (encoding the power-series
\(\sum_{e\ge 0} a_p(e) X^e\)), then `A.mul B` encodes the coefficient system for the product of
these power series, i.e. the Cauchy product on each prime `p`.
-/
noncomputable def mul (A B : LocalCoeffs) : LocalCoeffs where
  a p e := ∑ x ∈ Finset.antidiagonal e, A.a p x.1 * B.a p x.2
  a_zero p := by
    classical
    simp [Finset.antidiagonal_zero, A.a_zero, B.a_zero]

end LocalCoeffs

/-! ### `toArithmeticFunction` API -/

lemma toArithmeticFunction_coe_of_map_zero {f : ℕ → ℂ} (hf : f 0 = 0) :
    (_root_.toArithmeticFunction f : ℕ → ℂ) = f := by
  funext n
  by_cases hn : n = 0
  · subst hn; simp [_root_.toArithmeticFunction, hf]
  · simp [_root_.toArithmeticFunction, hn]

/-! ### Euler product for the naive L-series -/

section EulerProduct

variable (A : LocalCoeffs)

open LSeries EulerProduct Filter Nat Topology

/-- The Dirichlet-series term corresponding to `A.coeff`. -/
noncomputable abbrev term (s : ℂ) (n : ℕ) : ℂ := LSeries.term A.coeff s n

lemma term_zero (s : ℂ) : term (A := A) s 0 = 0 := by
  simp [term]

lemma term_one (s : ℂ) : term (A := A) s 1 = 1 := by
  simp [term, LocalCoeffs.coeff_one]

lemma term_mul_of_coprime {s : ℂ} {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hcop : Nat.Coprime m n) :
    term (A := A) s (m * n) = term (A := A) s m * term (A := A) s n := by
  -- This is the standard multiplicativity-on-coprime statement for `term` once `coeff` is.
  -- We expand definitions directly.
  -- The only nontrivial point is handling `((m*n) : ℂ) ^ s = (m : ℂ) ^ s * (n : ℂ) ^ s`,
  -- which holds for nonnegative reals via `mul_cpow_ofReal_nonneg`.
  have hcpow' :
      ((m : ℂ) * (n : ℂ)) ^ s = (m : ℂ) ^ s * (n : ℂ) ^ s := by
    -- rewrite casts into `ℂ` as `ofReal` casts from `ℝ`
    -- first turn `((m:ℂ)*(n:ℂ))` into `ofReal (m:ℝ) * ofReal (n:ℝ)`
    have :
        (Complex.ofReal (m : ℝ) * Complex.ofReal (n : ℝ)) ^ s =
          (Complex.ofReal (m : ℝ)) ^ s * (Complex.ofReal (n : ℝ)) ^ s := by
      simpa using mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg s
    simpa [ofReal_natCast] using this
  -- Now expand the terms. The remaining goal is a straightforward rearrangement in `ℂ`.
  simp [term, LSeries.term_of_ne_zero (mul_ne_zero hm hn), LSeries.term_of_ne_zero hm,
    LSeries.term_of_ne_zero hn, LocalCoeffs.coeff_mul_of_coprime A hm hn hcop,
    Nat.cast_mul, div_eq_mul_inv] at *
  -- use `hcpow'` to rewrite the denominator, then simplify.
  -- (commutativity lets us reorder freely)
  simp [hcpow', mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]

/--
Euler product for the `LSeries` attached to `A.coeff`, under an explicit summability hypothesis.

This is the precise “naive Euler product” statement one would want before attempting any
meromorphic continuation.
-/
theorem LSeries_eulerProduct_hasProd {s : ℂ} (hsum : LSeriesSummable A.coeff s) :
    HasProd (fun p : Nat.Primes => ∑' e : ℕ, term (A := A) s (p ^ e)) (LSeries A.coeff s) := by
  -- Apply the general Euler product theorem to `f := term A.coeff s`.
  have hmul : ∀ {m n}, Nat.Coprime m n →
      term (A := A) s (m * n) = term (A := A) s m * term (A := A) s n := by
    intro m n hcop
    by_cases hm : m = 0
    · subst hm; simp [term]
    by_cases hn : n = 0
    · subst hn; simp [term]
    exact term_mul_of_coprime (A := A) (s := s) hm hn hcop
  -- `EulerProduct.eulerProduct_hasProd` wants: `f 1 = 1`, `f 0 = 0`, multiplicative on coprime,
  -- and summability of `‖f‖`.
  have hnorm : Summable fun n : ℕ => ‖term (A := A) s n‖ := by
    -- `LSeriesSummable` is summability of `term`, hence also of `‖term‖`.
    simpa [LSeriesSummable, term] using hsum.norm
  simpa [term, LSeries, term_zero, term_one] using
    (EulerProduct.eulerProduct_hasProd (R := ℂ)
      (f := fun n => term (A := A) s n)
      (hf₁ := term_one (A := A) s)
      (hmul := fun {m n} => hmul (m := m) (n := n))
      (hsum := hnorm)
      (hf₀ := term_zero (A := A) s))

/-- `tprod` version of `LSeries_eulerProduct_hasProd`. -/
theorem LSeries_eulerProduct_tprod {s : ℂ} (hsum : LSeriesSummable A.coeff s) :
    ∏' p : Nat.Primes, ∑' e : ℕ, term (A := A) s (p ^ e) = LSeries A.coeff s :=
  (LSeries_eulerProduct_hasProd (A := A) (s := s) hsum).tprod_eq

/-- Finite partial-product version of `LSeries_eulerProduct_hasProd`. -/
theorem LSeries_eulerProduct {s : ℂ} (hsum : LSeriesSummable A.coeff s) :
    Tendsto (fun n : ℕ => ∏ p ∈ primesBelow n, ∑' e : ℕ, term (A := A) s (p ^ e)) atTop
      (𝓝 (LSeries A.coeff s)) := by
  have hnorm : Summable fun n : ℕ => ‖term (A := A) s n‖ := by
    simpa [LSeriesSummable, term] using hsum.norm
  have hmul : ∀ {m n}, Nat.Coprime m n →
      term (A := A) s (m * n) = term (A := A) s m * term (A := A) s n := by
    intro m n hcop
    by_cases hm : m = 0
    · subst hm; simp [term]
    by_cases hn : n = 0
    · subst hn; simp [term]
    exact term_mul_of_coprime (A := A) (s := s) hm hn hcop
  simpa [term, LSeries, term_zero, term_one] using
    (EulerProduct.eulerProduct (R := ℂ)
      (f := fun n => term (A := A) s n)
      (hf₁ := term_one (A := A) s)
      (hmul := fun {m n} => hmul (m := m) (n := n))
      (hsum := hnorm)
      (hf₀ := term_zero (A := A) s))

end EulerProduct

end ArtinLike

end PrimeNumberTheoremAnd
