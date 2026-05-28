import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Data.Complex.Basic
import PrimeNumberTheoremAnd.Chebotarev.Algebraic.EnoughRootsOfUnityComplex

/-!
## Cyclotomic case: orthogonality as an indicator function

Sharifi’s cyclotomic argument uses the standard orthogonality relation:

\[
\sum_{\chi \bmod n} \chi(a^{-1})\,\chi(b) =
\begin{cases}
\varphi(n) & a=b,\\
0 & a\neq b,
\end{cases}
\]

and hence (dividing by `φ(n)`) we obtain an *indicator function* for the congruence class `b=a`.

Mathlib provides the first identity as
`DirichletCharacter.sum_char_inv_mul_char_eq`.  Here we record the normalized form.
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev

open scoped Classical

namespace Dirichlet

open DirichletCharacter

section

variable {n : ℕ} [NeZero n]

/--
Normalized orthogonality for Dirichlet characters (indicator form).

For a unit `a : ZMod n` and any `b : ZMod n`,

`((∑ χ, χ a⁻¹ * χ b) / φ(n))` equals `1` if `a = b` and `0` otherwise.
-/
theorem sum_char_inv_mul_char_eq_indicator {a : ZMod n} (ha : IsUnit a) (b : ZMod n) :
    (∑ χ : DirichletCharacter ℂ n, χ a⁻¹ * χ b) / (n.totient : ℂ) =
      if a = b then (1 : ℂ) else 0 := by
  have hnφ : (n.totient : ℂ) ≠ 0 := by
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have hφ : 0 < n.totient := (Nat.totient_pos).2 hn
    exact_mod_cast hφ.ne'
  have h :=
    DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) (n := n) (a := a) ha b
  calc
    (∑ χ : DirichletCharacter ℂ n, χ a⁻¹ * χ b) / (n.totient : ℂ)
        = (if a = b then (n.totient : ℂ) else 0) / (n.totient : ℂ) := by
            simp [h]
    _ = if a = b then (1 : ℂ) else 0 := by
          by_cases hab : a = b <;> simp [hab, hnφ]

end

end Dirichlet

end Chebotarev

end PrimeNumberTheoremAnd
