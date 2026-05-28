import PrimeNumberTheoremAnd.Chebotarev.Density.FinitePrimeCorrection
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
## Cyclotomic case: bound the finite prime correction term

The cyclotomic Frobenius ratio contains a factor `(if p ∣ n then 0 else 1)`, so the difference from
the "pure" main term only involves the finitely many primes dividing `n`. This file isolates the
corresponding prime `tsum` and proves it is **uniformly bounded** for `s → 1⁺`.
-/

namespace PrimeNumberTheoremAnd
namespace Chebotarev
namespace Cyclotomic

open scoped Classical

open Filter Nat.Primes Complex

section

variable {n : ℕ} [NeZero n]

lemma eventually_norm_tsum_primes_dvd_le :
    ∃ M : ℝ,
      (fun s : ℝ ↦ ‖∑' p : Nat.Primes, (if (p.1 ∣ n) then (1 : ℂ) else 0) / ((p : ℂ) ^ (s : ℂ))‖)
        ≤ᶠ[nhdsWithin 1 (Set.Ioi 1)] fun _ ↦ M := by
  let P : Finset Nat.Primes := primesDividing n
  refine ⟨P.sum (fun p ↦ (1 : ℝ) / (p : ℝ)), ?_⟩
  have hs_gt : ∀ᶠ s : ℝ in nhdsWithin 1 (Set.Ioi 1), 1 < s := by
    simpa [Set.mem_Ioi] using (self_mem_nhdsWithin : Set.Ioi (1 : ℝ) ∈ nhdsWithin 1 (Set.Ioi 1))
  filter_upwards [hs_gt] with s hs
  have htsum :
      (∑' p : Nat.Primes, (if (p.1 ∣ n) then (1 : ℂ) else 0) / ((p : ℂ) ^ (s : ℂ)))
        =
        P.sum (fun p ↦ (1 : ℂ) / ((p : ℂ) ^ (s : ℂ))) := by
    have h0 :
        (∑' p : Nat.Primes, (if (p.1 ∣ n) then (1 : ℂ) else 0) / ((p : ℂ) ^ (s : ℂ)))
          =
        P.sum (fun p ↦ (if (p.1 ∣ n) then (1 : ℂ) else 0) / ((p : ℂ) ^ (s : ℂ))) := by
      refine tsum_eq_sum_primesDividing (n := n)
        (f := fun p : Nat.Primes ↦ (if (p.1 ∣ n) then (1 : ℂ) else 0) / ((p : ℂ) ^ (s : ℂ))) ?_
      intro p hp
      have : ¬ (p.1 ∣ n) := by
        intro hpn
        have : p ∈ P := (mem_primesDividing_iff (n := n) (p := p)).2 hpn
        exact hp this
      simp [this]
    refine h0.trans ?_
    refine Finset.sum_congr rfl ?_
    intro p hp
    have : (p.1 ∣ n) := (mem_primesDividing_iff (n := n) (p := p)).1 hp
    simp [this]
  have hterm (p : Nat.Primes) :
      ‖(1 : ℂ) / ((p : ℂ) ^ (s : ℂ))‖ ≤ (1 : ℝ) / (p : ℝ) := by
    have hsC : (s : ℂ).re ≠ 0 := by
      simpa using (ne_of_gt (show 0 < s by linarith))
    have hp1 : (1 : ℝ) < (p : ℝ) := by
      have : (2 : ℕ) ≤ p.1 := p.2.two_le
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) this)
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
    have hnorm :
        ‖(1 : ℂ) / ((p : ℂ) ^ (s : ℂ))‖ = ((p : ℝ) ^ s)⁻¹ := by
      calc
        ‖(1 : ℂ) / ((p : ℂ) ^ (s : ℂ))‖
            = ‖((p : ℂ) ^ (s : ℂ))⁻¹‖ := by simp [one_div]
        _ = ‖(p : ℂ) ^ (s : ℂ)‖⁻¹ := by simp
        _ = ((p : ℝ) ^ ((s : ℂ).re))⁻¹ := by
              simp [norm_natCast_cpow_of_re_ne_zero _ hsC]
        _ = ((p : ℝ) ^ s)⁻¹ := by simp
    have hle : (p : ℝ) ^ (1 : ℝ) ≤ (p : ℝ) ^ s :=
      Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
    have hinv : 1 / ((p : ℝ) ^ s) ≤ 1 / ((p : ℝ) ^ (1 : ℝ)) :=
      one_div_le_one_div_of_le (ha := Real.rpow_pos_of_pos hp_pos (1 : ℝ)) hle
    simpa [hnorm, one_div, Real.rpow_one] using hinv
  have hsum_le :
      ‖P.sum (fun p ↦ (1 : ℂ) / ((p : ℂ) ^ (s : ℂ)))‖ ≤ P.sum (fun p ↦ (1 : ℝ) / (p : ℝ)) := by
    have htri :
        ‖P.sum (fun p ↦ (1 : ℂ) / ((p : ℂ) ^ (s : ℂ)))‖
          ≤ P.sum (fun p ↦ ‖(1 : ℂ) / ((p : ℂ) ^ (s : ℂ))‖) := by
      simpa using (norm_sum_le (s := P) (f := fun p ↦ (1 : ℂ) / ((p : ℂ) ^ (s : ℂ))))
    refine le_trans htri ?_
    refine Finset.sum_le_sum ?_
    intro p hp
    exact hterm p
  simpa [htsum] using hsum_le

end

end Cyclotomic
end Chebotarev
end PrimeNumberTheoremAnd
