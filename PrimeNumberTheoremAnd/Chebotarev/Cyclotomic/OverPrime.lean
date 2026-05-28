import PrimeNumberTheoremAnd.Chebotarev.Cyclotomic.FrobeniusCyclotomic
import PrimeNumberTheoremAnd.Chebotarev.Algebraic.UnramifiedNat
import Mathlib.RingTheory.Ideal.Int
import Mathlib.SetTheory.Cardinal.Finite

/-!
## Cyclotomic case over `ℚ`: Frobenius acts by `p`-power

This is the exact “Frobenius-on-cyclotomics” lemma used in Sharifi’s cyclotomic base case:
for a prime `p ∤ n`, at any ideal `Q` of a `ℤ`-algebra lying over `(p)`, an arithmetic Frobenius
endomorphism acts on `μ_n` by the `p`-power map.

We express this in the general `ℤ`-algebra setting (no number-field hypotheses).
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev

open scoped Classical

section

variable {S : Type*} [CommRing S] [IsDomain S] [Algebra ℤ S]

lemma nat_card_int_quot_span_prime (p : ℕ) [Fact (Nat.Prime p)] :
    Nat.card (ℤ ⧸ Ideal.span ({(p : ℤ)} : Set ℤ)) = p := by
  have e : (ℤ ⧸ Ideal.span ({(p : ℤ)} : Set ℤ)) ≃+* ZMod p :=
    Int.quotientSpanNatEquivZMod p
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hz : Nat.card (ZMod p) = p := by
    simp [Nat.card_eq_fintype_card]
  simpa using (Nat.card_congr e.toEquiv).trans hz

/--
If `Q` lies over `(p)` and `p ∤ n`, then any arithmetic Frobenius at `Q` acts on `μ_n`
by `p`-powering.
-/
lemma AlgHom.IsArithFrobAt.apply_rootsOfUnity_eq_pow_prime {p n : ℕ} [Fact (Nat.Prime p)]
    (Q : Ideal S) [Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {φ : S →ₐ[ℤ] S} (hφ : φ.IsArithFrobAt Q) (t : rootsOfUnity n S) (hn : ¬ p ∣ n) :
    φ ((t : Sˣ) : S) = ((t : Sˣ) : S) ^ p := by
  have hnQ : (n : S) ∉ Q :=
    natCast_not_mem_of_liesOver_span_prime (S := S) (p := p) (n := n) Q hn
  have ht : ((t : Sˣ) : S) ^ n = 1 := by
    simpa using congrArg (fun u : Sˣ => (u : S)) (t.2)
  have h :=
    (AlgHom.IsArithFrobAt.apply_of_pow_eq_one (R := ℤ) (S := S) (φ := φ) (Q := Q)
      hφ ht hnQ)
  have hunder : Q.under ℤ = Ideal.span ({(p : ℤ)} : Set ℤ) := by
    simpa [Ideal.under_def] using (Q.over_def (Ideal.span ({(p : ℤ)} : Set ℤ))).symm
  simpa [hunder, nat_card_int_quot_span_prime (p := p)] using h

end

end Chebotarev

end PrimeNumberTheoremAnd
