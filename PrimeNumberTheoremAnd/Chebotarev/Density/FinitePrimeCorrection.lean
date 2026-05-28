import Mathlib.Data.Nat.Factors
import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
## Finite prime correction terms (primes dividing `n`)

In the cyclotomic Chebotarev argument, a main term involves an indicator `(if p ∣ n then 0 else 1)`.
Analytically, this differs from `1` only on the finitely many primes dividing `n`.

This file provides a clean way to rewrite `tsum` over `Nat.Primes` of such indicator terms as a
finite `Finset` sum over `n.primeFactors`, which is then obviously bounded near `s = 1⁺`.
-/

namespace PrimeNumberTheoremAnd
namespace Chebotarev
namespace Cyclotomic

open scoped Classical

open Filter
open Nat.Primes

section

variable (n : ℕ) [NeZero n]

noncomputable
def primesDividingEmb (n : ℕ) :
    {p : ℕ // p ∈ n.primeFactorsList.toFinset} ↪ Nat.Primes :=
  by
    classical
    refine ⟨fun p =>
        have hmemList : p.1 ∈ n.primeFactorsList := List.mem_toFinset.1 p.2
        ⟨p.1, (Nat.mem_primeFactorsList' (n := n) (p := p.1) |>.1 hmemList).1⟩, ?_⟩
    intro a b hab
    apply Subtype.ext
    -- compare the underlying naturals of the `Nat.Primes` images
    exact congrArg (fun q : Nat.Primes => (q : ℕ)) hab

noncomputable
def primesDividing (n : ℕ) : Finset Nat.Primes :=
  (n.primeFactorsList.toFinset).attach.map (primesDividingEmb n)

lemma mem_primesDividing_iff {p : Nat.Primes} :
    p ∈ primesDividing n ↔ (p.1 ∣ n) := by
  classical
  constructor
  · intro hp
    rcases Finset.mem_map.1 hp with ⟨q, hq, rfl⟩
    -- `q.1 ∈ n.primeFactorsList`
    have hmem : (q.1 ∈ n.primeFactorsList) := List.mem_toFinset.1 q.2
    exact (Nat.dvd_of_mem_primeFactorsList hmem)
  · intro hp
    have hp' : (p.1 ∈ n.primeFactorsList) := by
      -- `primeFactorsList` contains exactly primes dividing `n` (for `n ≠ 0`)
      have : p.1.Prime ∧ p.1 ∣ n ∧ n ≠ 0 := ⟨p.2, hp, NeZero.ne n⟩
      exact (Nat.mem_primeFactorsList' (n := n) (p := p.1)).2 this
    -- show membership in the `map`
    refine Finset.mem_map.2 ?_
    refine ⟨⟨p.1, (List.mem_toFinset.2 hp')⟩, ?_, ?_⟩
    · simp
    · apply Subtype.ext
      rfl

omit [NeZero n] in
lemma tsum_eq_sum_primesDividing {α : Type*} [TopologicalSpace α] [AddCommMonoid α]
    [T2Space α]
    {f : Nat.Primes → α} (hf : ∀ p : Nat.Primes, p ∉ primesDividing n → f p = 0) :
    (∑' p : Nat.Primes, f p) = (primesDividing n).sum f := by
  classical
  -- `hasSum_sum_of_ne_finset_zero` is the `to_additive` companion of
  -- `hasProd_prod_of_ne_finset_one` from `InfiniteSum/Defs`.
  have hsum : HasSum f ((primesDividing n).sum f) :=
    hasSum_sum_of_ne_finset_zero (s := primesDividing n) (hf := fun p hp ↦ hf p hp)
  simp [hsum.tsum_eq]

end

end Cyclotomic
end Chebotarev
end PrimeNumberTheoremAnd
