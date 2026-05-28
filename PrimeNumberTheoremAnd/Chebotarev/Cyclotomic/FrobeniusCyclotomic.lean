import PrimeNumberTheoremAnd.Chebotarev.Cyclotomic.FrobeniusRootsOfUnity

/-!
## Frobenius acts by powering on `μ_n`

This is the exact algebraic input needed in Sharifi’s cyclotomic step:
an arithmetic Frobenius at `Q` acts on `n`-th roots of unity by raising to the residue-field size,
provided `n` is invertible mod `Q` (expressed as `(n : S) ∉ Q`).

This is just a repackaging of `Chebotarev.IsArithFrobAt.smul_of_pow_eq_one`.
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev

open scoped Classical

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]

variable {Q : Ideal S} {σ : G}

variable {n : ℕ}

/--
If `σ` is an arithmetic Frobenius at `Q`, then it acts on any `n`-th root of unity `t`
by powering with `Nat.card (R ⧸ Q.under R)`, provided `(n : S) ∉ Q`.
-/
lemma IsArithFrobAt.smul_rootsOfUnity [IsDomain S]
    (hσ : IsArithFrobAt (R := R) σ Q) (t : rootsOfUnity n S) (hn : (n : S) ∉ Q) :
    σ • ((t : Sˣ) : S) = ((t : Sˣ) : S) ^ Nat.card (R ⧸ Q.under R) := by
  -- `t` is a root of unity, so it satisfies the needed power equation.
  have ht : ((t : Sˣ) : S) ^ n = 1 := by
    -- `t.2` is the defining property of `rootsOfUnity n S`.
    -- Coerce to `S` and simplify.
    simpa using congrArg (fun u : Sˣ => (u : S)) (t.2)
  simpa using
    (IsArithFrobAt.smul_of_pow_eq_one (R := R) (S := S) (σ := σ) (Q := Q)
      hσ (ζ := ((t : Sˣ) : S)) (m := n) ht hn)

end

end Chebotarev

end PrimeNumberTheoremAnd

