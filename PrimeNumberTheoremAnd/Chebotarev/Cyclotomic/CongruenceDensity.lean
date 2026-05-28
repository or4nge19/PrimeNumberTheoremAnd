import PrimeNumberTheoremAnd.Chebotarev.Cyclotomic.FrobeniusDensity
import PrimeNumberTheoremAnd.Chebotarev.Cyclotomic.PrimeSeries

import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

/-!
## Cyclotomic field: Dirichlet density of congruence classes

This file expresses the “Dirichlet theorem (density form)” consequence of the cyclotomic Chebotarev
development already present in this project:

For `a : (ZMod n)ˣ`, the set of primes `p` with `(p : ZMod n) = a` has Dirichlet density `1/φ(n)`.

The proof is purely *algebraic glue*:
- choose `σ : Gal(CyclotomicField n ℚ / ℚ)` corresponding to `a` via `autEquivPow`;
- observe `frobPrimeSet σ = congrPrimeSet a`;
- apply the already-proved density theorem for `frobPrimeSet`.
-/

namespace PrimeNumberTheoremAnd
namespace Chebotarev
namespace Cyclotomic

open scoped Classical Cyclotomic NumberField

open IsCyclotomicExtension
open PrimeNumberTheoremAnd.DirichletDensity

section

variable {n : ℕ} [NeZero n]

noncomputable
theorem hasDensity_congrPrimeSet_cyclotomicField (a : (ZMod n)ˣ) :
    HasDensity (congrPrimeSet (n := n) a) ((1 : ℂ) / (n.totient : ℂ)) := by
  classical
  -- Work in the cyclotomic field.
  let L : Type := CyclotomicField n ℚ
  -- `cyclotomic n ℚ` is irreducible.
  have hirr : Irreducible (Polynomial.cyclotomic n ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (NeZero.pos n)
  -- Choose `σ` corresponding to `a` via `autEquivPow`.
  let e : Gal(L/ℚ) ≃* (ZMod n)ˣ :=
    IsCyclotomicExtension.autEquivPow (n := n) (K := ℚ) (L := L) L hirr
  let σ : Gal(L/ℚ) := e.symm a
  have haut : (zeta_spec n ℚ L).autToPow ℚ σ = a := by
    -- `e` extends `autToPow`.
    simpa [σ, e]
  have hset : frobPrimeSet (n := n) (L := L) σ = congrPrimeSet (n := n) a := by
    -- `frobPrimeSet` is defined as the congruence set for `autToPow σ`.
    simp [frobPrimeSet, haut]
  -- Apply the cyclotomic density theorem.
  simpa [hset] using (hasDensity_frobPrimeSet (n := n) (L := L) σ)

end

end Cyclotomic
end Chebotarev
end PrimeNumberTheoremAnd
