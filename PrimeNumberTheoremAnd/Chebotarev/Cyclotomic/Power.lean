import Mathlib.NumberTheory.Cyclotomic.Gal

/-!
## Cyclotomic case: automorphisms act by powering `ζₙ`

Sharifi’s cyclotomic step uses that, in a cyclotomic extension `K(ζₙ)/K`, every `K`-automorphism
is determined by the image of `ζₙ`, and in fact sends `ζₙ` to a **coprime power** `ζₙ^a`.

Mathlib provides this via `IsPrimitiveRoot.autToPow` and `IsCyclotomicExtension.autEquivPow`.
Here we record the basic “powering” formula in a convenient lemma form.
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev

open scoped Classical Cyclotomic

open Polynomial IsCyclotomicExtension

section

variable {n : ℕ} [NeZero n]
variable (K : Type*) [Field K]
variable (L : Type*) [Field L] [Algebra K L] [IsCyclotomicExtension {n} K L]

local notation3 "ζ" => (zeta n K L)

/--
For a cyclotomic extension `K(ζₙ)/K`, every automorphism sends `ζₙ` to a power `ζₙ^a`,
with exponent encoded as a unit of `ZMod n`.

This is `IsPrimitiveRoot.autToPow_spec` specialized to `ζ := zeta n K L`.
-/
theorem gal_zeta_pow_eq (σ : Gal(L/K)) :
    ζ ^ ((zeta_spec n K L).autToPow K σ : ZMod n).val = σ ζ := by
  simp

theorem gal_zeta_eq_pow (σ : Gal(L/K)) :
    σ ζ = ζ ^ ((zeta_spec n K L).autToPow K σ : ZMod n).val := by
  simp

end

end Chebotarev

end PrimeNumberTheoremAnd
