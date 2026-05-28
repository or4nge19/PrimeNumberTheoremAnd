import Mathlib.NumberTheory.RamificationInertia.Basic

/-!
## Inertia degree one (degree-one primes)

Sharifi's reduction step uses primes of **degree 1** over the base field. The correct predicate
is mathlib's `Ideal.inertiaDeg p P = 1`; there is no need for a shadow definition.
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev

namespace DegreeOne

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

lemma inertiaDeg_eq_one_iff_finrank
    (p : Ideal R) (P : Ideal S) [P.LiesOver p] [p.IsMaximal] :
    p.inertiaDeg P = 1 ↔ Module.finrank (R ⧸ p) (S ⧸ P) = 1 := by
  simp

end DegreeOne

end Chebotarev

end PrimeNumberTheoremAnd
