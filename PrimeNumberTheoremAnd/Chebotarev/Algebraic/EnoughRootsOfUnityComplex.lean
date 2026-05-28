import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
## `ℂ` has enough roots of unity

Sharifi's arguments (and the standard Dirichlet/orthogonality manipulations) use that `ℂ` contains
primitive roots of unity of the relevant orders and that roots of unity are cyclic. In mathlib this
is expressed as `HasEnoughRootsOfUnity`.

This file provides the corresponding instance for `ℂ`, so later Chebotarev files do not need to
carry `HasEnoughRootsOfUnity ℂ ...` as an explicit assumption.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical

instance (n : ℕ) [NeZero n] : HasEnoughRootsOfUnity ℂ n := by
  classical
  refine HasEnoughRootsOfUnity.of_card_le (R := ℂ) (n := n) ?_
  -- `Fintype.card (rootsOfUnity n ℂ) = n` for `n ≠ 0`.
  simp [Complex.card_rootsOfUnity (n := n)]

end PrimeNumberTheoremAnd
