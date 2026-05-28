import PrimeNumberTheoremAnd.Chebotarev.Artin.Representation

import Mathlib.Data.Matrix.Block

/-!
## Artin representations: direct sums (block diagonal)

This file constructs the direct sum of two Artin representations as a representation into block
diagonal matrices, and records the corresponding multiplicativity of Euler polynomials/factors.

No analytic input appears here.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical BigOperators

namespace ArtinLSeries

open Matrix PowerSeries

namespace ArtinRep

variable {G : Type*} [Group G]

section

variable (ρ₁ ρ₂ : ArtinRep G)

private lemma det_fromBlocks_mat_ne_zero (g : G) :
    Matrix.det (Matrix.fromBlocks (ρ₁.mat g) 0 0 (ρ₂.mat g)) ≠ (0 : ℂ) := by
  classical
  have h₁ : Matrix.det (ρ₁.mat g) ≠ (0 : ℂ) := by
    simpa [ArtinRep.mat] using (Matrix.GeneralLinearGroup.det_ne_zero (g := ρ₁.ρ g))
  have h₂ : Matrix.det (ρ₂.mat g) ≠ (0 : ℂ) := by
    simpa [ArtinRep.mat] using (Matrix.GeneralLinearGroup.det_ne_zero (g := ρ₂.ρ g))
  -- Use the block-diagonal determinant formula.
  simpa [Matrix.det_fromBlocks_zero₂₁] using mul_ne_zero h₁ h₂

/--
The direct sum of two Artin representations, implemented as a block-diagonal representation.
-/
noncomputable def sum : ArtinRep G where
  n := ρ₁.n ⊕ ρ₂.n
  instFintype := inferInstance
  instDecEq := inferInstance
  ρ :=
    { toFun := fun g =>
        Matrix.GeneralLinearGroup.mkOfDetNeZero
          (Matrix.fromBlocks (ρ₁.mat g) 0 0 (ρ₂.mat g))
          (det_fromBlocks_mat_ne_zero (ρ₁ := ρ₁) (ρ₂ := ρ₂) g)
      map_one' := by
        classical
        -- Reduce to a pointwise statement about matrices.
        ext i j
        cases i <;> cases j <;> simp [ArtinRep.mat]
      map_mul' := by
        classical
        intro g h
        ext i j
        cases i <;> cases j <;>
          -- `fromBlocks_multiply` expands the product; the off-diagonal blocks vanish.
          simp [ArtinRep.mat, Matrix.fromBlocks_multiply]
    }

@[simp] lemma sum_mat (g : G) :
    (sum (ρ₁ := ρ₁) (ρ₂ := ρ₂)).mat g = Matrix.fromBlocks (ρ₁.mat g) 0 0 (ρ₂.mat g) := by
  rfl

@[simp] lemma eulerPolyAt_sum (g : G) :
    (sum (ρ₁ := ρ₁) (ρ₂ := ρ₂)).eulerPolyAt g = ρ₁.eulerPolyAt g * ρ₂.eulerPolyAt g := by
  classical
  -- Unfold to the matrix-level statement and apply `eulerPoly_fromBlocks` with explicit indices.
  simpa [ArtinRep.eulerPolyAt, sum_mat] using
    (ArtinLSeries.eulerPoly_fromBlocks (m := ρ₁.n) (n := ρ₂.n) (A := ρ₁.mat g) (D := ρ₂.mat g))

@[simp] lemma eulerFactorAt_sum (g : G) :
    (sum (ρ₁ := ρ₁) (ρ₂ := ρ₂)).eulerFactorAt g = ρ₁.eulerFactorAt g * ρ₂.eulerFactorAt g := by
  classical
  simpa [ArtinRep.eulerFactorAt, sum_mat] using
    (ArtinLSeries.eulerFactor_fromBlocks (m := ρ₁.n) (n := ρ₂.n) (A := ρ₁.mat g) (D := ρ₂.mat g))

@[simp] lemma eulerCoeffAt_sum (g : G) (e : ℕ) :
    (sum (ρ₁ := ρ₁) (ρ₂ := ρ₂)).eulerCoeffAt g e
      =
    ∑ p ∈ Finset.antidiagonal e,
      ρ₁.eulerCoeffAt g p.1 * ρ₂.eulerCoeffAt g p.2 := by
  classical
  -- This is the coefficient formula for products of power series, specialized to block diagonals.
  simpa [ArtinRep.eulerCoeffAt, ArtinRep.eulerFactorAt, sum_mat] using
    (ArtinLSeries.eulerCoeff_fromBlocks (m := ρ₁.n) (n := ρ₂.n) (A := ρ₁.mat g) (D := ρ₂.mat g) e)

@[simp] lemma eulerPolyClass_sum (C : ConjClasses G) :
    (sum (ρ₁ := ρ₁) (ρ₂ := ρ₂)).eulerPolyClass C = ρ₁.eulerPolyClass C * ρ₂.eulerPolyClass C := by
  classical
  refine Quotient.inductionOn C (fun g => ?_)
  simp [ArtinRep.eulerPolyClass]

@[simp] lemma eulerFactorClass_sum (C : ConjClasses G) :
    (sum (ρ₁ := ρ₁) (ρ₂ := ρ₂)).eulerFactorClass C =
      ρ₁.eulerFactorClass C * ρ₂.eulerFactorClass C := by
  classical
  refine Quotient.inductionOn C (fun g => ?_)
  simp [ArtinRep.eulerFactorClass]

@[simp] lemma eulerCoeffClass_sum (e : ℕ) (C : ConjClasses G) :
    (sum (ρ₁ := ρ₁) (ρ₂ := ρ₂)).eulerCoeffClass e C
      =
    ∑ p ∈ Finset.antidiagonal e,
      ρ₁.eulerCoeffClass p.1 C * ρ₂.eulerCoeffClass p.2 C := by
  classical
  refine Quotient.inductionOn C (fun g => ?_)
  simp [ArtinRep.eulerCoeffClass]

end

end ArtinRep

end ArtinLSeries

end PrimeNumberTheoremAnd
