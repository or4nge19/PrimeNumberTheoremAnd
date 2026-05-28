import Mathlib.Algebra.Group.Conj
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.PowerSeries.Inverse
import PrimeNumberTheoremAnd.Chebotarev.Artin.LikeLSeries

/-!
## Artin L-series (algebraic layer): Euler factors, representations, and characters

This file develops the matrix-level and representation-level infrastructure for Artin L-series:

* **Euler factors** `det(I - X A)⁻¹` for matrices `A`, including block-diagonal multiplicativity;
* **conjugation invariance** of Euler polynomials/factors;
* the `ArtinRep` structure and class functions on `ConjClasses G`;
* **characters** as matrix traces, descending to conjugacy classes.

No analytic continuation, nonvanishing, or convergence is asserted without explicit hypotheses
elsewhere.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical BigOperators

namespace ArtinLSeries

open Matrix PowerSeries

section EulerFactor

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The polynomial (in the power-series variable `X`) whose inverse is the Euler factor. -/
noncomputable def eulerPoly (A : Matrix n n ℂ) : ℂ⟦X⟧ :=
  Matrix.det
    ((1 : Matrix n n ℂ⟦X⟧) -
      (PowerSeries.X : ℂ⟦X⟧) • (PowerSeries.C : ℂ →+* ℂ⟦X⟧).mapMatrix A)

/--
The Euler factor as a power series:
\[
  ( \det(I - X A) )^{-1}.
\]

We implement the inverse via `PowerSeries.invOfUnit` with unit `1`, using the lemma
`eulerPoly_constantCoeff` below.
-/
noncomputable def eulerFactor (A : Matrix n n ℂ) : ℂ⟦X⟧ :=
  PowerSeries.invOfUnit (eulerPoly (n := n) A) (1 : ℂˣ)

/-- The `e`-th coefficient of the Euler factor power series. -/
noncomputable def eulerCoeff (A : Matrix n n ℂ) (e : ℕ) : ℂ :=
  PowerSeries.coeff e (eulerFactor (n := n) A)

lemma eulerPoly_constantCoeff (A : Matrix n n ℂ) :
    PowerSeries.constantCoeff (eulerPoly (n := n) A) = (1 : ℂ) := by
  classical
  let M : Matrix n n ℂ⟦X⟧ :=
    (1 : Matrix n n ℂ⟦X⟧) -
      (PowerSeries.X : ℂ⟦X⟧) • (PowerSeries.C : ℂ →+* ℂ⟦X⟧).mapMatrix A
  have :
      PowerSeries.constantCoeff (Matrix.det
          M) =
        Matrix.det
          (PowerSeries.constantCoeff.mapMatrix
            M) := by
    simpa using (PowerSeries.constantCoeff.map_det (M := M))
  have hmap : PowerSeries.constantCoeff.mapMatrix M = (1 : Matrix n n ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [M]
    · simp [M, hij]
  simpa [eulerPoly, M, hmap] using this.trans (by simp [hmap])

@[simp] lemma eulerCoeff_zero (A : Matrix n n ℂ) : eulerCoeff (n := n) A 0 = 1 := by
  classical
  simp [eulerCoeff, eulerFactor, eulerPoly_constantCoeff (n := n) A]

end EulerFactor

section Block

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

lemma eulerPoly_fromBlocks (A : Matrix m m ℂ) (D : Matrix n n ℂ) :
    eulerPoly (n := (m ⊕ n)) (Matrix.fromBlocks A 0 0 D)
      =
    eulerPoly (n := m) A * eulerPoly (n := n) D := by
  classical
  let c : ℂ →+* ℂ⟦X⟧ := (PowerSeries.C : ℂ →+* ℂ⟦X⟧)
  let MA : Matrix m m ℂ⟦X⟧ :=
    (1 : Matrix m m ℂ⟦X⟧) - (PowerSeries.X : ℂ⟦X⟧) • A.map (⇑c)
  let MD : Matrix n n ℂ⟦X⟧ :=
    (1 : Matrix n n ℂ⟦X⟧) - (PowerSeries.X : ℂ⟦X⟧) • D.map (⇑c)
  have hblock :
      ((1 : Matrix (m ⊕ n) (m ⊕ n) ℂ⟦X⟧) -
            (PowerSeries.X : ℂ⟦X⟧) •
              (Matrix.fromBlocks A 0 0 D).map (⇑c))
        =
      Matrix.fromBlocks MA 0 0 MD := by
    ext i j
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            by_cases h : i = j <;>
              simp [MA, MD, h, Matrix.fromBlocks_apply₁₁, Matrix.map_apply]
        | inr j =>
            simp [MA, MD, Matrix.fromBlocks_apply₁₂, Matrix.map_apply]
    | inr i =>
        cases j with
        | inl j =>
            simp [MA, MD, Matrix.fromBlocks_apply₂₁, Matrix.map_apply]
        | inr j =>
            by_cases h : i = j <;>
              simp [MA, MD, h, Matrix.fromBlocks_apply₂₂, Matrix.map_apply]
  simp [eulerPoly, hblock, MA, MD, c, RingHom.mapMatrix_apply]

lemma eulerFactor_fromBlocks (A : Matrix m m ℂ) (D : Matrix n n ℂ) :
    eulerFactor (n := (m ⊕ n)) (Matrix.fromBlocks A 0 0 D)
      =
    eulerFactor (n := m) A * eulerFactor (n := n) D := by
  classical
  set φ : ℂ⟦X⟧ := eulerPoly (n := (m ⊕ n)) (Matrix.fromBlocks A 0 0 D)
  set b : ℂ⟦X⟧ := eulerFactor (n := (m ⊕ n)) (Matrix.fromBlocks A 0 0 D)
  set c : ℂ⟦X⟧ := eulerFactor (n := m) A * eulerFactor (n := n) D
  have hb : φ * b = 1 := by
    simp [φ, b, eulerFactor, eulerPoly_constantCoeff]
  have hb' : b * φ = 1 := by
    simpa [mul_comm, φ, b] using hb
  have hc : φ * c = 1 := by
    simp [φ, c, eulerPoly_fromBlocks (A := A) (D := D), eulerFactor, eulerPoly_constantCoeff,
      mul_assoc, mul_left_comm, mul_comm]
  calc
    b = b * 1 := by simp
    _ = b * (φ * c) := by simp [hc]
    _ = (b * φ) * c := by simp [mul_assoc]
    _ = 1 * c := by simp [hb']
    _ = c := by simp

lemma eulerCoeff_fromBlocks (A : Matrix m m ℂ) (D : Matrix n n ℂ) (e : ℕ) :
    eulerCoeff (n := (m ⊕ n)) (Matrix.fromBlocks A 0 0 D) e
      =
    ∑ p ∈ Finset.antidiagonal e,
      eulerCoeff (n := m) A p.1 * eulerCoeff (n := n) D p.2 := by
  classical
  simp [eulerCoeff, eulerFactor_fromBlocks (A := A) (D := D), PowerSeries.coeff_mul]

end Block

section Assemble

variable {n : Type*} [Fintype n] [DecidableEq n]

/--
Build `ArtinLike.LocalCoeffs` from a family of matrices indexed by primes,
using coefficients of the Euler factor power series.
-/
noncomputable def localCoeffsOfMatrix (A : Nat.Primes → Matrix n n ℂ) :
    ArtinLike.LocalCoeffs where
  a p e := eulerCoeff (n := n) (A p) e
  a_zero p := by
    classical
    simp [eulerCoeff_zero (n := n) (A p)]

end Assemble

section MapInv

variable {R S : Type*} [CommRing R] [CommRing S]
variable {n : Type*} [Fintype n] [DecidableEq n]

namespace RingHom

/--
For a ring hom `f`, `f.mapMatrix` sends the (nonsingular) inverse of a *unit* matrix to the inverse
of the image matrix.
-/
lemma mapMatrix_inv_of_isUnit (f : R →+* S) (M : Matrix n n R) (hM : IsUnit M) :
    (f.mapMatrix : Matrix n n R →+* Matrix n n S) (M⁻¹) =
      ((f.mapMatrix : Matrix n n R →+* Matrix n n S) M)⁻¹ := by
  classical
  rcases hM with ⟨u, rfl⟩
  let F : Matrix n n R →+* Matrix n n S := (f.mapMatrix : Matrix n n R →+* Matrix n n S)
  let Fu : (Matrix n n S)ˣ := Units.map (RingHom.toMonoidHom F) u
  have hinvR : ((↑u : Matrix n n R)⁻¹) = (↑(u⁻¹) : Matrix n n R) := by
    simp
  have hinvS : ((↑Fu : Matrix n n S)⁻¹) = (↑(Fu⁻¹) : Matrix n n S) := by
    simp
  calc
    F ((↑u : Matrix n n R)⁻¹)
        = F (↑(u⁻¹) : Matrix n n R) := by simp_rw [hinvR]
    _ = (↑(Units.map (RingHom.toMonoidHom F) (u⁻¹)) : Matrix n n S) := rfl
    _ = (↑(Fu⁻¹) : Matrix n n S) := by simp [Fu]
    _ = (↑Fu : Matrix n n S)⁻¹ := by simp_rw [hinvS]
    _ = (F (↑u : Matrix n n R))⁻¹ := by rfl

end RingHom

end MapInv

section ConjInvariance

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma eulerPoly_conj (M A : Matrix n n ℂ) (hM : IsUnit M) :
    eulerPoly (n := n) (M * A * M⁻¹) = eulerPoly (n := n) A := by
  classical
  let f : ℂ →+* ℂ⟦X⟧ := PowerSeries.C
  let F : Matrix n n ℂ →+* Matrix n n ℂ⟦X⟧ := (f.mapMatrix : Matrix n n ℂ →+* Matrix n n ℂ⟦X⟧)
  let Mc : Matrix n n ℂ⟦X⟧ := F M
  have hMc : IsUnit Mc := hM.map F
  let Ac : Matrix n n ℂ⟦X⟧ := F A
  have hFinv : F (M⁻¹) = (F M)⁻¹ :=
    RingHom.mapMatrix_inv_of_isUnit (f := f) (M := M) hM
  have hFinv' : (M⁻¹).map f = (M.map f)⁻¹ := by
    simpa [F] using hFinv
  have hconj :
      F (M * A * M⁻¹) = Mc * Ac * Mc⁻¹ := by
    calc
      F (M * A * M⁻¹) = F M * F A * F (M⁻¹) := by simp [mul_assoc]
      _ = F M * F A * (F M)⁻¹ := by simp [hFinv]
      _ = Mc * Ac * Mc⁻¹ := by rfl
  have hx :
      (1 : Matrix n n ℂ⟦X⟧) - (PowerSeries.X : ℂ⟦X⟧) • (Mc * Ac * Mc⁻¹) =
        Mc * ((1 : Matrix n n ℂ⟦X⟧) - (PowerSeries.X : ℂ⟦X⟧) • Ac) * Mc⁻¹ := by
    have hdet : IsUnit (Matrix.det Mc) := (Matrix.isUnit_iff_isUnit_det (A := Mc)).1 hMc
    have hmul : Mc * Mc⁻¹ = (1 : Matrix n n ℂ⟦X⟧) := Matrix.mul_nonsing_inv (A := Mc) hdet
    ext i j
    simp [hmul, Mc, Ac, mul_assoc, mul_add, add_mul, sub_eq_add_neg]
  have hdet :
      Matrix.det ((1 : Matrix n n ℂ⟦X⟧) - (PowerSeries.X : ℂ⟦X⟧) • (Mc * Ac * Mc⁻¹)) =
        Matrix.det ((1 : Matrix n n ℂ⟦X⟧) - (PowerSeries.X : ℂ⟦X⟧) • Ac) := by
    simpa [hx] using (Matrix.det_conj (M := Mc) hMc
      ((1 : Matrix n n ℂ⟦X⟧) - (PowerSeries.X : ℂ⟦X⟧) • Ac))
  simpa [eulerPoly, f, F, Mc, Ac, hconj, hFinv'] using hdet

end ConjInvariance

section ArtinRep

variable (G : Type*) [Group G]

/-- An (algebraic) Artin representation into invertible matrices over `ℂ`. -/
structure ArtinRep where
  n : Type*
  instFintype : Fintype n
  instDecEq : DecidableEq n
  ρ : G →* Matrix.GeneralLinearGroup n ℂ

attribute [instance] ArtinRep.instFintype ArtinRep.instDecEq

namespace ArtinRep

variable {G} (ρ : ArtinRep G)

/-- The underlying matrix of `ρ g`. -/
noncomputable def mat (g : G) : Matrix ρ.n ρ.n ℂ :=
  (ρ.ρ g : Matrix ρ.n ρ.n ℂ)

/-- The Euler polynomial at `g`: `det(I - X ρ(g))`. -/
noncomputable def eulerPolyAt (g : G) : PowerSeries ℂ :=
  ArtinLSeries.eulerPoly (n := ρ.n) (ρ.mat g)

/-- The Euler factor at `g`: `(det(I - X ρ(g)))⁻¹`. -/
noncomputable def eulerFactorAt (g : G) : PowerSeries ℂ :=
  ArtinLSeries.eulerFactor (n := ρ.n) (ρ.mat g)

/-- The `e`-th coefficient of the Euler factor at `g`. -/
noncomputable def eulerCoeffAt (g : G) (e : ℕ) : ℂ :=
  PowerSeries.coeff e (ρ.eulerFactorAt g)

lemma eulerPolyAt_eq_of_isConj {g h : G} (hg : IsConj g h) :
    ρ.eulerPolyAt g = ρ.eulerPolyAt h := by
  classical
  rcases hg with ⟨c, hc⟩
  have hconj : (↑c : G) * g * (↑c : G)⁻¹ = h := by
    have := congrArg (fun t : G => t * (↑(c⁻¹) : G)) hc
    simp [mul_assoc] at this
    simpa [mul_assoc] using this
  have hunit : IsUnit (ρ.mat (↑c : G)) := by
    simp [ArtinRep.mat]
  have hmat :
      ρ.mat h = ρ.mat (↑c : G) * ρ.mat g * (ρ.mat (↑c : G))⁻¹ := by
    calc
      ρ.mat h = ρ.mat ((↑c : G) * g * (↑c : G)⁻¹) := by simp [hconj]
      _ = ρ.mat (↑c : G) * ρ.mat g * (ρ.mat (↑c : G))⁻¹ := by
            simp [ArtinRep.mat, map_mul, mul_assoc]
  simpa [ArtinRep.eulerPolyAt, hmat, mul_assoc] using
    (ArtinLSeries.eulerPoly_conj (n := ρ.n) (M := ρ.mat (↑c : G)) (A := ρ.mat g) hunit).symm

lemma eulerFactorAt_eq_of_isConj {g h : G} (hg : IsConj g h) :
    ρ.eulerFactorAt g = ρ.eulerFactorAt h := by
  classical
  have hpoly : ρ.eulerPolyAt g = ρ.eulerPolyAt h :=
    ρ.eulerPolyAt_eq_of_isConj (g := g) (h := h) hg
  simpa [ArtinRep.eulerFactorAt, ArtinRep.eulerPolyAt, ArtinLSeries.eulerFactor] using
    congrArg (fun p : PowerSeries ℂ => PowerSeries.invOfUnit p (1 : ℂˣ)) hpoly

lemma eulerCoeffAt_eq_of_isConj {g h : G} (hg : IsConj g h) (e : ℕ) :
    ρ.eulerCoeffAt g e = ρ.eulerCoeffAt h e := by
  simp [ArtinRep.eulerCoeffAt, ρ.eulerFactorAt_eq_of_isConj hg]

/-- The Euler polynomial as a class function `ConjClasses G → PowerSeries ℂ`. -/
noncomputable def eulerPolyClass : ConjClasses G → PowerSeries ℂ :=
  Quotient.lift (fun g => ρ.eulerPolyAt g) (by
    intro g h hgh
    exact ρ.eulerPolyAt_eq_of_isConj hgh)

/-- The Euler factor as a class function `ConjClasses G → PowerSeries ℂ`. -/
noncomputable def eulerFactorClass : ConjClasses G → PowerSeries ℂ :=
  Quotient.lift (fun g => ρ.eulerFactorAt g) (by
    intro g h hgh
    exact ρ.eulerFactorAt_eq_of_isConj hgh)

/-- The `e`-th Euler-factor coefficient as a class function `ConjClasses G → ℂ`. -/
noncomputable def eulerCoeffClass (e : ℕ) : ConjClasses G → ℂ :=
  Quotient.lift (fun g => ρ.eulerCoeffAt g e) (by
    intro g h hgh
    exact ρ.eulerCoeffAt_eq_of_isConj hgh e)

/-- The character of an Artin representation: `χ(g) = tr(ρ(g))`. -/
noncomputable def character (g : G) : ℂ :=
  Matrix.trace (ρ.mat g)

lemma character_eq_of_isConj {g h : G} (hg : IsConj g h) :
    ρ.character g = ρ.character h := by
  classical
  rcases hg with ⟨c, hc⟩
  have hconj : (↑c : G) * g * (↑c : G)⁻¹ = h := by
    have := congrArg (fun t : G => t * (↑(c⁻¹) : G)) hc
    simpa [mul_assoc] using this
  let u : (Matrix ρ.n ρ.n ℂ)ˣ := (ρ.ρ (↑c : G))
  have hmat :
      ρ.mat h = (↑u : Matrix ρ.n ρ.n ℂ) * ρ.mat g * (↑u⁻¹ : Matrix ρ.n ρ.n ℂ) := by
    calc
      ρ.mat h = ρ.mat ((↑c : G) * g * (↑c : G)⁻¹) := by simp [hconj]
      _ = (↑u : Matrix ρ.n ρ.n ℂ) * ρ.mat g * (↑u⁻¹ : Matrix ρ.n ρ.n ℂ) := by
            simp [ArtinRep.mat, u, map_mul, mul_assoc]
  simpa [ArtinRep.character, hmat] using (Matrix.trace_units_conj u (ρ.mat g)).symm

/-- The character as a class function on `ConjClasses G`. -/
noncomputable def characterClass : ConjClasses G → ℂ :=
  Quotient.lift (fun g : G => ρ.character g) (by
    intro g h hg
    exact ρ.character_eq_of_isConj (g := g) (h := h) hg)

@[simp] lemma characterClass_mk (g : G) :
    ρ.characterClass (ConjClasses.mk g) = ρ.character g :=
  rfl

end ArtinRep

end ArtinRep

end ArtinLSeries

end PrimeNumberTheoremAnd
