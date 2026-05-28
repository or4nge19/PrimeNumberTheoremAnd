import PrimeNumberTheoremAnd.Chebotarev.Algebraic.ConjugacyCounting
import PrimeNumberTheoremAnd.Mathlib.Algebra.Group.ConjClasses

import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Complex.Basic

/-!
## Chebotarev reduction: group-theoretic infrastructure

Sharifi’s reduction steps (Thm 7.2.2, Steps 1–2) require comparing conjugacy class sizes with
centralizer indices and with indices of cyclic subgroups.

This file collects **pure group-theoretic** lemmas about the Chebotarev density factor
\(|C|/|G|\) and Sharifi's index identity `[G : ⟨g⟩] = |C| · [Z(g) : ⟨g⟩]`.

No number-field input appears here.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical

namespace ChebotarevReduction

variable {G : Type*} [Group G]

open Chebotarev

/--
Every element of `⟨g⟩` commutes with `g`, hence `⟨g⟩ ⊆ Z({g})`.
-/
theorem zpowers_le_centralizer_singleton (g : G) :
    Subgroup.zpowers g ≤ Subgroup.centralizer ({g} : Set G) := by
  haveI : IsCyclic (Subgroup.zpowers g) := inferInstance
  have hg : g ∈ Subgroup.zpowers g := by
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨1, zpow_one g⟩
  intro h hh
  have hcomm :
      (⟨h, hh⟩ : Subgroup.zpowers g) * ⟨g, hg⟩ = ⟨g, hg⟩ * ⟨h, hh⟩ :=
    mul_comm' _ _
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  simpa [Subgroup.coe_mul] using (congrArg Subtype.val hcomm).symm

theorem index_zpowers_eq_index_centralizer_mul_relIndex (g : G) :
    (Subgroup.zpowers g).index =
      (Subgroup.centralizer ({g} : Set G)).index *
        (Subgroup.zpowers g).relIndex (Subgroup.centralizer ({g} : Set G)) := by
  have h := (Subgroup.relIndex_mul_index (H := Subgroup.zpowers g)
    (K := Subgroup.centralizer ({g} : Set G))
    (zpowers_le_centralizer_singleton g)).symm
  exact h.trans (mul_comm _ _)

section Counting

variable [Finite G]

/--
Sharifi’s expected density factor `|C|/|G|` for the conjugacy class of `g`, using
`|C| = [G : Z(g)]`.
-/
theorem natCard_conjClass_div_natCard (g : G) :
    (Nat.card (ConjClasses.mk g).carrier : ℂ) / (Nat.card G : ℂ) =
      (Subgroup.centralizer ({g} : Set G)).index / Nat.card G := by
  simp [Chebotarev.nat_card_conjClass_eq_index_centralizer (G := G) g]

theorem index_zpowers_eq_natCard_conjClass_mul_relIndex (g : G) :
    (Subgroup.zpowers g).index =
      Nat.card (ConjClasses.mk g).carrier *
        (Subgroup.zpowers g).relIndex (Subgroup.centralizer ({g} : Set G)) := by
  rw [index_zpowers_eq_index_centralizer_mul_relIndex,
    Chebotarev.nat_card_conjClass_eq_index_centralizer (G := G) g]

end Counting

end ChebotarevReduction

end PrimeNumberTheoremAnd
