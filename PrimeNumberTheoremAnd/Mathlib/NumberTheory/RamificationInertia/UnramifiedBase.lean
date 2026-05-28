import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Over

/-!
# Base-side unramified primes

Mathlib's `Algebra.IsUnramifiedAt` is formulated at a prime ideal of the **extension** ring.
For Chebotarev and prime-counting arguments one also needs the **base-side** predicate:
a prime `P` of `R` is unramified in `S/R` when every prime above `P` has ramification index `1`.

This file records that predicate in terms of `Ideal.ramificationIdx` and connects it to
`Algebra.IsUnramifiedAt` in the Dedekind-domain setting.
-/

namespace Ideal

open Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/--
A prime ideal `P` of the base ring is **unramified in** `S/R` if every prime of `S` lying over
`P` has ramification index `1`.

This is the base-side notion used in Chebotarev density statements. It is *not* the same as
`Algebra.IsUnramifiedAt`, which is formulated at a prime of the extension ring.
-/
def IsUnramifiedIn (P : Ideal R) : Prop :=
  ∀ {Q : Ideal S}, Q.IsPrime → Q.LiesOver P → P.ramificationIdx Q = 1

lemma isUnramifiedIn_iff (P : Ideal R) :
    IsUnramifiedIn (R := R) (S := S) P ↔
      ∀ Q : Ideal.primesOver P S, P.ramificationIdx (Q.1 : Ideal S) = 1 := by
  constructor
  · intro h Q
    exact h Q.2.1 Q.2.2
  · intro h Q hQ hOver
    exact h (Ideal.primesOver.mk (p := P) (P := Q))

section Tower

variable {R T S : Type*} [CommRing R] [CommRing T] [CommRing S]
variable [Algebra R T] [Algebra T S] [Algebra R S] [IsScalarTower R T S]
variable [IsDedekindDomain R] [IsDedekindDomain T] [IsDedekindDomain S]
variable [Module.IsTorsionFree R T] [Module.IsTorsionFree T S]

/--
A prime `Q` of an intermediate ring is **unramified above** in `S/T` if every prime of `S` lying
over `Q` has ramification index `1`.
-/
def IsUnramifiedAbove (Q : Ideal T) : Prop :=
  ∀ {P : Ideal S}, P.IsPrime → P.LiesOver Q → Q.ramificationIdx P = 1

lemma isUnramifiedAbove_iff (Q : Ideal T) :
    IsUnramifiedAbove (T := T) (S := S) Q ↔
      ∀ P : Ideal.primesOver Q S, Q.ramificationIdx (P.1 : Ideal S) = 1 := by
  constructor
  · intro h P
    exact h P.2.1 P.2.2
  · intro h P hP hOver
    exact h (Ideal.primesOver.mk (p := Q) (P := P))

private lemma eq_one_of_mul_eq_one_of_ne_zero {a b : ℕ} (h : a * b = 1)
    (ha : a ≠ 0) (hb : b ≠ 0) : a = 1 ∧ b = 1 := by
  have ha1 : a = 1 := by
    have ha_le : a ≤ 1 := by
      by_contra hgt
      push Not at hgt
      have h2 : 2 ≤ a := by omega
      have : 2 ≤ a * b := Nat.mul_le_mul h2 (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hb))
      rw [h] at this
      omega
    interval_cases a <;> simp_all
  exact ⟨ha1, by rw [ha1] at h; simp at h; exact h⟩

/--
If `P` is unramified in `S/R`, then every intermediate prime `Q` over `P` is unramified above
in `S/T`.
-/
theorem isUnramifiedAbove_of_isUnramifiedIn
    [Algebra.IsIntegral T S] {P : Ideal R} [P.IsPrime] {Q : Ideal T} [Q.IsPrime] [Q.LiesOver P]
    (hPne : P ≠ ⊥) (hP : IsUnramifiedIn (R := R) (S := S) P) :
    IsUnramifiedAbove (T := T) (S := S) Q := by
  intro P' hP' hOver
  have hP'OverP : P'.LiesOver P := LiesOver.trans P' Q P
  have hQne : Q ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hPne Q
  have hram :
      P.ramificationIdx P' =
        P.ramificationIdx Q * Q.ramificationIdx P' :=
    ramificationIdx_algebra_tower' (R := R) (S := T) (T := S) P Q P'
  have hProd : P.ramificationIdx Q * Q.ramificationIdx P' = 1 := by
    rw [← hram, hP hP' hP'OverP]
  have hQpos : P.ramificationIdx Q ≠ 0 :=
    IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver (R := R) (S := T) (P := Q) hPne
  have hP'pos : Q.ramificationIdx P' ≠ 0 :=
    IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver (R := T) (S := S) (P := P') hQne
  exact (eq_one_of_mul_eq_one_of_ne_zero hProd hQpos hP'pos).2

/--
If `P` is unramified in `T/R` and every prime of `T` above `P` is unramified above in `S/T`,
then `P` is unramified in `S/R`.
-/
theorem isUnramifiedIn_of_isUnramifiedAbove
    (P : Ideal R) [P.IsPrime] (hPne : P ≠ ⊥)
    (hP : IsUnramifiedIn (R := R) (S := T) P)
    (hAbove : ∀ Q : Ideal.primesOver P T, IsUnramifiedAbove (T := T) (S := S) Q.1) :
    IsUnramifiedIn (R := R) (S := S) P := by
  intro P' hP' hOver
  haveI : P'.LiesOver P := hOver
  have hQOver : (P'.under T).LiesOver P := LiesOver.tower_bot P' (P'.under T) P
  have hP'OverQ : P'.LiesOver (P'.under T) := inferInstance
  have hram :
      P.ramificationIdx P' =
        P.ramificationIdx (P'.under T) * (P'.under T).ramificationIdx P' :=
    ramificationIdx_algebra_tower' (R := R) (S := T) (T := S) P (P'.under T) P'
  have hQram := @hP (P'.under T) inferInstance hQOver
  have hP'ram :=
    (hAbove (Ideal.primesOver.mk (p := P) (P := P'.under T))) hP' hP'OverQ
  rw [hram, hQram, hP'ram, one_mul]

/--
If `P` is unramified in `S/R`, then it is unramified in every intermediate ring of the tower.
-/
theorem isUnramifiedIn_trans
    [Algebra.IsIntegral T S] (P : Ideal R) [P.IsPrime] (hPne : P ≠ ⊥)
    (hP : IsUnramifiedIn (R := R) (S := S) P) :
    IsUnramifiedIn (R := R) (S := T) P := by
  intro Q hQ hOver
  haveI : Q.LiesOver P := hOver
  obtain ⟨P', -, hP'Prime, hcomap⟩ :=
    exists_ideal_over_prime_of_isIntegral (R := T) (S := S) Q (⊥ : Ideal S) (by simp)
  haveI : P'.IsPrime := hP'Prime
  have hP'OverQ : P'.LiesOver Q := ⟨hcomap.symm⟩
  have hP'OverP : P'.LiesOver P := LiesOver.trans P' Q P
  have hQne : Q ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hPne Q
  have hram :
      P.ramificationIdx P' =
        P.ramificationIdx Q * Q.ramificationIdx P' :=
    ramificationIdx_algebra_tower' (R := R) (S := T) (T := S) P Q P'
  have hProd : P.ramificationIdx Q * Q.ramificationIdx P' = 1 := by
    rw [← hram, @hP P' hP'Prime hP'OverP]
  have hQpos : P.ramificationIdx Q ≠ 0 :=
    IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver (R := R) (S := T) (P := Q) hPne
  have hP'pos : Q.ramificationIdx P' ≠ 0 :=
    IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver (R := T) (S := S) (P := P') hQne
  exact (eq_one_of_mul_eq_one_of_ne_zero hProd hQpos hP'pos).1

end Tower

section Dedekind

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {P : Ideal R} [P.IsPrime]

/--
At a prime above `P`, unramifiedness in the extension-side sense is equivalent to
ramification index `1` in the Dedekind-domain setting.
-/
theorem isUnramifiedAt_iff_ramificationIdx_eq_one
    {Q : Ideal S} [Q.IsPrime] [Q.LiesOver P] [IsDedekindDomain S] [Algebra.EssFiniteType R S]
    [IsDomain R] [Module.Finite ℤ R] [CharZero R] [Algebra.IsIntegral R S] (hQ : Q ≠ ⊥) :
    Algebra.IsUnramifiedAt R Q ↔ P.ramificationIdx Q = 1 := by
  have hp : Q.under R = P := (Ideal.LiesOver.over (A := R) (B := S) (p := P) (P := Q)).symm
  simpa [hp] using (Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := R) (p := Q) hQ)

/--
If `P` is unramified in `S/R` in the base-side sense, then every prime above `P` is
unramified in the extension-side sense (under standard number-field hypotheses).
-/
theorem isUnramifiedAt_of_isUnramifiedIn
    {Q : Ideal S} [Q.IsPrime] [Q.LiesOver P] [IsDedekindDomain S] [Algebra.EssFiniteType R S]
    [IsDomain R] [Module.Finite ℤ R] [CharZero R] [Algebra.IsIntegral R S]
    (hP : IsUnramifiedIn (R := R) (S := S) P) (hQ : Q ≠ ⊥) :
    Algebra.IsUnramifiedAt R Q := by
  have hram : P.ramificationIdx Q = 1 := @hP Q inferInstance inferInstance
  exact (isUnramifiedAt_iff_ramificationIdx_eq_one (R := R) (S := S) (P := P) (Q := Q) hQ).2 hram

end Dedekind

end Ideal
