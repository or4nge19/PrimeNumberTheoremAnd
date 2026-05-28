import PrimeNumberTheoremAnd.Chebotarev.Cyclotomic.FrobeniusDensityConditional
import PrimeNumberTheoremAnd.Chebotarev.Density.DirichletCharacterPrimeSeriesBound

import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
## Cyclotomic case: unconditional Dirichlet density

We discharge the boundedness hypothesis in
`ChebotarevCyclotomicFrobeniusDensityConditional` using boundedness of
`∑' p, χ p / p^s` for nontrivial Dirichlet characters near `s = 1⁺`.
-/

namespace PrimeNumberTheoremAnd
namespace Chebotarev
namespace Cyclotomic

open scoped Classical Cyclotomic NumberField Topology BigOperators

open Filter Nat.Primes

open PrimeNumberTheoremAnd.DirichletDensity
open IsCyclotomicExtension

section

variable {n : ℕ} [NeZero n]
variable (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {n} ℚ L]

private noncomputable def aInv (σ : Gal(L/ℚ)) : ZMod n :=
  ((((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n)⁻¹)

private lemma primeSeries_eq_tsum_div (χ : _root_.DirichletCharacter ℂ n) (s : ℝ) :
    PrimeNumberTheoremAnd.Chebotarev.DirichletCharacterPrime.primeSeries (N := n) χ (s : ℂ) =
      ∑' p : Nat.Primes, (χ (p : ZMod n)) / ((p : ℂ) ^ (s : ℂ)) := by
  classical
  refine (tsum_congr ?_).symm
  intro p
  simp [PrimeNumberTheoremAnd.Chebotarev.DirichletCharacterPrime.primeSeries, div_eq_mul_inv,
    Complex.cpow_neg, one_div, mul_assoc]

private lemma nontrivPrimeError_eq_sum_primeSeries (σ : Gal(L/ℚ)) {s : ℝ} (hs : 1 < s) :
    nontrivPrimeError (n := n) (L := L) σ s
      = ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ n)),
          (((1 : ℂ) / (n.totient : ℂ)) * χ (aInv (n := n) (L := L) σ)) *
            PrimeNumberTheoremAnd.Chebotarev.DirichletCharacterPrime.primeSeries (N := n) χ (s : ℂ) := by
  classical
  set c : ℂ := (1 : ℂ) / (n.totient : ℂ)
  set S : Finset (DirichletCharacter ℂ n) := ({1}ᶜ : Finset (DirichletCharacter ℂ n))
  have hSummable :
      ∀ χ ∈ S,
        Summable (fun p : Nat.Primes ↦
          (c * χ (aInv (n := n) (L := L) σ)) * (χ (p : ZMod n) / ((p : ℂ) ^ (s : ℂ)))) := by
    intro χ hχ
    have hbase :
        Summable (fun p : Nat.Primes ↦ (1 : ℂ) / ((p : ℂ) ^ (s : ℂ))) :=
      PrimeNumberTheoremAnd.summable_primes_one_div_cpow_of_one_lt_real (s := s) hs
    have hbase' : Summable (fun p : Nat.Primes ↦ ‖(1 : ℂ) / ((p : ℂ) ^ (s : ℂ))‖) := hbase.norm
    have hbase'' :
        Summable (fun p : Nat.Primes ↦ ‖c‖ * ‖(1 : ℂ) / ((p : ℂ) ^ (s : ℂ))‖) :=
      hbase'.mul_left ‖c‖
    refine Summable.of_norm_bounded hbase'' (fun p => ?_)
    have hχa : ‖χ (aInv (n := n) (L := L) σ)‖ ≤ (1 : ℝ) :=
      DirichletCharacter.norm_le_one (χ := χ) _
    have hχp : ‖χ (p : ZMod n)‖ ≤ (1 : ℝ) :=
      DirichletCharacter.norm_le_one (χ := χ) _
    calc
      ‖(c * χ (aInv (n := n) (L := L) σ)) * (χ (p : ZMod n) / ((p : ℂ) ^ (s : ℂ)))‖
          = ‖c‖ * ‖χ (aInv (n := n) (L := L) σ)‖ * ‖χ (p : ZMod n) / ((p : ℂ) ^ (s : ℂ))‖ := by
              simp [norm_mul, mul_assoc, mul_left_comm, mul_comm]
      _ ≤ ‖c‖ * 1 * ‖χ (p : ZMod n) / ((p : ℂ) ^ (s : ℂ))‖ := by
            gcongr
      _ = ‖c‖ * ‖χ (p : ZMod n) / ((p : ℂ) ^ (s : ℂ))‖ := by simp
      _ ≤ ‖c‖ * ‖(1 : ℂ) / ((p : ℂ) ^ (s : ℂ))‖ := by
            gcongr
            calc
              ‖χ (p : ZMod n) / ((p : ℂ) ^ (s : ℂ))‖
                  = ‖χ (p : ZMod n)‖ * ‖(1 : ℂ) / ((p : ℂ) ^ (s : ℂ))‖ := by
                      simp [div_eq_mul_inv, norm_mul, one_div]
              _ ≤ 1 * ‖(1 : ℂ) / ((p : ℂ) ^ (s : ℂ))‖ := by
                    gcongr
              _ = ‖(1 : ℂ) / ((p : ℂ) ^ (s : ℂ))‖ := by simp
      _ = ‖c‖ * ‖(1 : ℂ) / ((p : ℂ) ^ (s : ℂ))‖ := rfl
  -- commute `tsum` and the finite sum over `S`
  have hswap :
      (∑' p : Nat.Primes, ∑ χ ∈ S,
        (c * χ (aInv (n := n) (L := L) σ)) * (χ (p : ZMod n) / ((p : ℂ) ^ (s : ℂ))))
        =
      ∑ χ ∈ S, ∑' p : Nat.Primes,
        (c * χ (aInv (n := n) (L := L) σ)) * (χ (p : ZMod n) / ((p : ℂ) ^ (s : ℂ))) := by
    simpa [S] using (Summable.tsum_finsetSum hSummable)
  calc
    nontrivPrimeError (n := n) (L := L) σ s
        = ∑' p : Nat.Primes, ∑ χ ∈ S,
            (c * χ (aInv (n := n) (L := L) σ)) * (χ (p : ZMod n) / ((p : ℂ) ^ (s : ℂ))) := by
          simp [nontrivPrimeError, c, S, aInv, div_eq_mul_inv, mul_assoc, Finset.mul_sum,
            Finset.sum_mul]
    _ = ∑ χ ∈ S, ∑' p : Nat.Primes,
            (c * χ (aInv (n := n) (L := L) σ)) * (χ (p : ZMod n) / ((p : ℂ) ^ (s : ℂ))) := hswap
    _ = ∑ χ ∈ S,
          (((1 : ℂ) / (n.totient : ℂ)) * χ (aInv (n := n) (L := L) σ)) *
            PrimeNumberTheoremAnd.Chebotarev.DirichletCharacterPrime.primeSeries (N := n) χ (s : ℂ) := by
          refine Finset.sum_congr rfl (fun χ hχ => ?_)
          have hbase :
              Summable (fun p : Nat.Primes ↦ (1 : ℂ) / ((p : ℂ) ^ (s : ℂ))) :=
            PrimeNumberTheoremAnd.summable_primes_one_div_cpow_of_one_lt_real (s := s) hs
          have hbase' : Summable (fun p : Nat.Primes ↦ ‖(1 : ℂ) / ((p : ℂ) ^ (s : ℂ))‖) := hbase.norm
          have hχsumm :
              Summable (fun p : Nat.Primes ↦ (χ (p : ZMod n)) / ((p : ℂ) ^ (s : ℂ))) := by
            refine Summable.of_norm_bounded hbase' (fun p => ?_)
            have hχp : ‖χ (p : ZMod n)‖ ≤ (1 : ℝ) := DirichletCharacter.norm_le_one (χ := χ) _
            calc
              ‖(χ (p : ZMod n)) / ((p : ℂ) ^ (s : ℂ))‖
                  = ‖χ (p : ZMod n)‖ * ‖(1 : ℂ) / ((p : ℂ) ^ (s : ℂ))‖ := by
                      simp [div_eq_mul_inv, norm_mul, one_div]
              _ ≤ 1 * ‖(1 : ℂ) / ((p : ℂ) ^ (s : ℂ))‖ := by gcongr
              _ = ‖(1 : ℂ) / ((p : ℂ) ^ (s : ℂ))‖ := by simp
          -- pull out the constant and rewrite the remaining `tsum` as `primeSeries`
          let d : ℂ := c * χ (aInv (n := n) (L := L) σ)
          have hmul :
              (∑' p : Nat.Primes, d * ((χ (p : ZMod n)) / ((p : ℂ) ^ (s : ℂ)))) =
                d * (∑' p : Nat.Primes, (χ (p : ZMod n)) / ((p : ℂ) ^ (s : ℂ))) := by
            simpa [d, mul_assoc, tsum_mul_left] using (hχsumm.tsum_mul_left d)
          have htsum :
              (∑' p : Nat.Primes, (χ (p : ZMod n)) / ((p : ℂ) ^ (s : ℂ))) =
                PrimeNumberTheoremAnd.Chebotarev.DirichletCharacterPrime.primeSeries (N := n) χ (s : ℂ) := by
            simpa using (primeSeries_eq_tsum_div (n := n) χ s).symm
          calc
            (∑' p : Nat.Primes, c * χ (aInv (n := n) (L := L) σ) *
                (χ (p : ZMod n) / ((p : ℂ) ^ (s : ℂ))))
                =
              ∑' p : Nat.Primes, d * (χ (p : ZMod n) / ((p : ℂ) ^ (s : ℂ))) := by
                refine tsum_congr ?_
                intro p
                simp [d, mul_assoc, mul_left_comm, mul_comm]
            _ = d * (∑' p : Nat.Primes, χ (p : ZMod n) / ((p : ℂ) ^ (s : ℂ))) := hmul
            _ = d * PrimeNumberTheoremAnd.Chebotarev.DirichletCharacterPrime.primeSeries (N := n) χ (s : ℂ) := by
                simp [htsum]
            _ = c * χ (aInv (n := n) (L := L) σ) *
                  PrimeNumberTheoremAnd.Chebotarev.DirichletCharacterPrime.primeSeries (N := n) χ (s : ℂ) := by
                simp [d, mul_assoc]

theorem bounded_nontrivPrimeError (σ : Gal(L/ℚ)) :
    ∃ M : ℝ,
      (fun s : ℝ ↦ ‖nontrivPrimeError (n := n) (L := L) σ s‖) ≤ᶠ[nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ))]
        fun _ ↦ M := by
  classical
  set c : ℂ := (1 : ℂ) / (n.totient : ℂ)
  set S : Finset (DirichletCharacter ℂ n) := ({1}ᶜ : Finset (DirichletCharacter ℂ n))
  have hχb :
      ∀ χ ∈ S, ∃ Mχ : ℝ,
        (fun s : ℝ ↦ ‖PrimeNumberTheoremAnd.Chebotarev.DirichletCharacterPrime.primeSeries (N := n) χ (s : ℂ)‖)
          ≤ᶠ[nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ))] fun _ ↦ Mχ := by
    intro χ hχ
    have hne : χ ≠ 1 := by simpa [S] using (Finset.mem_compl.1 hχ)
    simpa using PrimeNumberTheoremAnd.Chebotarev.DirichletCharacterPrime.bounded_primeSeries_near_one
      (N := n) (χ := χ) hne
  classical
  choose Mχ hMχ using hχb
  -- turn the dependent bounds `Mχ χ hχ` into a nondependent function using `if`
  let B : DirichletCharacter ℂ n → ℝ := fun χ => if h : χ ∈ S then Mχ χ h else 0
  have hB :
      ∀ χ ∈ S,
        (fun s : ℝ ↦ ‖PrimeNumberTheoremAnd.Chebotarev.DirichletCharacterPrime.primeSeries (N := n) χ (s : ℂ)‖)
          ≤ᶠ[nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ))] fun _ ↦ B χ := by
    intro χ hχ
    simpa [B, hχ] using (hMχ χ hχ)
  have hall :
      ∀ᶠ s : ℝ in nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)),
        ∀ χ ∈ S,
          ‖PrimeNumberTheoremAnd.Chebotarev.DirichletCharacterPrime.primeSeries (N := n) χ (s : ℂ)‖ ≤ B χ := by
    refine (S.eventually_all).2 ?_
    intro χ hχ
    exact (hB χ hχ)
  have hcoef : ∀ χ : _root_.DirichletCharacter ℂ n, ‖c * χ (aInv (n := n) (L := L) σ)‖ ≤ ‖c‖ := by
    intro χ
    have hχa : ‖χ (aInv (n := n) (L := L) σ)‖ ≤ (1 : ℝ) :=
      _root_.DirichletCharacter.norm_le_one (χ := χ) _
    simpa [norm_mul] using (mul_le_mul_of_nonneg_left hχa (by positivity : 0 ≤ ‖c‖))
  let M : ℝ := ‖c‖ * ∑ χ ∈ S, B χ
  refine ⟨M, ?_⟩
  have hs_gt : ∀ᶠ s : ℝ in nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)), 1 < s := by
    simpa [Set.mem_Ioi] using
      (self_mem_nhdsWithin : Set.Ioi (1 : ℝ) ∈ nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)))
  filter_upwards [hall, hs_gt] with s hsall hs1
  have hEq := nontrivPrimeError_eq_sum_primeSeries (n := n) (L := L) (σ := σ) hs1
  -- triangle inequality + pointwise bounds
  rw [hEq]
  have hnorm :
      ‖∑ χ ∈ S,
          (((1 : ℂ) / (n.totient : ℂ)) * χ (aInv (n := n) (L := L) σ)) *
            PrimeNumberTheoremAnd.Chebotarev.DirichletCharacterPrime.primeSeries (N := n) χ (s : ℂ)‖
        ≤ ∑ χ ∈ S,
            ‖(((1 : ℂ) / (n.totient : ℂ)) * χ (aInv (n := n) (L := L) σ)) *
              PrimeNumberTheoremAnd.Chebotarev.DirichletCharacterPrime.primeSeries (N := n) χ (s : ℂ)‖ :=
    norm_sum_le _ _
  refine le_trans hnorm ?_
  have hle :
      (∑ χ ∈ S,
          ‖(((1 : ℂ) / (n.totient : ℂ)) * χ (aInv (n := n) (L := L) σ)) *
              PrimeNumberTheoremAnd.Chebotarev.DirichletCharacterPrime.primeSeries (N := n) χ (s : ℂ)‖)
        ≤ ∑ χ ∈ S, ‖c‖ * B χ := by
    refine Finset.sum_le_sum ?_
    intro χ hχ
    have hps :
        ‖PrimeNumberTheoremAnd.Chebotarev.DirichletCharacterPrime.primeSeries (N := n) χ (s : ℂ)‖ ≤ B χ :=
      hsall χ hχ
    calc
      ‖(c * χ (aInv (n := n) (L := L) σ)) *
            PrimeNumberTheoremAnd.Chebotarev.DirichletCharacterPrime.primeSeries (N := n) χ (s : ℂ)‖
          = ‖c * χ (aInv (n := n) (L := L) σ)‖ *
              ‖PrimeNumberTheoremAnd.Chebotarev.DirichletCharacterPrime.primeSeries (N := n) χ (s : ℂ)‖ := by
                simp [norm_mul]
      _ ≤ ‖c‖ * B χ := by gcongr; exact hcoef χ
  refine le_trans hle ?_
  -- factor out `‖c‖` and match the chosen `M`
  have : (∑ χ ∈ S, ‖c‖ * B χ) = ‖c‖ * (∑ χ ∈ S, B χ) := by
    simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  simpa [M, this, mul_assoc] using (le_rfl : (‖c‖ * (∑ χ ∈ S, B χ)) ≤ (‖c‖ * (∑ χ ∈ S, B χ)))

theorem hasDensity_frobPrimeSet (σ : Gal(L/ℚ)) :
    HasDensity (frobPrimeSet (n := n) (L := L) σ) ((1 : ℂ) / (n.totient : ℂ)) := by
  exact hasDensity_frobPrimeSet_of_boundedNontriv (n := n) (L := L) σ
    (bounded_nontrivPrimeError (n := n) (L := L) σ)

end

end Cyclotomic
end Chebotarev
end PrimeNumberTheoremAnd
