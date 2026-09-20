import GuthMaynardS3MediumLiteralWeld
import GuthMaynardJIterationMediumRegionAggregation

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardS3MediumNonzeroActual

open GuthMaynardJIteration
open GuthMaynardS3MediumLiteralWeld
open GuthMaynardS3ZeroEllSupport
open GuthMaynardS3LiteralLemma92NonzeroMedium

theorem actual_card_sourceSignedDyadicRange_cast_le_four_mul
    {M : ℕ} (hM : 1 ≤ M) :
    ((sourceSignedDyadicRange M).card : ℝ) ≤ 4 * (M : ℝ) := by
  have hneg : Disjoint (Finset.Icc (-(2 * M : ℤ)) (-(M : ℤ)))
      (Finset.Icc (M : ℤ) (2 * M : ℤ)) := by
    rw [Finset.disjoint_left]
    intro m hmneg hmpos
    rw [Finset.mem_Icc] at hmneg hmpos
    omega
  rw [sourceSignedDyadicRange, Finset.card_union_of_disjoint hneg]
  have hcardNeg := Int.card_Icc (-(2 * M : ℤ)) (-(M : ℤ))
  have hcardPos := Int.card_Icc (M : ℤ) (2 * M : ℤ)
  have hnonnegNeg : (0 : ℤ) ≤ -(M : ℤ) + 1 - (-(2 * M : ℤ)) := by omega
  have hnonnegPos : (0 : ℤ) ≤ (2 * M : ℤ) + 1 - (M : ℤ) := by omega
  have hcastNeg :
      ((((-(M : ℤ) + 1 - (-(2 * M : ℤ))).toNat : ℕ) : ℝ)) =
        (-(M : ℤ) + 1 - (-(2 * M : ℤ)) : ℤ) := by
    exact_mod_cast (Int.toNat_of_nonneg hnonnegNeg)
  have hcastPos :
      ((((2 * M : ℤ) + 1 - (M : ℤ)).toNat : ℕ) : ℝ) =
        ((2 * M : ℤ) + 1 - (M : ℤ) : ℤ) := by
    exact_mod_cast (Int.toNat_of_nonneg hnonnegPos)
  rw [hcardNeg, hcardPos]
  have hsumcast :
      ((((-(M : ℤ) + 1 - (-(2 * M : ℤ))).toNat +
        ((2 * M : ℤ) + 1 - (M : ℤ)).toNat : ℕ) : ℝ)) =
        (-(M : ℤ) + 1 - (-(2 * M : ℤ)) : ℝ) +
          ((2 * M : ℤ) + 1 - (M : ℤ) : ℝ) := by
    push_cast
    rw [hcastNeg, hcastPos]
    ring_nf
    norm_num
    ring
  rw [hsumcast]
  push_cast
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  linarith

/-! The actual medium nonzero slice.  The pair count is supplied by the
uniform signed-divisor theorem, while the dyadic `m₁` count is derived from
the literal signed range.  No caller-level `P`, `hpairCard`, or `hcard1` is
left in the interface. -/
theorem sourceMediumNonzeroEllSum_integral_le_Ceta_actual
    {T eta : ℝ} {M1 M3 : ℕ} {Ceta Kpsi : ℝ}
    (hT : 1 ≤ T) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hM1 : 1 ≤ M1) (hM3 : 1 ≤ M3)
    (hM1T : (M1 : ℝ) ≤ T) (hM3T : (M3 : ℝ) ≤ T)
    (hCeta : 0 < Ceta) (hKpsi : 0 ≤ Kpsi)
    (hcount : ∀ ellRange : Finset ℤ, ∀ xi ∈
      mediumFrequencyRegion
        (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
        (sourceHighFrequencyCutoff T),
      ((sourceMediumLocalizedPairs (sourceSignedDyadicRange M1)
        (nonzeroEllRange ellRange) (M3 : ℝ) (Real.rpow T eta) xi).card : ℝ) ≤
        Ceta * Real.rpow T (2 * eta) *
          (1 + (M1 : ℝ) / (M3 : ℝ)))
    (ellRange m2Range : Finset ℤ) (F fhat : ℝ → ℂ)
    (psi2 : ℝ → ℝ) (M2 : ℝ)
    (hfhat : Continuous fhat)
    (hF : ∀ z, ‖F z‖ ≤ Kpsi)
    (hm2pos : ∀ m2 ∈ m2Range, 0 < m2)
    (hpsi2majorant : ∀ ell ∈ nonzeroEllRange ellRange,
      1 ≤ psi2 (M2 * (ell : ℝ) / T))
    (hleft : IntegrableOn (fun xi =>
      ‖sourceFirstPoissonLocalizedPairSum (sourceSignedDyadicRange M1)
        (nonzeroEllRange ellRange) m2Range F fhat
        (M3 : ℝ) (Real.rpow T eta) xi‖ ^ 2)
      (mediumFrequencyRegion
        (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
        (sourceHighFrequencyCutoff T))) :
    ∫ xi in mediumFrequencyRegion
        (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
        (sourceHighFrequencyCutoff T),
      ‖sourceMediumNonzeroEllSum (sourceSignedDyadicRange M1)
        ellRange m2Range F fhat (M3 : ℝ) (Real.rpow T eta) xi‖ ^ 2 ≤
      4 * Ceta * Real.rpow T (2 * eta) * Kpsi ^ 2 *
        ((M1 : ℝ) + (M3 : ℝ)) *
          sigmaIIFinite (nonzeroEllRange ellRange) m2Range psi2 fhat
            M2 T (M3 : ℝ) (Real.rpow T eta) := by
  let S : Set ℝ := mediumFrequencyRegion
    (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
    (sourceHighFrequencyCutoff T)
  let B : ℝ := Real.rpow T eta
  let M1R : ℝ := (M1 : ℝ)
  let M3R : ℝ := (M3 : ℝ)
  let N1 : ℝ := 4 * M1R
  let P : ℝ := Ceta * Real.rpow T (2 * eta) * (1 + M1R / M3R)
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hM1R : 0 < M1R := by
    dsimp only [M1R]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM1)
  have hM3R : 0 < M3R := by
    dsimp only [M3R]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM3)
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact Real.rpow_nonneg hT0 eta
  have hCeta0 : 0 ≤ Ceta := hCeta.le
  have hP0 : 0 ≤ P := by
    dsimp only [P]
    exact mul_nonneg (mul_nonneg hCeta0
      (Real.rpow_nonneg hT0 (2 * eta))) (by positivity)
  have hN10 : 0 ≤ N1 := by
    dsimp only [N1, M1R]
    positivity
  have hm1 : ∀ m1 ∈ sourceSignedDyadicRange M1, m1 ≠ 0 := by
    intro m1 hm1mem
    exact sourceSignedDyadicRange_ne_zero
      (lt_of_lt_of_le Nat.zero_lt_one hM1) hm1mem
  have hm1lo : ∀ m1 ∈ sourceSignedDyadicRange M1,
      M1R ≤ |(m1 : ℝ)| := by
    intro m1 hm1mem
    dsimp only [M1R]
    exact (sourceSignedDyadicRange_abs_bounds
      (lt_of_lt_of_le Nat.zero_lt_one hM1) hm1mem).1
  have hcard1 :
      ((sourceSignedDyadicRange M1).card : ℝ) ≤ N1 := by
    dsimp only [N1, M1R]
    exact (actual_card_sourceSignedDyadicRange_cast_le_four_mul hM1)
  have hpairCard : ∀ xi ∈ S,
      ((sourceMediumLocalizedPairs (sourceSignedDyadicRange M1)
        (nonzeroEllRange ellRange) M3R B xi).card : ℝ) ≤ P := by
    intro xi hxi
    have hcount' := hcount ellRange xi (by simpa only [S] using hxi)
    simpa only [P, M1R, M3R, B] using hcount'
  have hpsi2 : ∀ ell ∈ nonzeroEllRange ellRange,
      1 ≤ psi2 (M2 * (ell : ℝ) / T) := hpsi2majorant
  have hSigma0 : 0 ≤ sigmaIIFinite (nonzeroEllRange ellRange)
      m2Range psi2 fhat M2 T M3R B := by
    unfold sigmaIIFinite
    apply Finset.sum_nonneg
    intro ell hell
    exact mul_nonneg
      (le_trans (by norm_num) (hpsi2 ell hell))
      (intervalIntegral.integral_nonneg (by linarith)
        (fun tau _ => sq_nonneg _))
  have hmedium := sourceMediumNonzeroEllSum_integral_le_sigmaII
    S (sourceSignedDyadicRange M1) ellRange m2Range F fhat psi2 M2 T
    hfhat (measurableSet_mediumFrequencyRegion _ _)
    hM1R hM3R hB0 hKpsi hP0 hN10 hF hm1 hm1lo hm2pos hcard1
    hpairCard hpsi2 (by simpa only [S, B, M1R, M3R] using hleft)
  have hfactor :
      P * (N1 * (M3R * Kpsi ^ 2 / M1R)) *
          sigmaIIFinite (nonzeroEllRange ellRange) m2Range psi2 fhat
            M2 T M3R B ≤
        (Ceta * Real.rpow T (2 * eta) * 4 * Kpsi ^ 2) *
          (M1R + M3R) *
            sigmaIIFinite (nonzeroEllRange ellRange) m2Range psi2 fhat
              M2 T M3R B := by
    have hbase := sourceMediumSigmaOutsideFactor_le
      (M1 := M1R) (M3 := M3R) (Kpsi := Kpsi) (P := P) (N1 := N1)
      (Lpair := Ceta * Real.rpow T (2 * eta)) (c1 := 4)
      (Sigma := sigmaIIFinite (nonzeroEllRange ellRange)
        m2Range psi2 fhat M2 T M3R B)
      hM1R hM3R hN10
        (mul_nonneg hCeta0 (Real.rpow_nonneg hT0 (2 * eta))) hSigma0
      (by dsimp only [P, M1R, M3R]; rfl)
      (by dsimp only [N1]; exact le_rfl)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hbase
  calc
    (∫ xi in S,
        ‖sourceMediumNonzeroEllSum (sourceSignedDyadicRange M1)
          ellRange m2Range F fhat M3R B xi‖ ^ 2) ≤
      P * (N1 * (M3R * Kpsi ^ 2 / M1R)) *
        sigmaIIFinite (nonzeroEllRange ellRange) m2Range psi2 fhat
          M2 T M3R B := hmedium
    _ ≤ (Ceta * Real.rpow T (2 * eta) * 4 * Kpsi ^ 2) *
          (M1R + M3R) *
            sigmaIIFinite (nonzeroEllRange ellRange) m2Range psi2 fhat
              M2 T M3R B := hfactor
    _ = 4 * Ceta * Real.rpow T (2 * eta) * Kpsi ^ 2 *
          (M1R + M3R) *
            sigmaIIFinite (nonzeroEllRange ellRange) m2Range psi2 fhat
              M2 T M3R B := by ring
    _ = _ := by simp only [S, M1R, M3R, B]

theorem sigmaIIFinite_nonzeroEllRange_le_full
    {ellRange m2Range : Finset ℤ} (psi2 : ℝ → ℝ) (fhat : ℝ → ℂ)
    (M2 T M3 B : ℝ)
    (hB : 0 ≤ B)
    (hpsi2full : ∀ ell ∈ ellRange,
      0 ≤ psi2 (M2 * (ell : ℝ) / T)) :
    sigmaIIFinite (nonzeroEllRange ellRange) m2Range psi2 fhat M2 T M3 B ≤
      sigmaIIFinite ellRange m2Range psi2 fhat M2 T M3 B := by
  unfold sigmaIIFinite
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro ell hellSmall hellNotSmall
  exact mul_nonneg (hpsi2full ell hellSmall)
    (intervalIntegral.integral_nonneg (by linarith [hB])
      (fun tau _ => sq_nonneg _))

end GuthMaynardS3MediumNonzeroActual

#print axioms GuthMaynardS3MediumNonzeroActual.sourceMediumNonzeroEllSum_integral_le_Ceta_actual
