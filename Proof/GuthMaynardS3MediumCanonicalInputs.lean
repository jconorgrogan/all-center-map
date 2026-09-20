import GuthMaynardS3MediumConcreteWeld
import GuthMaynardLemma92ThreeScaleFrequencyInputs
import GuthMaynardJIterationMediumRegionGeometry

set_option maxHeartbeats 3000000

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory Metric

noncomputable section
namespace GuthMaynardS3MediumCanonicalInputs

open GuthMaynardJIteration
open GuthMaynardS3MediumConcreteWeld
open GuthMaynardS3LiteralLemma92NonzeroMedium

/-- The literal `T^115` budget behind the concrete medium weld. -/
theorem sourceMedium_canonical_budget
    {T eta : ℝ} {M3 q : ℕ}
    (hT6 : (6 : ℝ) ≤ T) (hM3 : 1 ≤ M3)
    (hM3T : (M3 : ℝ) ≤ T)
    (heta_q : (115 : ℝ) ≤ eta * (q : ℝ)) :
    (M3 : ℝ) * sourceBumpFourierConstant 1 zero_lt_one (q + 2) *
        ((1 + T ^ 6 / (1 / (M3 : ℝ))) ^ 2 *
          max 1 ((1 / (M3 : ℝ)) ^ 2) * integerQuadraticMass) * T ^ 100 ≤
      (4 * sourceBumpFourierConstant 1 zero_lt_one (q + 2) *
        integerQuadraticMass) * (Real.rpow T eta) ^ q := by
  have hT : 1 ≤ T := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hM3R : 1 ≤ (M3 : ℝ) := by exact_mod_cast hM3
  have hM3pos : 0 < (M3 : ℝ) := lt_of_lt_of_le zero_lt_one hM3R
  have hM3T' : (M3 : ℝ) ≤ T := hM3T
  have hT6one : 1 ≤ T ^ (6 : ℕ) := one_le_pow₀ hT
  have hM3inv0 : 0 ≤ 1 / (M3 : ℝ) := by positivity
  have hM3inv1 : 1 / (M3 : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hM3pos).2
    nlinarith
  have hM3inv_sq : (1 / (M3 : ℝ)) ^ 2 ≤ 1 := by
    simpa only [one_pow] using
      ((sq_le_sq₀ hM3inv0 (by norm_num)).2 hM3inv1)
  have hmax : max 1 ((1 / (M3 : ℝ)) ^ 2) = 1 :=
    max_eq_left hM3inv_sq
  have hdiv : T ^ 6 / (1 / (M3 : ℝ)) = T ^ 6 * (M3 : ℝ) := by
    field_simp [ne_of_gt hM3pos]
  have hprod : T ^ 6 * (M3 : ℝ) ≤ T ^ 7 := by
    calc
      T ^ 6 * (M3 : ℝ) ≤ T ^ 6 * T :=
        mul_le_mul_of_nonneg_left hM3T' (by positivity)
      _ = T ^ 7 := by ring
  have hsum : 1 + T ^ 6 * (M3 : ℝ) ≤ 2 * T ^ 7 := by
    nlinarith [hT6one, hprod]
  have hsum_sq : (1 + T ^ 6 * (M3 : ℝ)) ^ 2 ≤ (2 * T ^ 7) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hsum
  have hpoly : (M3 : ℝ) * (1 + T ^ 6 * (M3 : ℝ)) ^ 2 * T ^ 100 ≤
      4 * T ^ 115 := by
    calc
      (M3 : ℝ) * (1 + T ^ 6 * (M3 : ℝ)) ^ 2 * T ^ 100 ≤
          (M3 : ℝ) * (2 * T ^ 7) ^ 2 * T ^ 100 := by
            gcongr
      _ ≤ T * (2 * T ^ 7) ^ 2 * T ^ 100 := by
            gcongr
      _ = 4 * T ^ 115 := by ring
  have hK : 0 ≤ sourceBumpFourierConstant 1 zero_lt_one (q + 2) :=
    sourceBumpFourierConstant_nonneg 1 zero_lt_one (q + 2)
  have hmass : 0 ≤ integerQuadraticMass := integerQuadraticMass_nonneg
  have hpoly' :
      (sourceBumpFourierConstant 1 zero_lt_one (q + 2) *
        integerQuadraticMass) *
        ((M3 : ℝ) * (1 + T ^ 6 * (M3 : ℝ)) ^ 2 * T ^ 100) ≤
      (sourceBumpFourierConstant 1 zero_lt_one (q + 2) *
        integerQuadraticMass) * (4 * T ^ 115) :=
    mul_le_mul_of_nonneg_left hpoly (mul_nonneg hK hmass)
  have hTrpow : T ^ 115 ≤ (Real.rpow T eta) ^ q := by
    calc
      T ^ 115 = Real.rpow T (115 : ℝ) :=
        (Real.rpow_natCast T 115).symm
      _ ≤ Real.rpow T (eta * (q : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hT heta_q
      _ = (Real.rpow T eta) ^ q := Real.rpow_mul_natCast hT0 eta q
  rw [hmax, hdiv]
  calc
    (M3 : ℝ) * sourceBumpFourierConstant 1 zero_lt_one (q + 2) *
        ((1 + T ^ 6 * (M3 : ℝ)) ^ 2 * 1 * integerQuadraticMass) * T ^ 100 =
      (sourceBumpFourierConstant 1 zero_lt_one (q + 2) *
        integerQuadraticMass) *
        ((M3 : ℝ) * (1 + T ^ 6 * (M3 : ℝ)) ^ 2 * T ^ 100) := by ring
    _ ≤ (sourceBumpFourierConstant 1 zero_lt_one (q + 2) *
        integerQuadraticMass) * (4 * T ^ 115) := hpoly'
    _ ≤ (sourceBumpFourierConstant 1 zero_lt_one (q + 2) *
        integerQuadraticMass) * (4 * (Real.rpow T eta) ^ q) := by
          gcongr
    _ = (4 * sourceBumpFourierConstant 1 zero_lt_one (q + 2) *
        integerQuadraticMass) * (Real.rpow T eta) ^ q := by ring

/-- Canonical region-II inputs for the concrete medium weld.  The ell range is
fixed to the literal independent-scale three-scale cover, and the pair count
comes from the already-proved nonzero-ell uniform divisor theorem. -/
theorem sourceGFinite_medium_canonical_inputs
    {eta : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ∃ Ceta : ℝ, 0 < Ceta ∧
      ∀ (T : ℝ) (M1 M2 M3 q : ℕ),
        (6 : ℝ) ≤ T →
        1 ≤ M1 → 1 ≤ M2 → 1 ≤ M3 →
        (M1 : ℝ) ≤ T → (M3 : ℝ) ≤ T →
        (115 : ℝ) ≤ eta * (q : ℝ) →
      (∀ ellRange : Finset ℤ, ∀ xi ∈
        mediumFrequencyRegion
          (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
          (sourceHighFrequencyCutoff T),
        ((sourceMediumLocalizedPairs (sourceSignedDyadicRange M1)
          (nonzeroEllRange ellRange) (M3 : ℝ) (Real.rpow T eta) xi).card : ℝ) ≤
          Ceta * Real.rpow T (2 * eta) *
            (1 + (M1 : ℝ) / (M3 : ℝ))) ∧
      (∀ xi ∈ mediumFrequencyRegion
          (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
          (sourceHighFrequencyCutoff T),
        ∀ m1 ∈ sourceSignedDyadicRange M1, ∀ ell : ℤ,
          |xi - (m1 : ℝ) * (ell : ℝ)| <
            (|(m1 : ℝ)| / (M3 : ℝ)) * Real.rpow T eta →
          ell ∈ sourceLemma92ThreeScaleEllRange M1 M3 T (Real.rpow T eta)) ∧
      (∀ xi ∈ mediumFrequencyRegion
          (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
          (sourceHighFrequencyCutoff T),
        ∀ m1 ∈ sourceSignedDyadicRange M1,
          |xi / (m1 : ℝ)| ≤ T ^ 6) ∧
      (((sourceLemma92ThreeScaleEllRange M1 M3 T (Real.rpow T eta)).filter
          (fun ell : ℤ =>
            ¬ |(ell : ℝ)| ≤ 4 * Real.rpow T (1 + eta) / (M2 : ℝ))).card : ℝ) ≤
        T ^ (11 : ℝ) ∧
      (M3 : ℝ) * sourceBumpFourierConstant 1 zero_lt_one (q + 2) *
        ((1 + T ^ 6 / (1 / (M3 : ℝ))) ^ 2 *
          max 1 ((1 / (M3 : ℝ)) ^ 2) * integerQuadraticMass) * T ^ 100 ≤
        (4 * sourceBumpFourierConstant 1 zero_lt_one (q + 2) *
          integerQuadraticMass) * (Real.rpow T eta) ^ q := by
  obtain ⟨Ceta, hCeta, hcount0⟩ :=
    exists_uniform_sourceMediumLocalizedPairCard_nonzeroEll heta heta1
  refine ⟨Ceta, hCeta, ?_⟩
  intro T M1 M2 M3 q hT6 hM1 hM2 hM3 hM1T hM3T heta_q
  have hcount := hcount0 (T := T) (M1 := M1) (M3 := M3)
    (by linarith) hM1 hM3 hM1T hM3T
  have hT : 1 ≤ T := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hM1pos : 0 < M1 := lt_of_lt_of_le Nat.zero_lt_one hM1
  have hM3pos : 0 < M3 := lt_of_lt_of_le Nat.zero_lt_one hM3
  have hB0 : 0 ≤ Real.rpow T eta := Real.rpow_nonneg hT0 eta
  have hBT : Real.rpow T eta ≤ T ^ 6 := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hT heta1
    calc
      Real.rpow T eta ≤ T := by simpa only [Real.rpow_one] using hpow
      _ ≤ T ^ 6 := by
        simpa only [pow_one] using
          (pow_le_pow_right₀ hT (show (1 : ℕ) ≤ 6 by omega))
  refine ⟨hcount, ?_, ?_, ?_, ?_⟩
  · exact sourceLemma92ThreeScale_mediumFrequency_cover
      hM1pos hM3pos hT0 hB0
  · intro xi hxi m1 hm1
    have hm1lo : (1 : ℝ) ≤ |(m1 : ℝ)| := by
      have h := (sourceSignedDyadicRange_abs_bounds hM1pos hm1).1
      exact le_trans (by exact_mod_cast hM1) h
    have hratio := abs_div_le_of_mem_mediumFrequencyRegion
      (M1 := (1 : ℝ)) (by norm_num) hxi hm1lo
    simpa only [sourceHighFrequencyCutoff, div_one] using hratio
  · have hcard := card_sourceLemma92ThreeScaleEllRange_cast_le_seven_time_six
      hM1pos hM3pos hT hB0 hBT
    have hfilter := Finset.card_filter_le
      (sourceLemma92ThreeScaleEllRange M1 M3 T (Real.rpow T eta))
      (fun ell : ℤ => ¬ |(ell : ℝ)| ≤
        4 * Real.rpow T (1 + eta) / (M2 : ℝ))
    have hcardfilter :
        (((sourceLemma92ThreeScaleEllRange M1 M3 T (Real.rpow T eta)).filter
          (fun ell : ℤ => ¬ |(ell : ℝ)| ≤
            4 * Real.rpow T (1 + eta) / (M2 : ℝ))).card : ℝ) ≤
          ((sourceLemma92ThreeScaleEllRange M1 M3 T (Real.rpow T eta)).card : ℝ) := by
      exact_mod_cast hfilter
    have hT5 : (7 : ℝ) ≤ T ^ (5 : ℕ) := by
      have h6 : (6 : ℝ) ^ (5 : ℕ) ≤ T ^ (5 : ℕ) := by
        gcongr
      norm_num at h6 ⊢
      linarith
    calc
      _ ≤ ((sourceLemma92ThreeScaleEllRange M1 M3 T (Real.rpow T eta)).card : ℝ) := hcardfilter
      _ ≤ 7 * T ^ 6 := hcard
      _ ≤ T ^ 11 := by
        calc
          7 * T ^ 6 ≤ T ^ 5 * T ^ 6 := by gcongr
          _ = T ^ 11 := by ring
      _ ≤ T ^ (11 : ℝ) := by norm_num [Real.rpow_natCast]
  · exact sourceMedium_canonical_budget hT6 hM3 hM3T heta_q

end GuthMaynardS3MediumCanonicalInputs

#print axioms GuthMaynardS3MediumCanonicalInputs.sourceMedium_canonical_budget
#print axioms GuthMaynardS3MediumCanonicalInputs.sourceGFinite_medium_canonical_inputs
