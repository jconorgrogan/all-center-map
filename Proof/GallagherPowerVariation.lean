import GallagherEnergyExports

namespace MAPNearCollarGallagher

open AddCircle MeasureTheory Set
open scoped BigOperators ENNReal ArithmeticFunction
noncomputable section
open PrimePairEndpoints MAPMajorArcWeld
open MAPMajorArcIntegratedPowerWeld

/-- Cauchy--Schwarz on one literal symmetric paper interval, in ordinary
integral notation. -/
theorem integral_norm_Ioc_le_rpow_half_mul
    {F : ℝ → ℂ} {R : ℝ} (hF : Continuous F) (hR : 0 ≤ R) :
    (∫ beta in Set.Ioc (-R) R, ‖F beta‖) ≤
      (2 * R) ^ (1 / 2 : ℝ) *
        (∫ beta in Set.Ioc (-R) R, ‖F beta‖ ^ 2) ^ (1 / 2 : ℝ) := by
  let s : Set ℝ := Set.Ioc (-R) R
  let oneS : ℝ → ℂ := s.indicator (fun _ => (1 : ℂ))
  let FS : ℝ → ℂ := s.indicator F
  have hmeas : MeasurableSet s := measurableSet_Ioc
  have hsfinite : volume s ≠ ∞ := by
    exact measure_Ioc_lt_top.ne
  have hone : MemLp oneS 2 := by
    exact memLp_indicator_const 2 hmeas (1 : ℂ) (Or.inr hsfinite)
  have hFS : MemLp FS 2 := by
    rw [memLp_two_iff_integrable_sq_norm]
    · have hi : Integrable
          (s.indicator fun beta => ‖F beta‖ ^ 2) :=
        (hF.norm.pow 2).integrableOn_Ioc.integrable_indicator hmeas
      apply hi.congr
      filter_upwards with beta
      by_cases hb : beta ∈ s <;> simp [FS, hb]
    · exact (hF.aestronglyMeasurable.indicator hmeas)
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hone' : MemLp oneS (ENNReal.ofReal (2 : ℝ)) := by
    simpa using hone
  have hFS' : MemLp FS (ENNReal.ofReal (2 : ℝ)) := by
    simpa using hFS
  have hholder := integral_mul_norm_le_Lp_mul_Lq hpq hone' hFS'
  have hleft :
      (∫ beta : ℝ, ‖oneS beta‖ * ‖FS beta‖) =
        ∫ beta in s, ‖F beta‖ := by
    rw [← MeasureTheory.integral_indicator hmeas]
    apply integral_congr_ae
    filter_upwards with beta
    by_cases hb : beta ∈ s <;> simp [oneS, FS, hb]
  have honeSq :
      (∫ beta : ℝ, ‖oneS beta‖ ^ (2 : ℝ)) = 2 * R := by
    rw [show (fun beta : ℝ => ‖oneS beta‖ ^ (2 : ℝ)) =
        s.indicator (fun _ => (1 : ℝ)) by
      funext beta
      by_cases hb : beta ∈ s <;> simp [oneS, hb]]
    rw [MeasureTheory.integral_indicator hmeas]
    simp [s, hR]
    ring
  have hFSsq :
      (∫ beta : ℝ, ‖FS beta‖ ^ (2 : ℝ)) =
        ∫ beta in s, ‖F beta‖ ^ 2 := by
    rw [← MeasureTheory.integral_indicator hmeas]
    apply integral_congr_ae
    filter_upwards with beta
    by_cases hb : beta ∈ s <;> simp [FS, hb]
  rw [hleft, honeSq, hFSsq] at hholder
  simpa only [one_div] using hholder


/-- Trivial but exact uniform bound for the dyadic prime polynomial. -/
theorem norm_primeExponentialSum_le_atomicSlidingBound
    (X : ℝ) (alpha : UnitAddCircle) :
    ‖primeExponentialSum X alpha‖ ≤ atomicSlidingBound X := by
  unfold primeExponentialSum atomicSlidingBound
  calc
    ‖∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        (ArithmeticFunction.vonMangoldt n : ℂ) * fourier (n : ℤ) alpha‖ ≤
      ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        ‖(ArithmeticFunction.vonMangoldt n : ℂ) * fourier (n : ℤ) alpha‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one]

/-- One rational-arc power variation is controlled by the square root of its
literal signed Fourier discrepancy energy.  The prefactor is a completely
explicit trivial bound; no pointwise Siegel--Walfisz input occurs. -/
theorem rationalArcPowerVariation_le_rpow_half_energy
    {X R : ℝ} {q a : ℕ} (hX : 0 ≤ X) (hR : 0 ≤ R) (hq : 1 ≤ q) :
    rationalArcPowerVariation X R q a ≤
      (atomicSlidingBound X + 3 * X) *
        ((2 * R) ^ (1 / 2 : ℝ) *
          (∫ beta in Set.Ioc (-R) R,
            ‖signedFourierDiscrepancy X q a beta‖ ^ 2) ^ (1 / 2 : ℝ)) := by
  let actual : ℝ → ℂ := fun beta => primeExponentialSum X
    (rationalCenter q a + (beta : UnitAddCircle))
  let model : ℝ → ℂ := fun beta =>
    primeMajorCoefficient q * dyadicContinuousAmplitude X beta
  let D : ℝ → ℂ := fun beta => signedFourierDiscrepancy X q a beta
  let U : ℝ := atomicSlidingBound X + 3 * X
  have hU : 0 ≤ U := add_nonneg (atomicSlidingBound_nonneg X)
    (mul_nonneg (by norm_num) hX)
  have hactual : Continuous actual := by
    exact (MAPHarmonicEndpoint.primeExponentialSum_continuous X).comp (by fun_prop)
  have hmodel : Continuous model := by
    exact continuous_const.mul (by
      simpa only [dyadicContinuousAmplitude] using
        MAPContinuousOverlap.continuous_dyadicAmplitude X)
  have hD : Continuous D := continuous_signedFourierDiscrepancy_lift X q a
  have hmodelBound : ∀ beta, ‖model beta‖ ≤ X := by
    intro beta
    unfold model
    rw [norm_mul]
    have hc := MAPMajorArcIntegratedError.norm_primeMajorCoefficient_le_one hq
    have hv : ‖dyadicContinuousAmplitude X beta‖ ≤ X := by
      simpa only [dyadicContinuousAmplitude] using
        MAPContinuousOverlap.norm_dyadicAmplitude_le_length
          (X := X) (β := beta) hX
    nlinarith [norm_nonneg (primeMajorCoefficient q),
      norm_nonneg (dyadicContinuousAmplitude X beta)]
  have hDBound : ∀ beta, ‖D beta‖ ≤ atomicSlidingBound X + X := by
    intro beta
    unfold D
    exact (norm_signedFourierDiscrepancy_le q a hX beta).trans (by
      have hc := MAPMajorArcIntegratedError.norm_primeMajorCoefficient_le_one hq
      nlinarith [norm_nonneg (primeMajorCoefficient q)])
  have hpoint : ∀ beta,
      |‖actual beta‖ ^ 2 - ‖model beta‖ ^ 2| ≤ U * ‖D beta‖ := by
    intro beta
    have hdef : actual beta - model beta = D beta := by
      rfl
    have hbase := abs_normSq_sub_normSq_le_of_error
      (actual := actual beta) (model := model beta)
      (E := ‖D beta‖) (by rw [hdef])
    have hm := hmodelBound beta
    have hd := hDBound beta
    calc
      |‖actual beta‖ ^ 2 - ‖model beta‖ ^ 2| ≤
          ‖D beta‖ * (2 * ‖model beta‖ + ‖D beta‖) := hbase
      _ ≤ ‖D beta‖ * U := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        dsimp [U]
        linarith
      _ = U * ‖D beta‖ := by ring
  have hnormCS := integral_norm_Ioc_le_rpow_half_mul hD hR
  unfold rationalArcPowerVariation
  rw [intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
  calc
    (∫ beta in Set.Ioc (-R) R,
        |‖actual beta‖ ^ 2 - ‖model beta‖ ^ 2|) ≤
      ∫ beta in Set.Ioc (-R) R, U * ‖D beta‖ := by
        apply MeasureTheory.integral_mono
        · exact ((hactual.norm.pow 2).sub (hmodel.norm.pow 2)).abs.integrableOn_Ioc
        · exact (hD.norm.integrableOn_Ioc).const_mul U
        · intro beta
          exact hpoint beta
    _ = U * ∫ beta in Set.Ioc (-R) R, ‖D beta‖ := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ U * ((2 * R) ^ (1 / 2 : ℝ) *
          (∫ beta in Set.Ioc (-R) R, ‖D beta‖ ^ 2) ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hnormCS hU


/-- Total literal paper-major variation controlled by the total signed L²
energy.  The finite-family factor is the exact cardinality of the flattened
reduced rational set; no disjointness or hidden union normalization is used. -/
theorem paperMajorPowerVariation_le_signedFourierEnergy
    {X : ℝ} (B D : ℕ) (hX : 1 < X) :
    paperMajorPowerVariation X B D ≤
      (atomicSlidingBound X + 3 * X) *
        ((2 * paperArcRadius X D) ^ (1 / 2 : ℝ) *
          (((paperReducedPairs X B).card : ℝ) ^ (1 / 2 : ℝ) *
            (paperMajorSignedFourierEnergy X B D) ^ (1 / 2 : ℝ))) := by
  let pairs := paperReducedPairs X B
  let R := paperArcRadius X D
  let E : ℕ × ℕ → ℝ := fun qa =>
    ∫ beta in Set.Ioc (-R) R,
      ‖signedFourierDiscrepancy X qa.1 qa.2 beta‖ ^ 2
  let U : ℝ := atomicSlidingBound X + 3 * X
  have hX0 : 0 ≤ X := (zero_lt_one.trans hX).le
  have hR : 0 ≤ R := by
    unfold R paperArcRadius
    have hlog : 0 ≤ Real.log X := (Real.log_pos hX).le
    positivity
  have hU : 0 ≤ U := add_nonneg (atomicSlidingBound_nonneg X)
    (mul_nonneg (by norm_num) hX0)
  have hE : ∀ qa, 0 ≤ E qa := by
    intro qa
    exact setIntegral_nonneg measurableSet_Ioc fun _ _ => sq_nonneg _
  have hsumLocal :
      ∑ qa ∈ pairs, rationalArcPowerVariation X R qa.1 qa.2 ≤
        ∑ qa ∈ pairs,
          U * ((2 * R) ^ (1 / 2 : ℝ) * (E qa) ^ (1 / 2 : ℝ)) := by
    apply Finset.sum_le_sum
    intro qa hqa
    have hqa' : qa ∈ paperReducedPairs X B := hqa
    unfold paperReducedPairs at hqa'
    rcases Finset.mem_biUnion.mp hqa' with ⟨q, hq, himage⟩
    rcases Finset.mem_image.mp himage with ⟨a, ha, hpair⟩
    have hq1 : 1 ≤ qa.1 := by
      rw [← hpair]
      exact (Finset.mem_Icc.mp hq).1
    simpa only [U, R, E] using
      rationalArcPowerVariation_le_rpow_half_energy hX0 hR hq1
  have hCS :
      ∑ qa ∈ pairs, (E qa) ^ (1 / 2 : ℝ) ≤
        ((pairs.card : ℝ) ^ (1 / 2 : ℝ)) *
          (∑ qa ∈ pairs, E qa) ^ (1 / 2 : ℝ) := by
    have hsqrt := Real.sum_sqrt_mul_sqrt_le pairs
      (fun _ => by norm_num : ∀ _ : ℕ × ℕ, 0 ≤ (1 : ℝ)) hE
    simpa [Real.sqrt_eq_rpow] using hsqrt
  have hcoef : 0 ≤ U * (2 * R) ^ (1 / 2 : ℝ) :=
    mul_nonneg hU (Real.rpow_nonneg (mul_nonneg (by norm_num) hR) _)
  have hsumFactor :
      (∑ qa ∈ pairs,
          U * ((2 * R) ^ (1 / 2 : ℝ) * (E qa) ^ (1 / 2 : ℝ))) ≤
        U * (2 * R) ^ (1 / 2 : ℝ) *
          (((pairs.card : ℝ) ^ (1 / 2 : ℝ)) *
            (∑ qa ∈ pairs, E qa) ^ (1 / 2 : ℝ)) := by
    calc
      _ = U * (2 * R) ^ (1 / 2 : ℝ) *
          (∑ qa ∈ pairs, (E qa) ^ (1 / 2 : ℝ)) := by
        rw [← Finset.mul_sum]
        have hpull :
            (∑ qa ∈ pairs,
              (2 * R) ^ (1 / 2 : ℝ) * (E qa) ^ (1 / 2 : ℝ)) =
            (2 * R) ^ (1 / 2 : ℝ) *
              (∑ qa ∈ pairs, (E qa) ^ (1 / 2 : ℝ)) := by
          rw [Finset.mul_sum]
        rw [hpull]
        ring
      _ ≤ U * (2 * R) ^ (1 / 2 : ℝ) *
          (((pairs.card : ℝ) ^ (1 / 2 : ℝ)) *
            (∑ qa ∈ pairs, E qa) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hCS hcoef
  have henergy :
      ∑ qa ∈ pairs, E qa = paperMajorSignedFourierEnergy X B D := by
    unfold pairs E R paperMajorSignedFourierEnergy
    rw [sum_paperReducedPairs X B (fun q a =>
      ∫ beta in Set.Ioc (-(paperArcRadius X D)) (paperArcRadius X D),
        ‖signedFourierDiscrepancy X q a beta‖ ^ 2)]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro a ha
    rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hvariation :
      paperMajorPowerVariation X B D =
        ∑ qa ∈ pairs, rationalArcPowerVariation X R qa.1 qa.2 := by
    unfold paperMajorPowerVariation pairs R
    rw [sum_paperReducedPairs X B]
  rw [hvariation, ← henergy]
  exact hsumLocal.trans (by
    calc
      _ ≤ U * (2 * R) ^ (1 / 2 : ℝ) *
          (((pairs.card : ℝ) ^ (1 / 2 : ℝ)) *
            (∑ qa ∈ pairs, E qa) ^ (1 / 2 : ℝ)) := hsumFactor
      _ = U * ((2 * R) ^ (1 / 2 : ℝ) *
          (((pairs.card : ℝ) ^ (1 / 2 : ℝ)) *
            (∑ qa ∈ pairs, E qa) ^ (1 / 2 : ℝ))) := by ring)


/-- End-to-end deterministic bridge from the actual paper-major signed sliding
energy to the integrated square-power variation contract.  The remaining
source obligation is now exactly the AP sliding-energy estimate. -/
theorem paperMajorPowerVariation_le_slidingEnergy
    {X : ℝ} (B D : ℕ) (hX : 1 < X) :
    paperMajorPowerVariation X B D ≤
      (atomicSlidingBound X + 3 * X) *
        ((2 * paperArcRadius X D) ^ (1 / 2 : ℝ) *
          (((paperReducedPairs X B).card : ℝ) ^ (1 / 2 : ℝ) *
            (4 / paperGallagherWindow X D ^ 2 *
              paperMajorSignedSlidingEnergy X B D) ^ (1 / 2 : ℝ))) := by
  have hpower := paperMajorPowerVariation_le_signedFourierEnergy B D hX
  have hfourier := paperMajorSignedFourierEnergy_le_slidingEnergy B D hX
  have hslide0 : 0 ≤ paperMajorSignedSlidingEnergy X B D := by
    unfold paperMajorSignedSlidingEnergy
    positivity
  have hcoeff0 : 0 ≤ 4 / paperGallagherWindow X D ^ 2 := by positivity
  have henergy0 : 0 ≤ paperMajorSignedFourierEnergy X B D := by
    unfold paperMajorSignedFourierEnergy
    positivity
  have hsqrt := Real.rpow_le_rpow henergy0 hfourier (by norm_num : 0 ≤ (1 / 2 : ℝ))
  have hU : 0 ≤ atomicSlidingBound X + 3 * X :=
    add_nonneg (atomicSlidingBound_nonneg X)
      (mul_nonneg (by norm_num) (zero_lt_one.trans hX).le)
  have hR : 0 ≤ paperArcRadius X D := by
    unfold paperArcRadius
    have hlog : 0 ≤ Real.log X := (Real.log_pos hX).le
    positivity
  have hcard : 0 ≤ ((paperReducedPairs X B).card : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hfront : 0 ≤
      (atomicSlidingBound X + 3 * X) *
        (2 * paperArcRadius X D) ^ (1 / 2 : ℝ) *
          ((paperReducedPairs X B).card : ℝ) ^ (1 / 2 : ℝ) := by positivity
  calc
    paperMajorPowerVariation X B D ≤
      (atomicSlidingBound X + 3 * X) *
        ((2 * paperArcRadius X D) ^ (1 / 2 : ℝ) *
          (((paperReducedPairs X B).card : ℝ) ^ (1 / 2 : ℝ) *
            (paperMajorSignedFourierEnergy X B D) ^ (1 / 2 : ℝ))) := hpower
    _ = ((atomicSlidingBound X + 3 * X) *
        (2 * paperArcRadius X D) ^ (1 / 2 : ℝ) *
          ((paperReducedPairs X B).card : ℝ) ^ (1 / 2 : ℝ)) *
            (paperMajorSignedFourierEnergy X B D) ^ (1 / 2 : ℝ) := by ring
    _ ≤ ((atomicSlidingBound X + 3 * X) *
        (2 * paperArcRadius X D) ^ (1 / 2 : ℝ) *
          ((paperReducedPairs X B).card : ℝ) ^ (1 / 2 : ℝ)) *
            (4 / paperGallagherWindow X D ^ 2 *
              paperMajorSignedSlidingEnergy X B D) ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hsqrt hfront
    _ = (atomicSlidingBound X + 3 * X) *
        ((2 * paperArcRadius X D) ^ (1 / 2 : ℝ) *
          (((paperReducedPairs X B).card : ℝ) ^ (1 / 2 : ℝ) *
            (4 / paperGallagherWindow X D ^ 2 *
              paperMajorSignedSlidingEnergy X B D) ^ (1 / 2 : ℝ))) := by ring

end
end MAPNearCollarGallagher
