import MajorArcPublicLiftBridge
import ModelOverlapEnergy
import SupportBoundaryQuantitative

/-!
# Integrated major-arc power discrepancy

This module exposes the weaker major-arc input suggested by the signed
Gallagher route.  It does not assume pointwise Siegel--Walfisz.  Instead it
uses the literal L1 variation of the prime/model square-power discrepancy on
all paper rational arcs and proves that arbitrary logarithmic saving for that
variation supplies the prime-polynomial energy family consumed by the final
MAP weld.
-/

namespace MAPMajorArcIntegratedPowerWeld

open AddCircle MeasureTheory Set
open PrimePairEndpoints MAPMajorArcWeld MAPMajorArcIntegratedError
open MAPModelOverlapEnergy

noncomputable section

/-- L1 variation of the square-power discrepancy on one lifted rational arc. -/
def rationalArcPowerVariation
    (X R : ℝ) (q a : ℕ) : ℝ :=
  ∫ beta in -R..R,
    |‖primeExponentialSum X
          (rationalCenter q a + (beta : UnitAddCircle))‖ ^ 2 -
      ‖primeMajorCoefficient q * dyadicContinuousAmplitude X beta‖ ^ 2|

/-- Sum of the literal one-arc variations over the paper denominator cutoff. -/
def paperMajorPowerVariation (X : ℝ) (B D : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 (paperDenominatorCutoff X B),
    ∑ a ∈ reducedResidues q,
      rationalArcPowerVariation X (paperArcRadius X D) q a

/-- Source-facing integrated contract.  Unlike pointwise Siegel--Walfisz,
this is exactly an L1 square-power estimate on the rational arcs.  Signed
Gallagher plus Cauchy--Schwarz is expected to supply it from the same AP
sliding energy used by the near-collar branch. -/
def SelectableIntegratedMajorPowerVariationFamily : Prop :=
  ∀ A ε : ℝ, 0 < A → 0 < ε →
    ∀ B₀ D₀ : ℕ,
      ∃ B D : ℕ, B₀ ≤ B ∧ D₀ ≤ D ∧
        ∃ C X₀ : ℝ, 0 < C ∧ 3 ≤ X₀ ∧
          ∀ X : ℝ, X₀ ≤ X →
            paperMajorPowerVariation X B D ≤
              C * X * Real.rpow (Real.log X) (-A)

theorem norm_interval_normSq_phase_sub_le_variation
    {R : ℝ} (hR : 0 ≤ R) {actual model phase : ℝ → ℂ}
    (hactual : Continuous actual) (hmodel : Continuous model)
    (hphase : Continuous phase) (hphaseNorm : ∀ beta, ‖phase beta‖ = 1) :
    ‖(∫ beta in -R..R, ((‖actual beta‖ ^ 2 : ℝ) : ℂ) * phase beta) -
      ∫ beta in -R..R, ((‖model beta‖ ^ 2 : ℝ) : ℂ) * phase beta‖ ≤
        ∫ beta in -R..R,
          |‖actual beta‖ ^ 2 - ‖model beta‖ ^ 2| := by
  have hactualInt : IntervalIntegrable
      (fun beta => ((‖actual beta‖ ^ 2 : ℝ) : ℂ) * phase beta)
      volume (-R) R :=
    ((Complex.continuous_ofReal.comp (hactual.norm.pow 2)).mul hphase).intervalIntegrable _ _
  have hmodelInt : IntervalIntegrable
      (fun beta => ((‖model beta‖ ^ 2 : ℝ) : ℂ) * phase beta)
      volume (-R) R :=
    ((Complex.continuous_ofReal.comp (hmodel.norm.pow 2)).mul hphase).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub hactualInt hmodelInt]
  calc
    ‖∫ beta in -R..R,
        ((‖actual beta‖ ^ 2 : ℝ) : ℂ) * phase beta -
          ((‖model beta‖ ^ 2 : ℝ) : ℂ) * phase beta‖ ≤
        ∫ beta in -R..R,
          ‖((‖actual beta‖ ^ 2 : ℝ) : ℂ) * phase beta -
            ((‖model beta‖ ^ 2 : ℝ) : ℂ) * phase beta‖ :=
      intervalIntegral.norm_integral_le_integral_norm (neg_le_self hR)
    _ = ∫ beta in -R..R,
          |‖actual beta‖ ^ 2 - ‖model beta‖ ^ 2| := by
      apply intervalIntegral.integral_congr
      intro beta hbeta
      simp only
      rw [← sub_mul]
      rw [norm_mul, hphaseNorm, mul_one, ← Complex.ofReal_sub,
        Complex.norm_real,
        Real.norm_eq_abs]

/-- One lifted arc is bounded by its literal integrated power variation. -/
theorem norm_actualLiftedRationalArc_sub_modeled_le_variation
    {X R : ℝ} {q a : ℕ} {h : ℤ} (hX : 0 ≤ X) (hR : 0 ≤ R) :
    ‖actualLiftedRationalArc X R q a h -
        modeledRationalArc (dyadicContinuousAmplitude X) R q a h‖ ≤
      rationalArcPowerVariation X R q a := by
  unfold actualLiftedRationalArc modeledRationalArc rationalArcPowerVariation
  apply norm_interval_normSq_phase_sub_le_variation hR
  · exact continuous_primePolynomial_lift X q a
  · exact continuous_const.mul (by
      simpa only [dyadicContinuousAmplitude] using!
        MAPContinuousOverlap.continuous_dyadicAmplitude X)
  · fun_prop
  · intro beta
    rw [fourier_apply, Circle.norm_coe]

/-- The complete lifted paper major contribution is bounded by the sum of
the one-arc power variations. -/
theorem norm_actualLiftedPaperMajorContribution_sub_modeled_le_variation
    {X : ℝ} {B D : ℕ} {h : ℤ} (hX : 1 ≤ X) :
    ‖actualLiftedPaperMajorContribution X B D h -
        modeledPaperMajorContribution X B D h‖ ≤
      paperMajorPowerVariation X B D := by
  have hR : 0 ≤ paperArcRadius X D := by
    unfold paperArcRadius
    have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
    positivity
  unfold actualLiftedPaperMajorContribution modeledPaperMajorContribution
    actualLiftedMajorContribution modeledDyadicMajorContribution
    paperMajorPowerVariation
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ q ∈ Finset.Icc 1 (paperDenominatorCutoff X B),
        ((∑ a ∈ reducedResidues q, actualLiftedRationalArc X (paperArcRadius X D) q a h) -
          ∑ a ∈ reducedResidues q,
            modeledRationalArc (dyadicContinuousAmplitude X)
              (paperArcRadius X D) q a h)‖ ≤
      ∑ q ∈ Finset.Icc 1 (paperDenominatorCutoff X B),
        ‖(∑ a ∈ reducedResidues q, actualLiftedRationalArc X (paperArcRadius X D) q a h) -
          ∑ a ∈ reducedResidues q,
            modeledRationalArc (dyadicContinuousAmplitude X)
              (paperArcRadius X D) q a h‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.Icc 1 (paperDenominatorCutoff X B),
        ∑ a ∈ reducedResidues q,
          ‖actualLiftedRationalArc X (paperArcRadius X D) q a h -
            modeledRationalArc (dyadicContinuousAmplitude X)
              (paperArcRadius X D) q a h‖ := by
      gcongr with q hq
      rw [← Finset.sum_sub_distrib]
      exact norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.Icc 1 (paperDenominatorCutoff X B),
        ∑ a ∈ reducedResidues q,
          rationalArcPowerVariation X (paperArcRadius X D) q a := by
      gcongr with q hq a ha
      exact norm_actualLiftedRationalArc_sub_modeled_le_variation
        (zero_le_one.trans hX) hR

/-- Integrated major-arc power saving supplies exactly the selectable
prime-polynomial energy family used by the final deterministic MAP weld. -/
theorem selectablePrimePolynomialModelErrorEnergy_of_integratedPower
    (hIntegrated : SelectableIntegratedMajorPowerVariationFamily) :
    SelectablePrimePolynomialModelErrorEnergyFamily := by
  intro A ε hA hε B₀ D₀
  obtain ⟨B, D, hB, hD, C0, X0, hC0, hX0, hvar⟩ :=
    hIntegrated (A / 2) ε (by positivity) hε B₀ D₀
  obtain ⟨Xg, hg⟩ := MAPMajorArcPublicLiftBridge.eventually_paperArc_geometry B D
  let C : ℝ := 3 * C0 ^ 2
  let X₀ : ℝ := max X0 Xg
  have hC : 0 < C := by dsimp [C]; positivity
  have hX₀ : 3 ≤ X₀ := hX0.trans (le_max_left _ _)
  refine ⟨B, D, hB, hD, C, X₀, hC, hX₀, ?_⟩
  intro X H h₀ hXX₀ hlegal
  have hXX0 : X0 ≤ X := (le_max_left X0 Xg).trans hXX₀
  have hXXg : Xg ≤ X := (le_max_right X0 Xg).trans hXX₀
  obtain ⟨hX1, hR, hRhalf, hgrowth⟩ := hg X hXXg
  have hpoint : ∀ h : ℤ,
      ‖primePolynomialModelError X B D h‖ ≤
        C0 * X * Real.rpow (Real.log X) (-(A / 2)) := by
    intro h
    unfold primePolynomialModelError
    rw [MAPMajorArcPublicLiftBridge.majorCoefficient_eq_actualLiftedPaperMajorContribution
      hX1 hRhalf hgrowth]
    exact (norm_actualLiftedPaperMajorContribution_sub_modeled_le_variation
      hX1.le).trans (hvar X hXX0)
  have hH1 := SupportBoundaryQuantitative.one_le_H_of_legal hX1.le hε hlegal
  have hboundnonneg :
      0 ≤ C0 * X * Real.rpow (Real.log X) (-(A / 2)) := by
    exact mul_nonneg (mul_nonneg hC0.le (zero_le_one.trans hX1.le))
      (Real.rpow_nonneg (Real.log_pos hX1).le _)
  have hcard := SupportBoundaryQuantitative.translatedWindow_card_real_le
    (h₀ := h₀) (by linarith : 0 ≤ H)
  have hcard3 : ((translatedWindow H h₀).card : ℝ) ≤ 3 * H :=
    hcard.trans (by linarith)
  unfold primePolynomialModelErrorEnergy
  calc
    (∑ h ∈ translatedWindow H h₀,
        if h = 0 then 0 else ‖primePolynomialModelError X B D h‖ ^ 2) ≤
      ∑ _h ∈ translatedWindow H h₀,
        (C0 * X * Real.rpow (Real.log X) (-(A / 2))) ^ 2 := by
      apply Finset.sum_le_sum
      intro h hh
      split_ifs
      · positivity
      · exact sq_le_sq₀ (norm_nonneg _) hboundnonneg |>.2 (hpoint h)
    _ = ((translatedWindow H h₀).card : ℝ) *
        (C0 * X * Real.rpow (Real.log X) (-(A / 2))) ^ 2 := by simp
    _ ≤ (3 * H) *
        (C0 * X * Real.rpow (Real.log X) (-(A / 2))) ^ 2 := by
      gcongr
    _ = C * H * X ^ 2 * Real.rpow (Real.log X) (-A) := by
      dsimp [C]
      have hlogpos : 0 < Real.log X := Real.log_pos hX1
      have hrpow :
          Real.rpow (Real.log X) (-(A / 2)) *
              Real.rpow (Real.log X) (-(A / 2)) =
            Real.rpow (Real.log X) (-A) := by
        calc
          Real.rpow (Real.log X) (-(A / 2)) *
              Real.rpow (Real.log X) (-(A / 2)) =
            Real.rpow (Real.log X) (-(A / 2) + -(A / 2)) :=
              (Real.rpow_add hlogpos _ _).symm
          _ = Real.rpow (Real.log X) (-A) := by
            congr 1
            ring
      calc
        3 * H * (C0 * X * Real.rpow (Real.log X) (-(A / 2))) ^ 2 =
          3 * C0 ^ 2 * H * X ^ 2 *
            (Real.rpow (Real.log X) (-(A / 2)) *
              Real.rpow (Real.log X) (-(A / 2))) := by ring
        _ = 3 * C0 ^ 2 * H * X ^ 2 *
            Real.rpow (Real.log X) (-A) := by rw [hrpow]

end
end MAPMajorArcIntegratedPowerWeld

#print axioms MAPMajorArcIntegratedPowerWeld.selectablePrimePolynomialModelErrorEnergy_of_integratedPower
