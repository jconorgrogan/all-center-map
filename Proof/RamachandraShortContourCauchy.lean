import RamachandraShortHeadFamilyBudget
import RamachandraWeightedCauchyAE
import RamachandraShiftedHeadContourTails

/-!
# Weighted Cauchy for the literal short contour

The functional-factor exponent is kept until its conductor and external
ordinate powers cancel.  The single exceptional Mellin ordinate is discarded
only almost everywhere.  No quadrature or finite-rank replacement is used.
-/

namespace RamachandraShortContourCauchy

open scoped BigOperators Interval LSeries.notation
open Complex MeasureTheory
open BHPRamachandraMeanValueFromDyadicAFE
open RamachandraPrimitiveShiftedContourReduction
open RamachandraShiftedReflectedSeries
open RamachandraShiftedReflectedHeadAssembly
open RamachandraShortHeadFamilyBudget
open RamachandraShortFunctionalFactorMomentEnvelope
open RamachandraShiftedContourSharpEnvelopes
open RamachandraGammaWeightIntegrability
open RamachandraWeightedCauchyAE
open RamachandraShiftedHeadContourTails
open RamachandraShiftedHeadFiniteContour
open MAPMRTLemma210OrthogonalityReduction

noncomputable section

set_option maxHeartbeats 1000000

variable {d : ℕ} [NeZero d]

/-- A finite uniform norm bound for the literal reflected head. -/
def shortHeadUniformNormBound
    (psi : DirichletCharacter ℂ d) (X sigma : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
    ‖shiftedReflectedBlockCoeff sigma (-(Real.log X)⁻¹) 0 n * star psi n‖

private theorem norm_shiftedReflectedBlockCoeff_eq_zero
    (sigma u v : ℝ) (n : ℕ) :
    ‖shiftedReflectedBlockCoeff sigma u v n‖ =
      ‖shiftedReflectedBlockCoeff sigma u 0 n‖ := by
  unfold shiftedReflectedBlockCoeff
  rw [norm_mul, norm_mul, norm_twistedPhase, norm_twistedPhase]

theorem norm_shortReflectedHead_le_uniform
    (psi : DirichletCharacter ℂ d) {X : ℝ} (hX : 0 ≤ X)
    (sigma t v : ℝ) :
    ‖shortReflectedHead psi X sigma t v‖ ≤
      shortHeadUniformNormBound psi X sigma := by
  unfold shortReflectedHead
  rw [shortFunctionalPoint_eq_shifted]
  rw [ramachandraReflectedHead_eq_prefixPolynomial psi hX]
  unfold twistedFinitePolynomial shortHeadUniformNormBound
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul, norm_mul, norm_twistedPhase, mul_one,
    norm_shiftedReflectedBlockCoeff_eq_zero]
  rw [norm_mul]

theorem integrable_gammaWeight_mul_shortHead_sq
    (psi : DirichletCharacter ℂ d) {X sigma t : ℝ}
    (hX : 0 ≤ X) (hcLo : -1 < -(Real.log X)⁻¹)
    (hcHi : -(Real.log X)⁻¹ < 0) :
    Integrable (fun v : ℝ =>
      gammaPolynomialWeight (-(Real.log X)⁻¹) v *
        ‖shortReflectedHead psi X sigma t v‖ ^ 2) := by
  let C : ℝ := shortHeadUniformNormBound psi X sigma
  have hC : 0 ≤ C := by dsimp [C, shortHeadUniformNormBound]; positivity
  have hmajor : Integrable (fun v => C ^ 2 *
      gammaPolynomialWeight (-(Real.log X)⁻¹) v) :=
    (integrable_gammaPolynomialWeight hcLo hcHi).const_mul (C ^ 2)
  apply hmajor.mono'
  · exact ((continuous_gammaPolynomialWeight hcLo hcHi).mul
      (((continuous_uncurry_shortReflectedHead psi hX sigma).comp
        (continuous_id.prodMk continuous_const)).norm.pow 2)).aestronglyMeasurable
  · filter_upwards with v
    have hh := norm_shortReflectedHead_le_uniform psi hX sigma t v
    have hh2 : ‖shortReflectedHead psi X sigma t v‖ ^ 2 ≤ C ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hh 2
    rw [Real.norm_of_nonneg (mul_nonneg
      (gammaPolynomialWeight_nonneg _ _) (sq_nonneg _))]
    calc
      gammaPolynomialWeight (-(Real.log X)⁻¹) v *
          ‖shortReflectedHead psi X sigma t v‖ ^ 2 ≤
        gammaPolynomialWeight (-(Real.log X)⁻¹) v * C ^ 2 :=
          mul_le_mul_of_nonneg_left hh2 (gammaPolynomialWeight_nonneg _ _)
      _ = C ^ 2 * gammaPolynomialWeight (-(Real.log X)⁻¹) v := by ring

/-- Exact almost-everywhere square majorant for the short contour integrand. -/
theorem norm_shortContourIntegrand_sq_le_ae
    (psi : DirichletCharacter ℂ d) (hprim : psi.IsPrimitive)
    {X T sigma t : ℝ}
    (hXeq : X = (d : ℝ) * T) (hT : 3 ≤ T) (hX : 6 ≤ X)
    (hstrip : |sigma - (1 / 2 : ℝ)| ≤
      (100 * Real.log X)⁻¹) (ht : |t| ≤ T) :
    ∀ᵐ v : ℝ,
      ‖ramachandraShiftedContourIntegrand psi X sigma
          (-(Real.log X)⁻¹) t v false‖ ^ 2 ≤
        gammaPolynomialWeight (-(Real.log X)⁻¹) v *
          (shortFunctionalMomentConstant *
            gammaPolynomialWeight (-(Real.log X)⁻¹) v *
              ‖shortReflectedHead psi X sigma t v‖ ^ 2) := by
  filter_upwards [eventually_t_add_ne_zero t] with v hne
  have hfac := norm_functionalFactor_short_pow_four_le
    psi hprim hXeq hT hX hstrip ht hne
  have hXpos : 0 < X := by linarith
  have hscaleEq :
      ‖(X : ℂ) ^ (((-(Real.log X)⁻¹ : ℝ) : ℂ) + (v : ℂ) * I)‖ ^ 2 =
        Real.rpow X (-2 * (Real.log X)⁻¹) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hXpos]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      zero_mul, mul_zero, sub_zero, add_zero]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le]
    congr 1
    ring
  have hscale :
      Real.rpow X (-2 * (Real.log X)⁻¹) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
    have hi : 0 ≤ (Real.log X)⁻¹ := inv_nonneg.mpr (Real.log_pos (by linarith)).le
    linarith
  have hv1 : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
  have hvpow : (1 + |v|) ^ 3 ≤ (1 + |v|) ^ 12 := by gcongr <;> norm_num
  unfold ramachandraShiftedContourIntegrand shortReflectedHead
  rw [shortFunctionalPoint_eq_shifted]
  simp only [Bool.false_eq_true, ↓reduceIte, norm_mul, norm_pow]
  let R : ℝ := ‖ramachandraReflectedHead psi X
    (ramachandraShiftedPoint sigma t +
      (((-(Real.log X)⁻¹ : ℝ) : ℂ) + (v : ℂ) * I))‖ ^ 2
  let G : ℝ := ‖Complex.Gamma
    (((-(Real.log X)⁻¹ : ℝ) : ℂ) + (v : ℂ) * I)‖
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hG : 0 ≤ G := norm_nonneg _
  rw [show ramachandraShiftedPoint sigma t +
      ((↑(-(Real.log X)⁻¹) + ↑v * I)) = shortFunctionalPoint X sigma t v by
    exact (shortFunctionalPoint_eq_shifted X sigma t v).symm]
  have hReq : R = ‖ramachandraReflectedHead psi X
      (shortFunctionalPoint X sigma t v)‖ ^ 2 := by
    dsimp [R]
    rw [shortFunctionalPoint_eq_shifted]
  have hleft :
      (‖ramachandraFunctionalFactor psi (shortFunctionalPoint X sigma t v)‖ ^ 2 *
            ‖ramachandraReflectedHead psi X (shortFunctionalPoint X sigma t v)‖ * G *
          ‖(X : ℂ) ^ (((-(Real.log X)⁻¹ : ℝ) : ℂ) + (v : ℂ) * I)‖) ^ 2 ≤
        ‖ramachandraFunctionalFactor psi (shortFunctionalPoint X sigma t v)‖ ^ 4 *
          R * G ^ 2 := by
    rw [hReq]
    calc
      _ = ‖ramachandraFunctionalFactor psi (shortFunctionalPoint X sigma t v)‖ ^ 4 *
          ‖ramachandraReflectedHead psi X (shortFunctionalPoint X sigma t v)‖ ^ 2 *
          G ^ 2 *
          ‖(X : ℂ) ^ (((-(Real.log X)⁻¹ : ℝ) : ℂ) + (v : ℂ) * I)‖ ^ 2 := by ring
      _ = ‖ramachandraFunctionalFactor psi (shortFunctionalPoint X sigma t v)‖ ^ 4 *
          ‖ramachandraReflectedHead psi X (shortFunctionalPoint X sigma t v)‖ ^ 2 *
          G ^ 2 * Real.rpow X (-2 * (Real.log X)⁻¹) := by rw [hscaleEq]
      _ ≤ ‖ramachandraFunctionalFactor psi (shortFunctionalPoint X sigma t v)‖ ^ 4 *
          ‖ramachandraReflectedHead psi X (shortFunctionalPoint X sigma t v)‖ ^ 2 *
          G ^ 2 * 1 := by gcongr
      _ = _ := by ring
  apply hleft.trans
  unfold gammaPolynomialWeight
  calc
    ‖ramachandraFunctionalFactor psi (shortFunctionalPoint X sigma t v)‖ ^ 4 *
          R * G ^ 2 ≤
        (shortFunctionalMomentConstant * (1 + |v|) ^ 3) * R * G ^ 2 := by
      gcongr
    _ ≤ (G * (1 + |v|) ^ 6) *
        (shortFunctionalMomentConstant * (G * (1 + |v|) ^ 6) * R) := by
      have hP : 0 ≤ shortFunctionalMomentConstant * R * G ^ 2 :=
        mul_nonneg (mul_nonneg shortFunctionalMomentConstant_nonneg hR) (sq_nonneg G)
      calc
        (shortFunctionalMomentConstant * (1 + |v|) ^ 3) * R * G ^ 2 =
            (shortFunctionalMomentConstant * R * G ^ 2) * (1 + |v|) ^ 3 := by ring
        _ ≤ (shortFunctionalMomentConstant * R * G ^ 2) * (1 + |v|) ^ 12 :=
          mul_le_mul_of_nonneg_left hvpow hP
        _ = _ := by
          rw [hReq]
          dsimp [G]
          ring
    _ = _ := by
      rw [hReq]

/-- Weighted Cauchy for the normalized literal short contour. -/
theorem norm_primitiveShiftedShortContour_sq_le
    (psi : DirichletCharacter ℂ d) (hprim : psi.IsPrimitive)
    {T sigma t : ℝ} (hT : 3 ≤ T)
    (hX : 6 ≤ primitiveShiftedScale d T)
    (hstrip : |sigma - (1 / 2 : ℝ)| ≤
      (100 * Real.log (primitiveShiftedScale d T))⁻¹)
    (ht : |t| ≤ T) :
    ‖primitiveShiftedShortContour psi T sigma t‖ ^ 2 ≤
      (∫ v : ℝ, gammaPolynomialWeight
        (-(Real.log (primitiveShiftedScale d T))⁻¹) v) *
        ∫ v : ℝ,
          shortFunctionalMomentConstant *
            gammaPolynomialWeight
              (-(Real.log (primitiveShiftedScale d T))⁻¹) v *
              ‖shortReflectedHead psi (primitiveShiftedScale d T) sigma t v‖ ^ 2 := by
  let X := primitiveShiftedScale d T
  let w : ℝ → ℝ := gammaPolynomialWeight (-(Real.log X)⁻¹)
  let g : ℝ → ℝ := fun v => shortFunctionalMomentConstant * w v *
    ‖shortReflectedHead psi X sigma t v‖ ^ 2
  let f : ℝ → ℂ := fun v => ramachandraShiftedContourIntegrand
    psi X sigma (-(Real.log X)⁻¹) t v false
  have hXpos : 0 < X := by dsimp [X]; linarith
  have hlog : 1 < Real.log X :=
    RamachandraShiftedDirectParameters.one_lt_log_of_three_le (by linarith)
  have hcLo : -1 < -(Real.log X)⁻¹ := by
    have hi : (Real.log X)⁻¹ < 1 := (inv_lt_one₀ (by linarith)).2 hlog
    linarith
  have hcHi : -(Real.log X)⁻¹ < 0 := by
    have hi : 0 < (Real.log X)⁻¹ := inv_pos.mpr (by linarith)
    linarith
  have hab := shortExponent_bounds (by simpa [X] using hX)
    (by simpa [X] using hstrip)
  have hrlo : -(1 / 4 : ℝ) ≤ sigma - (Real.log X)⁻¹ := by
    change 0 ≤ _ ∧ _ at hab
    linarith [hab.2.2]
  have hrhi : sigma - (Real.log X)⁻¹ ≤ 1 / 2 := by
    change 0 ≤ _ ∧ _ at hab
    linarith [hab.1]
  have hf : Integrable f := by
    have h := integrable_shiftedHead_vertical psi hprim
      (ramachandraShiftedPoint sigma t) hXpos hcLo hcHi
      (by simpa [ramachandraShiftedPoint, add_comm] using hrlo)
      (by simpa [ramachandraShiftedPoint] using hrhi)
    simpa [f, ramachandraShiftedContourIntegrand, shiftedHeadIntegrand] using h
  have hw : Integrable w := integrable_gammaPolynomialWeight hcLo hcHi
  have hhead := integrable_gammaWeight_mul_shortHead_sq
    psi hXpos.le hcLo hcHi (sigma := sigma) (t := t)
  have hg : Integrable g := by
    simpa [g, w, mul_assoc] using hhead.const_mul shortFunctionalMomentConstant
  have hw0 (v : ℝ) : 0 ≤ w v := gammaPolynomialWeight_nonneg _ _
  have hg0 (v : ℝ) : 0 ≤ g v := by
    dsimp [g]
    exact mul_nonneg
      (mul_nonneg shortFunctionalMomentConstant_nonneg
        (gammaPolynomialWeight_nonneg _ _)) (sq_nonneg _)
  have hsq := norm_shortContourIntegrand_sq_le_ae psi hprim
    (X := X) (T := T) (sigma := sigma) (t := t)
    (by rfl) hT (by simpa [X] using hX) (by simpa [X] using hstrip) ht
  have hfg : ∀ᵐ v : ℝ, ‖f v‖ ≤ Real.sqrt (w v) * Real.sqrt (g v) := by
    filter_upwards [hsq] with v hv
    have hsqroot : ‖f v‖ ≤ Real.sqrt (w v * g v) := by
      rw [← Real.sqrt_sq (norm_nonneg _)]
      exact Real.sqrt_le_sqrt (by simpa [f, g, w, mul_assoc] using hv)
    rwa [Real.sqrt_mul (hw0 v)] at hsqroot
  have hcauchy := norm_integral_sq_le_integral_mul_integral_ae
    f w g hf hw hg hw0 hg0 hfg
  let If : ℂ := ∫ v : ℝ, f v
  change ‖If‖ ^ 2 ≤ (∫ v, w v) * ∫ v, g v at hcauchy
  have hpref : ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ ^ 2 ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hi : 0 ≤ (1 / (2 * Real.pi) : ℝ) := by positivity
    have hi1 : (1 / (2 * Real.pi) : ℝ) ≤ 1 := (div_le_one (by positivity)).2 hpi
    nlinarith
  unfold primitiveShiftedShortContour ramachandraShiftedContourPiece
  change ‖(((1 / (2 * Real.pi) : ℝ) : ℂ)) * If‖ ^ 2 ≤ _
  rw [norm_mul, mul_pow]
  calc
    ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ ^ 2 * ‖If‖ ^ 2 ≤
        1 * ‖If‖ ^ 2 := by gcongr
    _ ≤ (∫ v, w v) * ∫ v, g v := by simpa using hcauchy
    _ = _ := by rfl

end
end RamachandraShortContourCauchy

#print axioms RamachandraShortContourCauchy.norm_primitiveShiftedShortContour_sq_le
