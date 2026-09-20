import HarmonicFrontend
import NormalizedCoefficientWrapper

/-!
# The unconditional mixed-mean sinc-square weld

This module supplies the missing analytic bridge between the manuscript's
literal compact rectangle and the checked finite tuple model.  The original
mixed mean remains complex-valued; the first lemmas identify it with a real,
nonnegative integral.  The paper's two sinc-square majorants then give the
literal factor `4 * 4 = 16`.  Finally, finite Fubini and the already checked
Fourier pair expand the whole-line weighted integral into the simultaneous
two-frequency survivor set, with both scale factors and the translated
`t`-center phase visible.
-/

noncomputable section

namespace MixedMeanMajorantWeld

open MeasureTheory
open DeterminantCountWeld
open MixedMeanFrontend
open MAPMixedHarmonic
open MixedMellinCert

/-! ## Real form of the complex energy and compact mixed mean -/

/-- The existing complex energy is exactly the real squared norm. -/
theorem energy_eq_sq_norm (z : ℂ) :
    energy z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [energy, show star z = (starRingEnd ℂ) z by rfl,
    Complex.mul_conj, Complex.sq_norm]

/-- The real mixed mean represented by the original complex definition. -/
def literalMixedMeanReal (M N : ℕ) (β g : ℕ → ℂ)
    (t₀ T U : ℝ) : ℝ :=
  ∫ t in (t₀ - T / 2)..(t₀ + T / 2),
    ‖longFactor N g t‖ ^ 2 *
      (∫ u in (-2 * U)..(2 * U), ‖shortFactor M β (t + u)‖ ^ 2)

/-- The original complex-valued mixed mean is the real embedding of
`literalMixedMeanReal`; in particular, no reality assumption is imposed. -/
theorem literalMixedMean_eq_ofReal
    (M N : ℕ) (β g : ℕ → ℂ) (t₀ T U : ℝ) :
    literalMixedMean M N β g t₀ T U =
      (literalMixedMeanReal M N β g t₀ T U : ℂ) := by
  unfold literalMixedMean literalMixedMeanReal
  simp_rw [energy_eq_sq_norm]
  simp_rw [intervalIntegral.integral_ofReal]
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro t ht
  change ((‖longFactor N g t‖ ^ 2 : ℝ) : ℂ) *
      ((∫ u in (-2 * U)..(2 * U), ‖shortFactor M β (t + u)‖ ^ 2 : ℝ) : ℂ) =
    ((‖longFactor N g t‖ ^ 2 *
      ∫ u in (-2 * U)..(2 * U), ‖shortFactor M β (t + u)‖ ^ 2 : ℝ) : ℂ)
  exact (Complex.ofReal_mul _ _).symm

theorem literalMixedMean_im_eq_zero
    (M N : ℕ) (β g : ℕ → ℂ) (t₀ T U : ℝ) :
    (literalMixedMean M N β g t₀ T U).im = 0 := by
  rw [literalMixedMean_eq_ofReal]
  simp

theorem literalMixedMean_re_eq
    (M N : ℕ) (β g : ℕ → ℂ) (t₀ T U : ℝ) :
    (literalMixedMean M N β g t₀ T U).re =
      literalMixedMeanReal M N β g t₀ T U := by
  rw [literalMixedMean_eq_ofReal]
  simp

theorem literalMixedMeanReal_nonneg
    (M N : ℕ) (β g : ℕ → ℂ) (t₀ : ℝ)
    {T U : ℝ} (hT : 0 ≤ T) (hU : 0 ≤ U) :
    0 ≤ literalMixedMeanReal M N β g t₀ T U := by
  unfold literalMixedMeanReal
  apply intervalIntegral.integral_nonneg (by linarith)
  intro t ht
  exact mul_nonneg (sq_nonneg _) <|
    intervalIntegral.integral_nonneg (by linarith) (fun u hu ↦ sq_nonneg _)

/-! ## Whole-line weighted mixed mean -/

/-- Real, pointwise nonnegative whole-line mixed mean with the paper's exact
sinc-square kernels and scales. -/
def wholeLineSincMixedMeanReal
    (M N : ℕ) (β g : ℕ → ℂ) (center St Su : ℝ) : ℝ :=
  ∫ t : ℝ,
    eta ((t - center) / St) * ‖longFactor N g t‖ ^ 2 *
      (∫ u : ℝ,
        eta (u / Su) * ‖shortFactor M β (t + u)‖ ^ 2)

/-- Complex form of the same whole-line integral, kept in the coefficient
field used by the exact square and Fourier expansions. -/
def wholeLineSincMixedMean
    (M N : ℕ) (β g : ℕ → ℂ) (center St Su : ℝ) : ℂ :=
  ∫ t : ℝ,
    (eta ((t - center) / St) : ℂ) * energy (longFactor N g t) *
      (∫ u : ℝ,
        (eta (u / Su) : ℂ) * energy (shortFactor M β (t + u)))

/-- Integrability of a translated and scaled paper kernel. -/
theorem eta_scaled_integrable {S : ℝ} (hS : S ≠ 0) (center : ℝ) :
    Integrable (fun x : ℝ ↦ eta ((x - center) / S)) := by
  have h := (eta_integrable.comp_div hS).comp_add_right (-center)
  simpa [sub_eq_add_neg, add_div] using h

/-- The complex whole-line definition is again exactly real. -/
theorem wholeLineSincMixedMean_eq_ofReal
    (M N : ℕ) (β g : ℕ → ℂ) (center St Su : ℝ) :
    wholeLineSincMixedMean M N β g center St Su =
      (wholeLineSincMixedMeanReal M N β g center St Su : ℂ) := by
  unfold wholeLineSincMixedMean wholeLineSincMixedMeanReal
  simp_rw [energy_eq_sq_norm]
  simp_rw [← Complex.ofReal_mul, integral_complex_ofReal]
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with t
  push_cast
  ring

theorem wholeLineSincMixedMeanReal_nonneg
    (M N : ℕ) (β g : ℕ → ℂ) (center St Su : ℝ) :
    0 ≤ wholeLineSincMixedMeanReal M N β g center St Su := by
  unfold wholeLineSincMixedMeanReal
  apply integral_nonneg
  intro t
  exact mul_nonneg
    (mul_nonneg (eta_nonneg _) (sq_nonneg _))
    (integral_nonneg (fun u ↦ mul_nonneg (eta_nonneg _) (sq_nonneg _)))

/-! ## Integrability and exact tuple evaluation -/

/-- The two-kernel integrand attached to one literal tuple. -/
def sincTupleIntegrand (β g : ℕ → ℂ) (center St Su : ℝ)
    (q : LiteralTuple) (t u : ℝ) : ℂ :=
  (eta ((t - center) / St) : ℂ) * (eta (u / Su) : ℂ) *
    tupleTerm β g q t u

theorem integrable_sincTupleIntegrand_u
    (β g : ℕ → ℂ) (center St : ℝ) {Su : ℝ} (hSu : Su ≠ 0)
    (q : LiteralTuple) (t : ℝ) :
    Integrable (fun u : ℝ ↦ sincTupleIntegrand β g center St Su q t u) := by
  have heta : Integrable (fun u : ℝ ↦ (eta (u / Su) : ℂ)) :=
    by simpa using (eta_scaled_integrable hSu 0).ofReal
  have hbounded : ∀ᵐ u : ℝ,
      ‖tupleTerm β g q t u‖ ≤ ‖tupleCoefficient β g q‖ := by
    filter_upwards with u
    rw [tupleTerm_frequency_form, norm_mul,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have htuple : AEStronglyMeasurable (fun u : ℝ ↦ tupleTerm β g q t u) := by
    apply Continuous.aestronglyMeasurable
    rw [show (fun u : ℝ ↦ tupleTerm β g q t u) =
        fun u : ℝ ↦ tupleCoefficient β g q *
          Complex.exp
            (((t * jointFrequency q + u * shortFrequency q : ℝ) : ℂ) *
              Complex.I) by
      funext u
      exact tupleTerm_frequency_form β g q t u]
    fun_prop
  have hu : Integrable (fun u : ℝ ↦
      (eta (u / Su) : ℂ) * tupleTerm β g q t u) :=
    heta.mul_bdd htuple hbounded
  unfold sincTupleIntegrand
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    hu.const_mul (eta ((t - center) / St) : ℂ)

/-- The oscillatory factor in `scaledEtaAngularMoment` can be written with
the clock variable on the left. -/
theorem scaledEtaAngularMoment_eq_comm
    (S center omega : ℝ) :
    (∫ t : ℝ, (eta ((t - center) / S) : ℂ) *
      Complex.exp ((((t * omega : ℝ) : ℂ) * Complex.I))) =
      scaledEtaAngularMoment S center omega := by
  unfold scaledEtaAngularMoment
  apply integral_congr_ae
  filter_upwards with t
  congr 2
  push_cast
  ring

theorem integral_sincTupleIntegrand_u
    (β g : ℕ → ℂ) (center St Su : ℝ)
    (q : LiteralTuple) (t : ℝ) :
    (∫ u : ℝ, sincTupleIntegrand β g center St Su q t u) =
      (eta ((t - center) / St) : ℂ) * tupleCoefficient β g q *
        Complex.exp
          ((((t * jointFrequency q : ℝ) : ℂ) * Complex.I)) *
        scaledEtaAngularMoment Su 0 (shortFrequency q) := by
  have hsplit (u : ℝ) :
      Complex.exp
          (((t * jointFrequency q + u * shortFrequency q : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((((t * jointFrequency q : ℝ) : ℂ) * Complex.I)) *
          Complex.exp ((((u * shortFrequency q : ℝ) : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [show (fun u : ℝ ↦ sincTupleIntegrand β g center St Su q t u) =
      fun u : ℝ ↦
        ((eta ((t - center) / St) : ℂ) * tupleCoefficient β g q *
          Complex.exp ((((t * jointFrequency q : ℝ) : ℂ) * Complex.I))) *
          ((eta (u / Su) : ℂ) *
            Complex.exp ((((u * shortFrequency q : ℝ) : ℂ) * Complex.I))) by
    funext u
    unfold sincTupleIntegrand
    rw [tupleTerm_frequency_form, hsplit]
    ring]
  rw [integral_const_mul]
  have hmom :
      (∫ a : ℝ, (eta (a / Su) : ℂ) *
        Complex.exp ((((a * shortFrequency q : ℝ) : ℂ) * Complex.I))) =
        scaledEtaAngularMoment Su 0 (shortFrequency q) := by
    simpa only [sub_zero] using
      scaledEtaAngularMoment_eq_comm Su 0 (shortFrequency q)
  rw [hmom]

theorem integrable_integral_sincTupleIntegrand_u
    (β g : ℕ → ℂ) {St Su : ℝ} (hSt : St ≠ 0)
    (center : ℝ) (q : LiteralTuple) :
    Integrable (fun t : ℝ ↦
      ∫ u : ℝ, sincTupleIntegrand β g center St Su q t u) := by
  rw [show (fun t : ℝ ↦
      ∫ u : ℝ, sincTupleIntegrand β g center St Su q t u) =
    fun t : ℝ ↦
      (eta ((t - center) / St) : ℂ) *
        (tupleCoefficient β g q *
          Complex.exp ((((t * jointFrequency q : ℝ) : ℂ) * Complex.I)) *
          scaledEtaAngularMoment Su 0 (shortFrequency q)) by
      funext t
      rw [integral_sincTupleIntegrand_u]
      ring]
  have heta : Integrable (fun t : ℝ ↦
      (eta ((t - center) / St) : ℂ)) :=
    (eta_scaled_integrable hSt center).ofReal
  apply heta.mul_bdd (c :=
    ‖tupleCoefficient β g q‖ *
      ‖scaledEtaAngularMoment Su 0 (shortFrequency q)‖)
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · filter_upwards with t
    rw [norm_mul, norm_mul]
    rw [Complex.norm_exp]
    simp

/-- One tuple's iterated whole-line integral is the product of the two exact
scaled sinc moments. -/
theorem iteratedIntegral_sincTupleIntegrand
    (β g : ℕ → ℂ) (center St Su : ℝ) (q : LiteralTuple) :
    (∫ t : ℝ, ∫ u : ℝ, sincTupleIntegrand β g center St Su q t u) =
      sincWeightedTupleTerm β g St center Su q := by
  simp_rw [integral_sincTupleIntegrand_u]
  rw [show (fun t : ℝ ↦
      (eta ((t - center) / St) : ℂ) * tupleCoefficient β g q *
        Complex.exp (↑(t * jointFrequency q) * Complex.I) *
          scaledEtaAngularMoment Su 0 (shortFrequency q)) =
    fun t : ℝ ↦ tupleCoefficient β g q *
      ((eta ((t - center) / St) : ℂ) *
        Complex.exp (↑(t * jointFrequency q) * Complex.I)) *
      scaledEtaAngularMoment Su 0 (shortFrequency q) by
        funext t
        ring]
  rw [integral_mul_const, integral_const_mul]
  rw [scaledEtaAngularMoment_eq_comm]
  rfl

/-- Unconditional finite Fubini weld from the whole-line product of the two
paper kernels to the literal dyadic tuple model. -/
theorem wholeLineSincMixedMean_eq_model
    (M N : ℕ) (β g : ℕ → ℂ)
    {St Su : ℝ} (hSt : St ≠ 0) (hSu : Su ≠ 0) (center : ℝ) :
    wholeLineSincMixedMean M N β g center St Su =
      sincWeightedTupleModel M N β g St center Su := by
  unfold wholeLineSincMixedMean sincWeightedTupleModel
  have hpoint (t u : ℝ) :
      (eta ((t - center) / St) : ℂ) * energy (longFactor N g t) *
          ((eta (u / Su) : ℂ) * energy (shortFactor M β (t + u))) =
        ∑ q ∈ dyadicTupleBox M N,
          sincTupleIntegrand β g center St Su q t u := by
    calc
      _ = ((eta ((t - center) / St) : ℂ) * (eta (u / Su) : ℂ)) *
          (energy (longFactor N g t) * energy (shortFactor M β (t + u))) := by
            ring
      _ = ((eta ((t - center) / St) : ℂ) * (eta (u / Su) : ℂ)) *
          ∑ q ∈ dyadicTupleBox M N, tupleTerm β g q t u := by
            rw [mixed_integrand_expansion]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        unfold sincTupleIntegrand
        ring
  calc
    (∫ t : ℝ,
        (eta ((t - center) / St) : ℂ) * energy (longFactor N g t) *
          ∫ u : ℝ, (eta (u / Su) : ℂ) *
            energy (shortFactor M β (t + u))) =
      ∫ t : ℝ, ∫ u : ℝ,
        ∑ q ∈ dyadicTupleBox M N,
          sincTupleIntegrand β g center St Su q t u := by
            apply integral_congr_ae
            filter_upwards with t
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with u
            exact hpoint t u
    _ = ∫ t : ℝ,
        ∑ q ∈ dyadicTupleBox M N,
          ∫ u : ℝ, sincTupleIntegrand β g center St Su q t u := by
            apply integral_congr_ae
            filter_upwards with t
            rw [integral_finsetSum]
            intro q hq
            exact integrable_sincTupleIntegrand_u β g center St hSu q t
    _ = ∑ q ∈ dyadicTupleBox M N,
        ∫ t : ℝ, ∫ u : ℝ,
          sincTupleIntegrand β g center St Su q t u := by
            rw [integral_finsetSum]
            intro q hq
            exact integrable_integral_sincTupleIntegrand_u β g hSt center q
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      exact iteratedIntegral_sincTupleIntegrand β g center St Su q

/-! ## Explicit supported tuple formula -/

/-- A tuple term after both scaling laws have been evaluated.  The positive
phase is the translated `t`-center phase from the manuscript. -/
def explicitSincTupleTerm (β g : ℕ → ℂ) (center St Su : ℝ)
    (q : LiteralTuple) : ℂ :=
  tupleCoefficient β g q *
    ((St : ℂ) *
      Complex.exp ((((jointFrequency q * center : ℝ) : ℂ) * Complex.I)) *
      triangularProfile (-(St * jointFrequency q) / (2 * Real.pi))) *
    ((Su : ℂ) *
      triangularProfile (-(Su * shortFrequency q) / (2 * Real.pi)))

theorem sincWeightedTupleTerm_eq_explicit
    (β g : ℕ → ℂ) {St Su : ℝ} (hSt : 0 < St) (hSu : 0 < Su)
    (center : ℝ) (q : LiteralTuple) :
    sincWeightedTupleTerm β g St center Su q =
      explicitSincTupleTerm β g center St Su q := by
  unfold sincWeightedTupleTerm explicitSincTupleTerm
  rw [scaledEtaAngularMoment_eq hSt,
    scaledEtaAngularMoment_eq hSu]
  rw [etaAngularMoment_eq_fourier, etaAngularMoment_eq_fourier]
  rw [fourier_eta_eq_triangularProfile]
  simp

/-- Exact supported finite expansion, including the `T`, `U`, Fourier
normalization, and translated center phase. -/
theorem wholeLineSincMixedMean_eq_checked_explicit
    (M N : ℕ) (β g : ℕ → ℂ) (center : ℝ)
    {St Su : ℝ} (hSt : 0 < St) (hSu : 0 < Su) :
    wholeLineSincMixedMean M N β g center St Su =
      ∑ q ∈ frequencyTuples M N
          (Real.pi / (2 * Su)) (Real.pi / (2 * St)),
        explicitSincTupleTerm β g center St Su q := by
  rw [wholeLineSincMixedMean_eq_model M N β g hSt.ne' hSu.ne' center]
  rw [sincWeightedTupleModel_eq_checked M N β g hSt hSu center]
  unfold checkedSincTupleModel
  apply Finset.sum_congr rfl
  intro q hq
  exact sincWeightedTupleTerm_eq_explicit β g hSt hSu center q

/-! ## Triangle and profile-norm bridge -/

/-- The compact Fourier profile is a real nonnegative number of size at most
`4`.  This is proved from its definition rather than imposed as a weight-side
assumption. -/
theorem norm_triangularProfile_le_four (xi : ℝ) :
    ‖triangularProfile xi‖ ≤ 4 := by
  have hnonneg : 0 ≤ 4 * max (1 - 4 * |xi|) 0 :=
    mul_nonneg (by norm_num) (le_max_right _ _)
  have hmax : max (1 - 4 * |xi|) 0 ≤ 1 := by
    apply max_le
    · linarith [abs_nonneg xi]
    · norm_num
  unfold triangularProfile
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  nlinarith

/-- The positive tuple mass left after both sinc-square cutoffs. -/
def positiveSincSurvivorMass
    (M N : ℕ) (β g : ℕ → ℂ) (St Su : ℝ) : ℝ :=
  weightedMass (fun q ↦ ‖tupleCoefficient β g q‖)
    (frequencyTuples M N
      (Real.pi / (2 * Su)) (Real.pi / (2 * St)))

/-- Each explicit survivor has norm at most `16*T*U` times the norm of its
coefficient.  The translated center phase disappears here because it has
norm exactly one. -/
theorem norm_explicitSincTupleTerm_le
    (β g : ℕ → ℂ) (center : ℝ) {St Su : ℝ}
    (hSt : 0 < St) (hSu : 0 < Su) (q : LiteralTuple) :
    ‖explicitSincTupleTerm β g center St Su q‖ ≤
      16 * St * Su * ‖tupleCoefficient β g q‖ := by
  have htriT := norm_triangularProfile_le_four
    (-(St * jointFrequency q) / (2 * Real.pi))
  have htriU := norm_triangularProfile_le_four
    (-(Su * shortFrequency q) / (2 * Real.pi))
  have hTnonneg : 0 ≤ St := hSt.le
  have hUnonneg : 0 ≤ Su := hSu.le
  unfold explicitSincTupleTerm
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hSt, abs_of_pos hSu, Complex.norm_exp_ofReal_mul_I]
  have hleft :
      St * 1 * ‖triangularProfile
          (-(St * jointFrequency q) / (2 * Real.pi))‖ ≤ St * 4 := by
    nlinarith
  have hright :
      Su * ‖triangularProfile
          (-(Su * shortFrequency q) / (2 * Real.pi))‖ ≤ Su * 4 := by
    nlinarith
  calc
    ‖tupleCoefficient β g q‖ *
          (St * 1 * ‖triangularProfile
            (-(St * jointFrequency q) / (2 * Real.pi))‖) *
        (Su * ‖triangularProfile
            (-(Su * shortFrequency q) / (2 * Real.pi))‖) ≤
      ‖tupleCoefficient β g q‖ * (St * 4) * (Su * 4) := by
        gcongr
    _ = 16 * St * Su * ‖tupleCoefficient β g q‖ := by ring

/-- Exact complex expansion followed by the triangle inequality and the two
profile bounds.  The right side is a positive weighted tuple mass, with no
counting statement hidden in a premise. -/
theorem norm_wholeLineSincMixedMean_le_positiveSurvivorMass
    (M N : ℕ) (β g : ℕ → ℂ) (center : ℝ)
    {St Su : ℝ} (hSt : 0 < St) (hSu : 0 < Su) :
    ‖wholeLineSincMixedMean M N β g center St Su‖ ≤
      16 * St * Su * positiveSincSurvivorMass M N β g St Su := by
  let s := frequencyTuples M N
    (Real.pi / (2 * Su)) (Real.pi / (2 * St))
  rw [wholeLineSincMixedMean_eq_checked_explicit M N β g center hSt hSu]
  calc
    ‖∑ q ∈ s, explicitSincTupleTerm β g center St Su q‖ ≤
        ∑ q ∈ s, ‖explicitSincTupleTerm β g center St Su q‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ s, 16 * St * Su * ‖tupleCoefficient β g q‖ := by
      apply Finset.sum_le_sum
      intro q hq
      exact norm_explicitSincTupleTerm_le β g center hSt hSu q
    _ = 16 * St * Su * positiveSincSurvivorMass M N β g St Su := by
      simp only [positiveSincSurvivorMass, weightedMass, s]
      rw [Finset.mul_sum]

/-- Real/nonnegative form of the preceding complex triangle estimate. -/
theorem wholeLineSincMixedMeanReal_le_positiveSurvivorMass
    (M N : ℕ) (β g : ℕ → ℂ) (center : ℝ)
    {St Su : ℝ} (hSt : 0 < St) (hSu : 0 < Su) :
    wholeLineSincMixedMeanReal M N β g center St Su ≤
      16 * St * Su * positiveSincSurvivorMass M N β g St Su := by
  have h := norm_wholeLineSincMixedMean_le_positiveSurvivorMass
    M N β g center hSt hSu
  rw [wholeLineSincMixedMean_eq_ofReal] at h
  simpa [Real.norm_eq_abs,
    abs_of_nonneg (wholeLineSincMixedMeanReal_nonneg M N β g center St Su)] using h

/-! ## The literal factor-16 majorant -/

theorem continuous_sq_norm_shortFactor
    (M : ℕ) (β : ℕ → ℂ) (t : ℝ) :
    Continuous (fun u : ℝ ↦ ‖shortFactor M β (t + u)‖ ^ 2) := by
  unfold shortFactor dirichletPoly mellinPhase
  fun_prop

theorem continuous_sq_norm_longFactor
    (N : ℕ) (g : ℕ → ℂ) :
    Continuous (fun t : ℝ ↦ ‖longFactor N g t‖ ^ 2) := by
  unfold longFactor dirichletPoly mellinPhase
  fun_prop

/-- Uniform elementary `L¹` bound for every finite Dirichlet polynomial. -/
theorem norm_dirichletPoly_le
    (s : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖dirichletPoly s a t‖ ≤ ∑ n ∈ s, ‖a n‖ := by
  unfold dirichletPoly
  calc
    ‖∑ n ∈ s, a n * mellinPhase n t‖ ≤
        ∑ n ∈ s, ‖a n * mellinPhase n t‖ := norm_sum_le _ _
    _ = ∑ n ∈ s, ‖a n‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul]
      have hphase : ‖mellinPhase n t‖ = 1 := by
        unfold mellinPhase
        simpa using Complex.norm_exp_ofReal_mul_I
          (-(t * Real.log (n : ℝ)))
      rw [hphase, mul_one]

def shortCoeffL1 (M : ℕ) (β : ℕ → ℂ) : ℝ :=
  ∑ m ∈ dyadic M, ‖β m‖

def longCoeffL1 (N : ℕ) (g : ℕ → ℂ) : ℝ :=
  ∑ n ∈ dyadic N, ‖g n‖

theorem sq_norm_shortFactor_le
    (M : ℕ) (β : ℕ → ℂ) (t : ℝ) :
    ‖shortFactor M β t‖ ^ 2 ≤ shortCoeffL1 M β ^ 2 := by
  exact (sq_le_sq₀ (norm_nonneg _)
    (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)).2
      (norm_dirichletPoly_le _ _ _)

theorem sq_norm_longFactor_le
    (N : ℕ) (g : ℕ → ℂ) (t : ℝ) :
    ‖longFactor N g t‖ ^ 2 ≤ longCoeffL1 N g ^ 2 := by
  exact (sq_le_sq₀ (norm_nonneg _)
    (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)).2
      (norm_dirichletPoly_le _ _ _)

theorem integrable_weighted_short_energy
    (M : ℕ) (β : ℕ → ℂ) (t : ℝ)
    {Su : ℝ} (hSu : Su ≠ 0) :
    Integrable (fun u : ℝ ↦
      eta (u / Su) * ‖shortFactor M β (t + u)‖ ^ 2) := by
  have heta : Integrable (fun u : ℝ ↦ eta (u / Su)) := by
    simpa using eta_scaled_integrable hSu 0
  apply heta.mul_bdd
  · exact (continuous_sq_norm_shortFactor M β t).aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_norm_shortFactor_le M β (t + u)

theorem inner_whole_nonneg
    (M : ℕ) (β : ℕ → ℂ) (t Su : ℝ) :
    0 ≤ ∫ u : ℝ, eta (u / Su) * ‖shortFactor M β (t + u)‖ ^ 2 :=
  integral_nonneg (fun u ↦ mul_nonneg (eta_nonneg _) (sq_nonneg _))

theorem inner_compact_le_four_mul_whole
    (M : ℕ) (β : ℕ → ℂ) (t : ℝ)
    {U : ℝ} (hU : 0 < U) :
    (∫ u in (-2 * U)..(2 * U), ‖shortFactor M β (t + u)‖ ^ 2) ≤
      4 * ∫ u : ℝ, eta (u / U) * ‖shortFactor M β (t + u)‖ ^ 2 := by
  let f : ℝ → ℝ := fun u ↦ ‖shortFactor M β (t + u)‖ ^ 2
  let w : ℝ → ℝ := fun u ↦ eta (u / U) * f u
  have hbounds : -2 * U ≤ 2 * U := by linarith
  have hfint : IntervalIntegrable f volume (-2 * U) (2 * U) :=
    (continuous_sq_norm_shortFactor M β t).intervalIntegrable _ _
  have hwint : Integrable w := integrable_weighted_short_energy M β t hU.ne'
  have hmajor : ∀ u ∈ Set.Icc (-2 * U) (2 * U), f u ≤ 4 * w u := by
    intro u hu
    have habs : |u / U| ≤ 2 := by
      rw [abs_div, abs_of_pos hU]
      apply (div_le_iff₀ hU).2
      rw [abs_le]
      constructor <;> linarith [hu.1, hu.2]
    have heta := one_le_four_mul_eta_of_abs_le_two habs
    dsimp [f, w]
    nlinarith [sq_nonneg ‖shortFactor M β (t + u)‖]
  calc
    (∫ u in (-2 * U)..(2 * U), f u) ≤
        ∫ u in (-2 * U)..(2 * U), 4 * w u := by
          apply intervalIntegral.integral_mono_on hbounds hfint
            (hwint.const_mul 4).intervalIntegrable
          exact hmajor
    _ = 4 * ∫ u in Set.Ioc (-2 * U) (2 * U), w u := by
          rw [intervalIntegral.integral_of_le hbounds, integral_const_mul]
    _ ≤ 4 * ∫ u : ℝ, w u := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact setIntegral_le_integral hwint
            (Filter.Eventually.of_forall fun u ↦
              mul_nonneg (eta_nonneg _) (sq_nonneg _))

theorem inner_weighted_continuous
    (M : ℕ) (β : ℕ → ℂ) {U : ℝ} (hU : U ≠ 0) :
    Continuous (fun t : ℝ ↦
      ∫ u : ℝ, eta (u / U) * ‖shortFactor M β (t + u)‖ ^ 2) := by
  have hcomplex :
      (fun t : ℝ ↦
        ((∫ u : ℝ, eta (u / U) * ‖shortFactor M β (t + u)‖ ^ 2 : ℝ) : ℂ)) =
      fun t : ℝ ↦
        ∑ m ∈ (dyadic M).product (dyadic M),
          (β m.1 * star (β m.2)) *
            Complex.exp
              ((((t * (Real.log m.2 - Real.log m.1) : ℝ) : ℂ) * Complex.I)) *
            scaledEtaAngularMoment U 0 (Real.log m.2 - Real.log m.1) := by
    funext t
    rw [← integral_complex_ofReal]
    simp_rw [Complex.ofReal_mul, ← energy_eq_sq_norm]
    unfold shortFactor
    simp_rw [energy_dirichletPoly_expansion]
    rw [show (fun x : ℝ ↦
        (eta (x / U) : ℂ) *
          ∑ i ∈ dyadic M, ∑ j ∈ dyadic M, pairTerm β i j (t + x)) =
      fun x : ℝ ↦ (eta (x / U) : ℂ) *
        ∑ m ∈ (dyadic M).product (dyadic M),
          pairTerm β m.1 m.2 (t + x) by
            funext x
            congr 1
            exact (Finset.sum_product (dyadic M) (dyadic M)
              (fun m : ℕ × ℕ ↦ pairTerm β m.1 m.2 (t + x))).symm]
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro m hm
      simp_rw [pairTerm_frequency_form]
      have hsplit (u : ℝ) :
          Complex.exp
              (((((t + u) * (Real.log m.2 - Real.log m.1) : ℝ) : ℂ) * Complex.I)) =
            Complex.exp
                ((((t * (Real.log m.2 - Real.log m.1) : ℝ) : ℂ) * Complex.I)) *
              Complex.exp
                ((((u * (Real.log m.2 - Real.log m.1) : ℝ) : ℂ) * Complex.I)) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      simp_rw [hsplit]
      rw [show (fun u : ℝ ↦
          (eta (u / U) : ℂ) *
            ((β m.1 * star (β m.2)) *
              (Complex.exp (↑(t * (Real.log m.2 - Real.log m.1)) * Complex.I) *
                Complex.exp (↑(u * (Real.log m.2 - Real.log m.1)) * Complex.I)))) =
        fun u : ℝ ↦
          ((β m.1 * star (β m.2)) *
            Complex.exp (↑(t * (Real.log m.2 - Real.log m.1)) * Complex.I)) *
          ((eta (u / U) : ℂ) *
            Complex.exp (↑(u * (Real.log m.2 - Real.log m.1)) * Complex.I)) by
              funext u
              ring]
      rw [integral_const_mul]
      have hmom :
          (∫ a : ℝ, (eta (a / U) : ℂ) *
            Complex.exp
              ((((a * (Real.log m.2 - Real.log m.1) : ℝ) : ℂ) * Complex.I))) =
            scaledEtaAngularMoment U 0 (Real.log m.2 - Real.log m.1) := by
        simpa only [sub_zero] using scaledEtaAngularMoment_eq_comm U 0
          (Real.log m.2 - Real.log m.1)
      rw [hmom]
      push_cast
      rfl
    · intro m hm
      have heta : Integrable (fun u : ℝ ↦ (eta (u / U) : ℂ)) :=
        by simpa using (eta_scaled_integrable hU 0).ofReal
      apply heta.mul_bdd (c := ‖β m.1 * star (β m.2)‖)
      · apply Continuous.aestronglyMeasurable
        rw [show (fun u : ℝ ↦ pairTerm β m.1 m.2 (t + u)) =
            fun u : ℝ ↦
              (β m.1 * star (β m.2)) *
                Complex.exp
                  (((((t + u) * (Real.log m.2 - Real.log m.1) : ℝ) : ℂ) *
                    Complex.I)) by
          funext u
          exact pairTerm_frequency_form β m.1 m.2 (t + u)]
        fun_prop
      · filter_upwards with u
        rw [pairTerm_frequency_form, norm_mul,
          Complex.norm_exp_ofReal_mul_I, mul_one]
  have hc : Continuous (fun t : ℝ ↦
      ∑ m ∈ (dyadic M).product (dyadic M),
        (β m.1 * star (β m.2)) *
          Complex.exp
            ((((t * (Real.log m.2 - Real.log m.1) : ℝ) : ℂ) * Complex.I)) *
          scaledEtaAngularMoment U 0 (Real.log m.2 - Real.log m.1)) := by
    fun_prop
  have hofReal : Continuous (fun t : ℝ ↦
      ((∫ u : ℝ, eta (u / U) * ‖shortFactor M β (t + u)‖ ^ 2 : ℝ) : ℂ)) := by
    rw [hcomplex]
    exact hc
  simpa using Complex.continuous_re.comp hofReal

/-- The compact short-energy integral varies continuously with the translated
`t` clock. -/
theorem inner_compact_continuous
    (M : ℕ) (β : ℕ → ℂ) (U : ℝ) :
    Continuous (fun t : ℝ ↦
      ∫ u in (-2 * U)..(2 * U), ‖shortFactor M β (t + u)‖ ^ 2) := by
  let base : ℝ → ℝ := fun x ↦ ‖shortFactor M β x‖ ^ 2
  let F : ℝ → ℝ := fun x ↦ ∫ y in (0 : ℝ)..x, base y
  have hbase : Continuous base := by
    dsimp [base]
    simpa [add_zero] using continuous_sq_norm_shortFactor M β 0
  have hF : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hbase.integral_hasStrictDerivAt 0 x).hasDerivAt.continuousAt
  have heq (t : ℝ) :
      (∫ u in (-2 * U)..(2 * U), ‖shortFactor M β (t + u)‖ ^ 2) =
        F (2 * U + t) - F (-2 * U + t) := by
    calc
      (∫ u in (-2 * U)..(2 * U), ‖shortFactor M β (t + u)‖ ^ 2) =
          ∫ u in (-2 * U)..(2 * U), base (u + t) := by
            apply intervalIntegral.integral_congr
            intro u hu
            dsimp [base]
            rw [add_comm]
      _ = ∫ x in (-2 * U + t)..(2 * U + t), base x := by
            exact intervalIntegral.integral_comp_add_right base t
      _ = F (2 * U + t) - F (-2 * U + t) := by
            have hadd := intervalIntegral.integral_add_adjacent_intervals
              (hbase.intervalIntegrable (μ := volume) 0 (-2 * U + t))
              (hbase.intervalIntegrable (μ := volume)
                (-2 * U + t) (2 * U + t))
            dsimp [F]
            linarith
  rw [show (fun t : ℝ ↦
      ∫ u in (-2 * U)..(2 * U), ‖shortFactor M β (t + u)‖ ^ 2) =
    fun t : ℝ ↦ F (2 * U + t) - F (-2 * U + t) by
      funext t
      exact heq t]
  fun_prop

theorem integrable_weighted_outer
    (M N : ℕ) (β g : ℕ → ℂ) (center : ℝ)
    {T U : ℝ} (hT : T ≠ 0) (hU : U ≠ 0) :
    Integrable (fun t : ℝ ↦
      eta ((t - center) / T) * ‖longFactor N g t‖ ^ 2 *
        (∫ u : ℝ, eta (u / U) * ‖shortFactor M β (t + u)‖ ^ 2)) := by
  rw [show (fun t : ℝ ↦
      eta ((t - center) / T) * ‖longFactor N g t‖ ^ 2 *
        (∫ u : ℝ, eta (u / U) * ‖shortFactor M β (t + u)‖ ^ 2)) =
    fun t : ℝ ↦ eta ((t - center) / T) *
      (‖longFactor N g t‖ ^ 2 *
        (∫ u : ℝ, eta (u / U) * ‖shortFactor M β (t + u)‖ ^ 2)) by
          funext t
          ring]
  apply (eta_scaled_integrable hT center).mul_bdd
  · apply Continuous.aestronglyMeasurable
    exact (continuous_sq_norm_longFactor N g).mul
      (inner_weighted_continuous M β hU)
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · apply mul_le_mul
        (sq_norm_longFactor_le N g t)
        (show (∫ u : ℝ,
            eta (u / U) * ‖shortFactor M β (t + u)‖ ^ 2) ≤
          ∫ u : ℝ, eta (u / U) * shortCoeffL1 M β ^ 2 by
            apply integral_mono
            · exact integrable_weighted_short_energy M β t hU
            · simpa using (eta_scaled_integrable hU 0).mul_const
                (shortCoeffL1 M β ^ 2)
            · intro u
              exact mul_le_mul_of_nonneg_left
                (sq_norm_shortFactor_le M β (t + u)) (eta_nonneg _))
        (inner_whole_nonneg M β t U) (sq_nonneg _)
    · exact mul_nonneg (sq_nonneg _) (inner_whole_nonneg M β t U)

/-- The manuscript rectangle is bounded by the fixed factor `16` times its
whole-line product sinc-square majorant. -/
theorem literalMixedMeanReal_le_sixteen_mul_wholeLine
    (M N : ℕ) (β g : ℕ → ℂ) (t₀ : ℝ)
    {T U : ℝ} (hT : 0 < T) (hU : 0 < U) :
    literalMixedMeanReal M N β g t₀ T U ≤
      16 * wholeLineSincMixedMeanReal M N β g t₀ T U := by
  let innerCompact : ℝ → ℝ := fun t ↦
    ∫ u in (-2 * U)..(2 * U), ‖shortFactor M β (t + u)‖ ^ 2
  let innerWhole : ℝ → ℝ := fun t ↦
    ∫ u : ℝ, eta (u / U) * ‖shortFactor M β (t + u)‖ ^ 2
  let f : ℝ → ℝ := fun t ↦ ‖longFactor N g t‖ ^ 2 * innerWhole t
  let w : ℝ → ℝ := fun t ↦ eta ((t - t₀) / T) * f t
  have htBounds : t₀ - T / 2 ≤ t₀ + T / 2 := by linarith
  have hinner (t : ℝ) : innerCompact t ≤ 4 * innerWhole t :=
    inner_compact_le_four_mul_whole M β t hU
  have hfirst : literalMixedMeanReal M N β g t₀ T U ≤
      4 * ∫ t in (t₀ - T / 2)..(t₀ + T / 2), f t := by
    unfold literalMixedMeanReal
    calc
      (∫ t in (t₀ - T / 2)..(t₀ + T / 2),
          ‖longFactor N g t‖ ^ 2 * innerCompact t) ≤
        ∫ t in (t₀ - T / 2)..(t₀ + T / 2), 4 * f t := by
          apply intervalIntegral.integral_mono_on htBounds
          · exact ((continuous_sq_norm_longFactor N g).mul
              (inner_compact_continuous M β U)).intervalIntegrable _ _
          · exact (Continuous.const_mul
              ((continuous_sq_norm_longFactor N g).mul
                (inner_weighted_continuous M β hU.ne')) 4).intervalIntegrable _ _
          · intro t ht
            dsimp [innerCompact, innerWhole, f]
            nlinarith [sq_nonneg ‖longFactor N g t‖, hinner t]
      _ = 4 * ∫ t in (t₀ - T / 2)..(t₀ + T / 2), f t := by
        rw [intervalIntegral.integral_const_mul]
  have hfint : IntervalIntegrable f volume (t₀ - T / 2) (t₀ + T / 2) := by
    simpa [f, innerWhole] using
      (((continuous_sq_norm_longFactor N g).mul
        (inner_weighted_continuous M β hU.ne')).intervalIntegrable
          (t₀ - T / 2) (t₀ + T / 2))
  have hwint : Integrable w :=
    by simpa [w, f, innerWhole, mul_assoc] using
      integrable_weighted_outer M N β g t₀ hT.ne' hU.ne'
  have htmajor : ∀ t ∈ Set.Icc (t₀ - T / 2) (t₀ + T / 2),
      f t ≤ 4 * w t := by
    intro t ht
    have habs : |(t - t₀) / T| ≤ 2 := by
      rw [abs_div, abs_of_pos hT]
      apply (div_le_iff₀ hT).2
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have heta := one_le_four_mul_eta_of_abs_le_two habs
    have hfnonneg : 0 ≤ f t :=
      mul_nonneg (sq_nonneg _) (inner_whole_nonneg M β t U)
    dsimp [w]
    nlinarith
  have hsecond : (∫ t in (t₀ - T / 2)..(t₀ + T / 2), f t) ≤
      4 * ∫ t : ℝ, w t := by
    calc
      (∫ t in (t₀ - T / 2)..(t₀ + T / 2), f t) ≤
          ∫ t in (t₀ - T / 2)..(t₀ + T / 2), 4 * w t := by
            apply intervalIntegral.integral_mono_on htBounds hfint
              (hwint.const_mul 4).intervalIntegrable
            exact htmajor
      _ = 4 * ∫ t in Set.Ioc (t₀ - T / 2) (t₀ + T / 2), w t := by
            rw [intervalIntegral.integral_of_le htBounds, integral_const_mul]
      _ ≤ 4 * ∫ t : ℝ, w t := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact setIntegral_le_integral hwint
              (Filter.Eventually.of_forall fun t ↦
                mul_nonneg (eta_nonneg _)
                  (mul_nonneg (sq_nonneg _) (inner_whole_nonneg M β t U)))
  have hfinal : literalMixedMeanReal M N β g t₀ T U ≤
      16 * ∫ t : ℝ, w t := by
    nlinarith
  simpa [wholeLineSincMixedMeanReal, w, f, innerWhole, mul_assoc] using hfinal

/-- User-facing complex-to-real formulation of the proved analytic
majorization. -/
theorem literalMixedMean_re_le_sixteen_mul_wholeLine
    (M N : ℕ) (β g : ℕ → ℂ) (t₀ : ℝ)
    {T U : ℝ} (hT : 0 < T) (hU : 0 < U) :
    (literalMixedMean M N β g t₀ T U).re ≤
      16 * wholeLineSincMixedMeanReal M N β g t₀ T U := by
  rw [literalMixedMean_re_eq]
  exact literalMixedMeanReal_le_sixteen_mul_wholeLine
    M N β g t₀ hT hU

/-- The complete harmonic bridge: the literal compact rectangle is bounded
by an explicit positive mass on the exact two-frequency survivor set.  The
factor is `16` from the rectangle majorant times `4*4` from the two triangular
profiles. -/
theorem literalMixedMeanReal_le_positiveSurvivorMass
    (M N : ℕ) (β g : ℕ → ℂ) (t₀ : ℝ)
    {T U : ℝ} (hT : 0 < T) (hU : 0 < U) :
    literalMixedMeanReal M N β g t₀ T U ≤
      256 * T * U * positiveSincSurvivorMass M N β g T U := by
  calc
    literalMixedMeanReal M N β g t₀ T U ≤
        16 * wholeLineSincMixedMeanReal M N β g t₀ T U :=
      literalMixedMeanReal_le_sixteen_mul_wholeLine M N β g t₀ hT hU
    _ ≤ 16 * (16 * T * U * positiveSincSurvivorMass M N β g T U) := by
      exact mul_le_mul_of_nonneg_left
        (wholeLineSincMixedMeanReal_le_positiveSurvivorMass
          M N β g t₀ hT hU) (by norm_num)
    _ = 256 * T * U * positiveSincSurvivorMass M N β g T U := by ring

theorem literalMixedMean_re_le_positiveSurvivorMass
    (M N : ℕ) (β g : ℕ → ℂ) (t₀ : ℝ)
    {T U : ℝ} (hT : 0 < T) (hU : 0 < U) :
    (literalMixedMean M N β g t₀ T U).re ≤
      256 * T * U * positiveSincSurvivorMass M N β g T U := by
  rw [literalMixedMean_re_eq]
  exact literalMixedMeanReal_le_positiveSurvivorMass M N β g t₀ hT hU

/-! ## Paper-facing square-root normalization -/

/-- The coefficient supplied to the Lean Dirichlet polynomial when the
manuscript writes `a(n) n^{-1/2-it}`. -/
def invSqrtCoeff (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a n / (Real.sqrt n : ℂ)

def paperLiteralMixedMean (M N : ℕ) (βraw graw : ℕ → ℂ)
    (t₀ T U : ℝ) : ℂ :=
  literalMixedMean M N (invSqrtCoeff βraw) (invSqrtCoeff graw) t₀ T U

def paperWholeLineSincMixedMean (M N : ℕ) (βraw graw : ℕ → ℂ)
    (center St Su : ℝ) : ℂ :=
  wholeLineSincMixedMean M N (invSqrtCoeff βraw) (invSqrtCoeff graw)
    center St Su

theorem paperLiteralMixedMean_re_le_sixteen_mul_wholeLine
    (M N : ℕ) (βraw graw : ℕ → ℂ) (t₀ : ℝ)
    {T U : ℝ} (hT : 0 < T) (hU : 0 < U) :
    (paperLiteralMixedMean M N βraw graw t₀ T U).re ≤
      16 * wholeLineSincMixedMeanReal M N
        (invSqrtCoeff βraw) (invSqrtCoeff graw) t₀ T U := by
  exact literalMixedMean_re_le_sixteen_mul_wholeLine
    M N (invSqrtCoeff βraw) (invSqrtCoeff graw) t₀ hT hU

theorem paperWholeLineSincMixedMean_eq_checked_explicit
    (M N : ℕ) (βraw graw : ℕ → ℂ) (center : ℝ)
    {St Su : ℝ} (hSt : 0 < St) (hSu : 0 < Su) :
    paperWholeLineSincMixedMean M N βraw graw center St Su =
      ∑ q ∈ frequencyTuples M N
          (Real.pi / (2 * Su)) (Real.pi / (2 * St)),
        explicitSincTupleTerm (invSqrtCoeff βraw) (invSqrtCoeff graw)
          center St Su q := by
  exact wholeLineSincMixedMean_eq_checked_explicit M N
    (invSqrtCoeff βraw) (invSqrtCoeff graw) center hSt hSu

theorem norm_invSqrtCoeff_le_on_dyadic
    {X n : ℕ} {a : ℕ → ℂ} {A : ℝ}
    (hn : n ∈ dyadic X) (hA : 0 ≤ A) (ha : ‖a n‖ ≤ A) :
    ‖invSqrtCoeff a n‖ ≤ A / Real.sqrt X := by
  have hX : 0 < X := by
    simp only [dyadic, Finset.mem_Ioc] at hn
    omega
  have hnX : X ≤ n := by
    simp only [dyadic, Finset.mem_Ioc] at hn
    omega
  have hsqrtX : 0 < Real.sqrt X :=
    Real.sqrt_pos.2 (by exact_mod_cast hX)
  have hsqrt : Real.sqrt X ≤ Real.sqrt n :=
    Real.sqrt_le_sqrt (by exact_mod_cast hnX)
  unfold invSqrtCoeff
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_div₀ hA ha hsqrtX hsqrt

/-- The four paper coefficients contribute exactly the advertised dyadic
`(MN)⁻¹` scale, before any divisor or logarithmic estimate. -/
theorem norm_paper_tupleCoefficient_le
    {M N : ℕ} {βraw graw : ℕ → ℂ} {B G : ℝ}
    (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hβ : ∀ m ∈ dyadic M, ‖βraw m‖ ≤ B)
    (hg : ∀ n ∈ dyadic N, ‖graw n‖ ≤ G)
    {q : LiteralTuple} (hq : q ∈ dyadicTupleBox M N) :
    ‖tupleCoefficient (invSqrtCoeff βraw) (invSqrtCoeff graw) q‖ ≤
      B ^ 2 * G ^ 2 / ((M : ℝ) * (N : ℝ)) := by
  rcases q with ⟨⟨m₁, m₂⟩, ⟨n₁, n₂⟩⟩
  simp [dyadicTupleBox] at hq
  rcases hq with ⟨⟨hm₁, hm₂⟩, hn₁, hn₂⟩
  have hM : 0 < M := by
    simp only [dyadic, Finset.mem_Ioc] at hm₁
    omega
  have hN : 0 < N := by
    simp only [dyadic, Finset.mem_Ioc] at hn₁
    omega
  have hMr : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hb₁ := norm_invSqrtCoeff_le_on_dyadic hm₁ hB (hβ m₁ hm₁)
  have hb₂ := norm_invSqrtCoeff_le_on_dyadic hm₂ hB (hβ m₂ hm₂)
  have hg₁ := norm_invSqrtCoeff_le_on_dyadic hn₁ hG (hg n₁ hn₁)
  have hg₂ := norm_invSqrtCoeff_le_on_dyadic hn₂ hG (hg n₂ hn₂)
  have hbs : 0 ≤ B / Real.sqrt M := div_nonneg hB (Real.sqrt_nonneg _)
  have hgs : 0 ≤ G / Real.sqrt N := div_nonneg hG (Real.sqrt_nonneg _)
  have hbprod :
      ‖invSqrtCoeff βraw m₁‖ * ‖invSqrtCoeff βraw m₂‖ ≤
        (B / Real.sqrt M) * (B / Real.sqrt M) :=
    mul_le_mul hb₁ hb₂ (norm_nonneg _) hbs
  have hgprod :
      ‖invSqrtCoeff graw n₁‖ * ‖invSqrtCoeff graw n₂‖ ≤
        (G / Real.sqrt N) * (G / Real.sqrt N) :=
    mul_le_mul hg₁ hg₂ (norm_nonneg _) hgs
  have hprod :
      (‖invSqrtCoeff graw n₁‖ * ‖invSqrtCoeff graw n₂‖) *
          (‖invSqrtCoeff βraw m₁‖ * ‖invSqrtCoeff βraw m₂‖) ≤
        ((G / Real.sqrt N) * (G / Real.sqrt N)) *
          ((B / Real.sqrt M) * (B / Real.sqrt M)) :=
    mul_le_mul hgprod hbprod
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_nonneg hgs hgs)
  have hsM : Real.sqrt (M : ℝ) ^ 2 = (M : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsN : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt (by positivity)
  calc
    ‖tupleCoefficient (invSqrtCoeff βraw) (invSqrtCoeff graw)
        ((m₁, m₂), (n₁, n₂))‖ =
      (‖invSqrtCoeff graw n₁‖ * ‖invSqrtCoeff graw n₂‖) *
        (‖invSqrtCoeff βraw m₁‖ * ‖invSqrtCoeff βraw m₂‖) := by
          simp [tupleCoefficient, norm_mul]
    _ ≤ ((G / Real.sqrt N) * (G / Real.sqrt N)) *
          ((B / Real.sqrt M) * (B / Real.sqrt M)) := hprod
    _ = B ^ 2 * G ^ 2 / ((M : ℝ) * (N : ℝ)) := by
      have hsMne : Real.sqrt (M : ℝ) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 hMr)
      have hsNne : Real.sqrt (N : ℝ) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 hNr)
      field_simp [hsMne, hsNne]
      rw [hsM, hsN]
      ring

/-! ## Paper coefficient envelope and exact sector split -/

/-- The nonnegative arithmetic weight that remains after extracting the four
square-root denominators and the common logarithmic factor. -/
def tauTupleWeight (k : ℕ) (q : LiteralTuple) : ℝ :=
  (tauAF k q.2.1 : ℝ) * (tauAF k q.2.2 : ℝ)

/-- The exact Fourier-survivor mass appearing in (2.2), before replacing the
logarithmic bands by arithmetic collars. -/
def paperTauSurvivorMass
    (k M N : ℕ) (T U : ℝ) : ℝ :=
  weightedMass (tauTupleWeight k)
    (frequencyTuples M N
      (Real.pi / (2 * U)) (Real.pi / (2 * T)))

/-- The local paper normalization agrees definitionally with the separately
certified normalized-coefficient wrapper. -/
theorem invSqrtCoeff_eq_sqrtNormalizedCoeff (a : ℕ → ℂ) :
    invSqrtCoeff a = MAPNormalizedWrapper.sqrtNormalizedCoeff a := by
  funext n
  rfl

/-- Literal pointwise manuscript coefficient bound on every exact survivor.
No tuple count or mixed-mean estimate is assumed. -/
theorem norm_paper_tupleCoefficient_le_tau_commonLog
    {M N a k : ℕ} {βraw graw : ℕ → ℂ} {q : LiteralTuple}
    (hM : 2 ≤ M) (hN : 2 ≤ N)
    (hq : q ∈ dyadicTupleBox M N)
    (hcoeff : MAPNormalizedWrapper.PaperCoefficientBounds
      M N a k βraw graw) :
    ‖tupleCoefficient (invSqrtCoeff βraw) (invSqrtCoeff graw) q‖ ≤
      tauTupleWeight k q *
          Real.log (2 * (M : ℝ) * (N : ℝ)) ^ (4 * a) /
        ((M : ℝ) * (N : ℝ)) := by
  simpa [tauTupleWeight, MAPNormalizedWrapper.paperTupleCoefficient,
    MAPNormalizedWrapper.sqrtNormalizedCoeff, invSqrtCoeff] using
    (MAPNormalizedWrapper.norm_paperTupleCoefficient_le_commonLog_div
      (M := M) (N := N) (a := a) (k := k)
      (β := βraw) (g := graw) hM hN hq hcoeff)

/-- Sum the pointwise normalized coefficient envelope over the exact
survivors.  This is the maximal coefficient-side implication before any
determinant-sector counting. -/
theorem positiveSincSurvivorMass_paper_le_tau
    {M N a k : ℕ} {βraw graw : ℕ → ℂ}
    {T U : ℝ} (hM : 2 ≤ M) (hN : 2 ≤ N)
    (hcoeff : MAPNormalizedWrapper.PaperCoefficientBounds
      M N a k βraw graw) :
    positiveSincSurvivorMass M N
        (invSqrtCoeff βraw) (invSqrtCoeff graw) T U ≤
      (Real.log (2 * (M : ℝ) * (N : ℝ)) ^ (4 * a) /
        ((M : ℝ) * (N : ℝ))) *
        paperTauSurvivorMass k M N T U := by
  let s := frequencyTuples M N
    (Real.pi / (2 * U)) (Real.pi / (2 * T))
  unfold positiveSincSurvivorMass paperTauSurvivorMass weightedMass
  calc
    (∑ q ∈ s,
        ‖tupleCoefficient (invSqrtCoeff βraw) (invSqrtCoeff graw) q‖) ≤
      ∑ q ∈ s,
        tauTupleWeight k q *
            Real.log (2 * (M : ℝ) * (N : ℝ)) ^ (4 * a) /
          ((M : ℝ) * (N : ℝ)) := by
        apply Finset.sum_le_sum
        intro q hq
        exact norm_paper_tupleCoefficient_le_tau_commonLog hM hN
          (Finset.mem_filter.mp hq).1 hcoeff
    _ = (Real.log (2 * (M : ℝ) * (N : ℝ)) ^ (4 * a) /
          ((M : ℝ) * (N : ℝ))) *
        ∑ q ∈ s, tauTupleWeight k q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring

/-- The compact paper mean, reduced completely to the positive arithmetic
mass in (2.2), with every harmonic and coefficient constant explicit. -/
theorem paperLiteralMixedMean_re_le_tauSurvivorMass
    {M N a k : ℕ} {βraw graw : ℕ → ℂ} (t₀ : ℝ)
    {T U : ℝ} (hM : 2 ≤ M) (hN : 2 ≤ N)
    (hT : 0 < T) (hU : 0 < U)
    (hcoeff : MAPNormalizedWrapper.PaperCoefficientBounds
      M N a k βraw graw) :
    (paperLiteralMixedMean M N βraw graw t₀ T U).re ≤
      256 * T * U *
        (Real.log (2 * (M : ℝ) * (N : ℝ)) ^ (4 * a) /
          ((M : ℝ) * (N : ℝ))) *
        paperTauSurvivorMass k M N T U := by
  have hharm := literalMixedMean_re_le_positiveSurvivorMass
    M N (invSqrtCoeff βraw) (invSqrtCoeff graw) t₀ hT hU
  have hcoeffMass := positiveSincSurvivorMass_paper_le_tau
    (M := M) (N := N) (a := a) (k := k)
    (βraw := βraw) (graw := graw) (T := T) (U := U) hM hN hcoeff
  unfold paperLiteralMixedMean
  calc
    (literalMixedMean M N (invSqrtCoeff βraw) (invSqrtCoeff graw)
        t₀ T U).re ≤
      256 * T * U * positiveSincSurvivorMass M N
        (invSqrtCoeff βraw) (invSqrtCoeff graw) T U := hharm
    _ ≤ 256 * T * U *
        ((Real.log (2 * (M : ℝ) * (N : ℝ)) ^ (4 * a) /
          ((M : ℝ) * (N : ℝ))) *
          paperTauSurvivorMass k M N T U) := by
      exact mul_le_mul_of_nonneg_left hcoeffMass (by positivity)
    _ = _ := by ring

/-- Exact determinant-sector decomposition of the positive arithmetic mass.
This is an equality, not an assumed aggregate estimate. -/
theorem paperTauSurvivorMass_eq_sector_sum
    (k M N : ℕ) (T U : ℝ) :
    paperTauSurvivorMass k M N T U =
      weightedMass (tauTupleWeight k)
        (equalShortFrequencySector M N
          (Real.pi / (2 * U)) (Real.pi / (2 * T))) +
      weightedMass (tauTupleWeight k)
        (positiveFrequencySector M N
          (Real.pi / (2 * U)) (Real.pi / (2 * T))) +
      weightedMass (tauTupleWeight k)
        (negativeFrequencySector M N
          (Real.pi / (2 * U)) (Real.pi / (2 * T))) +
      weightedMass (tauTupleWeight k)
        (zeroFrequencySector M N
          (Real.pi / (2 * U)) (Real.pi / (2 * T))) := by
  exact weighted_frequency_sector_decomposition
    (tauTupleWeight k) M N
      (Real.pi / (2 * U)) (Real.pi / (2 * T))

/-! ## Exact surface of manuscript Lemma 2.1 -/

/-- The literal quantified content of manuscript Lemma 2.1.  Arbitrary
complex coefficients cover the advertised fixed character phases, since the
hypotheses constrain only their norms.  This proposition is deliberately not
postulated as an axiom. -/
def PaperMixedMeanLemma21 (c : ℝ) (a k : ℕ) : Prop :=
  0 < c → 1 ≤ k →
  ∃ C : ℝ, 0 < C ∧
    ∀ (M N : ℕ) (βraw graw : ℕ → ℂ) (t₀ T U : ℝ),
      2 ≤ M → 2 ≤ N →
      c * (M : ℝ) ^ 2 ≤ (N : ℝ) →
      1 ≤ T → 1 ≤ U →
      MAPNormalizedWrapper.PaperCoefficientBounds
        M N a k βraw graw →
      (paperLiteralMixedMean M N βraw graw t₀ T U).re ≤
        C * Real.log (2 * (M : ℝ) * (N : ℝ)) ^
            (4 * a + 2 * max 2 (k * k) + 2) *
          (U * T + U * (N : ℝ) + (M : ℝ) * (N : ℝ) + T)

end MixedMeanMajorantWeld
