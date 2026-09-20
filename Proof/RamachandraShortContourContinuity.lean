import RamachandraShortContourCauchy
import RamachandraFunctionalFactorEnvelope
import RamachandraLongContourContinuity

/-!
# Continuity of the literal short contour

The parameter-dependent full Mellin integral is handled by dominated
convergence.  The majorant is built from the certified global functional
factor envelope and the finite exact reflected-head bound.
-/

namespace RamachandraShortContourContinuity

open scoped BigOperators Interval
open Complex MeasureTheory Filter Topology
open RamachandraPrimitiveShiftedContourReduction
open RamachandraShortContourCauchy
open RamachandraShortHeadFamilyBudget
open RamachandraShortFunctionalFactorMomentEnvelope
open RamachandraShiftedContourSharpEnvelopes
open RamachandraGammaWeightIntegrability
open RamachandraFunctionalFactorEnvelope
open RamachandraLongContourContinuity
open RamachandraShiftedHeadFiniteContour
open BHPRamachandraMeanValueFromDyadicAFE

noncomputable section

set_option maxHeartbeats 1200000

variable {d : ℕ} [NeZero d]

/-- Joint continuity of the exact short-contour integrand in external and
Mellin ordinates. -/
theorem continuous_uncurry_shortContourIntegrand
    (psi : DirichletCharacter ℂ d) {X sigma : ℝ} (hX : 0 < X)
    (hcLo : -1 < -(Real.log X)⁻¹) (hcHi : -(Real.log X)⁻¹ < 0)
    (hrlo : -(1 / 4 : ℝ) ≤ sigma - (Real.log X)⁻¹)
    (hrhi : sigma - (Real.log X)⁻¹ ≤ 1 / 2) :
    Continuous (Function.uncurry (fun t v =>
      ramachandraShiftedContourIntegrand psi X sigma
        (-(Real.log X)⁻¹) t v false)) := by
  rw [continuous_iff_continuousAt]
  intro p
  let z : ℂ := shortFunctionalPoint X sigma p.1 p.2
  let w : ℂ := ((-(Real.log X)⁻¹ : ℝ) : ℂ) + (p.2 : ℂ) * I
  have hzinner : ContinuousAt (fun y : ℝ × ℝ =>
      shortFunctionalPoint X sigma y.1 y.2) p := by
    unfold shortFunctionalPoint ramachandraShiftedPoint
    fun_prop
  have hzre : z.re = sigma - (Real.log X)⁻¹ := by
    dsimp [z]
    exact shortFunctionalPoint_re X sigma p.1 p.2
  have hfacDiff := differentiableAt_ramachandraFunctionalFactor psi
    (z := z) (by rw [sub_re, one_re, hzre]; linarith)
  have hfac : ContinuousAt (fun y : ℝ × ℝ =>
      ramachandraFunctionalFactor psi
        (shortFunctionalPoint X sigma y.1 y.2)) p := by
    change ContinuousAt
      (ramachandraFunctionalFactor psi ∘
        (fun y : ℝ × ℝ => shortFunctionalPoint X sigma y.1 y.2)) p
    exact ContinuousAt.comp
      (f := fun y : ℝ × ℝ => shortFunctionalPoint X sigma y.1 y.2)
      (g := ramachandraFunctionalFactor psi)
      (by simpa [z] using hfacDiff.continuousAt) hzinner
  have hhead : ContinuousAt (fun y : ℝ × ℝ =>
      shortReflectedHead psi X sigma y.1 y.2) p := by
    have h := (continuous_uncurry_shortReflectedHead psi hX.le sigma).comp
      continuous_swap
    simpa only [Function.uncurry_apply_pair, Function.comp_apply,
      Prod.swap_prod_mk] using h.continuousAt
  have hwinner : ContinuousAt (fun y : ℝ × ℝ =>
      (((-(Real.log X)⁻¹ : ℝ) : ℂ) + (y.2 : ℂ) * I)) p := by fun_prop
  have hGammaDiff : DifferentiableAt ℂ Complex.Gamma w := by
    apply Complex.differentiableAt_Gamma
    intro n hn
    have hre : -(Real.log X)⁻¹ = -(n : ℝ) := by
      calc
        -(Real.log X)⁻¹ = w.re := by simp [w]
        _ = (-((n : ℂ))).re := congrArg Complex.re hn
        _ = -(n : ℝ) := by simp
    by_cases hn0 : n = 0
    · subst n
      have hzero : -(Real.log X)⁻¹ = 0 := by simpa using hre
      exact (ne_of_lt hcHi) hzero
    · have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn0)
      linarith
  have hGamma : ContinuousAt (fun y : ℝ × ℝ =>
      Complex.Gamma
        (((-(Real.log X)⁻¹ : ℝ) : ℂ) + (y.2 : ℂ) * I)) p := by
    change ContinuousAt (Complex.Gamma ∘ (fun y : ℝ × ℝ =>
      (((-(Real.log X)⁻¹ : ℝ) : ℂ) + (y.2 : ℂ) * I))) p
    exact ContinuousAt.comp
      (f := fun y : ℝ × ℝ =>
        (((-(Real.log X)⁻¹ : ℝ) : ℂ) + (y.2 : ℂ) * I))
      (g := Complex.Gamma) hGammaDiff.continuousAt hwinner
  have hcpowDiff : DifferentiableAt ℂ (fun a : ℂ => (X : ℂ) ^ a) w :=
    differentiableAt_id.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  have hcpow : ContinuousAt (fun y : ℝ × ℝ =>
      (X : ℂ) ^ (((-(Real.log X)⁻¹ : ℝ) : ℂ) + (y.2 : ℂ) * I)) p := by
    change ContinuousAt ((fun a : ℂ => (X : ℂ) ^ a) ∘ (fun y : ℝ × ℝ =>
      (((-(Real.log X)⁻¹ : ℝ) : ℂ) + (y.2 : ℂ) * I))) p
    exact ContinuousAt.comp
      (f := fun y : ℝ × ℝ =>
        (((-(Real.log X)⁻¹ : ℝ) : ℂ) + (y.2 : ℂ) * I))
      (g := fun a : ℂ => (X : ℂ) ^ a) hcpowDiff.continuousAt hwinner
  unfold Function.uncurry ramachandraShiftedContourIntegrand
  simp only [Bool.false_eq_true, ↓reduceIte]
  simpa [shortReflectedHead, shortFunctionalPoint, add_assoc] using
    (((hfac.pow 2).mul hhead).mul hGamma).mul hcpow

/-- A global integrable-weight majorant, uniform in the external ordinate
apart from a fixed sixth power. -/
theorem norm_shortContourIntegrand_le_global
    (psi : DirichletCharacter ℂ d)
    {X sigma t v Cgamma : ℝ} (hX : 6 ≤ X)
    (hstrip : |sigma - (1 / 2 : ℝ)| ≤ (100 * Real.log X)⁻¹)
    (hCgamma : 0 ≤ Cgamma)
    (hglobal : ∀ z : ℂ,
      -(1 / 4 : ℝ) ≤ z.re → z.re ≤ 1 / 2 →
      ‖ramachandraFunctionalFactor psi z‖ ≤
        Real.rpow (d : ℝ) (1 / 2 - z.re) *
          (Cgamma * (1 + |z.im|) ^ 3)) :
    ‖ramachandraShiftedContourIntegrand psi X sigma
        (-(Real.log X)⁻¹) t v false‖ ≤
      (Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 * (1 + |t|) ^ 6) *
        gammaPolynomialWeight (-(Real.log X)⁻¹) v *
          shortHeadUniformNormBound psi X sigma := by
  have hab := shortExponent_bounds hX hstrip
  let a : ℝ := (1 / 2 : ℝ) - (sigma - (Real.log X)⁻¹)
  change 0 ≤ a ∧ a ≤ 2 / Real.log X ∧ a ≤ 3 / 4 at hab
  have ha0 := hab.1
  have ha34 := hab.2.2
  have hrlo : -(1 / 4 : ℝ) ≤ sigma - (Real.log X)⁻¹ := by
    dsimp [a] at ha34
    linarith
  have hrhi : sigma - (Real.log X)⁻¹ ≤ 1 / 2 := by
    dsimp [a] at ha0
    linarith
  have hfac := hglobal (shortFunctionalPoint X sigma t v)
    (by simpa [shortFunctionalPoint_re] using hrlo)
    (by simpa [shortFunctionalPoint_re] using hrhi)
  rw [shortFunctionalPoint_re, shortFunctionalPoint_im] at hfac
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast NeZero.pos d
  have hdexp : 2 * a ≤ 3 / 2 := by linarith
  have hdpow : Real.rpow (d : ℝ) (2 * a) ≤
      Real.rpow (d : ℝ) (3 / 2) :=
    Real.rpow_le_rpow_of_exponent_le hd1 hdexp
  have hfac2 : ‖ramachandraFunctionalFactor psi
      (shortFunctionalPoint X sigma t v)‖ ^ 2 ≤
      Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
        (1 + |t + v|) ^ 6 := by
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) hfac 2
    have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
    have hdpowEq : (Real.rpow (d : ℝ) a) ^ 2 =
        Real.rpow (d : ℝ) (2 * a) := by
      calc
        (Real.rpow (d : ℝ) a) ^ 2 = Real.rpow (d : ℝ) (a * (2 : ℝ)) :=
          (Real.rpow_mul_natCast hd0 a 2).symm
        _ = _ := by ring
    calc
      _ ≤ (Real.rpow (d : ℝ) a *
          (Cgamma * (1 + |t + v|) ^ 3)) ^ 2 := hsquare
      _ = Real.rpow (d : ℝ) (2 * a) * Cgamma ^ 2 *
          (1 + |t + v|) ^ 6 := by rw [mul_pow, hdpowEq]; ring
      _ ≤ _ := by gcongr
  have hsep : 1 + |t + v| ≤ (1 + |t|) * (1 + |v|) := by
    have ht := abs_add_le t v
    nlinarith [abs_nonneg t, abs_nonneg v]
  have hsep6 : (1 + |t + v|) ^ 6 ≤
      (1 + |t|) ^ 6 * (1 + |v|) ^ 6 := by
    calc
      _ ≤ ((1 + |t|) * (1 + |v|)) ^ 6 := pow_le_pow_left₀ (by positivity) hsep 6
      _ = _ := by ring
  have hscale : ‖(X : ℂ) ^
      (((-(Real.log X)⁻¹ : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤ 1 := by
    have hXpos : 0 < X := by linarith
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hXpos]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      zero_mul, mul_zero, sub_zero, add_zero]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
      (neg_nonpos.mpr (inv_nonneg.mpr (Real.log_pos (by linarith)).le))
  have hhead := norm_shortReflectedHead_le_uniform psi (by linarith : 0 ≤ X)
    sigma t v
  have hhead' : ‖ramachandraReflectedHead psi X
      (shortFunctionalPoint X sigma t v)‖ ≤
      shortHeadUniformNormBound psi X sigma := by
    simpa [shortReflectedHead] using hhead
  have hChead0 : 0 ≤ shortHeadUniformNormBound psi X sigma := by
    unfold shortHeadUniformNormBound
    positivity
  unfold ramachandraShiftedContourIntegrand
  simp only [Bool.false_eq_true, ↓reduceIte, norm_mul, norm_pow]
  rw [show ramachandraShiftedPoint sigma t +
      (((-(Real.log X)⁻¹ : ℝ) : ℂ) + (v : ℂ) * I) =
        shortFunctionalPoint X sigma t v by
    exact (shortFunctionalPoint_eq_shifted X sigma t v).symm]
  unfold gammaPolynomialWeight
  have hnonneg : 0 ≤ Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _) (sq_nonneg Cgamma)
  calc
    ‖ramachandraFunctionalFactor psi (shortFunctionalPoint X sigma t v)‖ ^ 2 *
          ‖ramachandraReflectedHead psi X (shortFunctionalPoint X sigma t v)‖ *
        ‖Complex.Gamma (((-(Real.log X)⁻¹ : ℝ) : ℂ) + (v : ℂ) * I)‖ *
      ‖(X : ℂ) ^ (((-(Real.log X)⁻¹ : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
        (Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 * (1 + |t + v|) ^ 6) *
          shortHeadUniformNormBound psi X sigma *
          ‖Complex.Gamma (((-(Real.log X)⁻¹ : ℝ) : ℂ) + (v : ℂ) * I)‖ * 1 := by
      have hGamma0 : 0 ≤ ‖Complex.Gamma
          (((-(Real.log X)⁻¹ : ℝ) : ℂ) + (v : ℂ) * I)‖ := norm_nonneg _
      calc
        _ ≤ (Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
              (1 + |t + v|) ^ 6) *
            ‖ramachandraReflectedHead psi X (shortFunctionalPoint X sigma t v)‖ *
            ‖Complex.Gamma (((-(Real.log X)⁻¹ : ℝ) : ℂ) + (v : ℂ) * I)‖ *
            ‖(X : ℂ) ^ (((-(Real.log X)⁻¹ : ℝ) : ℂ) + (v : ℂ) * I)‖ := by
          gcongr
        _ ≤ (Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
              (1 + |t + v|) ^ 6) *
            shortHeadUniformNormBound psi X sigma *
            ‖Complex.Gamma (((-(Real.log X)⁻¹ : ℝ) : ℂ) + (v : ℂ) * I)‖ * 1 := by
          gcongr
    _ ≤ (Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
          ((1 + |t|) ^ 6 * (1 + |v|) ^ 6)) *
          shortHeadUniformNormBound psi X sigma *
          ‖Complex.Gamma (((-(Real.log X)⁻¹ : ℝ) : ℂ) + (v : ℂ) * I)‖ := by
      have hGamma0 : 0 ≤ ‖Complex.Gamma
          (((-(Real.log X)⁻¹ : ℝ) : ℂ) + (v : ℂ) * I)‖ := norm_nonneg _
      have hcoef0 : 0 ≤ Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
          shortHeadUniformNormBound psi X sigma *
          ‖Complex.Gamma (((-(Real.log X)⁻¹ : ℝ) : ℂ) + (v : ℂ) * I)‖ := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hsep6 hcoef0]
    _ = _ := by ring

/-- The literal normalized short contour is continuous in the source
ordinate. -/
theorem continuous_primitiveShiftedShortContour
    (psi : DirichletCharacter ℂ d)
    {T sigma : ℝ} (hT : 3 ≤ T) (hX : 6 ≤ primitiveShiftedScale d T)
    (hstrip : |sigma - (1 / 2 : ℝ)| ≤
      (100 * Real.log (primitiveShiftedScale d T))⁻¹) :
    Continuous (fun t => primitiveShiftedShortContour psi T sigma t) := by
  let X := primitiveShiftedScale d T
  rcases RamachandraLongContourContinuity.exists_norm_ramachandraFunctionalFactor_le_global_character psi with
    ⟨Cgamma, hCgamma, hglobal⟩
  have hab := shortExponent_bounds (by simpa [X] using hX)
    (by simpa [X] using hstrip)
  have hrlo : -(1 / 4 : ℝ) ≤ sigma - (Real.log X)⁻¹ := by
    change 0 ≤ _ ∧ _ at hab
    linarith [hab.2.2]
  have hrhi : sigma - (Real.log X)⁻¹ ≤ 1 / 2 := by
    change 0 ≤ _ ∧ _ at hab
    linarith [hab.1]
  have hlog : 1 < Real.log X :=
    RamachandraShiftedDirectParameters.one_lt_log_of_three_le
      (by dsimp [X]; linarith)
  have hcLo : -1 < -(Real.log X)⁻¹ := by
    have hi : (Real.log X)⁻¹ < 1 := (inv_lt_one₀ (by linarith)).2 hlog
    linarith
  have hcHi : -(Real.log X)⁻¹ < 0 := by
    have hi : 0 < (Real.log X)⁻¹ := inv_pos.mpr (by linarith)
    linarith
  let Chead := shortHeadUniformNormBound psi X sigma
  have hintCont : Continuous (fun t => ∫ v : ℝ,
      ramachandraShiftedContourIntegrand psi X sigma
        (-(Real.log X)⁻¹) t v false) := by
    rw [continuous_iff_continuousAt]
    intro t₁
    have htNear1 : ∀ᶠ t in 𝓝 t₁, |t| ≤ |t₁| + 1 := by
      have hdist : ∀ᶠ t in 𝓝 t₁, t ∈ Metric.ball t₁ 1 :=
        Metric.ball_mem_nhds t₁ (by norm_num)
      filter_upwards [hdist] with t ht
      have ht' : dist t t₁ < 1 := by simpa [Metric.mem_ball] using ht
      rw [Real.dist_eq] at ht'
      calc
        |t| = |(t - t₁) + t₁| := by ring_nf
        _ ≤ |t - t₁| + |t₁| := abs_add_le _ _
        _ ≤ |t₁| + 1 := by linarith
    let B₁ : ℝ := Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 *
      (1 + (|t₁| + 1)) ^ 6
    let bound₁ : ℝ → ℝ := fun v => (B₁ * Chead) *
      gammaPolynomialWeight (-(Real.log X)⁻¹) v
    apply tendsto_integral_filter_of_dominated_convergence bound₁
    · filter_upwards with t
      exact ((continuous_uncurry_shortContourIntegrand psi (by dsimp [X]; linarith)
        hcLo hcHi hrlo hrhi).comp
          (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · filter_upwards [htNear1] with t ht
      filter_upwards with v
      have hraw := norm_shortContourIntegrand_le_global psi
        (X := X) (sigma := sigma) (t := t) (v := v) (Cgamma := Cgamma)
        (by simpa [X] using hX) (by simpa [X] using hstrip)
        hCgamma
        (fun z hzlo hzhi => hglobal z hzlo hzhi)
      have ht6 : (1 + |t|) ^ 6 ≤ (1 + (|t₁| + 1)) ^ 6 := by gcongr
      have hW0 := gammaPolynomialWeight_nonneg (-(Real.log X)⁻¹) v
      have hC0 : 0 ≤ Chead := by dsimp [Chead, shortHeadUniformNormBound]; positivity
      calc
        _ ≤ (Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 * (1 + |t|) ^ 6) *
            gammaPolynomialWeight (-(Real.log X)⁻¹) v * Chead := hraw
        _ ≤ B₁ * gammaPolynomialWeight (-(Real.log X)⁻¹) v * Chead := by
          have hbase : 0 ≤ Real.rpow (d : ℝ) (3 / 2) * Cgamma ^ 2 :=
            mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _) (sq_nonneg Cgamma)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left ht6 hbase) hW0) hC0
        _ = bound₁ v := by dsimp [bound₁, B₁]; ring
    · exact (integrable_gammaPolynomialWeight hcLo hcHi).const_mul (B₁ * Chead)
    · filter_upwards with v
      have hcont := (continuous_uncurry_shortContourIntegrand psi
        (by dsimp [X]; linarith) hcLo hcHi hrlo hrhi).comp
        (continuous_id.prodMk (continuous_const : Continuous (fun _t : ℝ => v)))
      simpa only [Function.uncurry_apply_pair] using hcont.continuousAt
  unfold primitiveShiftedShortContour ramachandraShiftedContourPiece
  exact continuous_const.mul hintCont

end
end RamachandraShortContourContinuity

#print axioms RamachandraShortContourContinuity.continuous_primitiveShiftedShortContour
