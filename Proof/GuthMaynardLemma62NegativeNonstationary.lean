import GuthMaynardLemma62FiniteFactorization
import MRTNonstationaryPhaseInverse

/-!
# The opposite-sign sector in Guth--Maynard Lemma 6.2

For `t > 0`, the negative Fourier frequencies have phase derivative
`t/(2πu)+ξ`, so there is no stationary point on the cutoff support.  This
file performs the literal one-fold integration by parts.  It is the missing
sign-sensitive estimate behind the phrase "the negative terms are analogous"
on page 19 of the source.
-/

namespace GuthMaynardLemma62NegativeNonstationary

open Real Complex Set MeasureTheory
open scoped FourierTransform SchwartzMap BigOperators ContDiff
open GuthMaynardSectionThreeCutoff
open GuthMaynardSectionThreeCutoffDerivativeBudget
open GuthMaynardLemma62FarTail
open GuthMaynardLemma62MellinInsertion
open GuthMaynardLemma62Fubini
open GuthMaynardLemma62ReflectionSubstitution
open GuthMaynardLemma62FiniteFactorization
open GuthMaynardLemma62AbsoluteMellinTail
open MAPMRTCorollary53Source
open MAPMRTVanDerCorputProof
open MAPMRTNonstationaryPhaseInverse

noncomputable section

def negativeFrequencyPhase (t xi u : ℝ) : ℝ :=
  t / (2 * Real.pi) * Real.log u + xi * u

def negativeFrequencyPhaseDeriv (t xi u : ℝ) : ℝ :=
  t / (2 * Real.pi * u) + xi

def negativeFrequencyPhaseSecond (t u : ℝ) : ℝ :=
  -t / (2 * Real.pi * u ^ 2)

theorem hasDerivAt_negativeFrequencyPhase
    {t xi u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (negativeFrequencyPhase t xi)
      (negativeFrequencyPhaseDeriv t xi u) u := by
  unfold negativeFrequencyPhase negativeFrequencyPhaseDeriv
  convert (Real.hasDerivAt_log hu).const_mul (t / (2 * Real.pi)) |>.add
    ((hasDerivAt_id u).const_mul xi) using 1 <;>
    field_simp [Real.pi_ne_zero, hu]

theorem hasDerivAt_negativeFrequencyPhaseDeriv
    {t xi u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (negativeFrequencyPhaseDeriv t xi)
      (negativeFrequencyPhaseSecond t u) u := by
  unfold negativeFrequencyPhaseDeriv negativeFrequencyPhaseSecond
  convert (hasDerivAt_inv hu).const_mul (t / (2 * Real.pi)) |>.add_const xi
    using 1 <;> field_simp [Real.pi_ne_zero, hu]

theorem sectionThreeBaseIntegrand_negative_eq_phase
    {t xi u : ℝ} (hu : 0 < u) :
    sectionThreeBaseIntegrand t (-xi) u =
      additivePhase (negativeFrequencyPhase t xi u) *
        sectionThreeCutoff u := by
  unfold sectionThreeBaseIntegrand sectionThreeFourierPhase
    sectionThreeOscillatory negativeFrequencyPhase additivePhase
  rw [← oscillatoryPowerExp_eq_cpow hu]
  unfold oscillatoryPowerExp
  calc
    Complex.exp (((-2 * Real.pi * u * -xi : ℝ) : ℂ) * Complex.I) *
        (sectionThreeCutoff u *
          Complex.exp ((Complex.I * (t : ℂ)) * (Real.log u : ℂ))) =
      (Complex.exp (((-2 * Real.pi * u * -xi : ℝ) : ℂ) * Complex.I) *
          Complex.exp ((Complex.I * (t : ℂ)) * (Real.log u : ℂ))) *
        sectionThreeCutoff u := by ring
    _ = Complex.exp
          (2 * (Real.pi : ℂ) *
            ((t / (2 * Real.pi) * Real.log u + xi * u : ℝ) : ℂ) *
            Complex.I) * sectionThreeCutoff u := by
      congr 1
      rw [← Complex.exp_add]
      congr 1
      push_cast
      field_simp [Real.pi_ne_zero]
      ring

theorem sectionThreeCutoff_one : sectionThreeCutoff 1 = 0 := by
  unfold sectionThreeCutoff sectionThreeCutoffReal
  rw [GuthMaynardJIteration.sourceBump_eq_zero_of_two_mul_le_abs
    (x := (1 : ℝ) - 7 / 5) (1 / 5) fifth_pos (by norm_num),
    GuthMaynardJIteration.sourceBump_eq_zero_of_two_mul_le_abs
    (x := (1 : ℝ) - 8 / 5) (1 / 5) fifth_pos (by norm_num)]
  norm_num

theorem sectionThreeCutoff_two : sectionThreeCutoff 2 = 0 := by
  unfold sectionThreeCutoff sectionThreeCutoffReal
  rw [GuthMaynardJIteration.sourceBump_eq_zero_of_two_mul_le_abs
    (x := (2 : ℝ) - 7 / 5) (1 / 5) fifth_pos (by norm_num),
    GuthMaynardJIteration.sourceBump_eq_zero_of_two_mul_le_abs
    (x := (2 : ℝ) - 8 / 5) (1 / 5) fifth_pos (by norm_num)]
  norm_num

theorem negativeFrequencyPhaseDeriv_lower
    {t xi u : ℝ} (ht : 0 < t) (hxi : 0 < xi)
    (hu : u ∈ Set.Icc (1 : ℝ) 2) :
    t / (4 * Real.pi) + xi ≤
      |negativeFrequencyPhaseDeriv t xi u| := by
  have huPos : 0 < u := by linarith [hu.1]
  have hdenPos : 0 < 2 * Real.pi * u := by positivity
  have hphasePos : 0 < negativeFrequencyPhaseDeriv t xi u := by
    unfold negativeFrequencyPhaseDeriv
    positivity
  rw [abs_of_pos hphasePos]
  unfold negativeFrequencyPhaseDeriv
  have hden : 2 * Real.pi * u ≤ 4 * Real.pi := by
    calc
      2 * Real.pi * u ≤ 2 * Real.pi * 2 :=
        mul_le_mul_of_nonneg_left hu.2 (by positivity)
      _ = 4 * Real.pi := by ring
  have hdiv : t / (4 * Real.pi) ≤ t / (2 * Real.pi * u) :=
    div_le_div_of_nonneg_left ht.le hdenPos hden
  linarith

theorem negativeFrequencyPhaseSecond_upper
    {t u : ℝ} (ht : 0 < t) (hu : u ∈ Set.Icc (1 : ℝ) 2) :
    |negativeFrequencyPhaseSecond t u| ≤ t / (2 * Real.pi) := by
  have huPos : 0 < u := by linarith [hu.1]
  unfold negativeFrequencyPhaseSecond
  rw [abs_div, abs_neg, abs_of_pos ht, abs_mul,
    abs_of_pos (by positivity : 0 < 2 * Real.pi), abs_pow,
    abs_of_pos huPos]
  apply div_le_div_of_nonneg_left ht.le (by positivity)
  have huSq : (1 : ℝ) ≤ u ^ 2 := by nlinarith [hu.1]
  simpa using mul_le_mul_of_nonneg_left huSq
    (show (0 : ℝ) ≤ 2 * Real.pi by positivity)

/-- Exact one-fold integration-by-parts identity for one negative frequency.
The boundary terms vanish because the concrete cutoff vanishes at both
endpoints. -/
theorem sectionThreeFourierCoefficient_negative_ibp
    {t xi : ℝ} (ht : 0 < t) (hxi : 0 < xi) :
    sectionThreeFourierCoefficient t (-xi) =
      -∫ u : ℝ in 1..2,
        ((deriv sectionThreeCutoff u *
              inversePhaseDerivative
                (negativeFrequencyPhaseDeriv t xi) u) +
            sectionThreeCutoff u *
              inversePhaseDerivativeDeriv
                (negativeFrequencyPhaseDeriv t xi)
                (negativeFrequencyPhaseSecond t) u) *
          additivePhase (negativeFrequencyPhase t xi u) := by
  let p : ℝ → ℝ := negativeFrequencyPhaseDeriv t xi
  let p' : ℝ → ℝ := negativeFrequencyPhaseSecond t
  let E : ℝ → ℂ := fun u =>
    additivePhase (negativeFrequencyPhase t xi u)
  let Ed : ℝ → ℂ := fun u =>
    ((2 * Real.pi : ℂ) * Complex.I * (p u : ℂ)) * E u
  let q : ℝ → ℂ := inversePhaseDerivative p
  let qd : ℝ → ℂ := inversePhaseDerivativeDeriv p p'
  let a : ℝ → ℂ := sectionThreeCutoff
  let ad : ℝ → ℂ := deriv sectionThreeCutoff
  let v : ℝ → ℂ := fun u => a u * q u
  let vd : ℝ → ℂ := fun u => ad u * q u + a u * qd u
  have hp0 : ∀ u ∈ Set.Icc (1 : ℝ) 2, p u ≠ 0 := by
    intro u hu
    have hlower := negativeFrequencyPhaseDeriv_lower ht hxi hu
    have hd : 0 < t / (4 * Real.pi) + xi := by positivity
    exact abs_pos.mp (hd.trans_le hlower)
  have hphase : ∀ u ∈ Set.Icc (1 : ℝ) 2,
      HasDerivAt (negativeFrequencyPhase t xi) (p u) u := by
    intro u hu
    exact hasDerivAt_negativeFrequencyPhase (by linarith [hu.1])
  have hp : ∀ u ∈ Set.Icc (1 : ℝ) 2, HasDerivAt p (p' u) u := by
    intro u hu
    exact hasDerivAt_negativeFrequencyPhaseDeriv (by linarith [hu.1])
  have hE : ∀ u ∈ Set.Icc (1 : ℝ) 2, HasDerivAt E (Ed u) u := by
    intro u hu
    exact hasDerivAt_additivePhase_comp (hphase u hu)
  have hq : ∀ u ∈ Set.Icc (1 : ℝ) 2, HasDerivAt q (qd u) u := by
    intro u hu
    exact hasDerivAt_inversePhaseDerivative (hp0 u hu) (hp u hu)
  have ha : ∀ u ∈ Set.Icc (1 : ℝ) 2, HasDerivAt a (ad u) u := by
    intro u hu
    exact sectionThreeCutoff_contDiff.differentiable (by simp) u |>.hasDerivAt
  have hv : ∀ u ∈ Set.Icc (1 : ℝ) 2, HasDerivAt v (vd u) u := by
    intro u hu
    exact (ha u hu).mul (hq u hu)
  have hpCont : ContinuousOn p (Set.Icc (1 : ℝ) 2) :=
    fun u hu => (hp u hu).continuousAt.continuousWithinAt
  have hp'Cont : ContinuousOn p' (Set.Icc (1 : ℝ) 2) := by
    intro u hu
    have hu0 : u ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith [hu.1])
    unfold p' negativeFrequencyPhaseSecond
    exact (continuousAt_const.div
      (continuousAt_const.mul (continuousAt_id.pow 2))
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hu0)).continuousWithinAt
  have hECont : ContinuousOn E (Set.Icc (1 : ℝ) 2) :=
    fun u hu => (hE u hu).continuousAt.continuousWithinAt
  have hEdCont : ContinuousOn Ed (Set.Icc (1 : ℝ) 2) := by
    unfold Ed
    exact ((continuousOn_const.mul continuousOn_const).mul
      (Complex.continuous_ofReal.comp_continuousOn hpCont)).mul hECont
  have hqCont : ContinuousOn q (Set.Icc (1 : ℝ) 2) :=
    fun u hu => (hq u hu).continuousAt.continuousWithinAt
  have hqdCont : ContinuousOn qd (Set.Icc (1 : ℝ) 2) := by
    unfold qd inversePhaseDerivativeDeriv
    apply ContinuousOn.mul
    · apply Complex.continuous_ofReal.comp_continuousOn
      apply ContinuousOn.div
      · exact hp'Cont
      · exact continuousOn_const.mul (hpCont.pow 2)
      · intro u hu
        exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
          (pow_ne_zero 2 (hp0 u hu))
    · exact continuousOn_const
  have hvdCont : ContinuousOn vd (Set.Icc (1 : ℝ) 2) := by
    exact (sectionThreeCutoff_contDiff.continuous_deriv (by simp)).continuousOn.mul
      hqCont |>.add
      (sectionThreeCutoff_contDiff.continuous.continuousOn.mul
        hqdCont)
  have hiEd : IntervalIntegrable Ed volume 1 2 :=
    (by
      apply ContinuousOn.intervalIntegrable
      simpa [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using hEdCont)
  have hivd : IntervalIntegrable vd volume 1 2 :=
    (by
      apply ContinuousOn.intervalIntegrable
      simpa [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using hvdCont)
  have hinverse : ∀ u ∈ Set.Icc (1 : ℝ) 2, q u * Ed u = E u := by
    intro u hu
    exact inversePhaseDerivative_mul_phaseDeriv (hp0 u hu)
  have hibp : (∫ u : ℝ in 1..2, v u * Ed u) =
      v 2 * E 2 - v 1 * E 1 - ∫ u : ℝ in 1..2, vd u * E u := by
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (by simpa using hv) (by simpa using hE) hivd hiEd
  rw [sectionThreeFourierCoefficient_eq_extendedIntegral t (-xi)
    (by norm_num : (1 : ℝ) ≤ 1) (by norm_num : (2 : ℝ) ≤ 2)]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2)]
  have hsource : ∫ u : ℝ in 1..2, sectionThreeBaseIntegrand t (-xi) u =
      ∫ u : ℝ in 1..2, E u * a u := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Set.Icc (1 : ℝ) 2 := by
      simpa [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using hu
    exact sectionThreeBaseIntegrand_negative_eq_phase (by linarith [hu'.1])
  rw [hsource]
  have hfactor : ∀ u ∈ Set.uIcc (1 : ℝ) 2,
      E u * a u = v u * Ed u := by
    intro u hu
    have hu' : u ∈ Set.Icc (1 : ℝ) 2 := by
      simpa [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using hu
    unfold v
    rw [mul_assoc, hinverse u hu']
    ring
  rw [intervalIntegral.integral_congr hfactor, hibp]
  simp [v, a, ad, sectionThreeCutoff_one, sectionThreeCutoff_two, vd, q, qd,
    p, p', E]

/-- Quantitative opposite-sign estimate.  Unlike the generic Fourier-IBP
bound, its denominator grows with `t+ξ`, so summing the nonstationary sector
does not lose a power of the spectral height. -/
theorem norm_sectionThreeFourierCoefficient_negative_le
    {t xi : ℝ} (ht : 0 < t) (hxi : 0 < xi) :
    ‖sectionThreeFourierCoefficient t (-xi)‖ ≤
      cutoffDerivativeSup 1 /
          (t / (4 * Real.pi) + xi) +
        cutoffDerivativeSup 0 *
          ((t / (2 * Real.pi)) /
            (t / (4 * Real.pi) + xi) ^ 2) := by
  let d : ℝ := t / (4 * Real.pi) + xi
  let P : ℝ := t / (2 * Real.pi)
  let integrand : ℝ → ℂ := fun u =>
    ((deriv sectionThreeCutoff u *
          inversePhaseDerivative
            (negativeFrequencyPhaseDeriv t xi) u) +
        sectionThreeCutoff u *
          inversePhaseDerivativeDeriv
            (negativeFrequencyPhaseDeriv t xi)
            (negativeFrequencyPhaseSecond t) u) *
      additivePhase (negativeFrequencyPhase t xi u)
  have hd : 0 < d := by dsimp only [d]; positivity
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hpoint : ∀ u ∈ Set.uIoc (1 : ℝ) 2,
      ‖integrand u‖ ≤
        cutoffDerivativeSup 1 / d +
          cutoffDerivativeSup 0 * (P / d ^ 2) := by
    intro u hu
    have hu' : u ∈ Set.Icc (1 : ℝ) 2 := by
      have := Set.uIoc_subset_uIcc hu
      simpa [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using this
    have hq := norm_inversePhaseDerivative_le hd
      (negativeFrequencyPhaseDeriv_lower ht hxi hu')
    have hqd := norm_inversePhaseDerivativeDeriv_le hd hP
      (negativeFrequencyPhaseDeriv_lower ht hxi hu')
      (negativeFrequencyPhaseSecond_upper ht hu')
    have ha := norm_iteratedDeriv_sectionThreeCutoff_le 0 u
    have had := norm_iteratedDeriv_sectionThreeCutoff_le 1 u
    simp only [iteratedDeriv_zero] at ha
    simp only [iteratedDeriv_one] at had
    have hfirst :
        ‖deriv sectionThreeCutoff u‖ *
            ‖inversePhaseDerivative
              (negativeFrequencyPhaseDeriv t xi) u‖ ≤
          cutoffDerivativeSup 1 * (1 / d) := by
      exact (mul_le_mul_of_nonneg_right had (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hq (cutoffDerivativeSup_nonneg 1))
    have hsecond :
        ‖sectionThreeCutoff u‖ *
            ‖inversePhaseDerivativeDeriv
              (negativeFrequencyPhaseDeriv t xi)
              (negativeFrequencyPhaseSecond t) u‖ ≤
          cutoffDerivativeSup 0 * (P / d ^ 2) := by
      exact (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hqd (cutoffDerivativeSup_nonneg 0))
    unfold integrand
    rw [norm_mul, norm_additivePhase, mul_one]
    calc
      ‖deriv sectionThreeCutoff u *
          inversePhaseDerivative (negativeFrequencyPhaseDeriv t xi) u +
        sectionThreeCutoff u *
          inversePhaseDerivativeDeriv
            (negativeFrequencyPhaseDeriv t xi)
            (negativeFrequencyPhaseSecond t) u‖ ≤
        ‖deriv sectionThreeCutoff u *
          inversePhaseDerivative (negativeFrequencyPhaseDeriv t xi) u‖ +
        ‖sectionThreeCutoff u *
          inversePhaseDerivativeDeriv
            (negativeFrequencyPhaseDeriv t xi)
            (negativeFrequencyPhaseSecond t) u‖ := norm_add_le _ _
      _ = ‖deriv sectionThreeCutoff u‖ *
            ‖inversePhaseDerivative
              (negativeFrequencyPhaseDeriv t xi) u‖ +
          ‖sectionThreeCutoff u‖ *
            ‖inversePhaseDerivativeDeriv
              (negativeFrequencyPhaseDeriv t xi)
              (negativeFrequencyPhaseSecond t) u‖ := by
        rw [norm_mul, norm_mul]
      _ ≤ cutoffDerivativeSup 1 * (1 / d) +
          cutoffDerivativeSup 0 * (P / d ^ 2) :=
        add_le_add hfirst hsecond
      _ = cutoffDerivativeSup 1 / d +
          cutoffDerivativeSup 0 * (P / d ^ 2) := by ring
  rw [sectionThreeFourierCoefficient_negative_ibp ht hxi, norm_neg]
  have hraw := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  norm_num at hraw
  simpa [integrand, d, P] using hraw

def negativeSectorConstant : ℝ :=
  4 * Real.pi * cutoffDerivativeSup 1 +
    8 * Real.pi * cutoffDerivativeSup 0

theorem negativeSectorConstant_nonneg : 0 ≤ negativeSectorConstant := by
  unfold negativeSectorConstant
  exact add_nonneg
    (mul_nonneg (by positivity) (cutoffDerivativeSup_nonneg 1))
    (mul_nonneg (by positivity) (cutoffDerivativeSup_nonneg 0))

theorem norm_sectionThreeFourierCoefficient_negative_le_inv
    {t xi : ℝ} (ht : 0 < t) (hxi : 0 < xi) :
    ‖sectionThreeFourierCoefficient t (-xi)‖ ≤
      negativeSectorConstant / t := by
  have hraw := norm_sectionThreeFourierCoefficient_negative_le ht hxi
  let d : ℝ := t / (4 * Real.pi) + xi
  have hd : 0 < d := by dsimp only [d]; positivity
  have hdLower : t / (4 * Real.pi) ≤ d := by
    dsimp only [d]
    linarith
  have htQuarter : 0 < t / (4 * Real.pi) := by positivity
  have hone : 1 / d ≤ 4 * Real.pi / t := by
    calc
      1 / d ≤ 1 / (t / (4 * Real.pi)) :=
        one_div_le_one_div_of_le htQuarter hdLower
      _ = 4 * Real.pi / t := by
        field_simp [ht.ne', Real.pi_ne_zero]
  have htwo :
      (t / (2 * Real.pi)) / d ^ 2 ≤ 8 * Real.pi / t := by
    calc
      (t / (2 * Real.pi)) / d ^ 2 ≤
          (t / (2 * Real.pi)) / (t / (4 * Real.pi)) ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity)
          (sq_pos_of_pos htQuarter)
        exact pow_le_pow_left₀ htQuarter.le hdLower 2
      _ = 8 * Real.pi / t := by
        field_simp [ht.ne', Real.pi_ne_zero]
        ring
  calc
    ‖sectionThreeFourierCoefficient t (-xi)‖ ≤
        cutoffDerivativeSup 1 / d +
          cutoffDerivativeSup 0 *
            ((t / (2 * Real.pi)) / d ^ 2) := by
      simpa only [d] using hraw
    _ ≤ cutoffDerivativeSup 1 * (4 * Real.pi / t) +
          cutoffDerivativeSup 0 * (8 * Real.pi / t) := by
      exact add_le_add
        (by
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hone)
            (cutoffDerivativeSup_nonneg 1))
        (mul_le_mul_of_nonneg_left htwo (cutoffDerivativeSup_nonneg 0))
    _ = negativeSectorConstant / t := by
      unfold negativeSectorConstant
      field_simp [ht.ne']

theorem norm_finite_negative_coefficients_le_inv
    {t N : ℝ} (ht : 0 < t) (hN : 0 < N) (L : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 L,
        sectionThreeFourierCoefficient t (-((m : ℝ) * N))‖ ≤
      (L : ℝ) * (negativeSectorConstant / t) := by
  calc
    ‖∑ m ∈ Finset.Icc 1 L,
        sectionThreeFourierCoefficient t (-((m : ℝ) * N))‖ ≤
      ∑ m ∈ Finset.Icc 1 L,
        ‖sectionThreeFourierCoefficient t (-((m : ℝ) * N))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.Icc 1 L, negativeSectorConstant / t := by
      apply Finset.sum_le_sum
      intro m hm
      have hmPos : (0 : ℝ) < m := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm).1)
      exact norm_sectionThreeFourierCoefficient_negative_le_inv ht
        (mul_pos hmPos hN)
    _ = (L : ℝ) * (negativeSectorConstant / t) := by simp

/-- The complete finite AFE in the useful source scale: central reflected
positive frequencies plus an exterior Mellin-tail error and an `L/t`
opposite-sign error. -/
theorem norm_finite_twoSided_coefficients_sub_central_le_strong
    (t : ℝ) {N R : ℝ} (ht : 0 < t) (hN : 0 < N) (hR : 0 < R)
    (L : ℕ) (hL : 1 ≤ L) (k : ℕ) (hk : 2 ≤ k) :
    ‖((∑ m ∈ Finset.Icc 1 L,
          sectionThreeFourierCoefficient t ((m : ℝ) * N)) +
        (∑ m ∈ Finset.Icc 1 L,
          sectionThreeFourierCoefficient t (-((m : ℝ) * N))) -
        (∫ r : ℝ in Set.Ioc (-R) R,
          factorizedReflectedOuter t N L r))‖ ≤
      ((1 / (2 * Real.pi)) * Real.log (2 * (L : ℝ)) * (L : ℝ)) *
          (2 * (((2 * Real.pi) ^ k * sectionThreeMellinSeminorm k) *
            (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)))) +
        (L : ℝ) * (negativeSectorConstant / t) := by
  let P : ℂ := ∑ m ∈ Finset.Icc 1 L,
    sectionThreeFourierCoefficient t ((m : ℝ) * N)
  let Q : ℂ := ∑ m ∈ Finset.Icc 1 L,
    sectionThreeFourierCoefficient t (-((m : ℝ) * N))
  let C : ℂ := ∫ r : ℝ in Set.Ioc (-R) R,
    factorizedReflectedOuter t N L r
  have hreassoc : P + Q - C = (P - C) + Q := by ring
  rw [show
      ((∑ m ∈ Finset.Icc 1 L,
          sectionThreeFourierCoefficient t ((m : ℝ) * N)) +
        (∑ m ∈ Finset.Icc 1 L,
          sectionThreeFourierCoefficient t (-((m : ℝ) * N))) -
        (∫ r : ℝ in Set.Ioc (-R) R,
          factorizedReflectedOuter t N L r)) = P + Q - C by rfl,
    hreassoc]
  exact (norm_add_le (P - C) Q).trans
    (add_le_add
      (norm_finite_positive_coefficients_sub_central_le hN hR L hL k hk)
      (norm_finite_negative_coefficients_le_inv ht hN L))

/-- Finite source-facing form of Guth--Maynard Lemma 6.2.  At an exact
dyadic length it bounds the complete nonzero-frequency block by the central
reflected Dirichlet-polynomial integral, with only the explicit Mellin-tail
and opposite-sign errors. -/
theorem norm_finite_twoSided_coefficients_le_reflectedPolynomialIntegral
    (t : ℝ) {N R : ℝ} (hN : 0 < N) (hR : 0 < R) (htR : R < t)
    (J k : ℕ) (hk : 2 ≤ k) :
    ‖(∑ m ∈ Finset.Icc (1 : ℕ) (2 ^ J),
        sectionThreeFourierCoefficient t ((m : ℝ) * N)) +
      (∑ m ∈ Finset.Icc (1 : ℕ) (2 ^ J),
        sectionThreeFourierCoefficient t (-((m : ℝ) * N)))‖ ≤
      (∫ r : ℝ in Set.Ioc (-R) R,
        ((1 / (2 * Real.pi)) *
          ((J + 1) * (20 * Real.sqrt (8 * Real.pi) /
            Real.sqrt (t - R)))) *
          (‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖ *
            ‖reflectedDirichletPolynomial (2 ^ J) (t - r)‖)) +
      ((1 / (2 * Real.pi)) *
          Real.log (2 * ((2 ^ J : ℕ) : ℝ)) * ((2 ^ J : ℕ) : ℝ)) *
        (2 * (((2 * Real.pi) ^ k * sectionThreeMellinSeminorm k) *
          (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)))) +
      ((2 ^ J : ℕ) : ℝ) * (negativeSectorConstant / t) := by
  let S : ℂ :=
    (∑ m ∈ Finset.Icc (1 : ℕ) (2 ^ J),
      sectionThreeFourierCoefficient t ((m : ℝ) * N)) +
    (∑ m ∈ Finset.Icc (1 : ℕ) (2 ^ J),
      sectionThreeFourierCoefficient t (-((m : ℝ) * N)))
  let C : ℂ := ∫ r : ℝ in Set.Ioc (-R) R,
    factorizedReflectedOuter t N (2 ^ J) r
  have ht : 0 < t := hR.trans htR
  have hL : 1 ≤ (2 ^ J : ℕ) := by
    exact Nat.one_le_pow J 2 (by norm_num)
  have herror := norm_finite_twoSided_coefficients_sub_central_le_strong
    t ht hN hR (2 ^ J) hL k hk
  have hcentral := norm_integral_factorizedReflectedOuter_central_le
    hN hR htR J
  have herror' :
      ‖S - C‖ ≤
        ((1 / (2 * Real.pi)) *
            Real.log (2 * ((2 ^ J : ℕ) : ℝ)) * ((2 ^ J : ℕ) : ℝ)) *
          (2 * (((2 * Real.pi) ^ k * sectionThreeMellinSeminorm k) *
            (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)))) +
        ((2 ^ J : ℕ) : ℝ) * (negativeSectorConstant / t) := by
    simpa only [S, C] using herror
  have hcentral' :
      ‖C‖ ≤
        ∫ r : ℝ in Set.Ioc (-R) R,
          ((1 / (2 * Real.pi)) *
            ((J + 1) * (20 * Real.sqrt (8 * Real.pi) /
              Real.sqrt (t - R)))) *
            (‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖ *
              ‖reflectedDirichletPolynomial (2 ^ J) (t - r)‖) := by
    simpa only [C] using hcentral
  have htri : ‖S‖ ≤ ‖S - C‖ + ‖C‖ := by
    have h := norm_add_le (S - C) C
    simpa [sub_add_cancel] using h
  exact htri.trans (by
    simpa only [add_assoc, add_comm, add_left_comm] using
      (add_le_add herror' hcentral'))

/-- Exact finite far-frequency truncation appended to the source-facing AFE.
The tail length `K` is arbitrary, while the bound is independent of `K`;
this is the finite statement from which the full summable tail is obtained. -/
theorem norm_finite_extended_twoSided_coefficients_le_reflectedPolynomialIntegral
    (t : ℝ) {N R : ℝ} (hN : 0 < N) (hR : 0 < R) (htR : R < t)
    (J K k ell : ℕ) (hk : 2 ≤ k) (hell : 2 ≤ ell) :
    ‖((∑ m ∈ Finset.Icc (1 : ℕ) (2 ^ J),
          sectionThreeFourierCoefficient t ((m : ℝ) * N)) +
        (∑ m ∈ Finset.Icc (1 : ℕ) (2 ^ J),
          sectionThreeFourierCoefficient t (-((m : ℝ) * N))) +
        (∑ i ∈ Finset.range K,
          sectionThreeFourierCoefficient t
            (((2 ^ J + (i + 1 : ℕ) : ℕ) : ℝ) * N)) +
        (∑ i ∈ Finset.range K,
          sectionThreeFourierCoefficient t
            (-(((2 ^ J + (i + 1 : ℕ) : ℕ) : ℝ) * N))))‖ ≤
      (∫ r : ℝ in Set.Ioc (-R) R,
        ((1 / (2 * Real.pi)) *
          ((J + 1) * (20 * Real.sqrt (8 * Real.pi) /
            Real.sqrt (t - R)))) *
          (‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖ *
            ‖reflectedDirichletPolynomial (2 ^ J) (t - r)‖)) +
      ((1 / (2 * Real.pi)) *
          Real.log (2 * ((2 ^ J : ℕ) : ℝ)) * ((2 ^ J : ℕ) : ℝ)) *
        (2 * (((2 * Real.pi) ^ k * sectionThreeMellinSeminorm k) *
          (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)))) +
      ((2 ^ J : ℕ) : ℝ) * (negativeSectorConstant / t) +
      2 * ((lemma43DerivativeConstant ell * (1 + |t|) ^ ell *
          N ^ (-(ell : ℝ))) *
        (((2 ^ J : ℕ) : ℝ) ^ (1 - (ell : ℝ)) /
          ((ell : ℝ) - 1))) := by
  let Base : ℂ :=
    (∑ m ∈ Finset.Icc (1 : ℕ) (2 ^ J),
      sectionThreeFourierCoefficient t ((m : ℝ) * N)) +
    (∑ m ∈ Finset.Icc (1 : ℕ) (2 ^ J),
      sectionThreeFourierCoefficient t (-((m : ℝ) * N)))
  let TailPos : ℂ := ∑ i ∈ Finset.range K,
    sectionThreeFourierCoefficient t
      (((2 ^ J + (i + 1 : ℕ) : ℕ) : ℝ) * N)
  let TailNeg : ℂ := ∑ i ∈ Finset.range K,
    sectionThreeFourierCoefficient t
      (-(((2 ^ J + (i + 1 : ℕ) : ℕ) : ℝ) * N))
  have hbase := norm_finite_twoSided_coefficients_le_reflectedPolynomialIntegral
    t hN hR htR J k hk
  have hM : 1 ≤ (2 ^ J : ℕ) := Nat.one_le_pow J 2 (by norm_num)
  have htailRaw := finite_twoSided_fourier_tail_le
    t hN (M := 2 ^ J) (K := K) hM hell
  have htailNorm : ‖TailPos + TailNeg‖ ≤
      2 * ((lemma43DerivativeConstant ell * (1 + |t|) ^ ell *
          N ^ (-(ell : ℝ))) *
        (((2 ^ J : ℕ) : ℝ) ^ (1 - (ell : ℝ)) /
          ((ell : ℝ) - 1))) := by
    calc
      ‖TailPos + TailNeg‖ ≤ ‖TailPos‖ + ‖TailNeg‖ := norm_add_le _ _
      _ ≤
          (∑ i ∈ Finset.range K,
            ‖sectionThreeFourierCoefficient t
              (((2 ^ J + (i + 1 : ℕ) : ℕ) : ℝ) * N)‖) +
          (∑ i ∈ Finset.range K,
            ‖sectionThreeFourierCoefficient t
              (-(((2 ^ J + (i + 1 : ℕ) : ℕ) : ℝ) * N))‖) :=
        add_le_add (by simpa only [TailPos] using norm_sum_le _ _)
          (by simpa only [TailNeg] using norm_sum_le _ _)
      _ ≤ _ := htailRaw
  have htotal : ‖Base + (TailPos + TailNeg)‖ ≤
      ‖Base‖ + ‖TailPos + TailNeg‖ := norm_add_le _ _
  change ‖Base + TailPos + TailNeg‖ ≤ _
  rw [add_assoc]
  exact htotal.trans (add_le_add (by simpa only [Base] using hbase) htailNorm)

end

end GuthMaynardLemma62NegativeNonstationary

#print axioms GuthMaynardLemma62NegativeNonstationary.sectionThreeFourierCoefficient_negative_ibp
#print axioms GuthMaynardLemma62NegativeNonstationary.norm_sectionThreeFourierCoefficient_negative_le
#print axioms GuthMaynardLemma62NegativeNonstationary.norm_finite_twoSided_coefficients_sub_central_le_strong
#print axioms GuthMaynardLemma62NegativeNonstationary.norm_finite_twoSided_coefficients_le_reflectedPolynomialIntegral
#print axioms GuthMaynardLemma62NegativeNonstationary.norm_finite_extended_twoSided_coefficients_le_reflectedPolynomialIntegral
