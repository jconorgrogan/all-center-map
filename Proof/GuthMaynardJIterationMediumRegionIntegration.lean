import GuthMaynardJIterationMediumLocalizedPairs

open scoped BigOperators Real FourierTransform
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-! Exact measurable and signed-affine bookkeeping for TeX 1588--1598. -/

def sourceMediumPairWindow (M3 B : ℝ) (p : ℤ × ℤ) : Set ℝ :=
  {xi | |xi - (p.1 : ℝ) * (p.2 : ℝ)| < (|(p.1 : ℝ)| / M3) * B}

theorem measurableSet_sourceMediumPairWindow
    (M3 B : ℝ) (p : ℤ × ℤ) :
    MeasurableSet (sourceMediumPairWindow M3 B p) := by
  unfold sourceMediumPairWindow
  exact measurableSet_lt
    ((measurable_id.sub measurable_const).abs) measurable_const

theorem mem_sourceMediumPairWindow_iff
    {M3 B : ℝ} {p : ℤ × ℤ} {xi : ℝ} :
    xi ∈ sourceMediumPairWindow M3 B p ↔
      |xi - (p.1 : ℝ) * (p.2 : ℝ)| < (|(p.1 : ℝ)| / M3) * B := by
  rfl

/-- The variable localized finset is exactly a fixed product finset with
each summand cut off by its strict source window. -/
theorem sourceMediumLocalizedPairSum_eq_indicatorSum
    (m1Range ellRange : Finset ℤ) (M3 B : ℝ)
    (H : (ℤ × ℤ) → ℝ → ℝ) (xi : ℝ) :
    (∑ p ∈ sourceMediumLocalizedPairs m1Range ellRange M3 B xi, H p xi) =
      ∑ p ∈ m1Range ×ˢ ellRange,
        (sourceMediumPairWindow M3 B p).indicator (H p) xi := by
  unfold sourceMediumLocalizedPairs sourceMediumPairWindow
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp_all

/-- Finite Tonelli/Fubini step for the nonnegative localized-pair envelope.
Only integrability on each literal strict window is required. -/
theorem integral_sourceMediumLocalizedPairSum
    (m1Range ellRange : Finset ℤ) (M3 B : ℝ)
    (H : (ℤ × ℤ) → ℝ → ℝ)
    (hH : ∀ p ∈ m1Range ×ˢ ellRange,
      IntegrableOn (H p) (sourceMediumPairWindow M3 B p)) :
    (∫ xi : ℝ,
      ∑ p ∈ sourceMediumLocalizedPairs m1Range ellRange M3 B xi, H p xi) =
      ∑ p ∈ m1Range ×ˢ ellRange,
        ∫ xi in sourceMediumPairWindow M3 B p, H p xi := by
  apply Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun xi =>
    sourceMediumLocalizedPairSum_eq_indicatorSum
      m1Range ellRange M3 B H xi))
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [integral_indicator (measurableSet_sourceMediumPairWindow M3 B p)]
  · intro p hp
    exact (hH p hp).integrable_indicator
      (measurableSet_sourceMediumPairWindow M3 B p)

/-- Restricting the nonnegative localized envelope to any measurable region
can only decrease its integral; the right side is the exact sum of window
integrals from the preceding finite interchange. -/
theorem setIntegral_sourceMediumLocalizedPairSum_le
    (m1Range ellRange : Finset ℤ) (M3 B : ℝ)
    (S : Set ℝ)
    (H : (ℤ × ℤ) → ℝ → ℝ)
    (hH0 : ∀ p ∈ m1Range ×ˢ ellRange, ∀ xi, 0 ≤ H p xi)
    (hH : ∀ p ∈ m1Range ×ˢ ellRange,
      IntegrableOn (H p) (sourceMediumPairWindow M3 B p)) :
    (∫ xi in S,
      ∑ p ∈ sourceMediumLocalizedPairs m1Range ellRange M3 B xi, H p xi) ≤
      ∑ p ∈ m1Range ×ˢ ellRange,
        ∫ xi in sourceMediumPairWindow M3 B p, H p xi := by
  let G : ℝ → ℝ := fun xi =>
    ∑ p ∈ sourceMediumLocalizedPairs m1Range ellRange M3 B xi, H p xi
  have hG_eq : G = fun xi => ∑ p ∈ m1Range ×ˢ ellRange,
      (sourceMediumPairWindow M3 B p).indicator (H p) xi := by
    funext xi
    exact sourceMediumLocalizedPairSum_eq_indicatorSum
      m1Range ellRange M3 B H xi
  have hGint : Integrable G := by
    rw [hG_eq]
    apply integrable_finsetSum
    intro p hp
    exact (hH p hp).integrable_indicator
      (measurableSet_sourceMediumPairWindow M3 B p)
  calc
    (∫ xi in S, G xi) ≤ ∫ xi : ℝ, G xi := by
      exact setIntegral_le_integral hGint
        (Filter.Eventually.of_forall fun xi => by
          dsimp only [G]
          apply Finset.sum_nonneg
          intro p hp
          exact hH0 p (Finset.mem_filter.mp hp).1 xi)
    _ = ∑ p ∈ m1Range ×ˢ ellRange,
        ∫ xi in sourceMediumPairWindow M3 B p, H p xi :=
      integral_sourceMediumLocalizedPairSum m1Range ellRange M3 B H hH

/-- Real-valued affine substitution on the whole line. -/
theorem integral_affine_change_real (F : ℝ → ℝ) (a b : ℝ) :
    (∫ tau : ℝ, F (b + a * tau)) =
      |a⁻¹| * ∫ xi : ℝ, F xi := by
  calc
    (∫ tau : ℝ, F (b + a * tau)) =
        ∫ tau : ℝ, (fun x : ℝ => F (b + x)) (a * tau) := by rfl
    _ = |a⁻¹| • ∫ x : ℝ, F (b + x) :=
      Measure.integral_comp_mul_left (fun x : ℝ => F (b + x)) a
    _ = |a⁻¹| • ∫ xi : ℝ, F xi := by
      congr 1
      exact (measurePreserving_add_left volume b).integral_comp
        (Homeomorph.addLeft b).measurableEmbedding F
    _ = |a⁻¹| * ∫ xi : ℝ, F xi := rfl

/-- Real-valued inverse affine substitution with the absolute Jacobian. -/
theorem integral_eq_abs_mul_affine_real (F : ℝ → ℝ) {a : ℝ}
    (ha : a ≠ 0) (b : ℝ) :
    (∫ xi : ℝ, F xi) = |a| * ∫ tau : ℝ, F (b + a * tau) := by
  calc
    (∫ xi : ℝ, F xi) =
        ∫ xi : ℝ, (fun tau : ℝ => F (b + a * tau))
          (-b / a + a⁻¹ * xi) := by
      apply integral_congr_ae
      filter_upwards with xi
      congr 1
      field_simp [ha]
      ring
    _ = |(a⁻¹)⁻¹| * ∫ tau : ℝ, F (b + a * tau) :=
      integral_affine_change_real (fun tau : ℝ => F (b + a * tau))
        a⁻¹ (-b / a)
    _ = |a| * ∫ tau : ℝ, F (b + a * tau) := by
      rw [inv_inv]

/-- Signed source substitution on one strict localization window.  The
Jacobian is absolute, so this holds for both signs of `m1`. -/
theorem setIntegral_sourceMediumPairWindow_affine
    (H : ℝ → ℝ) {M3 B : ℝ} (hM3 : 0 < M3)
    (m1 ell : ℤ) (hm1 : m1 ≠ 0) :
    (∫ xi in sourceMediumPairWindow M3 B (m1, ell), H xi) =
      (|(m1 : ℝ)| / M3) *
        ∫ tau in Set.Ioo (-B) B,
          H ((ell : ℝ) * (m1 : ℝ) + ((m1 : ℝ) / M3) * tau) := by
  let a : ℝ := (m1 : ℝ) / M3
  let c : ℝ := (ell : ℝ) * (m1 : ℝ)
  let W : Set ℝ := sourceMediumPairWindow M3 B (m1, ell)
  have hm1R : (m1 : ℝ) ≠ 0 := by exact_mod_cast hm1
  have ha : a ≠ 0 := div_ne_zero hm1R hM3.ne'
  have haabs : |a| = |(m1 : ℝ)| / M3 := by
    simp [a, abs_div, abs_of_pos hM3]
  have hpre (tau : ℝ) : c + a * tau ∈ W ↔ tau ∈ Set.Ioo (-B) B := by
    change |c + a * tau - (m1 : ℝ) * (ell : ℝ)| <
        |(m1 : ℝ)| / M3 * B ↔ -B < tau ∧ tau < B
    have hapos : 0 < |(m1 : ℝ)| / M3 := div_pos (abs_pos.mpr hm1R) hM3
    rw [show c + a * tau - (m1 : ℝ) * (ell : ℝ) = a * tau by
      dsimp only [c]
      ring]
    rw [abs_mul, haabs, mul_lt_mul_iff_of_pos_left hapos]
    exact abs_lt
  have hchange := integral_eq_abs_mul_affine_real
    (fun xi : ℝ => W.indicator H xi) ha c
  change (∫ xi in W, H xi) =
    (|(m1 : ℝ)| / M3) * ∫ tau in Set.Ioo (-B) B, H (c + a * tau)
  rw [← integral_indicator (measurableSet_sourceMediumPairWindow M3 B (m1, ell))]
  rw [hchange, haabs]
  congr 1
  rw [← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards with tau
  by_cases htau : tau ∈ Set.Ioo (-B) B
  · rw [Set.indicator_of_mem htau, Set.indicator_of_mem ((hpre tau).mpr htau)]
  · rw [Set.indicator_of_notMem htau,
      Set.indicator_of_notMem (fun h => htau ((hpre tau).mp h))]

/-- The corrected absolute Fourier dilation at the signed source affine
frequency.  Positivity of the dyadic `m2` range converts `|m2|` back to the
literal coefficient `m2` in `Sigma_II`. -/
theorem sourceCorrectedM2FourierInner_at_affine
    (m2Range : Finset ℤ) (fhat : ℝ → ℂ)
    {M3 : ℝ} (hM3 : M3 ≠ 0) (m1 ell : ℤ) (hm1 : m1 ≠ 0)
    (hm2pos : ∀ m2 ∈ m2Range, 0 < m2) (tau : ℝ) :
    sourceCorrectedM2FourierInner m2Range fhat m1
        ((ell : ℝ) * (m1 : ℝ) + ((m1 : ℝ) / M3) * tau) =
      ((1 / |(m1 : ℝ)| : ℝ) : ℂ) *
        ∑ m2 ∈ m2Range, sigmaIIFourierSummand M3 fhat ell m2 tau := by
  unfold sourceCorrectedM2FourierInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m2 hm2
  unfold sigmaIIFourierSummand
  have hm1R : (m1 : ℝ) ≠ 0 := by exact_mod_cast hm1
  have hm2R : 0 < (m2 : ℝ) := by exact_mod_cast hm2pos m2 hm2
  have hfreq :
      ((m2 : ℝ) / (m1 : ℝ)) *
          ((ell : ℝ) * (m1 : ℝ) + ((m1 : ℝ) / M3) * tau) =
        sigmaIIAffineFrequency M3 ell m2 tau := by
    unfold sigmaIIAffineFrequency
    exact source_frequency_affine_argument hm1R hM3
      (ell : ℝ) (m2 : ℝ) tau
  rw [hfreq, abs_div, abs_of_pos hm2R]
  push_cast
  field_simp [hm1R]

theorem norm_sourceCorrectedM2FourierInner_at_affine_sq
    (m2Range : Finset ℤ) (fhat : ℝ → ℂ)
    {M3 : ℝ} (hM3 : M3 ≠ 0) (m1 ell : ℤ) (hm1 : m1 ≠ 0)
    (hm2pos : ∀ m2 ∈ m2Range, 0 < m2) (tau : ℝ) :
    ‖sourceCorrectedM2FourierInner m2Range fhat m1
        ((ell : ℝ) * (m1 : ℝ) + ((m1 : ℝ) / M3) * tau)‖ ^ 2 =
      (1 / |(m1 : ℝ)|) ^ 2 *
        ‖∑ m2 ∈ m2Range,
          sigmaIIFourierSummand M3 fhat ell m2 tau‖ ^ 2 := by
  rw [sourceCorrectedM2FourierInner_at_affine
    m2Range fhat hM3 m1 ell hm1 hm2pos tau]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have habs : 0 < |(m1 : ℝ)| := abs_pos.mpr (by exact_mod_cast hm1)
  rw [abs_of_pos (one_div_pos.mpr habs), mul_pow]

/-- One localized first-Poisson square becomes exactly a bounded `tau`
integral with the absolute signed Jacobian.  This is the measure-theoretic
core of TeX 1595--1598. -/
theorem setIntegral_correctedM2Inner_sq_affine
    (m2Range : Finset ℤ) (fhat : ℝ → ℂ)
    {M3 B : ℝ} (hM3 : 0 < M3) (hB : 0 ≤ B)
    (m1 ell : ℤ) (hm1 : m1 ≠ 0)
    (hm2pos : ∀ m2 ∈ m2Range, 0 < m2) :
    (∫ xi in sourceMediumPairWindow M3 B (m1, ell),
        ‖sourceCorrectedM2FourierInner m2Range fhat m1 xi‖ ^ 2) =
      (1 / (M3 * |(m1 : ℝ)|)) *
        ∫ tau in -B..B,
          ‖∑ m2 ∈ m2Range,
            sigmaIIFourierSummand M3 fhat ell m2 tau‖ ^ 2 := by
  rw [setIntegral_sourceMediumPairWindow_affine
    (fun xi => ‖sourceCorrectedM2FourierInner m2Range fhat m1 xi‖ ^ 2)
    hM3 m1 ell hm1]
  have hsetInterval :
      (∫ tau in Set.Ioo (-B) B,
          ‖∑ m2 ∈ m2Range,
            sigmaIIFourierSummand M3 fhat ell m2 tau‖ ^ 2) =
        ∫ tau in -B..B,
          ‖∑ m2 ∈ m2Range,
            sigmaIIFourierSummand M3 fhat ell m2 tau‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith : -B ≤ B),
      integral_Ioc_eq_integral_Ioo]
  have hm1abs : 0 < |(m1 : ℝ)| := abs_pos.mpr (by exact_mod_cast hm1)
  calc
    (|(m1 : ℝ)| / M3) *
        ∫ tau in Set.Ioo (-B) B,
          ‖sourceCorrectedM2FourierInner m2Range fhat m1
            ((ell : ℝ) * (m1 : ℝ) + (m1 : ℝ) / M3 * tau)‖ ^ 2 =
      (|(m1 : ℝ)| / M3) *
        ∫ tau in Set.Ioo (-B) B,
          (1 / |(m1 : ℝ)|) ^ 2 *
            ‖∑ m2 ∈ m2Range,
              sigmaIIFourierSummand M3 fhat ell m2 tau‖ ^ 2 := by
        congr 1
        apply setIntegral_congr_fun measurableSet_Ioo
        intro tau htau
        exact norm_sourceCorrectedM2FourierInner_at_affine_sq
          m2Range fhat hM3.ne' m1 ell hm1 hm2pos tau
    _ = (|(m1 : ℝ)| / M3) * (1 / |(m1 : ℝ)|) ^ 2 *
        ∫ tau in Set.Ioo (-B) B,
          ‖∑ m2 ∈ m2Range,
            sigmaIIFourierSummand M3 fhat ell m2 tau‖ ^ 2 := by
      rw [MeasureTheory.integral_const_mul]
      ring
    _ = (1 / (M3 * |(m1 : ℝ)|)) *
        ∫ tau in -B..B,
          ‖∑ m2 ∈ m2Range,
            sigmaIIFourierSummand M3 fhat ell m2 tau‖ ^ 2 := by
      rw [hsetInterval]
      field_simp [hM3.ne', hm1abs.ne']

theorem continuous_sourceCorrectedM2FourierInner
    (m2Range : Finset ℤ) (fhat : ℝ → ℂ) (hfhat : Continuous fhat)
    (m1 : ℤ) :
    Continuous (sourceCorrectedM2FourierInner m2Range fhat m1) := by
  unfold sourceCorrectedM2FourierInner
  apply continuous_finsetSum
  intro m2 hm2
  fun_prop

theorem integrableOn_correctedM2Inner_sq_sourceMediumPairWindow
    (m2Range : Finset ℤ) (fhat : ℝ → ℂ) (hfhat : Continuous fhat)
    {M3 B : ℝ} (hM3 : 0 < M3) (hB : 0 ≤ B) (p : ℤ × ℤ) :
    IntegrableOn
      (fun xi => ‖sourceCorrectedM2FourierInner m2Range fhat p.1 xi‖ ^ 2)
      (sourceMediumPairWindow M3 B p) := by
  let c : ℝ := (p.1 : ℝ) * (p.2 : ℝ)
  let r : ℝ := (|(p.1 : ℝ)| / M3) * B
  have hr : 0 ≤ r := mul_nonneg (div_nonneg (abs_nonneg _) hM3.le) hB
  have hsub : sourceMediumPairWindow M3 B p ⊆ Set.Icc (c - r) (c + r) := by
    intro xi hxi
    change |xi - c| < r at hxi
    rw [abs_lt] at hxi
    constructor <;> linarith
  apply (Continuous.integrableOn_Icc
    ((continuous_sourceCorrectedM2FourierInner m2Range fhat hfhat p.1).norm.pow 2)).mono_set
  exact hsub

/-- Region-II integration of the exact outer Cauchy bound.  `P` is the
explicit uniform localized-pair count supplied by the preceding integer
window and signed-divisor lemmas.  The conclusion already has the corrected
`M3` affine frequency and the absolute signed Jacobian. -/
theorem setIntegral_norm_sourceFirstPoissonLocalizedPairSum_sq_le_affine
    (m1Range ellRange m2Range : Finset ℤ) (F fhat : ℝ → ℂ)
    (hfhat : Continuous fhat) (S : Set ℝ) (hS : MeasurableSet S)
    {M3 B Kpsi P : ℝ} (hM3 : 0 < M3) (hB : 0 ≤ B)
    (hKpsi : 0 ≤ Kpsi) (hP : 0 ≤ P)
    (hF : ∀ z, ‖F z‖ ≤ Kpsi)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm2pos : ∀ m2 ∈ m2Range, 0 < m2)
    (hcard : ∀ xi ∈ S,
      ((sourceMediumLocalizedPairs m1Range ellRange M3 B xi).card : ℝ) ≤ P)
    (hleft : IntegrableOn (fun xi =>
      ‖sourceFirstPoissonLocalizedPairSum
        m1Range ellRange m2Range F fhat M3 B xi‖ ^ 2) S) :
    (∫ xi in S,
      ‖sourceFirstPoissonLocalizedPairSum
        m1Range ellRange m2Range F fhat M3 B xi‖ ^ 2) ≤
      P * ∑ p ∈ m1Range ×ˢ ellRange,
        ((M3 * Kpsi) ^ 2 * (1 / (M3 * |(p.1 : ℝ)|))) *
          ∫ tau in -B..B,
            ‖∑ m2 ∈ m2Range,
              sigmaIIFourierSummand M3 fhat p.2 m2 tau‖ ^ 2 := by
  let H : (ℤ × ℤ) → ℝ → ℝ := fun p xi =>
    (M3 * Kpsi) ^ 2 *
      ‖sourceCorrectedM2FourierInner m2Range fhat p.1 xi‖ ^ 2
  let G : ℝ → ℝ := fun xi =>
    ∑ p ∈ sourceMediumLocalizedPairs m1Range ellRange M3 B xi, H p xi
  have hHint : ∀ p ∈ m1Range ×ˢ ellRange,
      IntegrableOn (H p) (sourceMediumPairWindow M3 B p) := by
    intro p hp
    exact (integrableOn_correctedM2Inner_sq_sourceMediumPairWindow
      m2Range fhat hfhat hM3 hB p).const_mul _
  have hGint : Integrable G := by
    have hEq : G = fun xi => ∑ p ∈ m1Range ×ˢ ellRange,
        (sourceMediumPairWindow M3 B p).indicator (H p) xi := by
      funext xi
      exact sourceMediumLocalizedPairSum_eq_indicatorSum
        m1Range ellRange M3 B H xi
    rw [hEq]
    apply integrable_finsetSum
    intro p hp
    exact (hHint p hp).integrable_indicator
      (measurableSet_sourceMediumPairWindow M3 B p)
  have hpoint : ∀ xi ∈ S,
      ‖sourceFirstPoissonLocalizedPairSum
        m1Range ellRange m2Range F fhat M3 B xi‖ ^ 2 ≤ P * G xi := by
    intro xi hxi
    refine (norm_sourceFirstPoissonLocalizedPairSum_sq_le
      m1Range ellRange m2Range F fhat hM3.le hKpsi hF xi).trans ?_
    apply mul_le_mul
    · exact hcard xi hxi
    · exact le_rfl
    · dsimp only [G, H]
      positivity
    · exact hP
  have hregion :
      (∫ xi in S,
        ‖sourceFirstPoissonLocalizedPairSum
          m1Range ellRange m2Range F fhat M3 B xi‖ ^ 2) ≤
        P * ∑ p ∈ m1Range ×ˢ ellRange,
          ∫ xi in sourceMediumPairWindow M3 B p, H p xi := by
    calc
      (∫ xi in S,
          ‖sourceFirstPoissonLocalizedPairSum
            m1Range ellRange m2Range F fhat M3 B xi‖ ^ 2) ≤
        ∫ xi in S, P * G xi := by
          apply setIntegral_mono_on hleft ((hGint.const_mul P).integrableOn) hS
          exact hpoint
      _ = P * ∫ xi in S, G xi := by rw [MeasureTheory.integral_const_mul]
      _ ≤ P * ∑ p ∈ m1Range ×ˢ ellRange,
          ∫ xi in sourceMediumPairWindow M3 B p, H p xi := by
        apply mul_le_mul_of_nonneg_left _ hP
        exact setIntegral_sourceMediumLocalizedPairSum_le
          m1Range ellRange M3 B S H
          (fun p hp xi => by dsimp only [H]; positivity) hHint
  refine hregion.trans ?_
  apply mul_le_mul_of_nonneg_left _ hP
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro p hp
  have hp1 : p.1 ∈ m1Range := (Finset.mem_product.mp hp).1
  dsimp only [H]
  rw [MeasureTheory.integral_const_mul]
  rw [setIntegral_correctedM2Inner_sq_affine
    m2Range fhat hM3 hB p.1 p.2 (hm1 p.1 hp1) hm2pos]
  ring

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.sourceMediumLocalizedPairSum_eq_indicatorSum
#print axioms GuthMaynardJIteration.integral_sourceMediumLocalizedPairSum
#print axioms GuthMaynardJIteration.setIntegral_sourceMediumLocalizedPairSum_le
#print axioms GuthMaynardJIteration.setIntegral_sourceMediumPairWindow_affine
#print axioms GuthMaynardJIteration.sourceCorrectedM2FourierInner_at_affine
#print axioms GuthMaynardJIteration.norm_sourceCorrectedM2FourierInner_at_affine_sq
#print axioms GuthMaynardJIteration.setIntegral_correctedM2Inner_sq_affine
#print axioms GuthMaynardJIteration.integrableOn_correctedM2Inner_sq_sourceMediumPairWindow
#print axioms GuthMaynardJIteration.setIntegral_norm_sourceFirstPoissonLocalizedPairSum_sq_le_affine
