import GuthMaynardLemma295LineTwoFubini
import GuthMaynardLemma295CriticalSqrtPolynomial
import GuthMaynardLemma295CriticalTailIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Full-line integrability of the literal initial and reflected vertical integrands. -/
namespace GuthMaynardLemma295VerticalIntegrability

open Complex Real Set MeasureTheory
open GuthMaynardLemma295FiniteContour
open GuthMaynardLemma295ReflectedFiniteContour
open GuthMaynardLemma295MellinLineTwo
open GuthMaynardLemma295LineTwoFubini
open GuthMaynardLemma295CutoffAnalytic
open GuthMaynardLemma295MellinPolynomialDecay
open GuthMaynardLemma295CriticalTailIntegral
open GuthMaynardMellinTail
open GuthMaynardJutilaReflection2941
open GuthMaynardLemma295MellinAllLines
open GuthMaynardLemma295ThetaBounds
open GuthMaynardLemma295CriticalMajorant
open GuthMaynardLemma295ExactMScale

noncomputable section

theorem integrable_lineTwoZetaIntegrand
    {N : ℝ} (hN : 0 < N) (g : ℝ) :
    Integrable (lineTwoZetaIntegrand N g) := by
  have hs : Summable fun n : ℕ => 1 / (n + 1 : ℝ) ^ 2 := by
    have h := (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
    simpa [abs_of_nonneg, Real.rpow_two] using h
  have hm : Integrable (fun r : ℝ => mellin sourceHZero (lineTwoPoint r)) := by
    simpa [lineTwoPoint] using sourceHZero_verticalIntegrable_two
  have hnormsum (r : ℝ) : Summable fun n : ℕ => ‖lineTwoTerm N g n r‖ := by
    have h := (hs.mul_left (N ^ 2)).mul_right ‖mellin sourceHZero (lineTwoPoint r)‖
    exact h.congr (fun n => by rw [norm_lineTwoTerm hN]; ring)
  have heq : lineTwoZetaIntegrand N g = fun r => ∑' n, lineTwoTerm N g n r := by
    funext r
    exact (tsum_lineTwoTerm_eq_zetaIntegrand N g r).symm
  rw [heq]
  apply (hm.norm.const_mul (N ^ 2 * ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ 2)).mono'
  · exact AEStronglyMeasurable.tsum (fun n => (integrable_lineTwoTerm hN g n).aestronglyMeasurable)
  · filter_upwards [] with r
    calc
      ‖∑' n, lineTwoTerm N g n r‖ ≤ ∑' n, ‖lineTwoTerm N g n r‖ :=
        norm_tsum_le_tsum_norm (hnormsum r)
      _ = (N ^ 2 * ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ 2) *
          ‖mellin sourceHZero (lineTwoPoint r)‖ := by
        simp_rw [norm_lineTwoTerm hN, div_eq_mul_inv]
        rw [tsum_mul_right, tsum_mul_left]
        simp only [one_mul]

theorem continuous_reflectedFinite_vertical
    {N : ℝ} (hN : 0 < N) (g : ℝ) (K : ℕ)
    {a : ℝ} (ha : a < 1) :
    Continuous (fun t : ℝ => lemma295ReflectedFiniteIntegrand N g K
      ((a : ℂ) + t * I)) := by
  apply continuous_iff_continuousAt.2
  intro t
  exact (differentiableAt_lemma295ReflectedFiniteIntegrand hN g K
    (by simpa using ha)).continuousAt.comp (by fun_prop)

theorem integrable_reflectedFinite_critical
    {N : ℝ} (hN : 0 < N) (g : ℝ) (K : ℕ) :
    Integrable (fun t : ℝ => lemma295ReflectedFiniteIntegrand N g K
      (((1/2 : ℝ) : ℂ) + t * I)) := by
  let C : ℝ := Real.sqrt N * K *
    GuthMaynardLemma295MellinPolynomialDecay.sourceMellinDecayConstantAt (1/2) 2
  apply (integrable_inv_one_add_sq.const_mul C).mono'
  · exact (continuous_reflectedFinite_vertical hN g K (by norm_num)).aestronglyMeasurable
  · filter_upwards [] with t
    have h := GuthMaynardLemma295CriticalTailPointwise.norm_lemma295CriticalIntegrand_le_arbitraryOrder
      hN K 2 g (-t)
    have hw := GuthMaynardLemma295CriticalExactWeld.norm_reflectedFinite_critical_eq N g K (-t)
    simp only [Complex.ofReal_neg, neg_mul, sub_neg_eq_add] at hw
    rw [hw]
    simpa [C, abs_neg, sq_abs, div_eq_mul_inv, mul_assoc] using h

theorem integrable_raw_lineTwo
    {N : ℝ} (hN : 0 < N) (g : ℝ) :
    Integrable (fun t : ℝ => lemma295RawIntegrand N g ((2 : ℂ) + t * I)) := by
  simpa only [lemma295RawIntegrand, lineTwoZetaIntegrand,
    shiftedLineTwoPoint, lineTwoPoint] using integrable_lineTwoZetaIntegrand hN g

theorem integrable_reflectedFinite_critical_neg
    {N : ℝ} (hN : 0 < N) (g : ℝ) (K : ℕ) :
    Integrable (fun t : ℝ => lemma295ReflectedFiniteIntegrand N g K
      (((1 / 2 : ℝ) : ℂ) - t * I)) := by
  simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using
    (integrable_reflectedFinite_critical hN g K).comp_neg

theorem norm_reflectedFinite_critical_le_arbitraryOrder
    {N : ℝ} (hN : 0 < N) (K k : ℕ) (g t : ℝ) :
    ‖lemma295ReflectedFiniteIntegrand N g K
        (((1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      Real.sqrt N * K *
        (sourceMellinDecayConstantAt (1 / 2) k / (1 + |t| ^ k)) := by
  have hw := GuthMaynardLemma295CriticalExactWeld.norm_reflectedFinite_critical_eq N g K (-t)
  simp only [Complex.ofReal_neg, neg_mul, sub_neg_eq_add] at hw
  rw [hw]
  simpa only [abs_neg] using
    GuthMaynardLemma295CriticalTailPointwise.norm_lemma295CriticalIntegrand_le_arbitraryOrder
      hN K k g (-t)

 theorem norm_reflectedFinite_critical_positiveTail_le
    {N : ℝ} (hN : 0 < N) (K k : ℕ) (g : ℝ) {R : ℝ}
    (hk : 2 ≤ k) (hR : 0 < R) :
    ‖∫ t : ℝ in Ioi R, lemma295ReflectedFiniteIntegrand N g K (((1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      (Real.sqrt N * K * sourceMellinDecayConstantAt (1 / 2) k) *
        (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)) := by
  apply norm_positiveNatPowerTail_le hk hR
  intro t ht
  have ht0 : 0 < |t| := abs_pos.mpr (ne_of_gt (hR.trans ht))
  have hp := norm_reflectedFinite_critical_le_arbitraryOrder hN K k g t
  have hC0 : 0 ≤ Real.sqrt N * K := mul_nonneg (Real.sqrt_nonneg _) (by positivity)
  calc
    ‖lemma295ReflectedFiniteIntegrand N g K (((1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
        Real.sqrt N * K *
          (sourceMellinDecayConstantAt (1 / 2) k / (1 + |t| ^ k)) := hp
    _ = (Real.sqrt N * K * sourceMellinDecayConstantAt (1 / 2) k) *
          (1 / (1 + |t| ^ k)) := by ring
    _ ≤ (Real.sqrt N * K * sourceMellinDecayConstantAt (1 / 2) k) *
          Real.rpow t (-(k : ℝ)) := by
      have hinv : 1 / (1 + |t| ^ k) ≤ Real.rpow t (-(k : ℝ)) := by
        simpa [abs_of_pos (hR.trans ht)] using
          inv_one_add_abs_pow_le_rpow_neg k ht0
      exact mul_le_mul_of_nonneg_left
        hinv (mul_nonneg
          (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))
          (sourceMellinDecayConstantAt_nonneg _ _))

theorem norm_reflectedFinite_critical_negativeTail_le
    {N : ℝ} (hN : 0 < N) (K k : ℕ) (g : ℝ) {R : ℝ}
    (hk : 2 ≤ k) (hR : 0 < R) :
    ‖∫ t : ℝ in Iic (-R), lemma295ReflectedFiniteIntegrand N g K (((1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      (Real.sqrt N * K * sourceMellinDecayConstantAt (1 / 2) k) *
        (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)) := by
  apply norm_negativeNatPowerTail_le hk hR
  intro t ht
  have htneg : t < 0 := lt_of_lt_of_le ht (neg_nonpos.mpr hR.le)
  have ht0 : 0 < |t| := abs_pos.mpr (ne_of_lt htneg)
  have hp := norm_reflectedFinite_critical_le_arbitraryOrder hN K k g t
  calc
    ‖lemma295ReflectedFiniteIntegrand N g K (((1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
        Real.sqrt N * K *
          (sourceMellinDecayConstantAt (1 / 2) k / (1 + |t| ^ k)) := hp
    _ = (Real.sqrt N * K * sourceMellinDecayConstantAt (1 / 2) k) *
          (1 / (1 + |t| ^ k)) := by ring
    _ ≤ (Real.sqrt N * K * sourceMellinDecayConstantAt (1 / 2) k) *
          Real.rpow (-t) (-(k : ℝ)) := by
      have hinv : 1 / (1 + |t| ^ k) ≤ Real.rpow (-t) (-(k : ℝ)) := by
        simpa [abs_of_neg htneg] using
          inv_one_add_abs_pow_le_rpow_neg k ht0
      exact mul_le_mul_of_nonneg_left
        hinv (mul_nonneg
          (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))
          (sourceMellinDecayConstantAt_nonneg _ _))


theorem norm_reflectedFinite_critical_neg_le_arbitraryOrder
    {N : ℝ} (hN : 0 < N) (K k : ℕ) (g t : ℝ) :
    ‖lemma295ReflectedFiniteIntegrand N g K
        (((1 / 2 : ℝ) : ℂ) - t * I)‖ ≤
      Real.sqrt N * K *
        (sourceMellinDecayConstantAt (1 / 2) k / (1 + |t| ^ k)) := by
  rw [GuthMaynardLemma295CriticalExactWeld.norm_reflectedFinite_critical_eq]
  exact GuthMaynardLemma295CriticalTailPointwise.norm_lemma295CriticalIntegrand_le_arbitraryOrder
    hN K k g t


 theorem norm_reflectedFinite_critical_neg_positiveTail_le
    {N : ℝ} (hN : 0 < N) (K k : ℕ) (g : ℝ) {R : ℝ}
    (hk : 2 ≤ k) (hR : 0 < R) :
    ‖∫ t : ℝ in Ioi R, lemma295ReflectedFiniteIntegrand N g K (((1 / 2 : ℝ) : ℂ) - t * I)‖ ≤
      (Real.sqrt N * K * sourceMellinDecayConstantAt (1 / 2) k) *
        (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)) := by
  apply norm_positiveNatPowerTail_le hk hR
  intro t ht
  have ht0 : 0 < |t| := abs_pos.mpr (ne_of_gt (hR.trans ht))
  have hp := norm_reflectedFinite_critical_neg_le_arbitraryOrder hN K k g t
  have hC0 : 0 ≤ Real.sqrt N * K := mul_nonneg (Real.sqrt_nonneg _) (by positivity)
  calc
    ‖lemma295ReflectedFiniteIntegrand N g K (((1 / 2 : ℝ) : ℂ) - t * I)‖ ≤
        Real.sqrt N * K *
          (sourceMellinDecayConstantAt (1 / 2) k / (1 + |t| ^ k)) := hp
    _ = (Real.sqrt N * K * sourceMellinDecayConstantAt (1 / 2) k) *
          (1 / (1 + |t| ^ k)) := by ring
    _ ≤ (Real.sqrt N * K * sourceMellinDecayConstantAt (1 / 2) k) *
          Real.rpow t (-(k : ℝ)) := by
      have hinv : 1 / (1 + |t| ^ k) ≤ Real.rpow t (-(k : ℝ)) := by
        simpa [abs_of_pos (hR.trans ht)] using
          inv_one_add_abs_pow_le_rpow_neg k ht0
      exact mul_le_mul_of_nonneg_left
        hinv (mul_nonneg
          (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))
          (sourceMellinDecayConstantAt_nonneg _ _))

theorem norm_reflectedFinite_critical_neg_negativeTail_le
    {N : ℝ} (hN : 0 < N) (K k : ℕ) (g : ℝ) {R : ℝ}
    (hk : 2 ≤ k) (hR : 0 < R) :
    ‖∫ t : ℝ in Iic (-R), lemma295ReflectedFiniteIntegrand N g K (((1 / 2 : ℝ) : ℂ) - t * I)‖ ≤
      (Real.sqrt N * K * sourceMellinDecayConstantAt (1 / 2) k) *
        (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)) := by
  apply norm_negativeNatPowerTail_le hk hR
  intro t ht
  have htneg : t < 0 := lt_of_lt_of_le ht (neg_nonpos.mpr hR.le)
  have ht0 : 0 < |t| := abs_pos.mpr (ne_of_lt htneg)
  have hp := norm_reflectedFinite_critical_neg_le_arbitraryOrder hN K k g t
  calc
    ‖lemma295ReflectedFiniteIntegrand N g K (((1 / 2 : ℝ) : ℂ) - t * I)‖ ≤
        Real.sqrt N * K *
          (sourceMellinDecayConstantAt (1 / 2) k / (1 + |t| ^ k)) := hp
    _ = (Real.sqrt N * K * sourceMellinDecayConstantAt (1 / 2) k) *
          (1 / (1 + |t| ^ k)) := by ring
    _ ≤ (Real.sqrt N * K * sourceMellinDecayConstantAt (1 / 2) k) *
          Real.rpow (-t) (-(k : ℝ)) := by
      have hinv : 1 / (1 + |t| ^ k) ≤ Real.rpow (-t) (-(k : ℝ)) := by
        simpa [abs_of_neg htneg] using
          inv_one_add_abs_pow_le_rpow_neg k ht0
      exact mul_le_mul_of_nonneg_left
        hinv (mul_nonneg
          (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))
          (sourceMellinDecayConstantAt_nonneg _ _))

theorem norm_integral_reflectedFinite_critical_neg_le
    {N : ℝ} (hN : 0 < N) (K : ℕ) (g R : ℝ) :
    ‖∫ t : ℝ in Set.Icc (-R) R, lemma295ReflectedFiniteIntegrand N g K (((1 / 2 : ℝ) : ℂ) - t * I)‖ ≤
      sourceMellinDecayConstant (1 / 2) *
        lemma295CentralMajorant N K g R := by
  let C := sourceMellinDecayConstant (1 / 2)
  let major : ℝ → ℝ := fun t =>
    C * (Real.sqrt N *
      (‖lemma295ReflectedPolynomial K (g + t)‖ / (1 + t ^ 2)))
  have hpoly : Continuous (fun t : ℝ =>
      lemma295ReflectedPolynomial K (g + t)) := by
    unfold lemma295ReflectedPolynomial GuthMaynardHeathBrownMajorant.dirichletPhase
    fun_prop
  have hmajorContinuous : Continuous major := by
    dsimp [major, C]
    apply Continuous.const_mul
    apply Continuous.const_mul
    exact hpoly.norm.div
      (continuous_const.add (continuous_id.pow 2)) (fun t => by positivity)
  have hmajorInt : Integrable major (volume.restrict (Set.Icc (-R) R)) :=
    hmajorContinuous.continuousOn.integrableOn_compact isCompact_Icc
  calc
    ‖∫ t : ℝ in Set.Icc (-R) R, lemma295ReflectedFiniteIntegrand N g K (((1 / 2 : ℝ) : ℂ) - t * I)‖ ≤
        ∫ t : ℝ in Set.Icc (-R) R, major t :=
      norm_integral_le_of_norm_le hmajorInt
        (Filter.Eventually.of_forall fun t => by
          exact GuthMaynardLemma295CriticalExactWeld.norm_reflectedFinite_critical_le hN K g t)
    _ = C * (Real.sqrt N *
        ∫ t : ℝ in Set.Icc (-R) R,
          ‖lemma295ReflectedPolynomial K (g + t)‖ / (1 + t ^ 2)) := by
      simp only [major]
      rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
    _ = sourceMellinDecayConstant (1 / 2) *
        lemma295CentralMajorant N K g R := by
      rfl

theorem norm_integral_le_central_add_tails
    {F : ℝ → ℂ} (hF : Integrable F) {R : ℝ} (hR : 0 ≤ R)
    {C E : ℝ}
    (hc : ‖∫ t : ℝ in Icc (-R) R, F t‖ ≤ C)
    (hn : ‖∫ t : ℝ in Iic (-R), F t‖ ≤ E)
    (hp : ‖∫ t : ℝ in Ioi R, F t‖ ≤ E) :
    ‖∫ t : ℝ, F t‖ ≤ C + 2 * E := by
  have hsplit := intervalIntegral.integral_Iic_add_Ioi
    (b := -R) hF.integrableOn hF.integrableOn
  have hmid := intervalIntegral.integral_interval_add_Ioi
    (a := -R) (b := R) hF.integrableOn hF.integrableOn
  rw [intervalIntegral.integral_of_le (by linarith : -R ≤ R),
    ← integral_Icc_eq_integral_Ioc] at hmid
  rw [← hsplit, ← hmid]
  calc
    ‖(∫ t : ℝ in Iic (-R), F t) +
        ((∫ t : ℝ in Icc (-R) R, F t) + ∫ t : ℝ in Ioi R, F t)‖ ≤
      ‖∫ t : ℝ in Iic (-R), F t‖ +
        (‖∫ t : ℝ in Icc (-R) R, F t‖ + ‖∫ t : ℝ in Ioi R, F t‖) :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ C + 2 * E := by linarith

theorem norm_integral_reflectedFinite_critical_neg_le_central_add_tails
    {N : ℝ} (hN : 0 < N) (K k : ℕ) (g : ℝ) {R : ℝ}
    (hk : 2 ≤ k) (hR : 0 < R) :
    ‖∫ t : ℝ, lemma295ReflectedFiniteIntegrand N g K
      (((1 / 2 : ℝ) : ℂ) - t * I)‖ ≤
      sourceMellinDecayConstant (1 / 2) * lemma295CentralMajorant N K g R +
        2 * ((Real.sqrt N * K * sourceMellinDecayConstantAt (1 / 2) k) *
          (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1))) := by
  exact norm_integral_le_central_add_tails
    (integrable_reflectedFinite_critical_neg hN g K) hR.le
    (norm_integral_reflectedFinite_critical_neg_le hN K g R)
    (norm_reflectedFinite_critical_neg_negativeTail_le hN K k g hk hR)
    (norm_reflectedFinite_critical_neg_positiveTail_le hN K k g hk hR)

 theorem norm_lemma295CriticalIntegrand_le_sqrtOrder
    {N : ℝ} (hN : 0 < N) (K k : ℕ) (g t : ℝ) :
    ‖lemma295CriticalIntegrand N K g t‖ ≤
      Real.sqrt N * (2 * Real.sqrt K) *
        (sourceMellinDecayConstantAt (1 / 2) k /
          (1 + |t| ^ k)) := by
  have htheta := norm_sourceZetaTheta_criticalLine_eq_one (-(g + t))
  have htheta' :
      ‖sourceZetaTheta (((1 / 2 : ℝ) : ℂ) - (g + t) * I)‖ = 1 := by
    have harg :
        (((1 / 2 : ℝ) : ℂ) - (g + t) * I) =
          ((1 / 2 : ℝ) : ℂ) + ((-(g + t) : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [harg]
    exact htheta
  have hscale := norm_cpow_criticalScale_eq_sqrt hN g t
  have hpoly := GuthMaynardLemma295CriticalSqrtPolynomial.norm_lemma295ReflectedPolynomial_nat_le_sqrt K (g + t)
  have hmellin :=
    norm_mellin_sourceHZero_vertical_le_inv_one_add_abs_pow
      (1 / 2) k (-t)
  have hmellin' :
      ‖mellin sourceHZero (((1 / 2 : ℝ) : ℂ) - t * I)‖ ≤
        sourceMellinDecayConstantAt (1 / 2) k / (1 + |t| ^ k) := by
    simpa [sub_eq_add_neg] using hmellin
  unfold lemma295CriticalIntegrand
  repeat' rw [norm_mul]
  rw [htheta', one_mul, hscale]
  have hK0 : 0 ≤ 2 * Real.sqrt K := by positivity
  have hsqrt0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left hpoly hsqrt0) hmellin'
    (norm_nonneg _) (mul_nonneg hsqrt0 hK0)
theorem norm_positiveTail_of_inv_pow_envelope
    {F : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C) (k : ℕ) (hk : 2 ≤ k)
    {R : ℝ} (hR : 0 < R)
    (hb : ∀ t, ‖F t‖ ≤ C / (1 + |t| ^ k)) :
    ‖∫ t : ℝ in Ioi R, F t‖ ≤
      C * (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)) := by
  apply norm_positiveNatPowerTail_le hk hR
  intro t ht
  calc
    ‖F t‖ ≤ C / (1 + |t| ^ k) := hb t
    _ = C * (1 / (1 + |t| ^ k)) := by ring
    _ ≤ C * t ^ (-(k : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      simpa [abs_of_pos (hR.trans ht)] using
        inv_one_add_abs_pow_le_rpow_neg k (abs_pos.mpr (ne_of_gt (hR.trans ht)))

theorem norm_negativeTail_of_inv_pow_envelope
    {F : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C) (k : ℕ) (hk : 2 ≤ k)
    {R : ℝ} (hR : 0 < R)
    (hb : ∀ t, ‖F t‖ ≤ C / (1 + |t| ^ k)) :
    ‖∫ t : ℝ in Iic (-R), F t‖ ≤
      C * (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)) := by
  rw [← integral_comp_neg_Ioi]
  apply norm_positiveTail_of_inv_pow_envelope hC k hk hR
  intro t
  simpa only [abs_neg] using hb (-t)

/-- Uniform exact-length critical estimate, including arbitrarily small positive N. -/
theorem exists_norm_integral_reflectedFinite_critical_exactM_le
    {epsilon A : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T N g : ℝ}, 1 ≤ T → 0 < N →
        N ≤ sourceReflectionNumerator29_40 T epsilon →
        let M := reflectedLength29_40 T epsilon N
        let K := ⌊M⌋₊
        let R := Real.rpow T epsilon
        ‖∫ t : ℝ, lemma295ReflectedFiniteIntegrand N g K
          (((1 / 2 : ℝ) : ℂ) - t * I)‖ ≤
          sourceMellinDecayConstant (1 / 2) * lemma295CentralMajorant N M g R +
            C * Real.rpow T (-A) := by
  let k := criticalTailDecayOrder epsilon A
  let C₀ := sourceMellinDecayConstantAt (1 / 2) k
  refine ⟨4 * max 1 C₀, by positivity, ?_⟩
  intro T N g hT hN hNcap
  dsimp only
  let Q := sourceReflectionNumerator29_40 T epsilon
  let M := reflectedLength29_40 T epsilon N
  let K := ⌊M⌋₊
  let R := Real.rpow T epsilon
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hR : 0 < R := Real.rpow_pos_of_pos hTpos _
  have hk : 2 ≤ k := criticalTailDecayOrder_two_le _ _
  have hC₀ : 0 ≤ C₀ := sourceMellinDecayConstantAt_nonneg _ _
  have hQone : 1 ≤ Q := Real.one_le_rpow hT (by linarith : 0 ≤ 1 + epsilon)
  have hQ : 0 ≤ Q := zero_le_one.trans hQone
  have hM : 0 ≤ M := le_trans zero_le_one (one_le_reflectedLength29_40 hTpos hN hNcap)
  have hNK : N * (K : ℝ) ≤ Q := by
    calc
      N * (K : ℝ) ≤ N * M := mul_le_mul_of_nonneg_left (Nat.floor_le hM) hN.le
      _ = Q := N_mul_reflectedLength29_40 hN.ne'
  have hscale : Real.sqrt N * (2 * Real.sqrt K) ≤ 2 * Q := by
    have hs : Real.sqrt (N * (K : ℝ)) ≤ Q := by
      rw [Real.sqrt_le_iff]
      exact ⟨hQ, hNK.trans (by nlinarith)⟩
    rw [Real.sqrt_mul hN.le] at hs
    nlinarith
  let F : ℝ → ℂ := fun t => lemma295ReflectedFiniteIntegrand N g K
    (((1 / 2 : ℝ) : ℂ) - t * I)
  have hb (t : ℝ) : ‖F t‖ ≤ (2 * Q * C₀) / (1 + |t| ^ k) := by
    have hp := norm_lemma295CriticalIntegrand_le_sqrtOrder hN K k g t
    rw [← GuthMaynardLemma295CriticalExactWeld.norm_reflectedFinite_critical_eq] at hp
    calc
      ‖F t‖ ≤ Real.sqrt N * (2 * Real.sqrt K) *
        (C₀ / (1 + |t| ^ k)) := hp
      _ ≤ (2 * Q) * (C₀ / (1 + |t| ^ k)) :=
        mul_le_mul_of_nonneg_right hscale (div_nonneg hC₀ (by positivity))
      _ = (2 * Q * C₀) / (1 + |t| ^ k) := by ring
  have hden : 1 ≤ (k : ℝ) - 1 := by
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hfactor : R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1) ≤
      R ^ (1 - (k : ℝ)) := div_le_self (Real.rpow_nonneg hR.le _) hden
  have hcompose : R ^ (1 - (k : ℝ)) =
      T ^ (epsilon * (1 - (k : ℝ))) :=
    (Real.rpow_mul hTpos.le epsilon (1 - (k : ℝ))).symm
  have hproduct : Q * R ^ (1 - (k : ℝ)) =
      T ^ (1 + 2 * epsilon - epsilon * (k : ℝ)) := by
    dsimp [Q, sourceReflectionNumerator29_40]
    rw [hcompose, ← Real.rpow_add hTpos]
    congr 1
    ring
  have htime : Q * (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)) ≤ T ^ (-A) := by
    calc
      Q * (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)) ≤
          Q * R ^ (1 - (k : ℝ)) := mul_le_mul_of_nonneg_left hfactor hQ
      _ = T ^ (1 + 2 * epsilon - epsilon * (k : ℝ)) := hproduct
      _ ≤ T ^ (-A) := Real.rpow_le_rpow_of_exponent_le hT
        (criticalTailDecayOrder_exponent_le hepsilon)
  have ht : (2 * Q * C₀) * (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)) ≤
      (2 * max 1 C₀) * T ^ (-A) := by
    calc
      _ = (2 * C₀) * (Q * (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1))) := by ring
      _ ≤ (2 * C₀) * T ^ (-A) := mul_le_mul_of_nonneg_left htime (by positivity)
      _ ≤ (2 * max 1 C₀) * T ^ (-A) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num))
          (Real.rpow_nonneg hTpos.le _)
  have hcn : 0 ≤ 2 * Q * C₀ := by positivity
  have hn := (norm_negativeTail_of_inv_pow_envelope hcn k hk hR hb).trans ht
  have hp := (norm_positiveTail_of_inv_pow_envelope hcn k hk hR hb).trans ht
  have hc := norm_integral_reflectedFinite_critical_neg_le hN K g R
  have hmajor : lemma295CentralMajorant N K g R = lemma295CentralMajorant N M g R := by
    dsimp only [K]
    unfold lemma295CentralMajorant
    simp_rw [GuthMaynardLemma295FloorTruncation.lemma295ReflectedPolynomial_floor hM]
  rw [hmajor] at hc
  have hfull := norm_integral_le_central_add_tails
    (integrable_reflectedFinite_critical_neg hN g K) hR.le hc hn hp
  calc
    _ ≤ sourceMellinDecayConstant (1 / 2) * lemma295CentralMajorant N M g R +
        2 * ((2 * max 1 C₀) * T ^ (-A)) := hfull
    _ = _ := by dsimp [M, R]; ring

end
end GuthMaynardLemma295VerticalIntegrability

#print axioms GuthMaynardLemma295VerticalIntegrability.integrable_lineTwoZetaIntegrand
#print axioms GuthMaynardLemma295VerticalIntegrability.integrable_raw_lineTwo
#print axioms GuthMaynardLemma295VerticalIntegrability.integrable_reflectedFinite_critical
#print axioms GuthMaynardLemma295VerticalIntegrability.integrable_reflectedFinite_critical_neg

#print axioms GuthMaynardLemma295VerticalIntegrability.norm_reflectedFinite_critical_positiveTail_le
#print axioms GuthMaynardLemma295VerticalIntegrability.norm_reflectedFinite_critical_negativeTail_le

#print axioms GuthMaynardLemma295VerticalIntegrability.norm_integral_reflectedFinite_critical_neg_le

#print axioms GuthMaynardLemma295VerticalIntegrability.exists_norm_integral_reflectedFinite_critical_exactM_le
