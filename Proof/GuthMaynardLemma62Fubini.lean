import GuthMaynardLemma62MellinInsertion

/-!
# The Fubini step in Guth--Maynard Lemma 6.2

This file certifies the interchange between the compact `u` integral and the
vertical Mellin integral.  We use an exponential form of the complex powers,
which is literally equal to the source integrand on `[1,2]` and makes joint
measurability in `(u,r)` transparent.
-/

namespace GuthMaynardLemma62Fubini

open Real Complex Set MeasureTheory
open scoped FourierTransform SchwartzMap
open GuthMaynardMellinRapidDecay
open GuthMaynardSectionThreeCutoff
open GuthMaynardLemma62FarTail
open GuthMaynardLemma62MellinInversion
open GuthMaynardLemma62MellinInsertion

noncomputable section

def mellinPowerExp (u r : ℝ) : ℂ :=
  Complex.exp
    (((-(1 : ℂ) - (r : ℂ) * Complex.I)) * (Real.log u : ℂ))

def oscillatoryPowerExp (u t : ℝ) : ℂ :=
  Complex.exp
    ((Complex.I * (t : ℂ)) * (Real.log u : ℂ))

def sectionThreeMellinFubiniKernel (t xi u r : ℝ) : ℂ :=
  sectionThreeFourierPhase xi u *
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (mellinPowerExp u r *
        mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I))) *
    oscillatoryPowerExp u t

theorem mellinPowerExp_eq_cpow {u r : ℝ} (hu : 0 < u) :
    mellinPowerExp u r =
      (u : ℂ) ^ (-((1 : ℂ) + r * Complex.I)) := by
  unfold mellinPowerExp
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne')]
  have hlog : Complex.log (u : ℂ) = (Real.log u : ℂ) := by
    rw [← Complex.ofReal_log hu.le]
  rw [hlog]
  congr 1
  ring

theorem oscillatoryPowerExp_eq_cpow {u t : ℝ} (hu : 0 < u) :
    oscillatoryPowerExp u t = (u : ℂ) ^ (Complex.I * (t : ℂ)) := by
  unfold oscillatoryPowerExp
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne')]
  have hlog : Complex.log (u : ℂ) = (Real.log u : ℂ) := by
    rw [← Complex.ofReal_log hu.le]
  rw [hlog]
  congr 1
  ring

theorem continuous_mellin_line_sectionThree :
    Continuous (fun r : ℝ =>
      mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)) := by
  have hcont : Continuous (fun r : ℝ =>
      ((𝓕 sectionThreeMellinLogSchwartz : 𝓢(ℝ, ℂ))
        (r / (2 * Real.pi)))) :=
    (𝓕 sectionThreeMellinLogSchwartz : 𝓢(ℝ, ℂ)).continuous.comp
      (continuous_id.div_const (2 * Real.pi : ℝ))
  apply hcont.congr
  intro r
  rw [mellin_line_one_eq_fourier_logLift]
  exact congrFun
    (SchwartzMap.fourier_coe sectionThreeMellinLogSchwartz).symm _

theorem measurable_sectionThreeMellinFubiniKernel (t xi : ℝ) :
    Measurable (fun z : ℝ × ℝ =>
      sectionThreeMellinFubiniKernel t xi z.1 z.2) := by
  unfold sectionThreeMellinFubiniKernel sectionThreeFourierPhase
    mellinPowerExp oscillatoryPowerExp
  have hphase : Measurable (fun z : ℝ × ℝ =>
      Complex.exp (((-2 * Real.pi * z.1 * xi : ℝ) : ℂ) * Complex.I)) := by
    measurability
  have hlog : Measurable (fun z : ℝ × ℝ =>
      (Real.log z.1 : ℂ)) :=
    Complex.measurable_ofReal.comp (Real.measurable_log.comp measurable_fst)
  have hr : Measurable (fun z : ℝ × ℝ => (z.2 : ℂ)) :=
    Complex.measurable_ofReal.comp measurable_snd
  have hc : Measurable (fun _z : ℝ × ℝ =>
      (((1 / (2 * Real.pi) : ℝ) : ℂ))) := measurable_const
  have hnegOne : Measurable (fun _z : ℝ × ℝ => (-(1 : ℂ))) := measurable_const
  have hI : Measurable (fun _z : ℝ × ℝ => Complex.I) := measurable_const
  have ht : Measurable (fun _z : ℝ × ℝ => (t : ℂ)) := measurable_const
  have hMellin : Measurable (fun z : ℝ × ℝ =>
      mellin sectionThreeCutoff ((1 : ℂ) + (z.2 : ℂ) * Complex.I)) :=
    continuous_mellin_line_sectionThree.measurable.comp measurable_snd
  exact (hphase.mul <|
    hc.mul
      ((((hnegOne.sub (hr.mul hI)).mul hlog).cexp).mul hMellin)).mul
    (((hI.mul ht).mul hlog).cexp)

theorem norm_mellinPowerExp {u r : ℝ} (hu : 0 < u) :
    ‖mellinPowerExp u r‖ = u⁻¹ := by
  unfold mellinPowerExp
  rw [Complex.norm_exp]
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  norm_num
  rw [Real.exp_neg, Real.exp_log hu]

theorem norm_oscillatoryPowerExp (u t : ℝ) :
    ‖oscillatoryPowerExp u t‖ = 1 := by
  unfold oscillatoryPowerExp
  rw [Complex.norm_exp]
  simp

theorem norm_sectionThreeFourierPhase (xi u : ℝ) :
    ‖sectionThreeFourierPhase xi u‖ = 1 := by
  unfold sectionThreeFourierPhase
  rw [Complex.norm_exp]
  simp

theorem norm_sectionThreeMellinFubiniKernel
    {t xi u r : ℝ} (hu : 0 < u) :
    ‖sectionThreeMellinFubiniKernel t xi u r‖ =
      ((1 / (2 * Real.pi)) * u⁻¹) *
        ‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖ := by
  unfold sectionThreeMellinFubiniKernel
  rw [norm_mul, norm_mul, norm_mul, norm_mul,
    norm_sectionThreeFourierPhase, norm_oscillatoryPowerExp,
    norm_mellinPowerExp hu, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  ring

/-- Absolute integrability of the exact bivariate Mellin kernel.  This is the
load-bearing hypothesis of the Fubini interchange in the published proof. -/
theorem integrable_sectionThreeMellinFubiniKernel (t xi : ℝ) :
    Integrable
      (fun z : ℝ × ℝ =>
        sectionThreeMellinFubiniKernel t xi z.1 z.2)
      ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume) := by
  have hOne : Integrable (fun _u : ℝ => (1 : ℝ))
      (volume.restrict (Set.Icc (1 : ℝ) 2)) := by
    exact integrableOn_const (by simp [Real.volume_Icc])
  have hMellin : Integrable (fun r : ℝ =>
      ‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖) :=
    sectionThreeCutoff_verticalIntegrable.norm
  have hMajorant := hOne.mul_prod hMellin
  apply hMajorant.mono'
  · exact (measurable_sectionThreeMellinFubiniKernel t xi).aestronglyMeasurable
  · apply (MeasureTheory.Measure.ae_prod_iff_ae_ae (measurableSet_le
      (measurable_sectionThreeMellinFubiniKernel t xi).norm
      (measurable_const.mul
        (continuous_mellin_line_sectionThree.measurable.comp measurable_snd).norm))).2
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    filter_upwards with r
    have huPos : 0 < u := by linarith [hu.1]
    rw [norm_sectionThreeMellinFubiniKernel huPos]
    have hc : 1 / (2 * Real.pi) ≤ 1 := by
      have hpi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
      simpa [one_div] using
        ((inv_le_one₀ (by positivity : 0 < 2 * Real.pi)).2 hpi)
    have huInv : u⁻¹ ≤ 1 := (inv_le_one₀ huPos).2 hu.1
    have hcoef : (1 / (2 * Real.pi)) * u⁻¹ ≤ 1 :=
      mul_le_one₀ hc (inv_nonneg.mpr huPos.le) huInv
    calc
      ((1 / (2 * Real.pi)) * u⁻¹) *
          ‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖ ≤
        1 * ‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖ := by
          exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
      _ = _ := by simp [Function.comp_apply, mul_comm]

/-- Exact Fubini interchange used on p.19 of Guth--Maynard. -/
theorem sectionThreeMellinFubini_swap (t xi : ℝ) :
    (∫ u : ℝ in Set.Icc (1 : ℝ) 2,
      ∫ r : ℝ, sectionThreeMellinFubiniKernel t xi u r) =
      ∫ r : ℝ,
        ∫ u : ℝ in Set.Icc (1 : ℝ) 2,
          sectionThreeMellinFubiniKernel t xi u r := by
  exact integral_integral_swap
    (integrable_sectionThreeMellinFubiniKernel t xi)

/-- The same absolute-integrability statement on any compact interval bounded
away from zero.  The source uses this with `[a,b]=[1/m,2M/m]`, before making
the common substitution `v=Nmu`. -/
theorem integrable_sectionThreeMellinFubiniKernel_Icc
    (t xi : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Integrable
      (fun z : ℝ × ℝ =>
        sectionThreeMellinFubiniKernel t xi z.1 z.2)
      ((volume.restrict (Set.Icc a b)).prod volume) := by
  let C : ℝ := (1 / (2 * Real.pi)) * a⁻¹
  have hC : 0 ≤ C := by
    unfold C
    positivity
  have hConst : Integrable (fun _u : ℝ => C)
      (volume.restrict (Set.Icc a b)) := by
    exact integrableOn_const (by simp [Real.volume_Icc])
  have hMellin : Integrable (fun r : ℝ =>
      ‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖) :=
    sectionThreeCutoff_verticalIntegrable.norm
  have hMajorant := hConst.mul_prod hMellin
  apply hMajorant.mono'
  · exact (measurable_sectionThreeMellinFubiniKernel t xi).aestronglyMeasurable
  · apply (MeasureTheory.Measure.ae_prod_iff_ae_ae (measurableSet_le
      (measurable_sectionThreeMellinFubiniKernel t xi).norm
      (measurable_const.mul
        (continuous_mellin_line_sectionThree.measurable.comp measurable_snd).norm))).2
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    filter_upwards with r
    have huPos : 0 < u := ha.trans_le hu.1
    rw [norm_sectionThreeMellinFubiniKernel huPos]
    have hInv : u⁻¹ ≤ a⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le ha hu.1
    have hcoef : (1 / (2 * Real.pi)) * u⁻¹ ≤ C := by
      unfold C
      gcongr
    exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)

theorem sectionThreeMellinFubini_swap_Icc
    (t xi : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ u : ℝ in Set.Icc a b,
      ∫ r : ℝ, sectionThreeMellinFubiniKernel t xi u r) =
      ∫ r : ℝ,
        ∫ u : ℝ in Set.Icc a b,
          sectionThreeMellinFubiniKernel t xi u r := by
  exact integral_integral_swap
    (integrable_sectionThreeMellinFubiniKernel_Icc t xi ha hab)

/-- The literal Fourier coefficient after Mellin inversion and the justified
Fubini interchange.  This is the source formula immediately before the
substitution `v = N|m|u`. -/
theorem sectionThreeFourierCoefficient_eq_mellinFubini
    (t xi : ℝ) :
    sectionThreeFourierCoefficient t xi =
      ∫ r : ℝ,
        ∫ u : ℝ in Set.Icc (1 : ℝ) 2,
          sectionThreeMellinFubiniKernel t xi u r := by
  rw [sectionThreeFourierCoefficient_eq_mellinInserted]
  calc
    (∫ u : ℝ in Set.Icc (1 : ℝ) 2,
        sectionThreeFourierPhase xi u *
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            sectionThreeMellinLineIntegral u) *
          (u : ℂ) ^ (Complex.I * (t : ℂ))) =
      ∫ u : ℝ in Set.Icc (1 : ℝ) 2,
        ∫ r : ℝ, sectionThreeMellinFubiniKernel t xi u r := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      have huPos : 0 < u := by linarith [hu.1]
      unfold sectionThreeMellinFubiniKernel sectionThreeMellinLineIntegral
      simp_rw [← mellinPowerExp_eq_cpow huPos]
      rw [← oscillatoryPowerExp_eq_cpow huPos]
      rw [MeasureTheory.integral_mul_const]
      rw [← MeasureTheory.integral_const_mul]
      rw [← MeasureTheory.integral_const_mul]
    _ = _ := sectionThreeMellinFubini_swap t xi

end

end GuthMaynardLemma62Fubini

#print axioms GuthMaynardLemma62Fubini.sectionThreeMellinFubini_swap
#print axioms GuthMaynardLemma62Fubini.sectionThreeFourierCoefficient_eq_mellinFubini
