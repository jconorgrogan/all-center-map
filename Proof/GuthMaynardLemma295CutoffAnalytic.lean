import GuthMaynardSourceWZeroProperties
import GuthMaynardMellinRapidDecay
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Analytic facts for the literal cutoff in Lemma 29.5

The proof of Lemma 29.5 starts by asserting that the four-endpoint cutoff is
smooth and compactly supported.  The definitions in the endpoint package are
literally mathlib's `expNegInvGlue` and `Real.smoothTransition`; this file makes
that identification and discharges the smoothness/support claims without an
analytic premise.
-/

namespace GuthMaynardLemma295CutoffAnalytic

open GuthMaynardJutilaReflection2941
open GuthMaynardMellinRapidDecay
open Set
open MeasureTheory
open scoped FourierTransform SchwartzMap

noncomputable section

theorem sourceTheta_eq_expNegInvGlue (x : ℝ) :
    sourceTheta x = expNegInvGlue x := by
  unfold sourceTheta expNegInvGlue
  by_cases hx : 0 < x
  · simp [hx, not_le.mpr hx]
  · simp [hx, le_of_not_gt hx]

theorem sourceUpsilon_eq_smoothTransition (x : ℝ) :
    sourceUpsilon x = Real.smoothTransition x := by
  unfold sourceUpsilon Real.smoothTransition
  rw [sourceTheta_eq_expNegInvGlue, sourceTheta_eq_expNegInvGlue]

@[fun_prop]
theorem sourceTheta_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) sourceTheta := by
  rw [show sourceTheta = expNegInvGlue by
    funext x
    exact sourceTheta_eq_expNegInvGlue x]
  exact expNegInvGlue.contDiff

@[fun_prop]
theorem sourceUpsilon_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) sourceUpsilon := by
  rw [show sourceUpsilon = Real.smoothTransition by
    funext x
    exact sourceUpsilon_eq_smoothTransition x]
  exact Real.smoothTransition.contDiff

@[fun_prop]
theorem sourceWZero_contDiff (a b c d : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun alpha => sourceWZero alpha a b c d) := by
  unfold sourceWZero
  fun_prop

theorem sourceUpsilon_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    sourceUpsilon x = 0 := by
  rw [sourceUpsilon_eq_smoothTransition]
  exact Real.smoothTransition.zero_of_nonpos hx

theorem sourceWZero_eq_zero_left
    {alpha a b c d : ℝ} (hab : a < b) (ha : alpha ≤ a) :
    sourceWZero alpha a b c d = 0 := by
  unfold sourceWZero
  have hden : 0 < b - a := sub_pos.mpr hab
  have hquot : (alpha - a) / (b - a) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ha) hden.le
  rw [sourceUpsilon_eq_zero_of_nonpos hquot, zero_mul]

theorem sourceWZero_eq_zero_right
    {alpha a b c d : ℝ} (hcd : c < d) (hd : d ≤ alpha) :
    sourceWZero alpha a b c d = 0 := by
  unfold sourceWZero
  have hden : 0 < d - c := sub_pos.mpr hcd
  have hquot : (d - alpha) / (d - c) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hd) hden.le
  rw [sourceUpsilon_eq_zero_of_nonpos hquot, mul_zero]

theorem sourceWZero_big_support
    {alpha : ℝ} (h : alpha ∉ Set.Icc (1 / 2 : ℝ) (5 / 2 : ℝ)) :
    sourceWZero alpha (1 / 2) 1 2 (5 / 2) = 0 := by
  rw [Set.mem_Icc, not_and_or] at h
  rcases h with hleft | hright
  · exact sourceWZero_eq_zero_left (by norm_num) (le_of_not_ge hleft)
  · exact sourceWZero_eq_zero_right (by norm_num) (le_of_not_ge hright)

/-- The `g=0` profile whose Mellin transform occurs in the printed proof. -/
def sourceHZero (alpha : ℝ) : ℂ :=
  (sourceWZero alpha (1 / 2) 1 2 (5 / 2) : ℂ)

@[fun_prop]
theorem sourceHZero_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) sourceHZero := by
  unfold sourceHZero
  exact Complex.ofRealCLM.contDiff.comp
    (sourceWZero_contDiff (1 / 2) 1 2 (5 / 2))

theorem sourceHZero_support
    (alpha : ℝ) (h : alpha ∉ Set.Icc (1 / 2 : ℝ) (5 / 2 : ℝ)) :
    sourceHZero alpha = 0 := by
  simp only [sourceHZero, sourceWZero_big_support h, Complex.ofReal_zero]

theorem sourceHZero_hasCompactSupport : HasCompactSupport sourceHZero := by
  apply HasCompactSupport.intro (isCompact_Icc :
    IsCompact (Set.Icc (1 / 2 : ℝ) (5 / 2 : ℝ)))
  exact sourceHZero_support

theorem sourceHZero_mellinConvergent_one :
    MellinConvergent sourceHZero (1 : ℂ) := by
  apply GuthMaynardReflectionMellin.mellinConvergent_one_of_compactSupport
  · exact sourceHZero_contDiff.continuous
  · exact sourceHZero_hasCompactSupport

/-- The literal cutoff already has the quadratic vertical integrability
needed for exact Mellin inversion. -/
theorem sourceHZero_verticalIntegrable_one :
    Complex.VerticalIntegrable (mellin sourceHZero) 1 := by
  let psi : 𝓢(ℝ, ℂ) := mellinLogLiftSchwartz sourceHZero
    (mellinLogLift_hasCompactSupport (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 5 / 2) sourceHZero_support)
    (mellinLogLift_contDiff sourceHZero_contDiff)
  have hpsi : Integrable (fun r : ℝ => (𝓕 psi : 𝓢(ℝ, ℂ)) r) :=
    (𝓕 psi : 𝓢(ℝ, ℂ)).integrable
  have hscale : Integrable (fun r : ℝ =>
      (𝓕 psi : 𝓢(ℝ, ℂ)) ((1 / (2 * Real.pi)) * r)) :=
    hpsi.comp_mul_left' (by positivity)
  unfold Complex.VerticalIntegrable
  apply hscale.congr
  filter_upwards [] with r
  symm
  calc
    mellin sourceHZero ((1 : ℂ) + r * Complex.I) =
        𝓕 (mellinLogLift sourceHZero) (r / (2 * Real.pi)) :=
      mellin_line_one_eq_fourier_logLift sourceHZero r
    _ = (𝓕 psi : 𝓢(ℝ, ℂ)) (r / (2 * Real.pi)) :=
      congrFun (SchwartzMap.fourier_coe psi).symm _
    _ = (𝓕 psi : 𝓢(ℝ, ℂ)) ((1 / (2 * Real.pi)) * r) := by
      congr 2
      ring

/-- Exact inverse Mellin representation for the literal source cutoff. -/
theorem sourceHZero_mellin_inversion_one
    {x : ℝ} (hx : 0 < x) :
    sourceHZero x =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ r : ℝ,
          (x : ℂ) ^ (-((1 : ℂ) + r * Complex.I)) *
            mellin sourceHZero ((1 : ℂ) + r * Complex.I)) := by
  exact GuthMaynardReflectionMellin.mellin_inversion_line_one
    sourceHZero hx sourceHZero_mellinConvergent_one
      sourceHZero_verticalIntegrable_one sourceHZero_contDiff.continuous.continuousAt

/-! ## The exact zeta reflection used after the contour shift -/

/-- This is the source's `Theta(z)` in (29.31), written with mathlib's
completed-zeta gamma factor. -/
def sourceZetaTheta (z : ℂ) : ℂ :=
  Complex.Gammaℝ (1 - z) / Complex.Gammaℝ z

theorem sourceZetaTheta_eq_printed (z : ℂ) :
    sourceZetaTheta z =
      Complex.Gamma ((1 - z) / 2) / Complex.Gamma (z / 2) *
        (Real.pi : ℂ) ^ (z - 1 / 2) := by
  unfold sourceZetaTheta
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def]
  rw [div_eq_mul_inv, mul_inv_rev]
  rw [← Complex.cpow_neg]
  have hp :
      (Real.pi : ℂ) ^ (-(1 - z) / 2) *
          (Real.pi : ℂ) ^ (-(-z / 2)) =
        (Real.pi : ℂ) ^ (z - 1 / 2) := by
    rw [← Complex.cpow_add _ _
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
    congr 1
    ring
  calc
    (Real.pi : ℂ) ^ (-(1 - z) / 2) *
          Complex.Gamma ((1 - z) / 2) *
          ((Complex.Gamma (z / 2))⁻¹ *
            (Real.pi : ℂ) ^ (-(-z / 2))) =
        (Complex.Gamma ((1 - z) / 2) *
          (Complex.Gamma (z / 2))⁻¹) *
          ((Real.pi : ℂ) ^ (-(1 - z) / 2) *
            (Real.pi : ℂ) ^ (-(-z / 2))) := by ring
    _ = _ := by rw [hp]; simp only [div_eq_mul_inv]

/-- The functional equation in precisely the orientation used in the
printed proof of Lemma 29.5.  All exceptional points are explicit. -/
theorem riemannZeta_eq_sourceZetaTheta_mul
    {z : ℂ} (hz : z ≠ 0) (hdual : 1 - z ≠ 0)
    (hgamma : Complex.Gammaℝ z ≠ 0)
    (hgammaDual : Complex.Gammaℝ (1 - z) ≠ 0) :
    riemannZeta z = sourceZetaTheta z * riemannZeta (1 - z) := by
  rw [riemannZeta_def_of_ne_zero hz,
    riemannZeta_def_of_ne_zero hdual]
  rw [completedRiemannZeta_one_sub]
  unfold sourceZetaTheta
  field_simp [hgamma, hgammaDual]

/-- On every line used in the source contour shift, `z=s-ig` is nonzero
as soon as its real part is nonzero. -/
theorem ne_zero_of_re_ne_zero {z : ℂ} (hz : z.re ≠ 0) : z ≠ 0 := by
  intro h
  subst z
  exact hz rfl

end

end GuthMaynardLemma295CutoffAnalytic

#print axioms GuthMaynardLemma295CutoffAnalytic.sourceTheta_contDiff
#print axioms GuthMaynardLemma295CutoffAnalytic.sourceHZero_hasCompactSupport
#print axioms GuthMaynardLemma295CutoffAnalytic.sourceHZero_verticalIntegrable_one
#print axioms GuthMaynardLemma295CutoffAnalytic.sourceHZero_mellin_inversion_one
#print axioms GuthMaynardLemma295CutoffAnalytic.riemannZeta_eq_sourceZetaTheta_mul

namespace GuthMaynardLemma295MellinLineTwo

open MeasureTheory Set
open scoped FourierTransform SchwartzMap
open GuthMaynardMellinRapidDecay
open GuthMaynardLemma295CutoffAnalytic

noncomputable section

def sourceHZeroTimesX (x : ℝ) : ℂ := (x : ℂ) * sourceHZero x

@[fun_prop]
theorem sourceHZeroTimesX_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) sourceHZeroTimesX := by
  unfold sourceHZeroTimesX
  exact (Complex.ofRealCLM.contDiff.comp contDiff_id).mul
    GuthMaynardLemma295CutoffAnalytic.sourceHZero_contDiff

theorem sourceHZeroTimesX_support
    (x : ℝ) (hx : x ∉ Set.Icc (1 / 2 : ℝ) (5 / 2 : ℝ)) :
    sourceHZeroTimesX x = 0 := by
  rw [sourceHZeroTimesX, sourceHZero_support x hx, mul_zero]

theorem sourceHZeroTimesX_hasCompactSupport :
    HasCompactSupport sourceHZeroTimesX := by
  apply HasCompactSupport.intro (isCompact_Icc :
    IsCompact (Set.Icc (1 / 2 : ℝ) (5 / 2 : ℝ)))
  exact sourceHZeroTimesX_support

theorem sourceHZeroTimesX_mellinConvergent_one :
    MellinConvergent sourceHZeroTimesX (1 : ℂ) := by
  apply GuthMaynardReflectionMellin.mellinConvergent_one_of_compactSupport
  · exact sourceHZeroTimesX_contDiff.continuous
  · exact sourceHZeroTimesX_hasCompactSupport

theorem sourceHZero_mellinConvergent_two :
    MellinConvergent sourceHZero (2 : ℂ) := by
  have hw : MellinConvergent
      (fun t : ℝ => (t : ℂ) ^ (1 : ℂ) • sourceHZero t) (1 : ℂ) := by
    simpa only [Complex.cpow_one, one_smul] using
      sourceHZeroTimesX_mellinConvergent_one
  have h := (MellinConvergent.cpow_smul
    (f := sourceHZero) (s := (1 : ℂ)) (a := (1 : ℂ))).mp hw
  convert h using 1 <;> norm_num

private def timesXMellinLogLift (u : ℝ) : ℂ :=
  (Real.exp (-u) : ℂ) * sourceHZeroTimesX (Real.exp (-u))

private theorem timesXMellinLogLift_eq :
    timesXMellinLogLift = mellinLogLift sourceHZeroTimesX := rfl

private theorem sourceHZeroTimesX_verticalIntegrable_one :
    Complex.VerticalIntegrable (mellin sourceHZeroTimesX) 1 := by
  let psi : 𝓢(ℝ, ℂ) := mellinLogLiftSchwartz sourceHZeroTimesX
    (mellinLogLift_hasCompactSupport (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 5 / 2) sourceHZeroTimesX_support)
    (mellinLogLift_contDiff sourceHZeroTimesX_contDiff)
  have hpsi : Integrable (fun r : ℝ => (𝓕 psi : 𝓢(ℝ, ℂ)) r) :=
    (𝓕 psi : 𝓢(ℝ, ℂ)).integrable
  have hscale : Integrable (fun r : ℝ =>
      (𝓕 psi : 𝓢(ℝ, ℂ)) ((1 / (2 * Real.pi)) * r)) :=
    hpsi.comp_mul_left' (by positivity)
  unfold Complex.VerticalIntegrable
  apply hscale.congr
  filter_upwards [] with r
  symm
  calc
    mellin sourceHZeroTimesX ((1 : ℂ) + r * Complex.I) =
        𝓕 (mellinLogLift sourceHZeroTimesX) (r / (2 * Real.pi)) :=
      mellin_line_one_eq_fourier_logLift sourceHZeroTimesX r
    _ = (𝓕 psi : 𝓢(ℝ, ℂ)) (r / (2 * Real.pi)) :=
      congrFun (SchwartzMap.fourier_coe psi).symm _
    _ = (𝓕 psi : 𝓢(ℝ, ℂ)) ((1 / (2 * Real.pi)) * r) := by
      congr 2
      ring

theorem mellin_sourceHZeroTimesX_line_one_eq_line_two (r : ℝ) :
    mellin sourceHZeroTimesX ((1 : ℂ) + r * Complex.I) =
      mellin sourceHZero ((2 : ℂ) + r * Complex.I) := by
  have hfun : sourceHZeroTimesX = fun x : ℝ =>
      (x : ℂ) ^ (1 : ℂ) • sourceHZero x := by
    funext x
    simp [sourceHZeroTimesX]
  rw [hfun]
  have h := mellin_cpow_smul sourceHZero
    ((1 : ℂ) + r * Complex.I) (1 : ℂ)
  convert h using 1 <;> ring

theorem sourceHZero_verticalIntegrable_two :
    Complex.VerticalIntegrable (mellin sourceHZero) 2 := by
  unfold Complex.VerticalIntegrable at *
  exact sourceHZeroTimesX_verticalIntegrable_one.congr
    (Filter.Eventually.of_forall fun r =>
      mellin_sourceHZeroTimesX_line_one_eq_line_two r)

/-- Exact inverse Mellin formula on the printed initial line `Re s=2`. -/
theorem sourceHZero_mellin_inversion_two
    {x : ℝ} (hx : 0 < x) :
    mellinInv 2 (mellin sourceHZero) x = sourceHZero x := by
  exact mellinInv_mellin_eq 2 sourceHZero hx
    sourceHZero_mellinConvergent_two sourceHZero_verticalIntegrable_two
      sourceHZero_contDiff.continuous.continuousAt

/-- Absolute Dirichlet-series expansion on the exact initial contour after
the ordinate shift `s ↦ s - ig`. -/
theorem zeta_shift_dirichletSeries_line_two (g t : ℝ) :
    riemannZeta (((2 : ℂ) + t * Complex.I) - g * Complex.I) =
      ∑' n : ℕ, 1 /
        (n + 1 : ℂ) ^ ((((2 : ℂ) + t * Complex.I) - g * Complex.I)) := by
  apply zeta_eq_tsum_one_div_nat_add_one_cpow
  norm_num

/-- The exponential definition of the source phase is the positive-real
complex power used by Mellin inversion. -/
theorem sourceHPlus_eq_sourceHZero_mul_cpow
    {g alpha : ℝ} (halpha : 0 < alpha) :
    GuthMaynardJutilaReflection2941.sourceHPlus g alpha =
      sourceHZero alpha * (alpha : ℂ) ^ (g * Complex.I) := by
  unfold GuthMaynardJutilaReflection2941.sourceHPlus sourceHZero
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr halpha.ne')]
  rw [← Complex.ofReal_log halpha.le]
  congr 2
  push_cast
  ring

/-- The finite `natRealIoc` sum is exactly the source's sum over all
positive integers; the two omitted endpoints carry zero cutoff weight. -/
theorem tsum_sourceHPlus_eq_sourceHPlusSum
    {N : ℝ} (hN : 0 < N) (g : ℝ) :
    (∑' n : ℕ, GuthMaynardJutilaReflection2941.sourceHPlus g ((n : ℝ) / N)) =
      GuthMaynardJutilaReflection2941.sourceHPlusSum N g := by
  symm
  unfold GuthMaynardJutilaReflection2941.sourceHPlusSum
  rw [tsum_eq_sum]
  intro n hn
  have hnrange : ¬ (N / 2 < (n : ℝ) ∧ (n : ℝ) ≤ 5 * N / 2) := by
    intro h
    apply hn
    exact (GuthMaynardJutilaTransference.mem_natRealIoc_iff
      (by positivity : 0 ≤ 5 * N / 2)).2 h
  unfold GuthMaynardJutilaReflection2941.sourceHPlus
  by_cases hlow : (n : ℝ) / N ≤ 1 / 2
  · rw [GuthMaynardLemma295CutoffAnalytic.sourceWZero_eq_zero_left
      (by norm_num : (1 / 2 : ℝ) < 1) hlow]
    simp
  · have hlow' : N / 2 < (n : ℝ) := by
      have h := lt_of_not_ge hlow
      have h' := (lt_div_iff₀ hN).mp h
      linarith
    have hhigh : (5 / 2 : ℝ) < (n : ℝ) / N := by
      by_contra hnot
      have hnle : (n : ℝ) ≤ 5 * N / 2 := by
        have h := (div_le_iff₀ hN).mp (le_of_not_gt hnot)
        linarith
      exact hnrange ⟨hlow', hnle⟩
    rw [GuthMaynardLemma295CutoffAnalytic.sourceWZero_eq_zero_right
      (by norm_num : (2 : ℝ) < 5 / 2) hhigh.le]
    simp

end

end GuthMaynardLemma295MellinLineTwo

#print axioms GuthMaynardLemma295MellinLineTwo.sourceHZero_mellinConvergent_two
#print axioms GuthMaynardLemma295MellinLineTwo.sourceHZero_verticalIntegrable_two
#print axioms GuthMaynardLemma295MellinLineTwo.sourceHZero_mellin_inversion_two
#print axioms GuthMaynardLemma295MellinLineTwo.zeta_shift_dirichletSeries_line_two
#print axioms GuthMaynardLemma295MellinLineTwo.sourceHPlus_eq_sourceHZero_mul_cpow
#print axioms GuthMaynardLemma295MellinLineTwo.tsum_sourceHPlus_eq_sourceHPlusSum
