import GuthMaynardLemma92SubpowerProfile
import GuthMaynardHeathBrownIccIocEndpointAdapter

/-!
# A concrete positive ratio profile for Guth--Maynard (7.5)

The profile is built from the literal ratio kernel. Its cutoff is one on
[1/8,4], has compact support, and vanishes in a neighborhood of zero. The
smoothing scale is exactly NM. No profile regularity or norm hypothesis is
assumed in the construction below.
-/

namespace GuthMaynardS3LiteralProfile

open MeasureTheory
open scoped BigOperators
open GuthMaynardJIteration GuthMaynardRatioKernelIdentity
open GuthMaynardHeathBrownIccIocEndpointAdapter

noncomputable section

def ratioCutoff (u : ℝ) : ℝ :=
  sourceBump 2 (by norm_num) (u-2) *
    (1-sourceBump (1/16) (by norm_num) u)

theorem ratioCutoff_nonneg (u : ℝ) : 0 ≤ ratioCutoff u := by
  unfold ratioCutoff
  exact mul_nonneg (sourceBump_nonneg _ _ _) (sub_nonneg.mpr (sourceBump_le_one _ _ _))

theorem ratioCutoff_le_one (u : ℝ) : ratioCutoff u ≤ 1 := by
  have ha := sourceBump_nonneg 2 (by norm_num) (u-2)
  have hb := sourceBump_nonneg (1/16) (by norm_num) u
  have hc := sourceBump_le_one 2 (by norm_num) (u-2)
  have hd := sourceBump_le_one (1/16) (by norm_num) u
  unfold ratioCutoff
  nlinarith

theorem ratioCutoff_eq_one {u : ℝ} (hu : u ∈ Set.Icc (1/8 : ℝ) 4) :
    ratioCutoff u = 1 := by
  have hleft : |u-2| ≤ (2:ℝ) := abs_le.mpr ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have hright : 2*(1/16 : ℝ) ≤ |u| := by
    rw [abs_of_nonneg (by linarith [hu.1])]
    linarith [hu.1]
  simp only [ratioCutoff,sourceBump_eq_one_of_abs_le _ _ hleft,
    sourceBump_eq_zero_of_two_mul_le_abs _ _ hright]
  norm_num

theorem ratioCutoff_eq_zero_near_zero {u : ℝ} (hu : |u| ≤ (1/16 : ℝ)) :
    ratioCutoff u = 0 := by
  unfold ratioCutoff
  rw [sourceBump_eq_one_of_abs_le (1/16) (by norm_num) hu]
  ring

theorem ratioCutoff_supported {u : ℝ} (hu : ratioCutoff u ≠ 0) : |u| ≤ 6 := by
  have hleft : sourceBump 2 (by norm_num) (u-2) ≠ 0 := by
    intro hz
    exact hu (by simp [ratioCutoff,hz])
  have hs := sourceBump_supported_two_mul (by norm_num : (0:ℝ)<2) hleft
  have ht := abs_add_le (u-2) (2:ℝ)
  norm_num at hs ht
  have heq : u-2+2=u := by ring
  linarith

theorem ratioCutoff_continuous : Continuous ratioCutoff := by
  unfold ratioCutoff
  exact ((sourceBump_contDiff 2 (by norm_num)).continuous.comp
    (continuous_id.sub continuous_const)).mul
      (continuous_const.sub (sourceBump_contDiff (1/16) (by norm_num)).continuous)

theorem continuousAt_ratioDirichletKernel (W : Finset ℝ) {u : ℝ} (hu : u ≠ 0) :
    ContinuousAt (ratioDirichletKernel W) u := by
  have hl : ContinuousAt (fun x : ℝ => Real.log |x|) u :=
    (Real.continuousAt_log (abs_ne_zero.mpr hu)).comp continuous_abs.continuousAt
  have hterm (t : ℝ) : ContinuousAt
      (fun x : ℝ => Complex.exp (Complex.I*((t*Real.log |x| : ℝ) : ℂ))) u :=
    Complex.continuous_exp.continuousAt.comp
      (continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp
        (continuousAt_const.mul hl)))
  classical
  induction W using Finset.induction_on with
  | empty =>
      change ContinuousAt (fun _ : ℝ => (0 : ℂ)) u
      exact continuousAt_const
  | @insert t W ht ih =>
      change ContinuousAt (fun x : ℝ => ∑ s ∈ insert t W,
        Complex.exp (Complex.I*((s*Real.log |x| : ℝ) : ℂ))) u
      simp only [Finset.sum_insert ht]
      exact (hterm t).add ih

def ratioProfile (W : Finset ℝ) (u : ℝ) : ℝ :=
  ratioCutoff u * ‖ratioDirichletKernel W u‖^2

theorem ratioProfile_nonneg (W : Finset ℝ) (u : ℝ) : 0 ≤ ratioProfile W u :=
  mul_nonneg (ratioCutoff_nonneg u) (sq_nonneg _)

theorem ratioProfile_le_card_sq (W : Finset ℝ) (u : ℝ) :
    ratioProfile W u ≤ (W.card : ℝ)^2 := by
  have hn := norm_ratioDirichletKernel_le_card W u
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hm := mul_le_mul_of_nonneg_right (ratioCutoff_le_one u) (sq_nonneg ‖ratioDirichletKernel W u‖)
  unfold ratioProfile
  nlinarith only [hm,hs]

theorem ratioProfile_supported (W : Finset ℝ) {u : ℝ}
    (hu : ratioProfile W u ≠ 0) : |u| ≤ 6 := by
  apply ratioCutoff_supported
  intro hz
  exact hu (by simp [ratioProfile,hz])

theorem ratioProfile_continuous (W : Finset ℝ) : Continuous (ratioProfile W) := by
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hu : u=0
  · subst u
    have heq : ratioProfile W =ᶠ[nhds (0 : ℝ)] fun _ => 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0:ℝ)<1/16)] with x hx
      have hx' : |x| ≤ (1/16 : ℝ) := by
        have hh : |x| < (1/16 : ℝ) := by simpa [Metric.mem_ball,Real.dist_eq] using hx
        exact hh.le
      simp [ratioProfile,ratioCutoff_eq_zero_near_zero hx']
    exact continuousAt_const.congr_of_eventuallyEq heq
  · exact ratioCutoff_continuous.continuousAt.mul
      ((continuousAt_ratioDirichletKernel W hu).norm.pow 2)

theorem ratioProfile_hasCompactSupport (W : Finset ℝ) :
    HasCompactSupport (ratioProfile W) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-6 : ℝ) 6))
  intro u hu
  by_contra hne
  exact hu (abs_le.mp (ratioProfile_supported W hne))

theorem ratioProfile_integrable (W : Finset ℝ) : Integrable (ratioProfile W) :=
  (ratioProfile_continuous W).integrable_of_hasCompactSupport (ratioProfile_hasCompactSupport W)

theorem ratioProfile_squareIntegrable (W : Finset ℝ) :
    Integrable (fun u => ratioProfile W u ^ 2) :=
  ((ratioProfile_continuous W).pow 2).integrable_of_hasCompactSupport
    (by simpa only [pow_two,Pi.mul_apply] using
      ((ratioProfile_hasCompactSupport W).mul_right :
        HasCompactSupport ((ratioProfile W)*(ratioProfile W))))

/-- Literal squared R-tilde from (7.5), with B=NM. -/
def smoothedRatioSquare (B : ℝ) (W : Finset ℝ) : ℝ → ℝ :=
  affineSmoothing B (fun z => sourceBump 1 zero_lt_one z) (ratioProfile W)

def smoothedRatio (B : ℝ) (W : Finset ℝ) (u : ℝ) : ℝ :=
  Real.sqrt (smoothedRatioSquare B W u)

theorem smoothedRatioSquare_nonneg {B : ℝ} (hB : 0 < B) (W : Finset ℝ) (u : ℝ) :
    0 ≤ smoothedRatioSquare B W u :=
  affineSmoothing_nonneg (fun z => sourceBump 1 zero_lt_one z)
    (ratioProfile W) hB.le (sourceBump_nonneg 1 zero_lt_one) (ratioProfile_nonneg W) u

theorem smoothedRatio_sq {B : ℝ} (hB : 0 < B) (W : Finset ℝ) (u : ℝ) :
    smoothedRatio B W u ^ 2 = smoothedRatioSquare B W u :=
  Real.sq_sqrt (smoothedRatioSquare_nonneg hB W u)

theorem smoothedRatioSquare_supported {B u : ℝ} (hB : 0 < B) (W : Finset ℝ)
    (hu : smoothedRatioSquare B W u ≠ 0) : |u| ≤ 6+2/B := by
  exact affineSmoothing_abs_support hB _ _
    (fun z hz => by simpa only [mul_one] using sourceBump_supported_two_mul zero_lt_one hz)
    (fun z hz => ratioProfile_supported W hz) hu

theorem integral_smoothedRatio_sq_le {B : ℝ} (hB : 0 < B) (W : Finset ℝ) :
    (∫ u : ℝ, smoothedRatio B W u ^ 2) ≤ 4*∫ u : ℝ, ratioProfile W u := by
  simp_rw [smoothedRatio_sq hB]
  simpa only [smoothedRatioSquare,mul_one] using
    integral_affineSmoothing_sourceBump_le_four_mul hB zero_lt_one
      (ratioProfile_nonneg W) (ratioProfile_integrable W)

theorem integral_smoothedRatio_four_le {B : ℝ} (hB : 0 < B) (W : Finset ℝ) :
    (∫ u : ℝ, smoothedRatio B W u ^ 4) ≤ 16*∫ u : ℝ, ratioProfile W u ^ 2 := by
  have heq (u : ℝ) : smoothedRatio B W u ^ 4 = smoothedRatioSquare B W u ^ 2 := by
    rw [show (4:ℕ)=2*2 by norm_num,pow_mul,smoothedRatio_sq hB]
  simp_rw [heq]
  simpa only [smoothedRatioSquare,mul_one,show (4:ℝ)^2=16 by norm_num] using
    integral_sq_affineSmoothing_sourceBump_le_sixteen_mul hB zero_lt_one
      (ratioProfile_nonneg W) (ratioProfile_integrable W) (ratioProfile_squareIntegrable W)

end
end GuthMaynardS3LiteralProfile

#print axioms GuthMaynardS3LiteralProfile.integral_smoothedRatio_sq_le
#print axioms GuthMaynardS3LiteralProfile.integral_smoothedRatio_four_le
