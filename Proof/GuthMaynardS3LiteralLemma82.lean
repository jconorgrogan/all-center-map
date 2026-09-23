import GuthMaynardS3LiteralProfile
import GuthMaynardLemma118IntervalPacking
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Guth--Maynard Lemma 8.2: actual L² bound on the ratio kernel

Source (guth_maynard.txt, Lemma 8.2): if W is T^η-separated and contained in
an interval of length T, then ∫_{v≍1} |R(v)|² dv ≪_η |W|.

R is the literal kernel `ratioDirichletKernel` from (7.2). The S3 profile is
`ratioProfile W u = ratioCutoff u * ‖R(u)‖²`. Existing smoothing stability
gives ∫ smoothedRatio² ≤ 4 ∫ ratioProfile; that comparison is not this bound.

The argument is the source's weighted log-coordinate Fourier identity. With
ψ₂(τ) = 2π e^{-2πτ} ψ(e^{-2πτ}),
  ∫_{v>0} ψ(v) |R(v)|² dv = ∑_{t,s ∈ W} ψ̂₂(t-s),
then Schwartz decay of ψ̂₂ and T^η off-diagonal annihilation.
-/

namespace GuthMaynardS3LiteralLemma82

open MeasureTheory Set
open scoped BigOperators FourierTransform Real ContDiff SchwartzMap
open GuthMaynardS3LiteralProfile GuthMaynardRatioKernelIdentity
open GuthMaynardJIteration GuthMaynardHeathBrownInterface
open GuthMaynardLemma118

noncomputable section

/-! ## Cutoff regularity and the evenized weight -/

theorem ratioCutoff_contDiff : ContDiff ℝ ∞ ratioCutoff := by
  unfold ratioCutoff
  exact ((sourceBump_contDiff 2 (by norm_num)).comp
      (contDiff_id.sub contDiff_const)).mul
    (contDiff_const.sub (sourceBump_contDiff (1 / 16) (by norm_num)))

/-- Evenization of `ratioCutoff`, sampled on the positive ray by the log map. -/
def logWeight (u : ℝ) : ℝ :=
  ratioCutoff u + ratioCutoff (-u)

theorem logWeight_nonneg (u : ℝ) : 0 ≤ logWeight u :=
  add_nonneg (ratioCutoff_nonneg u) (ratioCutoff_nonneg (-u))

theorem logWeight_contDiff : ContDiff ℝ ∞ logWeight :=
  ratioCutoff_contDiff.add (ratioCutoff_contDiff.comp contDiff_neg)

theorem logWeight_eq_zero_of_le_inv_sixteen {u : ℝ} (hu : |u| ≤ (1 / 16 : ℝ)) :
    logWeight u = 0 := by
  unfold logWeight
  rw [ratioCutoff_eq_zero_near_zero hu,
    ratioCutoff_eq_zero_near_zero (by simpa using hu)]
  ring

theorem logWeight_eq_zero_of_six_lt {u : ℝ} (hu : 6 < |u|) : logWeight u = 0 := by
  have h1 : ratioCutoff u = 0 := by
    by_contra hne
    exact (not_le.mpr hu) (ratioCutoff_supported hne)
  have h2 : ratioCutoff (-u) = 0 := by
    by_contra hne
    have : |-u| ≤ 6 := ratioCutoff_supported hne
    exact (not_le.mpr hu) (by simpa using this)
  simp [logWeight, h1, h2]

theorem ratioDirichletKernel_neg (W : Finset ℝ) (v : ℝ) :
    ratioDirichletKernel W (-v) = ratioDirichletKernel W v := by
  unfold ratioDirichletKernel
  simp [abs_neg]

theorem ratioProfile_add_neg (W : Finset ℝ) (v : ℝ) :
    ratioProfile W v + ratioProfile W (-v) =
      logWeight v * ‖ratioDirichletKernel W v‖ ^ 2 := by
  unfold ratioProfile logWeight
  rw [ratioDirichletKernel_neg]
  ring

/-! ## Source ψ₂ in the coordinate τ with v = e^{-2πτ} -/

def logExpMap (τ : ℝ) : ℝ :=
  Real.exp (-(2 * Real.pi) * τ)

def logCoordinateWeight (τ : ℝ) : ℝ :=
  (2 * Real.pi) * Real.exp (-(2 * Real.pi) * τ) * logWeight (logExpMap τ)

theorem logExpMap_pos (τ : ℝ) : 0 < logExpMap τ :=
  Real.exp_pos _

theorem two_pi_pos : 0 < 2 * Real.pi := by positivity

theorem exp_one_ge_two : (2 : ℝ) ≤ Real.exp 1 := by
  have := Real.add_one_le_exp (1 : ℝ)
  linarith

theorem exp_four_ge_sixteen : (16 : ℝ) ≤ Real.exp 4 := by
  have h2 : (4 : ℝ) ≤ Real.exp 2 := by
    have h := mul_le_mul exp_one_ge_two exp_one_ge_two (by norm_num) (Real.exp_pos 1).le
    rw [← Real.exp_add, show (1 : ℝ) + 1 = 2 by norm_num] at h
    convert h using 1
    norm_num
  have h4 := mul_le_mul h2 h2 (by norm_num) (Real.exp_pos 2).le
  rw [← Real.exp_add, show (2 : ℝ) + 2 = 4 by norm_num] at h4
  convert h4 using 1
  norm_num

theorem exp_two_pi_ge_sixteen : (16 : ℝ) ≤ Real.exp (2 * Real.pi) :=
  exp_four_ge_sixteen.trans (Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three]))

theorem logCoordinateWeight_eq_zero_of_not_mem_Icc {τ : ℝ}
    (hτ : τ ∉ Icc (-1 : ℝ) 1) : logCoordinateWeight τ = 0 := by
  have hcases : τ < -1 ∨ 1 < τ := by
    rw [mem_Icc, not_and_or] at hτ
    rcases hτ with h | h
    · exact Or.inl (lt_of_not_ge h)
    · exact Or.inr (lt_of_not_ge h)
  rcases hcases with hτ | hτ
  · have hlt : Real.exp (2 * Real.pi) < logExpMap τ := by
      unfold logExpMap
      exact Real.exp_lt_exp.mpr (by nlinarith [two_pi_pos, hτ])
    have habs : 6 < |logExpMap τ| := by
      rw [abs_of_pos (logExpMap_pos τ)]
      linarith [exp_two_pi_ge_sixteen.trans hlt.le]
    simp [logCoordinateWeight, logWeight_eq_zero_of_six_lt habs]
  · have hle : logExpMap τ ≤ Real.exp (-(2 * Real.pi)) := by
      unfold logExpMap
      exact Real.exp_le_exp.mpr (by nlinarith [two_pi_pos, hτ.le])
    have hinv : Real.exp (-(2 * Real.pi)) ≤ (1 / 16 : ℝ) := by
      rw [Real.exp_neg]
      have h16 : (16 : ℝ) ≤ Real.exp (2 * Real.pi) := exp_two_pi_ge_sixteen
      have := (inv_le_inv₀ (Real.exp_pos (2 * Real.pi)) (by norm_num : (0 : ℝ) < 16)).mpr h16
      simpa using this
    have habs : |logExpMap τ| ≤ (1 / 16 : ℝ) := by
      rw [abs_of_pos (logExpMap_pos τ)]
      exact hle.trans hinv
    simp [logCoordinateWeight, logWeight_eq_zero_of_le_inv_sixteen habs]

theorem logCoordinateWeight_contDiff : ContDiff ℝ ∞ logCoordinateWeight := by
  have hexp : ContDiff ℝ ∞ fun τ : ℝ => Real.exp (-(2 * Real.pi) * τ) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  unfold logCoordinateWeight logExpMap
  exact (contDiff_const.mul hexp).mul (logWeight_contDiff.comp hexp)

theorem logCoordinateWeight_hasCompactSupport :
    HasCompactSupport logCoordinateWeight :=
  HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1))
    fun _ hτ => logCoordinateWeight_eq_zero_of_not_mem_Icc hτ

theorem logCoordinateWeight_complex_contDiff :
    ContDiff ℝ ∞ fun τ : ℝ => (logCoordinateWeight τ : ℂ) :=
  Complex.ofRealCLM.contDiff.comp logCoordinateWeight_contDiff

theorem logCoordinateWeight_complex_hasCompactSupport :
    HasCompactSupport fun τ : ℝ => (logCoordinateWeight τ : ℂ) :=
  logCoordinateWeight_hasCompactSupport.comp_left Complex.ofReal_zero

def logCoordinateWeightSchwartz : 𝓢(ℝ, ℂ) :=
  logCoordinateWeight_complex_hasCompactSupport.toSchwartzMap
    logCoordinateWeight_complex_contDiff

@[simp] theorem logCoordinateWeightSchwartz_apply (τ : ℝ) :
    logCoordinateWeightSchwartz τ = logCoordinateWeight τ :=
  rfl

def logCoordinateFourierConstant (q : ℕ) : ℝ :=
  2 ^ q * (Finset.Iic (q, 0)).sup
    (fun m => SchwartzMap.seminorm ℂ m.1 m.2)
      (𝓕 logCoordinateWeightSchwartz)

theorem logCoordinateFourierConstant_nonneg (q : ℕ) :
    0 ≤ logCoordinateFourierConstant q := by
  unfold logCoordinateFourierConstant
  positivity

/-- Arbitrary-order decay of ψ̂₂. This is the source bound |ψ̂₂(ξ)| ≪_j |ξ|^{-j}. -/
theorem logCoordinateWeight_fourier_decay (q : ℕ) (xi : ℝ) :
    ‖FourierTransform.fourier
        (fun τ : ℝ => (logCoordinateWeight τ : ℂ)) xi‖ ≤
      logCoordinateFourierConstant q / (1 + |xi|) ^ q := by
  let b : 𝓢(ℝ, ℂ) := logCoordinateWeightSchwartz
  let bhat : 𝓢(ℝ, ℂ) := 𝓕 b
  have hseminorm := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℂ) (m := (q, 0)) (k := q) (n := 0)
    le_rfl le_rfl bhat xi
  have hseminorm' :
      (1 + |xi|) ^ q * ‖bhat xi‖ ≤
        2 ^ q * (Finset.Iic (q, 0)).sup
          (fun m => SchwartzMap.seminorm ℂ m.1 m.2) bhat := by
    simpa only [Real.norm_eq_abs, norm_iteratedFDeriv_zero] using hseminorm
  have hden : 0 < (1 + |xi|) ^ q := by positivity
  change ‖bhat xi‖ ≤ logCoordinateFourierConstant q / (1 + |xi|) ^ q
  apply (le_div_iff₀ hden).2
  rw [mul_comm]
  simpa only [bhat, b, logCoordinateFourierConstant] using hseminorm'

theorem logCoordinateWeight_fourier_le_const (q : ℕ) (xi : ℝ) :
    ‖FourierTransform.fourier
        (fun τ : ℝ => (logCoordinateWeight τ : ℂ)) xi‖ ≤
      logCoordinateFourierConstant q := by
  have h := logCoordinateWeight_fourier_decay q xi
  have hden : (1 : ℝ) ≤ (1 + |xi|) ^ q :=
    one_le_pow₀ (by linarith [abs_nonneg xi])
  exact h.trans (div_le_self (logCoordinateFourierConstant_nonneg q) hden)

/-! ## Log-coordinate change of variables -/

theorem logExpMap_image : logExpMap '' (univ : Set ℝ) = Ioi (0 : ℝ) := by
  ext v
  constructor
  · rintro ⟨τ, -, rfl⟩
    exact logExpMap_pos τ
  · intro hv
    refine ⟨-(Real.log v) / (2 * Real.pi), mem_univ _, ?_⟩
    unfold logExpMap
    have hπ : (2 * Real.pi : ℝ) ≠ 0 := two_pi_pos.ne'
    field_simp [hπ]
    exact Real.exp_log hv

theorem logExpMap_injective : Function.Injective logExpMap := by
  intro x z hxz
  have := Real.exp_injective hxz
  have hπ : (2 * Real.pi : ℝ) ≠ 0 := two_pi_pos.ne'
  apply mul_left_cancel₀ (neg_ne_zero.mpr hπ)
  exact this

theorem logExpMap_hasDerivAt (τ : ℝ) :
    HasDerivAt logExpMap
      (Real.exp (-(2 * Real.pi) * τ) * -(2 * Real.pi)) τ := by
  have hlin' : HasDerivAt (fun t : ℝ => -(2 * Real.pi) * t) (-(2 * Real.pi)) τ := by
    simpa using (hasDerivAt_id τ).const_mul (-(2 * Real.pi))
  change HasDerivAt (fun t : ℝ => Real.exp (-(2 * Real.pi) * t)) _ τ
  simpa only [Function.comp_def] using!
    (Real.hasDerivAt_exp (-(2 * Real.pi) * τ)).comp τ hlin'

def logMellinKernel (ξ v : ℝ) : ℂ :=
  (logWeight v : ℂ) *
    Complex.exp (Complex.I * ((ξ * Real.log v : ℝ) : ℂ))

theorem logExpMap_abs_deriv (τ : ℝ) :
    |Real.exp (-(2 * Real.pi) * τ) * -(2 * Real.pi)| =
      (2 * Real.pi) * Real.exp (-(2 * Real.pi) * τ) := by
  rw [abs_mul, abs_neg, abs_of_pos (Real.exp_pos _), abs_of_pos two_pi_pos]
  ring

/-- The source identity ∫ ψ(v) e^{i ξ log v} dv = ψ̂₂(ξ), v = e^{-2πτ}. -/
theorem logMellinKernel_integral_eq_fourier (ξ : ℝ) :
    (∫ v : ℝ in Ioi (0 : ℝ), logMellinKernel ξ v) =
      FourierTransform.fourier
        (fun τ : ℝ => (logCoordinateWeight τ : ℂ)) ξ := by
  have hjac :=
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (s := univ) (f := logExpMap)
      (f' := fun τ => Real.exp (-(2 * Real.pi) * τ) * -(2 * Real.pi))
      MeasurableSet.univ
      (fun τ _ => (logExpMap_hasDerivAt τ).hasDerivWithinAt)
      logExpMap_injective.injOn (logMellinKernel ξ)
  rw [logExpMap_image] at hjac
  rw [hjac, Measure.restrict_univ, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with τ
  simp only [smul_eq_mul, logMellinKernel, logCoordinateWeight, logExpMap,
    logExpMap_abs_deriv, Complex.real_smul]
  have hlog : Real.log (Real.exp (-(2 * Real.pi) * τ)) = -(2 * Real.pi) * τ :=
    Real.log_exp _
  rw [hlog]
  have hphase :
      Complex.exp (Complex.I * ((ξ * (-(2 * Real.pi) * τ) : ℝ) : ℂ)) =
        Complex.exp ((↑(-2 * Real.pi * τ * ξ) : ℂ) * Complex.I) := by
    congr 1
    push_cast
    ring
  rw [hphase]
  push_cast
  try ring_nf
  try rfl

/-! ## Gram expansion of |R(v)|² -/

theorem star_dirichlet_phase (t v : ℝ) :
    star (Complex.exp (Complex.I * ((t * Real.log |v| : ℝ) : ℂ))) =
      Complex.exp (-Complex.I * ((t * Real.log |v| : ℝ) : ℂ)) := by
  have h := (Complex.exp_conj (Complex.I * ((t * Real.log |v| : ℝ) : ℂ))).symm
  simpa [map_mul, Complex.conj_I, Complex.conj_ofReal, mul_comm, mul_left_comm, mul_neg]
    using h

theorem ratioDirichletKernel_mul_star (W : Finset ℝ) (v : ℝ) :
    ratioDirichletKernel W v * star (ratioDirichletKernel W v) =
      ∑ t ∈ W, ∑ s ∈ W,
        Complex.exp (Complex.I * (((t - s) * Real.log |v| : ℝ) : ℂ)) := by
  unfold ratioDirichletKernel
  rw [star_sum]
  simp_rw [star_dirichlet_phase]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro t _ht
  apply Finset.sum_congr rfl
  intro s _hs
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ofReal_norm_sq_ratioDirichletKernel (W : Finset ℝ) (v : ℝ) :
    Complex.ofReal (‖ratioDirichletKernel W v‖ ^ 2) =
      ∑ t ∈ W, ∑ s ∈ W,
        Complex.exp (Complex.I * (((t - s) * Real.log |v| : ℝ) : ℂ)) := by
  calc
    Complex.ofReal (‖ratioDirichletKernel W v‖ ^ 2) =
        Complex.ofReal (Complex.normSq (ratioDirichletKernel W v)) := by
      rw [Complex.normSq_eq_norm_sq]
    _ = ratioDirichletKernel W v * star (ratioDirichletKernel W v) :=
      (Complex.mul_conj _).symm
    _ = _ := ratioDirichletKernel_mul_star W v

def weightedAbsPhase (ξ v : ℝ) : ℂ :=
  (logWeight v : ℂ) *
    Complex.exp (Complex.I * ((ξ * Real.log |v| : ℝ) : ℂ))

theorem weightedAbsPhase_eq_mellin {ξ v : ℝ} (hv : 0 < v) :
    weightedAbsPhase ξ v = logMellinKernel ξ v := by
  unfold weightedAbsPhase logMellinKernel
  rw [abs_of_pos hv]

theorem weightedAbsPhase_eq_zero_of_le_inv_sixteen {ξ v : ℝ}
    (hv : |v| ≤ (1 / 16 : ℝ)) : weightedAbsPhase ξ v = 0 := by
  simp [weightedAbsPhase, logWeight_eq_zero_of_le_inv_sixteen hv]

theorem weightedAbsPhase_eq_zero_of_six_lt {ξ v : ℝ}
    (hv : 6 < |v|) : weightedAbsPhase ξ v = 0 := by
  simp [weightedAbsPhase, logWeight_eq_zero_of_six_lt hv]

theorem continuous_weightedAbsPhase (ξ : ℝ) : Continuous (weightedAbsPhase ξ) := by
  rw [continuous_iff_continuousAt]
  intro v
  by_cases hv0 : v = 0
  · subst v
    have heq : weightedAbsPhase ξ =ᶠ[nhds (0 : ℝ)] fun _ => (0 : ℂ) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 16)] with x hx
      have hx' : |x| ≤ (1 / 16 : ℝ) := by
        have : |x| < (1 / 16 : ℝ) := by simpa [Metric.mem_ball, Real.dist_eq] using hx
        exact this.le
      exact weightedAbsPhase_eq_zero_of_le_inv_sixteen hx'
    exact continuousAt_const.congr_of_eventuallyEq heq
  · have hlog : ContinuousAt (fun x : ℝ => Real.log |x|) v :=
      (Real.continuousAt_log (abs_ne_zero.mpr hv0)).comp continuous_abs.continuousAt
    exact (Complex.ofRealCLM.continuous.continuousAt.comp
        logWeight_contDiff.continuous.continuousAt).mul
      (Complex.continuous_exp.continuousAt.comp
        (continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp
          (continuousAt_const.mul hlog))))

theorem weightedAbsPhase_hasCompactSupport (ξ : ℝ) :
    HasCompactSupport (weightedAbsPhase ξ) :=
  HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-6 : ℝ) 6)) fun v hv => by
    have : 6 < |v| := by
      rw [mem_Icc, not_and_or] at hv
      rcases hv with h | h
      · have : v < -6 := lt_of_not_ge h
        rw [abs_eq_neg_self.mpr (by linarith)]
        linarith
      · have : 6 < v := lt_of_not_ge h
        rw [abs_of_pos (by linarith : (0 : ℝ) < v)]
        exact this
    exact weightedAbsPhase_eq_zero_of_six_lt this

theorem integrable_weightedAbsPhase (ξ : ℝ) : Integrable (weightedAbsPhase ξ) :=
  (continuous_weightedAbsPhase ξ).integrable_of_hasCompactSupport
    (weightedAbsPhase_hasCompactSupport ξ)

theorem integrableOn_logMellinKernel (ξ : ℝ) :
    IntegrableOn (logMellinKernel ξ) (Ioi (0 : ℝ)) := by
  have h := (integrable_weightedAbsPhase ξ).integrableOn (s := Ioi (0 : ℝ))
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact weightedAbsPhase_eq_mellin hv

theorem logWeight_mul_normSq_eq_sum (W : Finset ℝ) {v : ℝ} (hv : 0 < v) :
    (logWeight v : ℂ) * Complex.ofReal (‖ratioDirichletKernel W v‖ ^ 2) =
      ∑ t ∈ W, ∑ s ∈ W, logMellinKernel (t - s) v := by
  rw [ofReal_norm_sq_ratioDirichletKernel, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _hs
  unfold logMellinKernel
  rw [abs_of_pos hv]

/-! ## Profile integral equals the positive Mellin pairing -/

set_option maxHeartbeats 800000 in
theorem integral_ratioProfile_eq_half_integral_logWeight_normSq (W : Finset ℝ) :
    ∫ v : ℝ, ratioProfile W v =
      (1 / 2 : ℝ) * ∫ v : ℝ, logWeight v * ‖ratioDirichletKernel W v‖ ^ 2 := by
  have hf := ratioProfile_integrable W
  have hneg :
      (∫ v : ℝ, ratioProfile W (-v)) = ∫ v : ℝ, ratioProfile W v := by
    have h := Measure.integral_comp_mul_left (fun v : ℝ => ratioProfile W v) (-1)
    simpa [abs_neg, abs_one, one_smul] using h
  have hfneg : Integrable fun v : ℝ => ratioProfile W (-v) := by
    convert hf.comp_mul_left' (by norm_num : (-1 : ℝ) ≠ 0) using 1
    ext v
    ring
  have hsum :
      (∫ v : ℝ, ratioProfile W v + ratioProfile W (-v)) =
        2 * ∫ v : ℝ, ratioProfile W v := by
    rw [integral_add hf hfneg, hneg]
    ring
  have hpoint : (fun v => ratioProfile W v + ratioProfile W (-v)) =
      fun v => logWeight v * ‖ratioDirichletKernel W v‖ ^ 2 := by
    funext v
    exact ratioProfile_add_neg W v
  rw [hpoint] at hsum
  linarith

theorem integrable_logWeight_normSq (W : Finset ℝ) :
    Integrable fun v : ℝ => logWeight v * ‖ratioDirichletKernel W v‖ ^ 2 := by
  have h := (ratioProfile_integrable W).add
    ((ratioProfile_integrable W).comp_mul_left' (by norm_num : (-1 : ℝ) ≠ 0))
  apply h.congr
  filter_upwards with v
  simp [ratioProfile_add_neg]

theorem integral_logWeight_normSq_eq_two_Ioi (W : Finset ℝ) :
    (∫ v : ℝ, logWeight v * ‖ratioDirichletKernel W v‖ ^ 2) =
      2 * ∫ v : ℝ in Ioi (0 : ℝ),
        logWeight v * ‖ratioDirichletKernel W v‖ ^ 2 := by
  let f : ℝ → ℝ := fun v => logWeight v * ‖ratioDirichletKernel W v‖ ^ 2
  have hf : Integrable f := integrable_logWeight_normSq W
  have heven (v : ℝ) : f (-v) = f v := by
    dsimp [f]
    unfold logWeight
    rw [neg_neg, add_comm, ratioDirichletKernel_neg]
  have hIic :
      (∫ v : ℝ in Iic (0 : ℝ), f v) = ∫ v : ℝ in Ioi (0 : ℝ), f v := by
    trans ∫ v : ℝ in Ioi (0 : ℝ), f (-v)
    · simpa using (integral_comp_neg_Ioi (0 : ℝ) f).symm
    · exact setIntegral_congr_fun measurableSet_Ioi fun v _hv => heven v
  have hsplit :=
    integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hf
  rw [compl_Ioi] at hsplit
  linarith

theorem integral_ratioProfile_eq_Ioi_logWeight_normSq (W : Finset ℝ) :
    ∫ v : ℝ, ratioProfile W v =
      ∫ v : ℝ in Ioi (0 : ℝ),
        logWeight v * ‖ratioDirichletKernel W v‖ ^ 2 := by
  have h1 := integral_ratioProfile_eq_half_integral_logWeight_normSq W
  have h2 := integral_logWeight_normSq_eq_two_Ioi W
  rw [h1, h2]
  ring

/-! ## Weighted log-coordinate Fourier identity -/

theorem integrableOn_sum_logMellinKernel (W : Finset ℝ) (t : ℝ) :
    IntegrableOn (fun v => ∑ s ∈ W, logMellinKernel (t - s) v) (Ioi (0 : ℝ)) :=
  integrable_finsetSum _ fun s _ => integrableOn_logMellinKernel (t - s)

theorem integral_Ioi_logWeight_normSq_eq_sum_fourier (W : Finset ℝ) :
    (∫ v : ℝ in Ioi (0 : ℝ),
        (logWeight v * ‖ratioDirichletKernel W v‖ ^ 2 : ℂ)) =
      ∑ t ∈ W, ∑ s ∈ W,
        FourierTransform.fourier
          (fun τ : ℝ => (logCoordinateWeight τ : ℂ)) (t - s) := by
  have hpoint :
      (fun v : ℝ => (logWeight v * ‖ratioDirichletKernel W v‖ ^ 2 : ℂ)) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun v => ∑ t ∈ W, ∑ s ∈ W, logMellinKernel (t - s) v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    simpa using logWeight_mul_normSq_eq_sum W hv
  have hsumt :
      IntegrableOn (fun v => ∑ t ∈ W, ∑ s ∈ W, logMellinKernel (t - s) v)
        (Ioi (0 : ℝ)) :=
    integrable_finsetSum _ fun t _ => integrableOn_sum_logMellinKernel W t
  rw [integral_congr_ae hpoint,
    integral_finsetSum W (fun t _ => (integrableOn_sum_logMellinKernel W t : Integrable _ _))]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [integral_finsetSum W (fun s _ => integrableOn_logMellinKernel (t - s))]
  apply Finset.sum_congr rfl
  intro s _hs
  exact logMellinKernel_integral_eq_fourier (t - s)

/-- Source identity: the profile mass is the Fourier pairing ∑_{t,s} ψ̂₂(t-s). -/
theorem integral_ratioProfile_eq_sum_fourier (W : Finset ℝ) :
    Complex.ofReal (∫ v : ℝ, ratioProfile W v) =
      ∑ t ∈ W, ∑ s ∈ W,
        FourierTransform.fourier
          (fun τ : ℝ => (logCoordinateWeight τ : ℂ)) (t - s) := by
  have hreal := integral_ratioProfile_eq_Ioi_logWeight_normSq W
  have hC := integral_Ioi_logWeight_normSq_eq_sum_fourier W
  have hμ :
      Complex.ofReal (∫ v : ℝ, ratioProfile W v) =
        ∫ v : ℝ in Ioi (0 : ℝ),
          (logWeight v * ‖ratioDirichletKernel W v‖ ^ 2 : ℂ) := by
    have h1 := congrArg Complex.ofReal hreal
    have h2 :
        Complex.ofReal
            (∫ v : ℝ in Ioi (0 : ℝ),
              logWeight v * ‖ratioDirichletKernel W v‖ ^ 2) =
          ∫ v : ℝ in Ioi (0 : ℝ),
            Complex.ofReal
              (logWeight v * ‖ratioDirichletKernel W v‖ ^ 2) :=
      integral_complex_ofReal.symm
    have h3 :
        (∫ v : ℝ in Ioi (0 : ℝ),
            Complex.ofReal
              (logWeight v * ‖ratioDirichletKernel W v‖ ^ 2)) =
          ∫ v : ℝ in Ioi (0 : ℝ),
            (logWeight v * ‖ratioDirichletKernel W v‖ ^ 2 : ℂ) := by
      apply integral_congr_ae
      filter_upwards with v
      simp [Complex.ofReal_mul, Complex.ofReal_pow]
    exact (h1.trans h2).trans h3
  exact hμ.trans hC

theorem integral_ratioProfile_le_sum_fourier_norm (W : Finset ℝ) :
    ∫ v : ℝ, ratioProfile W v ≤
      ∑ t ∈ W, ∑ s ∈ W,
        ‖FourierTransform.fourier
          (fun τ : ℝ => (logCoordinateWeight τ : ℂ)) (t - s)‖ := by
  have hC := integral_ratioProfile_eq_sum_fourier W
  have hre :
      ∫ v : ℝ, ratioProfile W v =
        (∑ t ∈ W, ∑ s ∈ W,
          FourierTransform.fourier
            (fun τ : ℝ => (logCoordinateWeight τ : ℂ)) (t - s)).re := by
    have := congrArg Complex.re hC
    simpa [integral_complex_ofReal, Complex.ofReal_re] using this
  rw [hre]
  exact (Complex.re_le_norm _).trans (norm_sum_le _ _) |>.trans
    (by
      apply Finset.sum_le_sum
      intro t _ht
      exact norm_sum_le _ _)

/-! ## T^η packing and the L² bound -/

/-- Source T^η-separation. Definitionally
`GuthMaynardJutilaReflection2941.TPowerSeparated`. -/
def TEtaSeparated (W : Finset ℝ) (T η : ℝ) : Prop :=
  ∀ t ∈ W, ∀ s ∈ W, t ≠ s → Real.rpow T η ≤ |t - s|

def lemma82DecayOrder (η : ℝ) : ℕ :=
  ⌈(2 : ℝ) / η⌉₊ + 1

def lemma82Constant (η : ℝ) : ℝ :=
  logCoordinateFourierConstant 0 +
    2 * logCoordinateFourierConstant (lemma82DecayOrder η)

theorem lemma82Constant_nonneg (η : ℝ) : 0 ≤ lemma82Constant η := by
  unfold lemma82Constant
  exact add_nonneg (logCoordinateFourierConstant_nonneg 0)
    (mul_nonneg (by norm_num) (logCoordinateFourierConstant_nonneg _))

theorem lemma82DecayOrder_mul_ge_two {η : ℝ} (hη : 0 < η) :
    (2 : ℝ) ≤ η * lemma82DecayOrder η := by
  have hceil : (2 : ℝ) / η ≤ ⌈(2 : ℝ) / η⌉₊ := Nat.le_ceil _
  have hη0 : 0 < η := hη
  have : (2 : ℝ) ≤ η * (⌈(2 : ℝ) / η⌉₊ : ℝ) := by
    have := mul_le_mul_of_nonneg_left hceil hη0.le
    field_simp at this
    exact this
  unfold lemma82DecayOrder
  have : (η : ℝ) * (⌈(2 : ℝ) / η⌉₊ + 1 : ℕ) =
      η * ⌈(2 : ℝ) / η⌉₊ + η := by
    push_cast
    ring
  linarith

theorem card_le_one_add_T {W : Finset ℝ} {T η : ℝ}
    (hT : 1 ≤ T) (hη : 0 < η)
    (hsep : TEtaSeparated W T η)
    (hW : ContainedInIntervalOfLength W T) :
    (W.card : ℝ) ≤ 1 + T := by
  obtain ⟨x, hx⟩ := hW
  have hδ : 0 < Real.rpow T η := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hT) η
  have hpack := card_cast_le_one_add_div W x T (Real.rpow T η)
    hδ (by linarith) hx hsep
  have hone : (1 : ℝ) ≤ Real.rpow T η := Real.one_le_rpow hT hη.le
  have hquot : T / Real.rpow T η ≤ T := by
    apply (div_le_iff₀ hδ).2
    nlinarith
  linarith

theorem fourier_off_diag_le {W : Finset ℝ} {T η t s : ℝ} {q : ℕ}
    (hT : 1 ≤ T) (hη : 0 < η)
    (hsep : TEtaSeparated W T η)
    (ht : t ∈ W) (hs : s ∈ W) (hts : t ≠ s)
    (hq : (2 : ℝ) ≤ η * q) :
    ‖FourierTransform.fourier
        (fun τ : ℝ => (logCoordinateWeight τ : ℂ)) (t - s)‖ ≤
      logCoordinateFourierConstant q / Real.rpow T (η * q) := by
  have hgap := hsep t ht s hs hts
  have hξ : Real.rpow T η ≤ |t - s| := hgap
  have hdecay := logCoordinateWeight_fourier_decay q (t - s)
  have hden : (Real.rpow T η) ^ q ≤ (1 + |t - s|) ^ q := by
    have h1 : Real.rpow T η ≤ 1 + |t - s| := by
      linarith [hξ, abs_nonneg (t - s)]
    have hpos : 0 ≤ Real.rpow T η := (Real.rpow_pos_of_pos (by linarith) η).le
    exact pow_le_pow_left₀ hpos h1 q
  have hrpow : (Real.rpow T η) ^ (q : ℝ) = Real.rpow T (η * q) :=
    (Real.rpow_mul (by linarith : (0 : ℝ) ≤ T) η (q : ℝ)).symm
  have hle :
      logCoordinateFourierConstant q / (1 + |t - s|) ^ q ≤
        logCoordinateFourierConstant q / Real.rpow T (η * q) := by
    apply div_le_div_of_nonneg_left (logCoordinateFourierConstant_nonneg q)
    · rw [← hrpow, Real.rpow_natCast]
      exact pow_pos (Real.rpow_pos_of_pos (by linarith) η) q
    · rwa [← hrpow, Real.rpow_natCast]
  exact hdecay.trans hle

theorem sum_fourier_norm_le {W : Finset ℝ} {T η : ℝ}
    (hT : 1 ≤ T) (hη : 0 < η)
    (hsep : TEtaSeparated W T η)
    (hW : ContainedInIntervalOfLength W T) :
    (∑ t ∈ W, ∑ s ∈ W,
        ‖FourierTransform.fourier
          (fun τ : ℝ => (logCoordinateWeight τ : ℂ)) (t - s)‖) ≤
      lemma82Constant η * W.card := by
  let q : ℕ := lemma82DecayOrder η
  have hq : (2 : ℝ) ≤ η * q := lemma82DecayOrder_mul_ge_two hη
  have hcard := card_le_one_add_T hT hη hsep hW
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hpow : Real.rpow T 2 ≤ Real.rpow T (η * q) :=
    Real.rpow_le_rpow_of_exponent_le hT hq
  have hquot : (1 + T) / Real.rpow T (η * q) ≤ 2 := by
    have hden : 0 < Real.rpow T (η * q) := Real.rpow_pos_of_pos hTpos _
    have hT2 : Real.rpow T 2 = T ^ 2 := Real.rpow_natCast T 2
    have hle : (1 + T) / Real.rpow T (η * q) ≤ (1 + T) / T ^ 2 := by
      have hden2 : 0 < T ^ 2 := sq_pos_of_pos hTpos
      have hnum : 0 ≤ 1 + T := add_nonneg (by norm_num) hTpos.le
      have hcmp : T ^ 2 ≤ Real.rpow T (η * q) := by
        simpa [hT2] using hpow
      exact div_le_div_of_nonneg_left hnum hden2 hcmp
    have hsimp : (1 + T) / T ^ 2 = T⁻¹ ^ 2 + T⁻¹ := by
      have hTne : T ≠ 0 := hTpos.ne'
      field_simp [hTne]
    have hbound : T⁻¹ ^ 2 + T⁻¹ ≤ 2 := by
      have hinv : T⁻¹ ≤ (1 : ℝ) := (inv_le_one_iff₀).2 (Or.inr hT)
      have hinv0 : 0 ≤ T⁻¹ := inv_nonneg.2 hTpos.le
      have hsq : T⁻¹ ^ 2 ≤ (1 : ℝ) := pow_le_one₀ hinv0 hinv
      nlinarith
    have : (1 + T) / T ^ 2 ≤ 2 := by
      rw [hsimp]
      exact hbound
    exact hle.trans this
  have hterm t s (ht : t ∈ W) (hs : s ∈ W) :
      ‖FourierTransform.fourier
          (fun τ : ℝ => (logCoordinateWeight τ : ℂ)) (t - s)‖ ≤
        (if t = s then logCoordinateFourierConstant 0
          else logCoordinateFourierConstant q / Real.rpow T (η * q)) := by
    by_cases hts : t = s
    · subst hts
      simpa using logCoordinateWeight_fourier_le_const 0 0
    · simpa [hts] using fourier_off_diag_le hT hη hsep ht hs hts hq
  have hsum :=
    Finset.sum_le_sum fun t ht =>
      Finset.sum_le_sum fun s hs => hterm t s ht hs
  refine hsum.trans ?_
  set K : ℝ := logCoordinateFourierConstant q / Real.rpow T (η * q)
  have hK0 : 0 ≤ K := div_nonneg (logCoordinateFourierConstant_nonneg q)
    (Real.rpow_nonneg (by linarith) _)
  have hite t (ht : t ∈ W) :
      (∑ s ∈ W,
          if t = s then logCoordinateFourierConstant 0 else K) =
        logCoordinateFourierConstant 0 + K * (W.card - 1 : ℕ) := by
    rw [← Finset.add_sum_erase _ (fun s => if t = s then logCoordinateFourierConstant 0 else K) ht]
    simp [if_pos]
    have hneq : ∀ s ∈ W.erase t, (if t = s then logCoordinateFourierConstant 0 else K) = K := by
      intro s hs
      have : t ≠ s := (Finset.mem_erase.mp hs).1.symm
      simp [this]
    rw [Finset.sum_congr rfl hneq, Finset.sum_const, nsmul_eq_mul,
      Finset.card_erase_of_mem ht]
    ring
  have hsum' :
      (∑ t ∈ W, ∑ s ∈ W,
          if t = s then logCoordinateFourierConstant 0 else K) =
        (W.card : ℝ) * logCoordinateFourierConstant 0 +
          (W.card : ℝ) * K * (W.card - 1 : ℕ) := by
    rw [Finset.sum_congr rfl fun t ht => hite t ht]
    simp [mul_add, add_mul]
    ring
  have hbound :
      (W.card : ℝ) * logCoordinateFourierConstant 0 +
          (W.card : ℝ) * K * (W.card - 1 : ℕ) ≤
        lemma82Constant η * W.card := by
    have hsub : ((W.card - 1 : ℕ) : ℝ) ≤ (W.card : ℝ) :=
      Nat.cast_le.mpr (Nat.sub_le W.card 1)
    have hCK : (W.card : ℝ) * K ≤ 2 * logCoordinateFourierConstant q := by
      have h1 : (W.card : ℝ) * K ≤ (1 + T) * K :=
        mul_le_mul_of_nonneg_right hcard hK0
      have hden : 0 < Real.rpow T (η * q) := Real.rpow_pos_of_pos hTpos _
      have h2 : (1 + T) * K ≤ 2 * logCoordinateFourierConstant q := by
        change (1 + T) * (logCoordinateFourierConstant q / Real.rpow T (η * q)) ≤ _
        calc
          (1 + T) * (logCoordinateFourierConstant q / Real.rpow T (η * q)) =
              ((1 + T) / Real.rpow T (η * q)) * logCoordinateFourierConstant q := by
            field_simp [hden.ne']
          _ ≤ 2 * logCoordinateFourierConstant q :=
            mul_le_mul_of_nonneg_right hquot (logCoordinateFourierConstant_nonneg q)
      exact h1.trans h2
    have hC0 : (0 : ℝ) ≤ logCoordinateFourierConstant 0 :=
      logCoordinateFourierConstant_nonneg 0
    have hrest : (W.card : ℝ) * K * (W.card - 1 : ℕ) ≤
        (W.card : ℝ) * (2 * logCoordinateFourierConstant q) := by
      calc
        (W.card : ℝ) * K * (W.card - 1 : ℕ) ≤ (W.card : ℝ) * K * (W.card : ℝ) :=
          mul_le_mul_of_nonneg_left hsub (mul_nonneg (Nat.cast_nonneg _) hK0)
        _ = (W.card : ℝ) * ((W.card : ℝ) * K) := by ring
        _ ≤ (W.card : ℝ) * (2 * logCoordinateFourierConstant q) :=
          mul_le_mul_of_nonneg_left hCK (Nat.cast_nonneg _)
    unfold lemma82Constant
    nlinarith [hC0, hrest]
  rw [hsum']
  exact hbound

/-- Lemma 8.2 for the literal S3 ratio profile. -/
theorem integral_ratioProfile_le {W : Finset ℝ} {T η : ℝ}
    (hT : 1 ≤ T) (hη : 0 < η)
    (hsep : TEtaSeparated W T η)
    (hW : ContainedInIntervalOfLength W T) :
    ∫ v : ℝ, ratioProfile W v ≤ lemma82Constant η * W.card :=
  (integral_ratioProfile_le_sum_fourier_norm W).trans
    (sum_fourier_norm_le hT hη hsep hW)

/-- Literal source range `v ≍ 1`: on `[1/2,2]` the cutoff equals one. -/
theorem integral_ratioDirichletKernel_sq_on_unit_le {W : Finset ℝ} {T η : ℝ}
    (hT : 1 ≤ T) (hη : 0 < η)
    (hsep : TEtaSeparated W T η)
    (hW : ContainedInIntervalOfLength W T) :
    (∫ v : ℝ in Icc (1 / 2 : ℝ) 2, ‖ratioDirichletKernel W v‖ ^ 2) ≤
      lemma82Constant η * W.card := by
  have hpt : ∀ v ∈ Icc (1 / 2 : ℝ) 2,
      ‖ratioDirichletKernel W v‖ ^ 2 = ratioProfile W v := by
    intro v hv
    have hv' : v ∈ Icc (1 / 8 : ℝ) 4 := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    unfold ratioProfile
    rw [ratioCutoff_eq_one hv']
    ring
  have hnonneg : 0 ≤ ratioProfile W := ratioProfile_nonneg W
  have hinterg := (ratioProfile_integrable W).integrableOn (s := Icc (1 / 2 : ℝ) 2)
  have hle :
      (∫ v : ℝ in Icc (1 / 2 : ℝ) 2, ‖ratioDirichletKernel W v‖ ^ 2) ≤
        ∫ v : ℝ, ratioProfile W v := by
    rw [setIntegral_congr_fun measurableSet_Icc hpt]
    exact setIntegral_le_integral (ratioProfile_integrable W)
      (Filter.Eventually.of_forall hnonneg)
  exact hle.trans (integral_ratioProfile_le hT hη hsep hW)

/-- Smoothing stability transfers Lemma 8.2 to the smoothed ratio. -/
theorem integral_smoothedRatio_sq_le {B : ℝ} (hB : 0 < B)
    {W : Finset ℝ} {T η : ℝ}
    (hT : 1 ≤ T) (hη : 0 < η)
    (hsep : TEtaSeparated W T η)
    (hW : ContainedInIntervalOfLength W T) :
    (∫ u : ℝ, smoothedRatio B W u ^ 2) ≤
      4 * lemma82Constant η * W.card := by
  have hstab := GuthMaynardS3LiteralProfile.integral_smoothedRatio_sq_le hB W
  have hprof := integral_ratioProfile_le hT hη hsep hW
  have : 4 * ∫ u : ℝ, ratioProfile W u ≤ 4 * lemma82Constant η * W.card := by
    have h4 : (0 : ℝ) ≤ 4 := by norm_num
    nlinarith [hprof]
  exact hstab.trans this

end
end GuthMaynardS3LiteralLemma82

#print axioms GuthMaynardS3LiteralLemma82.logCoordinateWeight_fourier_decay
#print axioms GuthMaynardS3LiteralLemma82.logMellinKernel_integral_eq_fourier
#print axioms GuthMaynardS3LiteralLemma82.integral_ratioProfile_eq_sum_fourier
#print axioms GuthMaynardS3LiteralLemma82.integral_ratioProfile_le
#print axioms GuthMaynardS3LiteralLemma82.integral_ratioDirichletKernel_sq_on_unit_le
#print axioms GuthMaynardS3LiteralLemma82.integral_smoothedRatio_sq_le
