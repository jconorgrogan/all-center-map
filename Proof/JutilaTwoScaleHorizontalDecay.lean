import JutilaTwoScaleSmoothing
import GammaCompactStripSharp
import PrimitiveLFixedStripGrowthCertified
import RamachandraShiftedGammaPoleContour

/-!
# Horizontal-edge decay in Jutila's two-scale contour

This is the quantitative step immediately after the finite-rectangle contour
identity in Jutila, Acta Arith. 32 (1977), Lemma 1, p. 58, proof of (2.1).
It proves an explicit exponentially decaying majorant for the *literal*
two-scale integrand.  In particular, it does not package horizontal-edge
decay as a new assumption.
-/

namespace JutilaTwoScaleHorizontalDecay

open Complex Real MeasureTheory Set Filter Topology
open JutilaTwoScaleSmoothing
open MAPGammaCompactStripSharp
open RamachandraShiftedGammaPoleContour

noncomputable section

/-- A fixed endpoint bound for the two positive Mellin scales. -/
def twoScaleCpowEndpointBound (N a b : ℝ) : ℝ :=
  max ((2 * N) ^ a) ((2 * N) ^ b) + max (N ^ a) (N ^ b)

theorem twoScaleCpowEndpointBound_nonneg {N : ℝ} (hN : 0 < N) (a b : ℝ) :
    0 ≤ twoScaleCpowEndpointBound N a b := by
  unfold twoScaleCpowEndpointBound
  have h2N : 0 < 2 * N := mul_pos (by norm_num) hN
  have h2a : 0 ≤ (2 * N) ^ a := Real.rpow_nonneg h2N.le a
  have h2b : 0 ≤ (2 * N) ^ b := Real.rpow_nonneg h2N.le b
  have hNa : 0 ≤ N ^ a := Real.rpow_nonneg hN.le a
  have hNb : 0 ≤ N ^ b := Real.rpow_nonneg hN.le b
  exact add_nonneg (h2a.trans (le_max_left _ _))
    (hNa.trans (le_max_left _ _))

/-- Away from the real axis, the removable two-scale quotient is bounded by
the two endpoint powers. -/
theorem norm_twoScaleRemovableQuotient_horizontal_le
    {N a b x t : ℝ} (hN : 0 < N) (hax : a ≤ x) (hxb : x ≤ b)
    (ht : 1 ≤ |t|) :
    ‖twoScaleRemovableQuotient N ((x : ℂ) + t * I)‖ ≤
      twoScaleCpowEndpointBound N a b := by
  have hw : ((x : ℂ) + t * I) ≠ 0 := by
    intro hw
    have him := congrArg Complex.im hw
    simp at him
    subst t
    norm_num at ht
  have h2N : 0 < 2 * N := mul_pos (by norm_num) hN
  have hp2 := norm_posReal_cpow_horizontal_le_max
    h2N hax hxb (t := t)
  have hp1 := norm_posReal_cpow_horizontal_le_max
    hN hax hxb (t := t)
  have hden : 1 ≤ ‖((x : ℂ) + t * I)‖ := by
    exact ht.trans (by
      simpa using Complex.abs_im_le_norm ((x : ℂ) + t * I))
  rw [twoScaleRemovableQuotient, Function.update_of_ne hw, norm_div]
  calc
    ‖twoScaleSpectralFactor N ((x : ℂ) + t * I)‖ /
          ‖((x : ℂ) + t * I)‖ ≤
        ‖twoScaleSpectralFactor N ((x : ℂ) + t * I)‖ / 1 := by
      exact div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hden
    _ = ‖twoScaleSpectralFactor N ((x : ℂ) + t * I)‖ := by ring
    _ ≤ ‖((2 * N : ℝ) : ℂ) ^ ((x : ℂ) + t * I)‖ +
          ‖(N : ℂ) ^ ((x : ℂ) + t * I)‖ := by
      exact norm_sub_le _ _
    _ ≤ twoScaleCpowEndpointBound N a b := by
      exact add_le_add hp2 hp1

/-- Explicit pointwise envelope on either horizontal edge.  The factor
`exp (-(pi/2)|t|/h)` is the source of the vanishing horizontal contribution. -/
theorem norm_twoScaleContourIntegrand_horizontal_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) (s : ℂ)
    {N h a b x t : ℝ} (hN : 0 < N) (hh : 1 ≤ h)
    (hax : a ≤ x) (hxb : x ≤ b)
    (haGamma : -(h / 2) ≤ a) (hbGamma : b ≤ h / 2)
    (hLLo : -1 ≤ s.re + a) (hLHi : s.re + b ≤ 2)
    (ht : 1 ≤ |t|) :
    ‖twoScaleContourIntegrand chi s N h ((x : ℂ) + t * I)‖ ≤
      2400 * (q : ℝ) ^ 2 * h ^ 2 *
        (5 + |s.im| + |t| / h) ^ 3 *
          Real.exp (-(Real.pi / 2) * (|t| / h)) *
            twoScaleCpowEndpointBound N a b := by
  have hh0 : 0 < h := lt_of_lt_of_le (by norm_num) hh
  let z : ℂ := s + ((x : ℂ) + t * I)
  have hzRe : z.re = s.re + x := by simp [z]
  have hzIm : z.im = s.im + t := by simp [z]
  have hzLo : -1 ≤ z.re := by rw [hzRe]; linarith
  have hzHi : z.re ≤ 2 := by rw [hzRe]; linarith
  have hrePos : 0 ≤ (z + 3).re := by
    rw [Complex.add_re, hzRe]
    norm_num
    linarith
  have hreAbs : |(z + 3).re| ≤ 5 := by
    rw [abs_of_nonneg hrePos, Complex.add_re, hzRe]
    norm_num
    linarith
  have himAbs : |(z + 3).im| ≤ |s.im| + |t| := by
    rw [Complex.add_im, hzIm]
    norm_num
    exact abs_add_le s.im t
  have hzNorm : ‖z + 3‖ ≤ 5 + |s.im| + |t| := by
    calc
      ‖z + 3‖ ≤ |(z + 3).re| + |(z + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 5 + (|s.im| + |t|) := add_le_add hreAbs himAbs
      _ = 5 + |s.im| + |t| := by ring
  have hL0 := PLInteriorGrowth.norm_LFunction_fixedStrip_le
    chi hchi hzLo hzHi
  have hL : ‖DirichletCharacter.LFunction chi z‖ ≤
      200 * (q : ℝ) ^ 2 * (5 + |s.im| + |t|) ^ 2 := by
    exact hL0.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hzNorm 2) (by positivity))
  have hGammaLo : (1 / 2 : ℝ) ≤ 1 + x / h := by
    have : -(h / 2) ≤ x := haGamma.trans hax
    have hxdiv : -(1 / 2 : ℝ) ≤ x / h := by
      apply (le_div_iff₀ hh0).2
      nlinarith
    linarith
  have hGammaHi : 1 + x / h ≤ (3 / 2 : ℝ) := by
    have : x ≤ h / 2 := hxb.trans hbGamma
    have hxdiv : x / h ≤ (1 / 2 : ℝ) := by
      apply (div_le_iff₀ hh0).2
      nlinarith
    linarith
  have hGammaPoint :
      1 + (((x : ℂ) + t * I) / (h : ℂ)) =
        GammaCompactStripScratch.stripPoint (1 + x / h) (t / h) := by
    apply Complex.ext <;> simp [GammaCompactStripScratch.stripPoint, hh0.ne']
  have hGamma := norm_Gamma_positive_strip_le_exp_pi_half
    hGammaLo hGammaHi (t := t / h)
  rw [← hGammaPoint] at hGamma
  have habsDiv : |t / h| = |t| / h := by
    rw [abs_div, abs_of_pos hh0]
  rw [habsDiv] at hGamma
  have hQ := norm_twoScaleRemovableQuotient_horizontal_le
    hN hax hxb ht
  have hQ0 : 0 ≤ twoScaleCpowEndpointBound N a b :=
    twoScaleCpowEndpointBound_nonneg hN a b
  have hC : 1 ≤ 5 + |s.im| := by linarith [abs_nonneg s.im]
  have hscale : 5 + |s.im| + |t| ≤
      h * (5 + |s.im| + |t| / h) := by
    rw [mul_add, mul_div_cancel₀ _ hh0.ne']
    nlinarith
  have hscale0 : 0 ≤ 5 + |s.im| + |t| / h := by positivity
  have hpow : (5 + |s.im| + |t|) ^ 2 ≤
      h ^ 2 * (5 + |s.im| + |t| / h) ^ 2 := by
    calc
      (5 + |s.im| + |t|) ^ 2 ≤
          (h * (5 + |s.im| + |t| / h)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hscale 2
      _ = h ^ 2 * (5 + |s.im| + |t| / h) ^ 2 := by ring
  have hone : 1 + |t| / h ≤ 5 + |s.im| + |t| / h := by linarith
  unfold twoScaleContourIntegrand
  rw [norm_mul, norm_mul]
  calc
    ‖Complex.Gamma (1 + ((x : ℂ) + t * I) / (h : ℂ))‖ *
          ‖twoScaleRemovableQuotient N ((x : ℂ) + t * I)‖ *
          ‖DirichletCharacter.LFunction chi z‖ ≤
        (12 * (1 + |t| / h) *
            Real.exp (-(Real.pi / 2) * (|t| / h))) *
          twoScaleCpowEndpointBound N a b *
            (200 * (q : ℝ) ^ 2 * (5 + |s.im| + |t|) ^ 2) := by
      gcongr
    _ ≤ 2400 * (q : ℝ) ^ 2 * h ^ 2 *
        (5 + |s.im| + |t| / h) ^ 3 *
          Real.exp (-(Real.pi / 2) * (|t| / h)) *
            twoScaleCpowEndpointBound N a b := by
      have hexp0 : 0 ≤ Real.exp (-(Real.pi / 2) * (|t| / h)) :=
        (Real.exp_pos _).le
      calc
        (12 * (1 + |t| / h) *
              Real.exp (-(Real.pi / 2) * (|t| / h))) *
            twoScaleCpowEndpointBound N a b *
              (200 * (q : ℝ) ^ 2 * (5 + |s.im| + |t|) ^ 2)
            ≤ (12 * (5 + |s.im| + |t| / h) *
              Real.exp (-(Real.pi / 2) * (|t| / h))) *
            twoScaleCpowEndpointBound N a b *
              (200 * (q : ℝ) ^ 2 *
                (h ^ 2 * (5 + |s.im| + |t| / h) ^ 2)) := by
              gcongr
        _ = 2400 * (q : ℝ) ^ 2 * h ^ 2 *
            (5 + |s.im| + |t| / h) ^ 3 *
              Real.exp (-(Real.pi / 2) * (|t| / h)) *
                twoScaleCpowEndpointBound N a b := by ring

/-- The uniform horizontal envelope, expressed in the scaled height `B/h`. -/
def twoScaleHorizontalEnvelope
    (q : ℕ) (s : ℂ) (N h a b B : ℝ) : ℝ :=
  2400 * (q : ℝ) ^ 2 * h ^ 2 *
    (5 + |s.im| + B / h) ^ 3 *
      Real.exp (-(Real.pi / 2) * (B / h)) *
        twoScaleCpowEndpointBound N a b

/-- Exponential Gamma decay beats the fixed cubic L-growth envelope. -/
theorem tendsto_twoScaleHorizontalEnvelope_zero
    (q : ℕ) (s : ℂ) {N h : ℝ} (hN : 0 < N) (hh : 1 ≤ h)
    (a b : ℝ) :
    Tendsto (twoScaleHorizontalEnvelope q s N h a b) atTop (𝓝 0) := by
  let C : ℝ := 5 + |s.im|
  let c : ℝ := Real.pi / 2
  let K : ℝ :=
    2400 * (q : ℝ) ^ 2 * h ^ 2 *
      twoScaleCpowEndpointBound N a b
  have hh0 : 0 < h := lt_of_lt_of_le (by norm_num) hh
  have hc : 1 ≤ c := by
    dsimp [c]
    nlinarith [Real.pi_gt_three]
  let G : ℝ → ℝ := fun B =>
    K * Real.exp C *
      ((C + c * (B / h)) ^ 3 * Real.exp (-(C + c * (B / h))))
  have hscale : Tendsto (fun B : ℝ => C + c * (B / h)) atTop atTop := by
    have hdiv : Tendsto (fun B : ℝ => (1 / h) * B) atTop atTop :=
      tendsto_id.const_mul_atTop (one_div_pos.mpr hh0)
    have hmul : Tendsto (fun B : ℝ => c * ((1 / h) * B)) atTop atTop :=
      hdiv.const_mul_atTop (lt_of_lt_of_le (by norm_num) hc)
    have hadd := tendsto_atTop_add_const_left atTop C hmul
    convert hadd using 1
    funext B
    field_simp
  have hpoly : Tendsto (fun B : ℝ =>
      (C + c * (B / h)) ^ 3 * Real.exp (-(C + c * (B / h))))
      atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).comp hscale
  have hG : Tendsto G atTop (𝓝 0) := by
    simpa [G] using hpoly.const_mul (K * Real.exp C)
  apply squeeze_zero' (g := G)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
    unfold twoScaleHorizontalEnvelope
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg (q : ℝ)))
            (sq_nonneg h))
          (pow_nonneg (by positivity) 3))
        (Real.exp_pos _).le)
      (twoScaleCpowEndpointBound_nonneg hN a b)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
    have hBh : 0 ≤ B / h := div_nonneg hB hh0.le
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hpolyLe : C + B / h ≤ C + c * (B / h) := by
      have hu := mul_le_mul_of_nonneg_right hc hBh
      nlinarith
    have hpowLe : (C + B / h) ^ 3 ≤ (C + c * (B / h)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hpolyLe 3
    have hexpRewrite :
        Real.exp C * Real.exp (-(C + c * (B / h))) =
          Real.exp (-(c * (B / h))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hleftEq : twoScaleHorizontalEnvelope q s N h a b B =
        K * ((C + B / h) ^ 3 * Real.exp (-(c * (B / h)))) := by
      dsimp [twoScaleHorizontalEnvelope, K, C, c]
      ring
    have hrightEq : G B =
        K * ((C + c * (B / h)) ^ 3 * Real.exp (-(c * (B / h)))) := by
      dsimp [G]
      calc
        K * Real.exp C *
              ((C + c * (B / h)) ^ 3 *
                Real.exp (-(C + c * (B / h)))) =
            K * (C + c * (B / h)) ^ 3 *
              (Real.exp C * Real.exp (-(C + c * (B / h)))) := by ring
        _ = K * ((C + c * (B / h)) ^ 3 *
              Real.exp (-(c * (B / h)))) := by rw [hexpRewrite]; ring
    rw [hleftEq, hrightEq]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hpowLe (Real.exp_pos _).le)
      (by
        dsimp [K]
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (by positivity) (sq_nonneg (q : ℝ))) (sq_nonneg h))
          (twoScaleCpowEndpointBound_nonneg hN a b))
  · exact hG

/-- The actual finite horizontal edge tends to zero. -/
theorem tendsto_twoScaleHorizontalIntegral_zero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) (s : ℂ)
    {N h a b : ℝ} (hN : 0 < N) (hh : 1 ≤ h)
    (hab : a ≤ b) (haGamma : -(h / 2) ≤ a) (hbGamma : b ≤ h / 2)
    (hLLo : -1 ≤ s.re + a) (hLHi : s.re + b ≤ 2) :
    Tendsto (fun B : ℝ =>
      ∫ x : ℝ in a..b,
        twoScaleContourIntegrand chi s N h ((x : ℂ) + B * I))
      atTop (𝓝 0) := by
  have henv := tendsto_twoScaleHorizontalEnvelope_zero q s hN hh a b
  have hbound : ∀ᶠ B : ℝ in atTop,
      ‖∫ x : ℝ in a..b,
          twoScaleContourIntegrand chi s N h ((x : ℂ) + B * I)‖ ≤
        twoScaleHorizontalEnvelope q s N h a b B * |b - a| := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with B hB
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Set.Icc a b := by
      have := Set.uIoc_subset_uIcc hx
      simpa [Set.uIcc_of_le hab] using this
    have hB0 : 0 ≤ B := le_trans (by norm_num) hB
    have hBabs : 1 ≤ |B| := by simpa [abs_of_nonneg hB0] using hB
    simpa [twoScaleHorizontalEnvelope, abs_of_nonneg hB0] using
      norm_twoScaleContourIntegrand_horizontal_le chi hchi s hN hh
        hx'.1 hx'.2 haGamma hbGamma hLLo hLHi hBabs
  have henvMul : Tendsto (fun B : ℝ =>
      twoScaleHorizontalEnvelope q s N h a b B * |b - a|)
      atTop (𝓝 0) := by
    simpa using henv.mul_const |b - a|
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
  · exact hbound
  · exact henvMul

end

end JutilaTwoScaleHorizontalDecay

#print axioms JutilaTwoScaleHorizontalDecay.norm_twoScaleRemovableQuotient_horizontal_le
#print axioms JutilaTwoScaleHorizontalDecay.norm_twoScaleContourIntegrand_horizontal_le
#print axioms JutilaTwoScaleHorizontalDecay.tendsto_twoScaleHorizontalEnvelope_zero
#print axioms JutilaTwoScaleHorizontalDecay.tendsto_twoScaleHorizontalIntegral_zero
