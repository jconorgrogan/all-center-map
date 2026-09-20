import JutilaP53FiniteShift
import GammaCompactStripSharp
import PrimitiveLFixedStripGrowthCertified
import RamachandraShiftedGammaPoleContour

/-!
# Quantitative left-line envelope for Jutila p.53

This attaches the certified Gamma decay and fixed-strip Dirichlet-L growth to
the literal p.53 two-scale contour.  It leaves no abstract contour-bound
premise: every factor of the pointwise envelope is displayed.
-/

namespace MAPJutilaP53LeftLineEstimate

open Complex Real MeasureTheory Set Filter Topology
open MAPJutilaP53TwoScaleContour
open MAPJutilaP53FiniteShift
open MAPGammaCompactStripSharp
open MAPPrimitiveLFixedStrip
open RamachandraShiftedGammaPoleContour

noncomputable section

def p53CpowEndpointBound (U V a b : ℝ) : ℝ :=
  max (U ^ a) (U ^ b) + max (V ^ a) (V ^ b)

theorem p53CpowEndpointBound_nonneg
    {U V : ℝ} (hU : 0 < U) (hV : 0 < V) (a b : ℝ) :
    0 ≤ p53CpowEndpointBound U V a b := by
  unfold p53CpowEndpointBound
  exact add_nonneg
    ((Real.rpow_nonneg hU.le a).trans (le_max_left _ _))
    ((Real.rpow_nonneg hV.le a).trans (le_max_left _ _))

theorem norm_p53ScaleRemovableQuotient_horizontal_le
    {U V a b x t : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hax : a ≤ x) (hxb : x ≤ b) (ht : 1 ≤ |t|) :
    ‖p53ScaleRemovableQuotient U V ((x : ℂ) + t * I)‖ ≤
      p53CpowEndpointBound U V a b := by
  have hw : ((x : ℂ) + t * I) ≠ 0 := by
    intro hw
    have him := congrArg Complex.im hw
    simp at him
    subst t
    norm_num at ht
  have hpU := norm_posReal_cpow_horizontal_le_max hU hax hxb (t := t)
  have hpV := norm_posReal_cpow_horizontal_le_max hV hax hxb (t := t)
  have hden : 1 ≤ ‖((x : ℂ) + t * I)‖ :=
    ht.trans (by simpa using Complex.abs_im_le_norm ((x : ℂ) + t * I))
  rw [p53ScaleRemovableQuotient, Function.update_of_ne hw, norm_div]
  calc
    ‖p53ScaleDifference U V ((x : ℂ) + t * I)‖ /
          ‖((x : ℂ) + t * I)‖ ≤
        ‖p53ScaleDifference U V ((x : ℂ) + t * I)‖ := by
      simpa using div_le_self (norm_nonneg _) hden
    _ ≤ ‖(U : ℂ) ^ ((x : ℂ) + t * I)‖ +
          ‖(V : ℂ) ^ ((x : ℂ) + t * I)‖ := by
      unfold p53ScaleDifference
      exact norm_sub_le _ _
    _ ≤ p53CpowEndpointBound U V a b := add_le_add hpU hpV

/-- Literal pointwise envelope on the shifted p.53 line `Re w = x`.
The hypotheses are exactly the Gamma strip and L-function strip conditions. -/
theorem norm_p53TwoScaleContourIntegrand_horizontal_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (s : ℂ) {U V a b x t : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hax : a ≤ x) (hxb : x ≤ b)
    (haGamma : -(1 / 2 : ℝ) ≤ x) (hbGamma : x ≤ 1 / 2)
    (hLLo : -1 ≤ 1 + s.re + x) (hLHi : 1 + s.re + x ≤ 2)
    (ht : 1 ≤ |t|) :
    ‖p53TwoScaleContourIntegrand chi s U V ((x : ℂ) + t * I)‖ ≤
      2400 * (q : ℝ) ^ 2 * (1 + |t|) *
        (5 + |s.im| + |t|) ^ 2 *
          Real.exp (-(Real.pi / 2) * |t|) *
            p53CpowEndpointBound U V a b := by
  let z : ℂ := 1 + s + ((x : ℂ) + t * I)
  have hzRe : z.re = 1 + s.re + x := by simp [z]
  have hzIm : z.im = s.im + t := by simp [z]
  have hL0 := PLInteriorGrowth.norm_LFunction_fixedStrip_le chi hchi
    (by rw [hzRe]; exact hLLo) (by rw [hzRe]; exact hLHi)
  have hzNorm : ‖z + 3‖ ≤ 5 + |s.im| + |t| := by
    calc
      ‖z + 3‖ ≤ |(z + 3).re| + |(z + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |4 + s.re + x| + |s.im + t| := by simp [z]; ring
      _ ≤ 5 + (|s.im| + |t|) := by
        have hre0 : 0 ≤ 4 + s.re + x := by linarith
        rw [abs_of_nonneg hre0]
        exact add_le_add (by linarith [hLHi]) (abs_add_le _ _)
      _ = 5 + |s.im| + |t| := by ring
  have hL : ‖DirichletCharacter.LFunction chi z‖ ≤
      200 * (q : ℝ) ^ 2 * (5 + |s.im| + |t|) ^ 2 :=
    hL0.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hzNorm 2) (by positivity))
  have hGammaPoint : 1 + ((x : ℂ) + t * I) =
      GammaCompactStripScratch.stripPoint (1 + x) t := by
    apply Complex.ext <;> simp [GammaCompactStripScratch.stripPoint]
  have hGamma := norm_Gamma_positive_strip_le_exp_pi_half
    (show (1 / 2 : ℝ) ≤ 1 + x by linarith)
    (show 1 + x ≤ (3 / 2 : ℝ) by linarith) (t := t)
  rw [← hGammaPoint] at hGamma
  have hQ := norm_p53ScaleRemovableQuotient_horizontal_le
    hU hV hax hxb ht
  have hQ0 := p53CpowEndpointBound_nonneg hU hV a b
  have hL' : ‖DirichletCharacter.LFunction chi
      (1 + s + ((x : ℂ) + t * I))‖ ≤
      200 * (q : ℝ) ^ 2 * (5 + |s.im| + |t|) ^ 2 := by
    simpa only [z] using hL
  unfold p53TwoScaleContourIntegrand
  simp only [norm_mul]
  calc
    ‖Complex.Gamma (((x : ℂ) + t * I) + 1)‖ *
          ‖p53ScaleRemovableQuotient U V ((x : ℂ) + t * I)‖ *
          ‖DirichletCharacter.LFunction chi z‖ ≤
        (12 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) *
          p53CpowEndpointBound U V a b *
            (200 * (q : ℝ) ^ 2 * (5 + |s.im| + |t|) ^ 2) := by
      gcongr
      · simpa only [add_comm] using hGamma
    _ = _ := by ring

/-- Uniform majorant for either horizontal edge of the literal p.53
rectangle. -/
def p53HorizontalEnvelope
    (q : ℕ) (s : ℂ) (U V a b B : ℝ) : ℝ :=
  2400 * (q : ℝ) ^ 2 * (1 + B) *
    (5 + |s.im| + B) ^ 2 * Real.exp (-(Real.pi / 2) * B) *
      p53CpowEndpointBound U V a b

/-- Gamma decay beats the quadratic fixed-strip L-growth in the p.53
horizontal majorant. -/
theorem tendsto_p53HorizontalEnvelope_zero
    (q : ℕ) (s : ℂ) {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    (a b : ℝ) :
    Tendsto (p53HorizontalEnvelope q s U V a b) atTop (𝓝 0) := by
  let C : ℝ := 5 + |s.im|
  let c : ℝ := Real.pi / 2
  let K : ℝ := 2400 * (q : ℝ) ^ 2 * p53CpowEndpointBound U V a b
  have hc : 1 ≤ c := by
    dsimp [c]
    nlinarith [Real.pi_gt_three]
  let G : ℝ → ℝ := fun B =>
    K * Real.exp C *
      ((C + c * B) ^ 3 * Real.exp (-(C + c * B)))
  have hscale : Tendsto (fun B : ℝ => C + c * B) atTop atTop := by
    exact tendsto_atTop_add_const_left atTop C
      (tendsto_id.const_mul_atTop (lt_of_lt_of_le (by norm_num) hc))
  have hpoly : Tendsto (fun B : ℝ =>
      (C + c * B) ^ 3 * Real.exp (-(C + c * B))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).comp hscale
  have hG : Tendsto G atTop (𝓝 0) := by
    simpa [G] using hpoly.const_mul (K * Real.exp C)
  apply squeeze_zero' (g := G)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
    unfold p53HorizontalEnvelope
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg (q : ℝ)))
            (by positivity))
          (sq_nonneg _))
        (Real.exp_pos _).le)
      (p53CpowEndpointBound_nonneg hU hV a b)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hCB : 1 + B ≤ C + B := by dsimp [C]; linarith [abs_nonneg s.im]
    have hCcB : C + B ≤ C + c * B := by
      have := mul_le_mul_of_nonneg_right hc hB
      linarith
    have hpow : (1 + B) * (C + B) ^ 2 ≤ (C + c * B) ^ 3 := by
      have h1 : 0 ≤ 1 + B := by linarith
      have h2 : 0 ≤ C + B := by positivity
      calc
        (1 + B) * (C + B) ^ 2 ≤ (C + B) * (C + B) ^ 2 :=
          mul_le_mul_of_nonneg_right hCB (sq_nonneg _)
        _ = (C + B) ^ 3 := by ring
        _ ≤ (C + c * B) ^ 3 := pow_le_pow_left₀ (by positivity) hCcB 3
    have hexpRewrite :
        Real.exp C * Real.exp (-(C + c * B)) = Real.exp (-(c * B)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hleft : p53HorizontalEnvelope q s U V a b B =
        K * ((1 + B) * (C + B) ^ 2 * Real.exp (-(c * B))) := by
      dsimp [p53HorizontalEnvelope, K, C, c]
      ring
    have hright : G B =
        K * ((C + c * B) ^ 3 * Real.exp (-(c * B))) := by
      dsimp [G]
      calc
        K * Real.exp C * ((C + c * B) ^ 3 *
            Real.exp (-(C + c * B))) =
            K * (C + c * B) ^ 3 *
              (Real.exp C * Real.exp (-(C + c * B))) := by ring
        _ = K * ((C + c * B) ^ 3 * Real.exp (-(c * B))) := by
          rw [hexpRewrite]
          ring
    rw [hleft, hright]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le)
      (by
        dsimp [K]
        exact mul_nonneg
          (mul_nonneg (by positivity) (sq_nonneg (q : ℝ)))
          (p53CpowEndpointBound_nonneg hU hV a b))
  · exact hG

/-- Either oriented horizontal edge tends to zero.  The sign parameter is
restricted to `±1`, exactly the two edges used by the finite rectangle. -/
theorem tendsto_p53HorizontalIntegral_zero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (s : ℂ) {U V a b ε : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hab : a ≤ b) (haGamma : -(1 / 2 : ℝ) ≤ a)
    (hbGamma : b ≤ 1 / 2)
    (hLLo : -1 ≤ 1 + s.re + a) (hLHi : 1 + s.re + b ≤ 2)
    (hε : |ε| = 1) :
    Tendsto (fun B : ℝ =>
      ∫ x : ℝ in a..b,
        p53TwoScaleContourIntegrand chi s U V ((x : ℂ) + (ε * B) * I))
      atTop (𝓝 0) := by
  have henv := tendsto_p53HorizontalEnvelope_zero q s hU hV a b
  have hbound : ∀ᶠ B : ℝ in atTop,
      ‖∫ x : ℝ in a..b,
          p53TwoScaleContourIntegrand chi s U V ((x : ℂ) + (ε * B) * I)‖ ≤
        p53HorizontalEnvelope q s U V a b B * |b - a| := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with B hB
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Set.Icc a b := by
      have := Set.uIoc_subset_uIcc hx
      simpa [Set.uIcc_of_le hab] using this
    have hB0 : 0 ≤ B := le_trans (by norm_num) hB
    have habs : 1 ≤ |ε * B| := by
      rw [abs_mul, hε, one_mul, abs_of_nonneg hB0]
      exact hB
    have haxGamma : -(1 / 2 : ℝ) ≤ x := haGamma.trans hx'.1
    have hxbGamma : x ≤ 1 / 2 := hx'.2.trans hbGamma
    have hxLLo : -1 ≤ 1 + s.re + x := by
      calc
        -1 ≤ 1 + s.re + a := hLLo
        _ ≤ 1 + s.re + x := by
          convert add_le_add_left hx'.1 (1 + s.re) using 1 <;> ring
    have hxLHi : 1 + s.re + x ≤ 2 := by
      calc
        1 + s.re + x ≤ 1 + s.re + b := by
          convert add_le_add_left hx'.2 (1 + s.re) using 1 <;> ring
        _ ≤ 2 := hLHi
    simpa [p53HorizontalEnvelope, abs_mul, hε, abs_of_nonneg hB0] using
      norm_p53TwoScaleContourIntegrand_horizontal_le chi hchi s hU hV
        hx'.1 hx'.2 haxGamma hxbGamma hxLLo hxLHi habs
  have henvMul : Tendsto (fun B : ℝ =>
      p53HorizontalEnvelope q s U V a b B * |b - a|) atTop (𝓝 0) := by
    simpa using henv.mul_const |b - a|
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
  · exact hbound
  · exact henvMul

/-- The literal p.53 integrand is integrable on the fixed deep line
`Re w = -1/2`.  The compact central segment is handled by holomorphy and the
tails by the displayed Gamma/L envelope. -/
theorem integrable_p53TwoScaleContourIntegrand_leftHalf
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (s : ℂ) {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hLLo : -1 ≤ 1 + s.re - 1 / 2)
    (hLHi : 1 + s.re - 1 / 2 ≤ 2) :
    Integrable (fun t : ℝ =>
      p53TwoScaleContourIntegrand chi s U V
        (((-(1 / 2 : ℝ)) : ℂ) + t * I)) := by
  let F : ℝ → ℂ := fun t =>
    p53TwoScaleContourIntegrand chi s U V
      (((-(1 / 2 : ℝ)) : ℂ) + t * I)
  let C : ℝ := 5 + |s.im|
  let K : ℝ := 2400 * (q : ℝ) ^ 2 * C ^ 2 *
    p53CpowEndpointBound U V (-(1 / 2)) (-(1 / 2))
  let E : ℝ → ℝ := fun t =>
    K * ((1 + |t|) ^ 6 * Real.exp (-|t|))
  let S : Set ℝ := {t | 1 ≤ |t|}
  have hcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro t
    have hinner : ContinuousAt (fun u : ℝ =>
        (((-(1 / 2 : ℝ)) : ℂ) + u * I)) t := by fun_prop
    have houter :=
      (differentiableAt_p53TwoScaleContourIntegrand_nonprincipal
        hchi s hU hV
        (((-(1 / 2 : ℝ)) : ℂ) + (t : ℂ) * I) (by norm_num)).continuousAt
    exact ContinuousAt.comp
      (f := fun u : ℝ => (((-(1 / 2 : ℝ)) : ℂ) + u * I))
      (g := p53TwoScaleContourIntegrand chi s U V)
      (x := t) houter hinner
  have hE : Integrable E := by
    exact integrable_one_add_abs_pow_six_mul_exp_neg_abs.const_mul K
  have htail : IntegrableOn F S := by
    apply hE.integrableOn.mono'
    · exact hcont.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem (by
          dsimp [S]
          exact measurableSet_le measurable_const measurable_abs :
            MeasurableSet S)] with t ht
      have hraw := norm_p53TwoScaleContourIntegrand_horizontal_le
        chi hchi s hU hV
        (a := -(1 / 2)) (b := -(1 / 2)) (x := -(1 / 2))
        (t := t) le_rfl le_rfl (by norm_num) (by norm_num)
        hLLo hLHi ht
      have hC : 1 ≤ C := by dsimp [C]; linarith [abs_nonneg s.im]
      have hu : 0 ≤ |t| := abs_nonneg t
      have hCu : C + |t| ≤ C * (1 + |t|) := by nlinarith
      have hCpow : (C + |t|) ^ 2 ≤ C ^ 2 * (1 + |t|) ^ 2 := by
        calc
          (C + |t|) ^ 2 ≤ (C * (1 + |t|)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hCu 2
          _ = C ^ 2 * (1 + |t|) ^ 2 := by ring
      have hpow : (1 + |t|) ^ 3 ≤ (1 + |t|) ^ 6 := by
        exact pow_le_pow_right₀ (by linarith) (by norm_num)
      have hexp : Real.exp (-(Real.pi / 2) * |t|) ≤ Real.exp (-|t|) := by
        apply Real.exp_le_exp.mpr
        have hpi : 1 ≤ Real.pi / 2 := by nlinarith [Real.pi_gt_three]
        nlinarith
      have hK0 : 0 ≤ 2400 * (q : ℝ) ^ 2 := by positivity
      have hendpoint0 := p53CpowEndpointBound_nonneg hU hV
        (-(1 / 2)) (-(1 / 2))
      calc
        ‖F t‖ ≤ 2400 * (q : ℝ) ^ 2 * (1 + |t|) *
            (C + |t|) ^ 2 * Real.exp (-(Real.pi / 2) * |t|) *
              p53CpowEndpointBound U V (-(1 / 2)) (-(1 / 2)) := by
          simpa [F, C] using hraw
        _ ≤ 2400 * (q : ℝ) ^ 2 * (1 + |t|) *
            (C ^ 2 * (1 + |t|) ^ 2) * Real.exp (-|t|) *
              p53CpowEndpointBound U V (-(1 / 2)) (-(1 / 2)) := by
          gcongr
        _ = K * ((1 + |t|) ^ 3 * Real.exp (-|t|)) := by
          dsimp [K]
          ring
        _ ≤ K * ((1 + |t|) ^ 6 * Real.exp (-|t|)) := by
          have hKnonneg : 0 ≤ K := by
            dsimp [K]
            exact mul_nonneg
              (mul_nonneg hK0 (sq_nonneg C)) hendpoint0
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le) hKnonneg
        _ = E t := rfl
  have hcentral : IntegrableOn F (Set.Icc (-1) 1) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hcover : Set.Icc (-1 : ℝ) 1 ∪ S = Set.univ := by
    ext t
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_setOf_eq, Set.mem_univ,
      iff_true]
    by_cases h : -1 ≤ t ∧ t ≤ 1
    · exact Or.inl h
    · right
      rw [not_and_or] at h
      rcases h with h | h
      · change 1 ≤ |t|
        rw [abs_of_neg (by linarith)]
        linarith
      · change 1 ≤ |t|
        rw [abs_of_pos (by linarith)]
        linarith
  have hall := hcentral.union htail
  rw [hcover] at hall
  exact integrableOn_univ.mp hall

/-- The complementary Gamma estimate on `1/2 ≤ Re w ≤ 1`, obtained by
one use of `Gamma (w+1) = w Gamma(w)`. -/
theorem norm_p53TwoScaleContourIntegrand_horizontal_rightHalf_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (s : ℂ) {U V a b x t : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hax : a ≤ x) (hxb : x ≤ b) (hxLo : 1 / 2 ≤ x) (hxHi : x ≤ 1)
    (hsHi : s.re ≤ 1 / 2) (hLLo : -1 ≤ 1 + s.re + x)
    (ht : 1 ≤ |t|) :
    ‖p53TwoScaleContourIntegrand chi s U V ((x : ℂ) + t * I)‖ ≤
      2400 * (q : ℝ) ^ 2 * (1 + |t|) ^ 2 *
        (6 + |s.im| + |t|) ^ 2 *
          Real.exp (-(Real.pi / 2) * |t|) *
            p53CpowEndpointBound U V a b := by
  let w : ℂ := (x : ℂ) + t * I
  let z : ℂ := 1 + s + w
  have hw : w ≠ 0 := by
    intro heq
    have hre := congrArg Complex.re heq
    simp [w] at hre
    linarith
  have hzRe : z.re = 1 + s.re + x := by simp [z, w]
  have hzNorm : ‖z + 3‖ ≤ 6 + |s.im| + |t| := by
    calc
      ‖z + 3‖ ≤ |(z + 3).re| + |(z + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |4 + s.re + x| + |s.im + t| := by simp [z, w]; ring
      _ ≤ 6 + (|s.im| + |t|) := by
        have hre0 : 0 ≤ 4 + s.re + x := by linarith
        rw [abs_of_nonneg hre0]
        exact add_le_add (by linarith) (abs_add_le _ _)
      _ = 6 + |s.im| + |t| := by ring
  have hL : ‖DirichletCharacter.LFunction chi z‖ ≤
      200 * (q : ℝ) ^ 2 * (6 + |s.im| + |t|) ^ 2 := by
    by_cases hzHi : z.re ≤ 2
    · have hL0 := PLInteriorGrowth.norm_LFunction_fixedStrip_le chi hchi
          (by rw [hzRe]; exact hLLo) hzHi
      exact hL0.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hzNorm 2) (by positivity))
    · have h3 := (norm_LFunction_lt_three_of_two_le_re chi
          (le_of_not_ge hzHi)).le
      have hq : (1 : ℝ) ≤ q := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
      have hbase : 1 ≤ 6 + |s.im| + |t| := by
        linarith [abs_nonneg s.im, abs_nonneg t]
      calc
        ‖DirichletCharacter.LFunction chi z‖ ≤ 3 := h3
        _ ≤ 200 * (q : ℝ) ^ 2 * (6 + |s.im| + |t|) ^ 2 := by
          nlinarith [sq_nonneg ((q : ℝ) - 1), sq_nonneg ((6 + |s.im| + |t|) - 1)]
  have hbase := norm_Gamma_positive_strip_le_exp_pi_half
    hxLo (hxHi.trans (by norm_num)) (t := t)
  have hbasePoint :
      GammaCompactStripScratch.stripPoint x t = w := by
    apply Complex.ext <;> simp [GammaCompactStripScratch.stripPoint, w]
  rw [hbasePoint] at hbase
  have hwNorm : ‖w‖ ≤ 1 + |t| := by
    calc
      ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im _
      _ = x + |t| := by simp [w, abs_of_nonneg (by linarith : 0 ≤ x)]
      _ ≤ 1 + |t| := by linarith
  have hGamma : ‖Complex.Gamma (w + 1)‖ ≤
      12 * (1 + |t|) ^ 2 * Real.exp (-(Real.pi / 2) * |t|) := by
    rw [Complex.Gamma_add_one w hw, norm_mul]
    calc
      ‖w‖ * ‖Complex.Gamma w‖ ≤
          (1 + |t|) *
            (12 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) := by
        gcongr
      _ = 12 * (1 + |t|) ^ 2 *
          Real.exp (-(Real.pi / 2) * |t|) := by ring
  have hQ := norm_p53ScaleRemovableQuotient_horizontal_le
    hU hV hax hxb ht
  have hQ0 := p53CpowEndpointBound_nonneg hU hV a b
  unfold p53TwoScaleContourIntegrand
  simp only [norm_mul]
  calc
    ‖Complex.Gamma (w + 1)‖ *
          ‖p53ScaleRemovableQuotient U V w‖ *
          ‖DirichletCharacter.LFunction chi z‖ ≤
        (12 * (1 + |t|) ^ 2 *
          Real.exp (-(Real.pi / 2) * |t|)) *
          p53CpowEndpointBound U V a b *
            (200 * (q : ℝ) ^ 2 * (6 + |s.im| + |t|) ^ 2) := by
      gcongr
    _ = _ := by ring

/-- Horizontal decay for the actual p.53 rectangle
`[-1/2,1] × [-B,B]`. -/
theorem tendsto_p53FullHorizontalIntegral_zero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (s : ℂ) {U V ε : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 2) (hε : |ε| = 1) :
    Tendsto (fun B : ℝ =>
      ∫ x : ℝ in -(1 / 2)..1,
        p53TwoScaleContourIntegrand chi s U V ((x : ℂ) + (ε * B) * I))
      atTop (𝓝 0) := by
  let C : ℝ := 6 + |s.im|
  let P : ℝ := p53CpowEndpointBound U V (-(1 / 2)) 1
  let K : ℝ := 2400 * (q : ℝ) ^ 2 * C ^ 2 * P
  let E : ℝ → ℝ := fun B =>
    K * ((1 + B) ^ 4 * Real.exp (-B))
  have hE : Tendsto E atTop (𝓝 0) := by
    have hshift : Tendsto (fun B : ℝ => 1 + B) atTop atTop :=
      Filter.tendsto_atTop_add_const_left atTop 1 tendsto_id
    have hcore :=
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).comp hshift
    have hscaled := hcore.const_mul (K * Real.exp 1)
    have hscaled' : Tendsto (fun B : ℝ =>
        (K * Real.exp 1) * ((1 + B) ^ 4 * Real.exp (-(1 + B))))
        atTop (𝓝 0) := by
      simpa only [Function.comp_apply, mul_zero] using hscaled
    convert hscaled' using 1
    funext B
    dsimp [E]
    have hexp : Real.exp 1 * Real.exp (-(1 + B)) = Real.exp (-B) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      K * ((1 + B) ^ 4 * Real.exp (-B)) =
          K * ((1 + B) ^ 4 *
            (Real.exp 1 * Real.exp (-(1 + B)))) := by rw [hexp]
      _ = K * Real.exp 1 *
          ((1 + B) ^ 4 * Real.exp (-(1 + B))) := by ring
  have hbound : ∀ᶠ B : ℝ in atTop,
      ‖∫ x : ℝ in -(1 / 2)..1,
          p53TwoScaleContourIntegrand chi s U V ((x : ℂ) + (ε * B) * I)‖ ≤
        E B * |(1 : ℝ) - (-(1 / 2))| := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with B hB
    have hB0 : 0 ≤ B := by linarith
    have habs : |ε * B| = B := by rw [abs_mul, hε, one_mul, abs_of_nonneg hB0]
    have ht : 1 ≤ |ε * B| := by rw [habs]; exact hB
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Set.Icc (-(1 / 2 : ℝ)) 1 := by
      have := Set.uIoc_subset_uIcc hx
      rw [Set.uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1)] at this
      exact this
    have hxLLo : -1 ≤ 1 + s.re + x := by linarith [hx'.1]
    have hpoint :
        ‖p53TwoScaleContourIntegrand chi s U V
            ((x : ℂ) + (ε * B) * I)‖ ≤
          2400 * (q : ℝ) ^ 2 * (1 + B) ^ 2 *
            (C + B) ^ 2 * Real.exp (-(Real.pi / 2) * B) * P := by
      by_cases hxhalf : x ≤ 1 / 2
      · have hxLHi : 1 + s.re + x ≤ 2 := by linarith
        have h := norm_p53TwoScaleContourIntegrand_horizontal_le
            chi hchi s hU hV (a := -(1 / 2)) (b := 1) (x := x)
            (t := ε * B) hx'.1 hx'.2 hx'.1 hxhalf hxLLo hxLHi ht
        calc
          _ ≤ 2400 * (q : ℝ) ^ 2 * (1 + B) *
              (5 + |s.im| + B) ^ 2 *
              Real.exp (-(Real.pi / 2) * B) * P := by
            simpa [P, habs] using h
          _ ≤ 2400 * (q : ℝ) ^ 2 * (1 + B) * (C + B) ^ 2 *
              Real.exp (-(Real.pi / 2) * B) * P := by
            have hsmall : 5 + |s.im| + B ≤ C + B := by dsimp [C]; linarith
            have hP0 : 0 ≤ P := by
              dsimp [P]
              exact p53CpowEndpointBound_nonneg hU hV _ _
            gcongr
          _ ≤ 2400 * (q : ℝ) ^ 2 * (1 + B) ^ 2 * (C + B) ^ 2 *
              Real.exp (-(Real.pi / 2) * B) * P := by
            have hfac : 1 + B ≤ (1 + B) ^ 2 := by nlinarith
            have hP0 : 0 ≤ P := by
              dsimp [P]
              exact p53CpowEndpointBound_nonneg hU hV _ _
            gcongr
      · have hxhalf' : 1 / 2 ≤ x := le_of_not_ge hxhalf
        have h := norm_p53TwoScaleContourIntegrand_horizontal_rightHalf_le
          chi hchi s hU hV (a := -(1 / 2)) (b := 1) (x := x)
          (t := ε * B) hx'.1 hx'.2 hxhalf' hx'.2 hsHi hxLLo ht
        simpa [C, P, habs] using h
    have hC : 1 ≤ C := by dsimp [C]; linarith [abs_nonneg s.im]
    have hCB : C + B ≤ C * (1 + B) := by nlinarith
    have hCBpow : (C + B) ^ 2 ≤ C ^ 2 * (1 + B) ^ 2 := by
      calc
        (C + B) ^ 2 ≤ (C * (1 + B)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hCB 2
        _ = C ^ 2 * (1 + B) ^ 2 := by ring
    have hexp : Real.exp (-(Real.pi / 2) * B) ≤ Real.exp (-B) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_gt_three]
    calc
      _ ≤ 2400 * (q : ℝ) ^ 2 * (1 + B) ^ 2 *
          (C + B) ^ 2 * Real.exp (-(Real.pi / 2) * B) * P := hpoint
      _ ≤ 2400 * (q : ℝ) ^ 2 * (1 + B) ^ 2 *
          (C ^ 2 * (1 + B) ^ 2) * Real.exp (-B) * P := by
        have hP0 : 0 ≤ P := by
          dsimp [P]
          exact p53CpowEndpointBound_nonneg hU hV _ _
        gcongr
      _ = E B := by dsimp [E, K, P]; ring
  have hEmul : Tendsto (fun B => E B * |(1 : ℝ) - (-(1 / 2))|)
      atTop (𝓝 0) := by simpa using hE.mul_const |(1 : ℝ) - (-(1 / 2))|
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
  · exact hbound
  · exact hEmul

/-- Uniform bound for the removable scale quotient on `Re w=-1/2`, including
the central ordinate. -/
theorem norm_p53ScaleRemovableQuotient_leftHalf_le
    {U V t : ℝ} (hU : 0 < U) (hV : 0 < V) :
    ‖p53ScaleRemovableQuotient U V
      (((-(1 / 2 : ℝ)) : ℂ) + t * I)‖ ≤
      2 * p53CpowEndpointBound U V (-(1 / 2)) (-(1 / 2)) := by
  let w : ℂ := (((-(1 / 2 : ℝ)) : ℂ) + t * I)
  have hw : w ≠ 0 := by
    intro heq
    have hre := congrArg Complex.re heq
    norm_num [w] at hre
  have hden : (1 / 2 : ℝ) ≤ ‖w‖ := by
    have := Complex.abs_re_le_norm w
    simpa [w] using this
  have hpU := norm_posReal_cpow_horizontal_le_max hU
    (a := -(1 / 2)) (b := -(1 / 2)) (x := -(1 / 2))
    (t := t) le_rfl le_rfl
  have hpV := norm_posReal_cpow_horizontal_le_max hV
    (a := -(1 / 2)) (b := -(1 / 2)) (x := -(1 / 2))
    (t := t) le_rfl le_rfl
  rw [p53ScaleRemovableQuotient, Function.update_of_ne hw, norm_div]
  calc
    ‖p53ScaleDifference U V w‖ / ‖w‖ ≤
        ‖p53ScaleDifference U V w‖ / (1 / 2 : ℝ) := by
      exact div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hden
    _ = 2 * ‖p53ScaleDifference U V w‖ := by ring
    _ ≤ 2 * (‖(U : ℂ) ^ w‖ + ‖(V : ℂ) ^ w‖) := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ 2 * p53CpowEndpointBound U V (-(1 / 2)) (-(1 / 2)) := by
      gcongr
      simpa [w, p53CpowEndpointBound] using add_le_add hpU hpV

/-- Global pointwise envelope on `Re w=-1/2`; unlike the horizontal estimate
this has no `|t|≥1` restriction. -/
theorem norm_p53TwoScaleContourIntegrand_leftHalf_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (s : ℂ) {U V t : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 2) :
    ‖p53TwoScaleContourIntegrand chi s U V
      (((-(1 / 2 : ℝ)) : ℂ) + t * I)‖ ≤
      4800 * (q : ℝ) ^ 2 * (1 + |t|) *
        (5 + |s.im| + |t|) ^ 2 *
          Real.exp (-(Real.pi / 2) * |t|) *
            p53CpowEndpointBound U V (-(1 / 2)) (-(1 / 2)) := by
  let x : ℝ := -(1 / 2)
  let w : ℂ := (x : ℂ) + t * I
  let z : ℂ := 1 + s + w
  have hzRe : z.re = 1 + s.re + x := by simp [z, w]
  have hzNorm : ‖z + 3‖ ≤ 5 + |s.im| + |t| := by
    calc
      ‖z + 3‖ ≤ |(z + 3).re| + |(z + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |4 + s.re + x| + |s.im + t| := by simp [z, w]; ring
      _ ≤ 5 + (|s.im| + |t|) := by
        have hre0 : 0 ≤ 4 + s.re + x := by dsimp [x]; linarith
        rw [abs_of_nonneg hre0]
        exact add_le_add (by dsimp [x]; linarith) (abs_add_le _ _)
      _ = 5 + |s.im| + |t| := by ring
  have hL0 := PLInteriorGrowth.norm_LFunction_fixedStrip_le chi hchi
    (by rw [hzRe]; dsimp [x]; linarith)
    (by rw [hzRe]; dsimp [x]; linarith)
  have hL : ‖DirichletCharacter.LFunction chi z‖ ≤
      200 * (q : ℝ) ^ 2 * (5 + |s.im| + |t|) ^ 2 :=
    hL0.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hzNorm 2) (by positivity))
  have hGammaPoint : w + 1 =
      GammaCompactStripScratch.stripPoint (1 / 2) t := by
    apply Complex.ext <;> simp [w, x, GammaCompactStripScratch.stripPoint] <;>
      norm_num
  have hGamma := norm_Gamma_positive_strip_le_exp_pi_half
    (show (1 / 2 : ℝ) ≤ 1 / 2 by rfl)
    (show (1 / 2 : ℝ) ≤ 3 / 2 by norm_num) (t := t)
  rw [← hGammaPoint] at hGamma
  have hQ := norm_p53ScaleRemovableQuotient_leftHalf_le hU hV (t := t)
  have hQ' : ‖p53ScaleRemovableQuotient U V w‖ ≤
      2 * p53CpowEndpointBound U V (-(1 / 2)) (-(1 / 2)) := by
    simpa [w, x] using hQ
  have hP0 := p53CpowEndpointBound_nonneg hU hV (-(1 / 2)) (-(1 / 2))
  have hcalc : ‖Complex.Gamma (w + 1)‖ *
      ‖p53ScaleRemovableQuotient U V w‖ *
      ‖DirichletCharacter.LFunction chi z‖ ≤
      4800 * (q : ℝ) ^ 2 * (1 + |t|) *
        (5 + |s.im| + |t|) ^ 2 *
          Real.exp (-(Real.pi / 2) * |t|) *
            p53CpowEndpointBound U V (-(1 / 2)) (-(1 / 2)) := by
    calc
      ‖Complex.Gamma (w + 1)‖ *
            ‖p53ScaleRemovableQuotient U V w‖ *
            ‖DirichletCharacter.LFunction chi z‖ ≤
          (12 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) *
            (2 * p53CpowEndpointBound U V (-(1 / 2)) (-(1 / 2))) *
            (200 * (q : ℝ) ^ 2 * (5 + |s.im| + |t|) ^ 2) := by
        gcongr
      _ = _ := by ring
  unfold p53TwoScaleContourIntegrand
  simp only [norm_mul]
  simpa [w, x, z] using hcalc

/-- Quantitative integral form of the left-line estimate.  The remaining
universal integral is finite and independent of every arithmetic parameter. -/
theorem norm_integral_p53TwoScaleContourIntegrand_leftHalf_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (s : ℂ) {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 2) :
    ‖∫ t : ℝ, p53TwoScaleContourIntegrand chi s U V
        (((-(1 / 2 : ℝ)) : ℂ) + t * I)‖ ≤
      (4800 * (q : ℝ) ^ 2 * (5 + |s.im|) ^ 2 *
        p53CpowEndpointBound U V (-(1 / 2)) (-(1 / 2))) *
        ∫ t : ℝ, (1 + |t|) ^ 6 * Real.exp (-|t|) := by
  let K : ℝ := 4800 * (q : ℝ) ^ 2 * (5 + |s.im|) ^ 2 *
    p53CpowEndpointBound U V (-(1 / 2)) (-(1 / 2))
  let E : ℝ → ℝ := fun t => K * ((1 + |t|) ^ 6 * Real.exp (-|t|))
  have hE : Integrable E :=
    integrable_one_add_abs_pow_six_mul_exp_neg_abs.const_mul K
  calc
    _ ≤ ∫ t : ℝ, E t := by
      apply MeasureTheory.norm_integral_le_of_norm_le hE
      filter_upwards [] with t
      have hraw := norm_p53TwoScaleContourIntegrand_leftHalf_le
        chi hchi s hU hV hsLo hsHi (t := t)
      have hC : 1 ≤ 5 + |s.im| := by linarith [abs_nonneg s.im]
      have hCu : 5 + |s.im| + |t| ≤
          (5 + |s.im|) * (1 + |t|) := by
        nlinarith [mul_nonneg
          (show 0 ≤ 4 + |s.im| by linarith [abs_nonneg s.im])
          (abs_nonneg t)]
      have hpow2 : (5 + |s.im| + |t|) ^ 2 ≤
          (5 + |s.im|) ^ 2 * (1 + |t|) ^ 2 := by
        calc
          _ ≤ ((5 + |s.im|) * (1 + |t|)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hCu 2
          _ = _ := by ring
      have hpow3 : (1 + |t|) ^ 3 ≤ (1 + |t|) ^ 6 :=
        pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by norm_num)
      have hexp : Real.exp (-(Real.pi / 2) * |t|) ≤ Real.exp (-|t|) := by
        apply Real.exp_le_exp.mpr
        nlinarith [Real.pi_gt_three, abs_nonneg t]
      have hP0 := p53CpowEndpointBound_nonneg hU hV
        (-(1 / 2)) (-(1 / 2))
      calc
        _ ≤ 4800 * (q : ℝ) ^ 2 * (1 + |t|) *
            (5 + |s.im| + |t|) ^ 2 *
              Real.exp (-(Real.pi / 2) * |t|) *
                p53CpowEndpointBound U V (-(1 / 2)) (-(1 / 2)) := hraw
        _ ≤ 4800 * (q : ℝ) ^ 2 * (1 + |t|) *
            ((5 + |s.im|) ^ 2 * (1 + |t|) ^ 2) *
              Real.exp (-(Real.pi / 2) * |t|) *
                p53CpowEndpointBound U V (-(1 / 2)) (-(1 / 2)) := by
          have hlead : 0 ≤ 4800 * (q : ℝ) ^ 2 * (1 + |t|) := by positivity
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpow2 hlead)
              (Real.exp_pos _).le) hP0
        _ ≤ 4800 * (q : ℝ) ^ 2 * (1 + |t|) *
            ((5 + |s.im|) ^ 2 * (1 + |t|) ^ 2) *
              Real.exp (-|t|) *
                p53CpowEndpointBound U V (-(1 / 2)) (-(1 / 2)) := by
          have hlead : 0 ≤ 4800 * (q : ℝ) ^ 2 * (1 + |t|) *
              ((5 + |s.im|) ^ 2 * (1 + |t|) ^ 2) := by positivity
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hexp hlead) hP0
        _ = K * ((1 + |t|) ^ 3 * Real.exp (-|t|)) := by
          dsimp [K]
          ring
        _ ≤ K * ((1 + |t|) ^ 6 * Real.exp (-|t|)) := by
          have hK0 : 0 ≤ K := by
            dsimp [K]
            exact mul_nonneg
              (mul_nonneg
                (mul_nonneg (by positivity) (sq_nonneg (q : ℝ)))
                (sq_nonneg (5 + |s.im|))) hP0
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hpow3 (Real.exp_pos _).le) hK0
        _ = E t := rfl
    _ = _ := by
      rw [MeasureTheory.integral_const_mul]

end

end MAPJutilaP53LeftLineEstimate

#print axioms MAPJutilaP53LeftLineEstimate.norm_p53TwoScaleContourIntegrand_horizontal_le
#print axioms MAPJutilaP53LeftLineEstimate.tendsto_p53FullHorizontalIntegral_zero
#print axioms MAPJutilaP53LeftLineEstimate.integrable_p53TwoScaleContourIntegrand_leftHalf
#print axioms MAPJutilaP53LeftLineEstimate.norm_integral_p53TwoScaleContourIntegrand_leftHalf_le
