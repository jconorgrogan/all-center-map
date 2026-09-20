import JutilaP53PrincipalLeftLineEstimate
import JutilaP53SourceLineEstimate

namespace MAPJutilaP53PrincipalSourceHorizontalDecay
open Complex Real MeasureTheory Set Filter Topology
open MAPJutilaP53TwoScaleContour MAPJutilaP53LeftLineEstimate
open MAPJutilaP53PrincipalLeftLineEstimate MAPJutilaP53SourceLineEstimate
open MAPGammaCompactStripSharp MAPPrimitiveLFixedStrip
open DirichletZeros MAPPrincipalZetaFixedStrip MAPBHPPrincipalNegativeEulerBound
noncomputable section
theorem norm_principal_LFunction_sourceHorizontal_le
    (q : ℕ) [NeZero q] {s : ℂ} (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 4)
    {x B epsilon : ℝ} (hxLo : -1 ≤ x) (hxHi : x ≤ 1)
    (hB : 2 * (1 + |s.im|) ≤ B) (hepsilon : |epsilon| = 1) :
    ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)
      (1 + s + ((x : ℂ) + (epsilon * B) * I))‖ ≤
      1600 * (2 : ℝ) ^ q.primeFactors.card *
        (7 + |s.im| + B) ^ 6 := by
  let z : ℂ := 1 + s + ((x : ℂ) + (epsilon * B) * I)
  have hB0 : 0 ≤ B := by linarith [abs_nonneg s.im]
  have hzRe : z.re = 1 + s.re + x := by simp [z]
  have hzIm : z.im = s.im + epsilon * B := by simp [z]
  have hzNorm : ‖z + 3‖ ≤ 7 + |s.im| + B := by
    calc
      ‖z + 3‖ ≤ |(z + 3).re| + |(z + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |4 + s.re + x| + |s.im + epsilon * B| := by simp [z]; ring
      _ ≤ (6 : ℝ) + (|s.im| + B) := by
        have hre0 : 0 ≤ 4 + s.re + x := by linarith
        rw [abs_of_nonneg hre0]
        have him := abs_add_le s.im (epsilon * B)
        rw [abs_mul, hepsilon, one_mul, abs_of_nonneg hB0] at him
        linarith
      _ ≤ 7 + |s.im| + B := by linarith
  by_cases hzHi : z.re ≤ 2
  · have hzLo : 0 ≤ z.re := by rw [hzRe]; linarith
    have hz1 : z ≠ 1 := by
      intro hzOne
      have himOne := congrArg Complex.im hzOne
      rw [hzIm] at himOne
      simp only [one_im] at himOne
      have hsep : 1 ≤ |s.im + epsilon * B| := by
        have htri : B ≤ |s.im + epsilon * B| + |s.im| := by
          calc
            B = |epsilon * B| := by
              rw [abs_mul, hepsilon, one_mul, abs_of_nonneg hB0]
            _ = |(s.im + epsilon * B) - s.im| := by ring_nf
            _ ≤ |s.im + epsilon * B| + |s.im| := abs_sub _ _
        linarith
      rw [himOne, abs_zero] at hsep
      norm_num at hsep
    have hregEq : regularizedLFunction (1 : DirichletCharacter ℂ q) z =
        (z - 1) * DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ q) z := by
      unfold regularizedLFunction
      simp only [if_pos]
      unfold DirichletCharacter.LFunctionTrivChar₁
      rw [Function.update_of_ne hz1]
    have hden : 1 ≤ ‖z - 1‖ := by
      have him : 1 ≤ |z.im| := by
        rw [hzIm]
        have htri : B ≤ |s.im + epsilon * B| + |s.im| := by
          calc
            B = |epsilon * B| := by
              rw [abs_mul, hepsilon, one_mul, abs_of_nonneg hB0]
            _ = |(s.im + epsilon * B) - s.im| := by ring_nf
            _ ≤ |s.im + epsilon * B| + |s.im| := abs_sub _ _
        linarith
      exact him.trans (by simpa using Complex.abs_im_le_norm (z - 1))
    have hreg := norm_regularized_principal_fixedStrip_le_twoPow q hzLo hzHi
    rw [hregEq, norm_mul] at hreg
    change ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) z‖ ≤ _
    calc
      _ ≤ ‖z - 1‖ * ‖DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ q) z‖ := by
        nlinarith [norm_nonneg (DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ q) z)]
      _ ≤ 1600 * ‖z + 3‖ ^ 6 * (2 : ℝ) ^ q.primeFactors.card := hreg
      _ ≤ 1600 * (7 + |s.im| + B) ^ 6 *
          (2 : ℝ) ^ q.primeFactors.card := by gcongr
      _ = _ := by ring
  · have hL := (norm_LFunction_lt_three_of_two_le_re
        (1 : DirichletCharacter ℂ q) (le_of_not_ge hzHi)).le
    change ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) z‖ ≤ _
    calc
      _ ≤ 3 := hL
      _ ≤ 1600 * (2 : ℝ) ^ q.primeFactors.card *
          (7 + |s.im| + B) ^ 6 := by
        have hbase : 1 ≤ 7 + |s.im| + B := by linarith [abs_nonneg s.im]
        have hpow : 1 ≤ (7 + |s.im| + B) ^ 6 := one_le_pow₀ hbase
        have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ q.primeFactors.card :=
          one_le_pow₀ (by norm_num)
        calc
          (3 : ℝ) ≤ 1600 := by norm_num
          _ ≤ 1600 * (2 : ℝ) ^ q.primeFactors.card := by nlinarith
          _ ≤ 1600 * (2 : ℝ) ^ q.primeFactors.card *
              (7 + |s.im| + B) ^ 6 := by
            have hcoef0 : 0 ≤ 1600 * (2 : ℝ) ^ q.primeFactors.card :=
              mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _)
            simpa using mul_le_mul_of_nonneg_left hpow hcoef0

theorem norm_p53PrincipalIntegrand_sourceHorizontal_le
    (q : ℕ) [NeZero q] (s : ℂ) {U V x B epsilon delta : ℝ}
    (hU : 0 < U) (hV : 0 < V)
    (hdelta : 0 < delta) (hdeltaHi : delta ≤ 1 / 8)
    (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 4)
    (hxLo : -1 + delta ≤ x) (hxHi : x ≤ 1)
    (hB : 2 * (1 + |s.im|) ≤ B) (hepsilon : |epsilon| = 1) :
    ‖p53TwoScaleContourIntegrand (1 : DirichletCharacter ℂ q) s U V
      ((x : ℂ) + (epsilon * B) * I)‖ ≤
      (19200 / delta) * (2 : ℝ) ^ q.primeFactors.card * (1 + B) ^ 2 *
        (7 + |s.im| + B) ^ 6 * Real.exp (-(Real.pi / 2) * B) *
        p53CpowEndpointBound U V (-1 + delta) 1 := by
  let t := epsilon * B
  let w : ℂ := (x : ℂ) + t * I
  have hB0 : 0 ≤ B := by linarith [abs_nonneg s.im]
  have htAbs : |t| = B := by
    dsimp [t]
    rw [abs_mul, hepsilon, one_mul, abs_of_nonneg hB0]
  have ht : 1 ≤ |t| := by rw [htAbs]; linarith [abs_nonneg s.im]
  have hGamma : ‖Complex.Gamma (w + 1)‖ ≤
      (12 / delta) * (1 + B) ^ 2 * Real.exp (-(Real.pi / 2) * B) := by
    by_cases hxdeep : x ≤ -(1 / 2)
    · have hraw := norm_Gamma_sourceStrip_le (t := t)
        (show 0 < 1 + x by linarith) (show 1 + x ≤ 1 / 2 by linarith)
      have hpoint : w + 1 = ((1 + x : ℝ) : ℂ) + (t : ℂ) * I := by
        apply Complex.ext <;> simp [w] <;> ring
      rw [hpoint]
      rw [htAbs] at hraw
      exact hraw.trans (by
        have hp : 1 + B ≤ (1 + B)^2 := by nlinarith
        gcongr <;> linarith)
    · have hxLo : -(1 / 2 : ℝ) ≤ x := le_of_not_ge hxdeep
      have hGammaOld : ‖Complex.Gamma (w + 1)‖ ≤
          12 * (1 + B) ^ 2 * Real.exp (-(Real.pi / 2) * B) := by
        by_cases hx : x ≤ 1 / 2
        · have hp := norm_Gamma_positive_strip_le_exp_pi_half
            (a := 1 + x) (t := t) (by linarith) (by linarith)
          have hpoint : w + 1 = GammaCompactStripScratch.stripPoint (1 + x) t := by
            apply Complex.ext <;> simp [w, GammaCompactStripScratch.stripPoint]
            ring
          rw [← hpoint, htAbs] at hp
          exact hp.trans (by
            have hfac : 1 + B ≤ (1 + B) ^ 2 := by nlinarith
            have hexp0 := (Real.exp_pos (-(Real.pi / 2) * B)).le
            nlinarith)
        · have hx' : 1 / 2 ≤ x := le_of_not_ge hx
          have hw : w ≠ 0 := by
            intro hw
            have hre := congrArg Complex.re hw
            simp [w] at hre
            linarith
          have hp := norm_Gamma_positive_strip_le_exp_pi_half
            (a := x) (t := t) hx' (hxHi.trans (by norm_num))
          have hpoint : w = GammaCompactStripScratch.stripPoint x t := by
            apply Complex.ext <;> simp [w, GammaCompactStripScratch.stripPoint]
          rw [← hpoint, htAbs] at hp
          have hwNorm : ‖w‖ ≤ 1 + B := by
            calc
              ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im _
              _ = |x| + B := by simp [w, htAbs]
              _ ≤ 1 + B := by
                have habsx : |x| ≤ 1 := abs_le.mpr ⟨by linarith, hxHi⟩
                linarith
          rw [Complex.Gamma_add_one w hw, norm_mul]
          calc
            ‖w‖ * ‖Complex.Gamma w‖ ≤
                (1 + B) * (12 * (1 + B) *
                  Real.exp (-(Real.pi / 2) * B)) := by gcongr
            _ = _ := by ring
      exact hGammaOld.trans (by
        have hc : (12 : ℝ) ≤ 12 / delta := (le_div_iff₀ hdelta).mpr (by linarith)
        gcongr)
  have hQ := norm_p53ScaleRemovableQuotient_horizontal_le hU hV
    (a := -1 + delta) (b := 1) (x := x) (t := t) hxLo hxHi ht
  have hL := norm_principal_LFunction_sourceHorizontal_le q hsLo hsHi (by linarith) hxHi
    hB hepsilon
  have hGamma' : ‖Complex.Gamma
      ((x : ℂ) + (epsilon * B) * I + 1)‖ ≤
      (12 / delta) * (1 + B) ^ 2 * Real.exp (-(Real.pi / 2) * B) := by
    simpa [w, t] using hGamma
  have hQ' : ‖p53ScaleRemovableQuotient U V
      ((x : ℂ) + (epsilon * B) * I)‖ ≤
      p53CpowEndpointBound U V (-1 + delta) 1 := by
    simpa [t] using hQ
  have hnonneg : 0 ≤
      (12 / delta) * (1 + B) ^ 2 * Real.exp (-(Real.pi / 2) * B) *
        p53CpowEndpointBound U V (-1 + delta) 1 := by
    exact mul_nonneg (by positivity)
      (p53CpowEndpointBound_nonneg hU hV _ _)
  unfold p53TwoScaleContourIntegrand
  simp only [norm_mul]
  calc
    _ ≤ ((12 / delta) * (1 + B) ^ 2 * Real.exp (-(Real.pi / 2) * B)) *
        p53CpowEndpointBound U V (-1 + delta) 1 *
        (1600 * (2 : ℝ) ^ q.primeFactors.card *
          (7 + |s.im| + B) ^ 6) := by
      exact mul_le_mul
        (mul_le_mul hGamma' hQ' (norm_nonneg _) (by positivity)) hL
        (norm_nonneg _) hnonneg
    _ = _ := by ring

theorem tendsto_p53PrincipalSourceFullHorizontalIntegral_zero
    (q : ℕ) [NeZero q] (s : ℂ) {U V epsilon delta : ℝ}
    (hU : 0 < U) (hV : 0 < V)
    (hdelta : 0 < delta) (hdeltaHi : delta ≤ 1 / 8)
    (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 4)
    (hepsilon : |epsilon| = 1) :
    Tendsto (fun B : ℝ =>
      ∫ x : ℝ in (-1 + delta)..1,
        p53TwoScaleContourIntegrand (1 : DirichletCharacter ℂ q) s U V
          ((x : ℂ) + (epsilon * B) * I)) atTop (𝓝 0) := by
  let C : ℝ := 7 + |s.im|
  let P : ℝ := p53CpowEndpointBound U V (-1 + delta) 1
  let K : ℝ := (19200 / delta) * (2 : ℝ) ^ q.primeFactors.card * C ^ 6 * P
  let E : ℝ → ℝ := fun B => K * ((1 + B) ^ 8 * Real.exp (-B))
  have hE : Tendsto E atTop (𝓝 0) := by
    have hshift : Tendsto (fun B : ℝ => 1 + B) atTop atTop :=
      Filter.tendsto_atTop_add_const_left atTop 1 tendsto_id
    have hcore := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 8).comp hshift
    have hscaled := hcore.const_mul (K * Real.exp 1)
    have hscaled' : Tendsto (fun B : ℝ =>
        (K * Real.exp 1) * ((1 + B) ^ 8 * Real.exp (-(1 + B))))
        atTop (𝓝 0) := by
      simpa only [Function.comp_apply, mul_zero] using hscaled
    convert hscaled' using 1
    funext B
    dsimp [E]
    have hexp : Real.exp 1 * Real.exp (-(1 + B)) = Real.exp (-B) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← hexp]
    ring
  have hbound : ∀ᶠ B : ℝ in atTop,
      ‖∫ x : ℝ in (-1 + delta)..1,
        p53TwoScaleContourIntegrand (1 : DirichletCharacter ℂ q) s U V
          ((x : ℂ) + (epsilon * B) * I)‖ ≤
        E B * |(1 : ℝ) - (-1 + delta)| := by
    filter_upwards [eventually_ge_atTop (max 1 (2 * (1 + |s.im|)))] with B hB
    have hBone : 1 ≤ B := (le_max_left _ _).trans hB
    have hBsep : 2 * (1 + |s.im|) ≤ B := (le_max_right _ _).trans hB
    have hB0 : 0 ≤ B := by linarith
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Set.Icc (-1 + delta) 1 := by
      have := Set.uIoc_subset_uIcc hx
      rw [Set.uIcc_of_le (by linarith : -1 + delta ≤ 1)] at this
      exact this
    have hpoint := norm_p53PrincipalIntegrand_sourceHorizontal_le q s hU hV hdelta hdeltaHi
      hsLo hsHi hx'.1 hx'.2 hBsep hepsilon
    have hC : 1 ≤ C := by dsimp [C]; linarith [abs_nonneg s.im]
    have hCB : C + B ≤ C * (1 + B) := by nlinarith
    have hpow : (C + B) ^ 6 ≤ C ^ 6 * (1 + B) ^ 6 := by
      calc
        _ ≤ (C * (1 + B)) ^ 6 := pow_le_pow_left₀ (by positivity) hCB 6
        _ = _ := by ring
    have hexp : Real.exp (-(Real.pi / 2) * B) ≤ Real.exp (-B) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_gt_three]
    have hP : 0 ≤ P := by
      dsimp [P]
      exact p53CpowEndpointBound_nonneg hU hV _ _
    calc
      _ ≤ (19200 / delta) * (2 : ℝ) ^ q.primeFactors.card * (1 + B) ^ 2 *
          (C + B) ^ 6 * Real.exp (-(Real.pi / 2) * B) * P := by
        simpa [C, P] using hpoint
      _ ≤ (19200 / delta) * (2 : ℝ) ^ q.primeFactors.card * (1 + B) ^ 2 *
          (C ^ 6 * (1 + B) ^ 6) * Real.exp (-B) * P := by gcongr
      _ = E B := by dsimp [E, K]; ring
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · exact hbound
  · simpa using hE.mul_const |(1 : ℝ) - (-1 + delta)|


end
end MAPJutilaP53PrincipalSourceHorizontalDecay
#print axioms MAPJutilaP53PrincipalSourceHorizontalDecay.tendsto_p53PrincipalSourceFullHorizontalIntegral_zero
