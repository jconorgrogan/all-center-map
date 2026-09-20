import KoukExercise12TwoLocalHorizontalAperture
import PrimitiveContourComponentBounds

/-!
# Pointwise explicit formula for Koukoulopoulos, Exercise 12.2(a)

This is the reusable pointwise form requested by both the primitive
Siegel--Walfisz endpoint and the aligned AP contour route.  It selects one
height in `(H,H+1)` and bounds the two shifted contour sides by the certified
local Blaschke logarithmic derivative.  The multiplicity-weighted zero sum
remains literal.
-/

namespace MAPKoukExercise12TwoPointwiseLocalFormula

open Complex Set DirichletZeros PrimitiveExplicitFormulaSpine
open PrimitiveTruncatedExplicitFormulaBridge PaperEdgePrimitiveComponents
open MAPLocalZeroWindow MAPPrimitiveLogDerivativeRemainderUnconditional
open WideDiskLFunctionGrowth WideDiskBlaschkeAssembly
open MAPKoukExercise12TwoContourAperture PrimitiveContourComponentBounds
open MAPKoukExercise12TwoLocalHorizontalAperture

noncomputable section

theorem standardEdge_lt_four (N : ℕ) (hN : 1 ≤ N) :
    standardEdge N < 4 := by
  have hx : (3 / 2 : ℝ) ≤ halfIntegerPoint N := by
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    unfold halfIntegerPoint
    linarith
  have hlogLower : (2 / 5 : ℝ) < Real.log (halfIntegerPoint N) := by
    have hbase := Real.lt_log_one_add_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
    have hlogMono := Real.log_le_log (by norm_num : (0 : ℝ) < 3 / 2) hx
    have hbase' : (2 / 5 : ℝ) < Real.log (3 / 2) := by
      convert hbase using 1 <;> norm_num
    exact hbase'.trans_le hlogMono
  have hinv : (Real.log (halfIntegerPoint N))⁻¹ < 5 / 2 := by
    have hlogPos : 0 < Real.log (halfIntegerPoint N) :=
      (by norm_num : (0 : ℝ) < 2 / 5).trans hlogLower
    rw [inv_eq_one_div]
    exact (div_lt_iff₀ hlogPos).2 (by nlinarith)
  unfold standardEdge
  linarith

private theorem mem_wide_of_zero_on_real_vertical
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {r t : ℝ} (hr0 : 0 < r) (hr4 : r < 4)
    (hzero : regularizedLFunction chi
      ((r : ℂ) + Complex.I * t) = 0) :
    (r : ℂ) + Complex.I * t ∈ wideZeroSupport chi t := by
  apply mem_wideZeroSupport_of_eq_zero_of_mem_ball chi _ hzero
  rw [Metric.mem_ball, dist_eq_norm]
  have hdiff :
      ((r : ℂ) + Complex.I * t) - wideCenter t = ((r - 2 : ℝ) : ℂ) := by
    unfold wideCenter
    push_cast
    ring
  rw [hdiff, Complex.norm_real, Real.norm_eq_abs, wideRadius, abs_lt]
  constructor <;> linarith

private theorem log_arithmeticScale_le_global
    {q : ℕ} [NeZero q] {H t : ℝ} (hH : 0 ≤ H)
    (ht : |t| ≤ H + 1) :
    Real.log (arithmeticScale q t) ≤
      Real.log ((q : ℝ) * (H + 3)) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hlocalPos : 0 < arithmeticScale q t := by
    linarith [two_le_arithmeticScale (q := q) t]
  apply Real.log_le_log hlocalPos
  unfold arithmeticScale
  exact mul_le_mul_of_nonneg_left (by linarith) hq0

/-- Horizontal contour bound with a square-root-sized corner range and a
separate source-local bound on the right-hand range. -/
theorem norm_horizontalBoundaryIntegral_le_of_split_logDeriv
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x sigma m c T Mlow Mhigh : ℝ}
    (hx : 1 ≤ x) (hsm : sigma ≤ m) (hmc : m ≤ c) (hT : 0 < T)
    (hMlow : 0 ≤ Mlow) (hMhigh : 0 ≤ Mhigh)
    (htopLow : ∀ r ∈ Set.Icc sigma m,
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) + Complex.I * T)‖ ≤ Mlow)
    (hbottomLow : ∀ r ∈ Set.Icc sigma m,
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) - Complex.I * T)‖ ≤ Mlow)
    (htopHigh : ∀ r ∈ Set.Icc m c,
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) + Complex.I * T)‖ ≤ Mhigh)
    (hbottomHigh : ∀ r ∈ Set.Icc m c,
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) - Complex.I * T)‖ ≤ Mhigh) :
    ‖horizontalBoundaryIntegral chi x sigma c T‖ ≤
      (c - sigma) / Real.pi *
        (Mlow * x ^ m / T + Mhigh * x ^ c / T) := by
  have hsc : sigma ≤ c := hsm.trans hmc
  have hpi : 0 < Real.pi := Real.pi_pos
  have habsT : |T| = T := abs_of_pos hT
  have habsNegT : |-T| = T := by simp [abs_of_pos hT]
  have hpointTop : ∀ r ∈ Set.Icc sigma c,
      ‖perronContourIntegrand chi x ((r : ℂ) + Complex.I * T)‖ ≤
        Mlow * x ^ m / T + Mhigh * x ^ c / T := by
    intro r hr
    by_cases hrm : r ≤ m
    · have hp := norm_perronContourIntegrand_horizontal_le chi hx hrm
        (by simpa [habsT] using hT) (htopLow r ⟨hr.1, hrm⟩)
      simpa [habsT] using hp.trans (le_add_of_nonneg_right (by positivity))
    · have hmr : m ≤ r := (lt_of_not_ge hrm).le
      have hp := norm_perronContourIntegrand_horizontal_le chi hx hr.2
        (by simpa [habsT] using hT) (htopHigh r ⟨hmr, hr.2⟩)
      simpa [habsT] using hp.trans (show
        Mhigh * x ^ c / |T| ≤
          Mlow * x ^ m / T + Mhigh * x ^ c / T by
            rw [habsT]
            exact le_add_of_nonneg_left (by positivity))
  have hpointBottom : ∀ r ∈ Set.Icc sigma c,
      ‖perronContourIntegrand chi x ((r : ℂ) - Complex.I * T)‖ ≤
        Mlow * x ^ m / T + Mhigh * x ^ c / T := by
    intro r hr
    by_cases hrm : r ≤ m
    · have hp := norm_perronContourIntegrand_horizontal_le chi hx hrm
        (tau := -T) (by simpa [habsNegT] using hT)
        (by simpa [sub_eq_add_neg] using hbottomLow r ⟨hr.1, hrm⟩)
      simpa [sub_eq_add_neg, habsNegT] using
        hp.trans (le_add_of_nonneg_right (by positivity))
    · have hmr : m ≤ r := (lt_of_not_ge hrm).le
      have hp := norm_perronContourIntegrand_horizontal_le chi hx hr.2
        (tau := -T) (by simpa [habsNegT] using hT)
        (by simpa [sub_eq_add_neg] using hbottomHigh r ⟨hmr, hr.2⟩)
      simpa [sub_eq_add_neg, habsNegT] using
        hp.trans (show Mhigh * x ^ c / |-T| ≤
            Mlow * x ^ m / T + Mhigh * x ^ c / T by
          rw [habsNegT]
          exact le_add_of_nonneg_left (by positivity))
  have htopint :
      ‖∫ r in sigma..c,
          perronContourIntegrand chi x ((r : ℂ) + Complex.I * T)‖ ≤
        (Mlow * x ^ m / T + Mhigh * x ^ c / T) * |c - sigma| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun r hr => by
      have hru : r ∈ Set.uIcc sigma c := Set.uIoc_subset_uIcc hr
      exact hpointTop r (by simpa [Set.uIcc_of_le hsc] using hru))
  have hbottomint :
      ‖∫ r in sigma..c,
          perronContourIntegrand chi x ((r : ℂ) - Complex.I * T)‖ ≤
        (Mlow * x ^ m / T + Mhigh * x ^ c / T) * |c - sigma| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun r hr => by
      have hru : r ∈ Set.uIcc sigma c := Set.uIoc_subset_uIcc hr
      exact hpointBottom r (by simpa [Set.uIcc_of_le hsc] using hru))
  let A : ℂ := ((2 * Real.pi : ℝ) : ℂ)⁻¹ * Complex.I
  let Itop : ℂ := ∫ r in sigma..c,
    perronContourIntegrand chi x ((r : ℂ) + Complex.I * T)
  let Ibottom : ℂ := ∫ r in sigma..c,
    perronContourIntegrand chi x ((r : ℂ) - Complex.I * T)
  have hA : ‖A‖ = (2 * Real.pi)⁻¹ := by
    dsimp [A]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (by norm_num) hpi), Complex.norm_I, mul_one]
  change ‖A * Itop - A * Ibottom‖ ≤ _
  calc
    ‖A * Itop - A * Ibottom‖ ≤ ‖A * Itop‖ + ‖A * Ibottom‖ := norm_sub_le _ _
    _ = (2 * Real.pi)⁻¹ * ‖Itop‖ + (2 * Real.pi)⁻¹ * ‖Ibottom‖ := by
      rw [norm_mul A Itop, norm_mul A Ibottom, hA]
    _ ≤ (2 * Real.pi)⁻¹ *
          ((Mlow * x ^ m / T + Mhigh * x ^ c / T) * |c - sigma|) +
        (2 * Real.pi)⁻¹ *
          ((Mlow * x ^ m / T + Mhigh * x ^ c / T) * |c - sigma|) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (by simpa [Itop] using htopint) (by positivity))
        (mul_le_mul_of_nonneg_left (by simpa [Ibottom] using hbottomint) (by positivity))
    _ = (c - sigma) / Real.pi *
          (Mlow * x ^ m / T + Mhigh * x ^ c / T) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hsc)]
      field_simp [ne_of_gt hpi]
      ring

/-- Selected-height pointwise primitive prefix formula.  The only unexpanded
term is the literal multiplicity-weighted zero sum; all contour and Perron
remainders are explicit scalar quantities. -/
theorem exists_norm_primitivePrefix_sub_characterMain_le_zeroSum_add_local_contour
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {t H : ℝ} (ht : 0 ≤ t) (hN : 1 ≤ ⌊t⌋₊) (hH : 1 ≤ H) :
    ∃ sigma ∈ Set.Ioo (0 : ℝ) (1 / 2),
      ∃ T ∈ Set.Ioo H (H + 1),
        let dLeft := exerciseRealClearance chi H
        let dHorizontal := exerciseHorizontalClearance chi H
        let dCorner := min dLeft dHorizontal
        let L := Real.log ((q : ℝ) * (H + 3))
        let RLeft :=
          20 * (Real.log 21600 + 2 * L) + 5520 * L + 5520 * L / dLeft
        let RHorizontal :=
          20 * (Real.log 21600 + 2 * L) + 5520 * L + 5520 * L / dHorizontal
        let RCorner :=
          20 * (Real.log 21600 + 2 * L) + 5520 * L + 5520 * L / dCorner
        dLeft ≤ sigma ∧
        ‖APFoundation.twistedMangoldtSum chi (Finset.Icc 1 ⌊t⌋₊) -
            MAPSiegelWalfiszCharacterReduction.characterMain chi t‖ ≤
          1 / 2 +
          ‖multiplicityWeightedPerronZeroSum chi sigma T
            (halfIntegerPoint ⌊t⌋₊)‖ +
          T / Real.pi *
            (RLeft * halfIntegerPoint ⌊t⌋₊ ^ sigma / sigma) +
          (standardEdge ⌊t⌋₊ - sigma) / Real.pi *
            (RCorner * halfIntegerPoint ⌊t⌋₊ ^ (1 / 2 : ℝ) / T +
              RHorizontal * halfIntegerPoint ⌊t⌋₊ ^ standardEdge ⌊t⌋₊ / T) +
          insideMajorant ⌊t⌋₊ T + outsideMajorant ⌊t⌋₊ T := by
  let N := ⌊t⌋₊
  let x := halfIntegerPoint N
  let c := standardEdge N
  let dLeft := exerciseRealClearance chi H
  let dHorizontal := exerciseHorizontalClearance chi H
  let dCorner := min dLeft dHorizontal
  let L := Real.log ((q : ℝ) * (H + 3))
  let RLeft :=
    20 * (Real.log 21600 + 2 * L) + 5520 * L + 5520 * L / dLeft
  let RHorizontal :=
    20 * (Real.log 21600 + 2 * L) + 5520 * L + 5520 * L / dHorizontal
  let RCorner :=
    20 * (Real.log 21600 + 2 * L) + 5520 * L + 5520 * L / dCorner
  obtain ⟨sigma, hsigma, T, hTIoo, hdSigma,
      hdistGlobalLeft, hdistGlobalBottom, hdistGlobalTop⟩ :=
    exists_exerciseLocalHorizontalAperture chi (H := H) (c := c)
  have hdLeft : 0 < dLeft := by
    dsimp [dLeft]
    exact exerciseRealClearance_pos chi H
  have hdHorizontal : 0 < dHorizontal := by
    dsimp [dHorizontal]
    exact exerciseHorizontalClearance_pos chi H
  have hdCorner : 0 < dCorner := by
    dsimp [dCorner]
    exact lt_min hdLeft hdHorizontal
  have hT : 0 < T := by linarith [hH, hTIoo.1]
  have hTabs : |T| ≤ H + 1 := by
    rw [abs_of_pos hT]
    exact hTIoo.2.le
  have hnegTabs : |-T| ≤ H + 1 := by simpa using hTabs
  have hx : 1 ≤ x := by
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp [x, halfIntegerPoint]
    linarith
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hc1 : 1 < c := by
    dsimp [c, N]
    exact standardEdge_gt_one ⌊t⌋₊ hN
  have hc4 : c < 4 := by
    dsimp [c, N]
    exact standardEdge_lt_four ⌊t⌋₊ hN
  have hsigmac : sigma ≤ c :=
    hsigma.2.le.trans ((by norm_num : (1 / 2 : ℝ) ≤ 1).trans hc1.le)
  have hdistLeft : ∀ u ∈ Set.Icc (-T) T,
      ∀ rho ∈ wideZeroSupport chi u,
        dLeft ≤ ‖((sigma : ℂ) + Complex.I * u) - rho‖ := by
    intro u hu rho hrho
    have huabs : |u| ≤ H + 1 := by
      rw [abs_le]
      exact ⟨by linarith [hu.1, hTIoo.2], by linarith [hu.2, hTIoo.2]⟩
    apply localClearance_le_norm_sub_wide chi hdLeft huabs hdSigma hrho
    intro z hz
    simpa only [mul_comm] using hdistGlobalLeft u hu z hz
  have hdHorizontalHalf : dHorizontal ≤ (1 / 2 : ℝ) := by
    dsimp [dHorizontal, exerciseHorizontalClearance]
    have hden : (2 : ℝ) ≤
        4 * (((exerciseLocalImagCoordinates chi H).card : ℝ) + 1) := by
      have hc : 0 ≤ ((exerciseLocalImagCoordinates chi H).card : ℝ) := by positivity
      nlinarith
    exact one_div_le_one_div_of_le (by norm_num) hden
  have hdistTopHigh : ∀ r ∈ Set.Icc (1 / 2 : ℝ) c,
      ∀ rho ∈ wideZeroSupport chi T,
        dHorizontal ≤ ‖((r : ℂ) + Complex.I * T) - rho‖ := by
    intro r hr rho hrho
    apply localClearance_le_norm_sub_wide chi hdHorizontal hTabs
      (hdHorizontalHalf.trans hr.1) hrho
    intro z hz
    simpa only [mul_comm] using hdistGlobalTop r
      ⟨hsigma.2.le.trans hr.1, hr.2⟩ z hz
  have hdistBottomHigh : ∀ r ∈ Set.Icc (1 / 2 : ℝ) c,
      ∀ rho ∈ wideZeroSupport chi (-T),
        dHorizontal ≤ ‖((r : ℂ) + Complex.I * (-T)) - rho‖ := by
    intro r hr rho hrho
    have hbase := localClearance_le_norm_sub_wide chi hdHorizontal hnegTabs
      (hdHorizontalHalf.trans hr.1) hrho (by
        intro z hz
        simpa only [mul_comm] using hdistGlobalBottom r
          ⟨hsigma.2.le.trans hr.1, hr.2⟩ z hz)
    simpa only [Complex.ofReal_neg] using hbase
  have hdistTopCorner : ∀ r ∈ Set.Icc sigma (1 / 2 : ℝ),
      ∀ rho ∈ wideZeroSupport chi T,
        dCorner ≤ ‖((r : ℂ) + Complex.I * T) - rho‖ := by
    intro r hr rho hrho
    apply localClearance_le_norm_sub_wide chi hdCorner hTabs
      ((min_le_left _ _).trans hdSigma |>.trans hr.1) hrho
    intro z hz
    exact (min_le_right _ _).trans (by
      simpa only [mul_comm] using hdistGlobalTop r
        ⟨hr.1, hr.2.trans
          ((by norm_num : (1 / 2 : ℝ) ≤ 1).trans hc1.le)⟩ z hz)
  have hdistBottomCorner : ∀ r ∈ Set.Icc sigma (1 / 2 : ℝ),
      ∀ rho ∈ wideZeroSupport chi (-T),
        dCorner ≤ ‖((r : ℂ) + Complex.I * (-T)) - rho‖ := by
    intro r hr rho hrho
    have hbase := localClearance_le_norm_sub_wide chi hdCorner hnegTabs
      ((min_le_left _ _).trans hdSigma |>.trans hr.1) hrho (by
        intro z hz
        exact (min_le_right _ _).trans (by
          simpa only [mul_comm] using hdistGlobalBottom r
            ⟨hr.1, hr.2.trans
              ((by norm_num : (1 / 2 : ℝ) ≤ 1).trans hc1.le)⟩ z hz))
    simpa only [Complex.ofReal_neg] using hbase
  have hleftNonzero : ∀ u ∈ Set.Icc (-T) T,
      regularizedLFunction chi
        ((sigma : ℂ) + (u : ℂ) * Complex.I) ≠ 0 := by
    intro u hu hzero
    have hwide : (sigma : ℂ) + Complex.I * u ∈ wideZeroSupport chi u :=
      mem_wide_of_zero_on_real_vertical chi hsigma.1 (by linarith) (by
        simpa only [mul_comm] using hzero)
    have hz := hdistLeft u hu _ hwide
    simp at hz
    linarith
  have htopNonzero : ∀ r ∈ Set.Icc sigma c,
      regularizedLFunction chi ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0 := by
    intro r hr hzero
    have hwide : (r : ℂ) + Complex.I * T ∈ wideZeroSupport chi T :=
      mem_wide_of_zero_on_real_vertical chi (hsigma.1.trans_le hr.1)
        (hr.2.trans_lt hc4) (by simpa only [mul_comm] using hzero)
    have hz : 0 < dCorner := hdCorner
    by_cases hrhalf : r ≤ 1 / 2
    · have hdist := hdistTopCorner r ⟨hr.1, hrhalf⟩ _ hwide
      simp at hdist
      linarith
    · have hdist := hdistTopHigh r ⟨(lt_of_not_ge hrhalf).le, hr.2⟩ _ hwide
      simp at hdist
      linarith
  have hbottomNonzero : ∀ r ∈ Set.Icc sigma c,
      regularizedLFunction chi
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro r hr hzero
    have hwide' : (r : ℂ) + Complex.I * ((-T : ℝ) : ℂ) ∈
        wideZeroSupport chi (-T) :=
      mem_wide_of_zero_on_real_vertical chi (hsigma.1.trans_le hr.1)
        (hr.2.trans_lt hc4) (by simpa only [mul_comm] using hzero)
    have hwide : (r : ℂ) + Complex.I * (-T) ∈ wideZeroSupport chi (-T) := by
      simpa only [Complex.ofReal_neg] using hwide'
    by_cases hrhalf : r ≤ 1 / 2
    · have hdist := hdistBottomCorner r ⟨hr.1, hrhalf⟩ _ hwide
      simp at hdist
      linarith
    · have hdist := hdistBottomHigh r ⟨(lt_of_not_ge hrhalf).le, hr.2⟩ _ hwide
      simp at hdist
      linarith
  have hlogBound (delta v r : ℝ) (hdelta : 0 < delta)
      (hv : |v| ≤ H + 1)
      (hr0 : 0 < r) (hr4 : r < 4)
      (hdist : ∀ rho ∈ wideZeroSupport chi v,
        delta ≤ ‖((r : ℂ) + Complex.I * v) - rho‖) :
      ‖logDeriv (DirichletCharacter.LFunction chi)
          ((r : ℂ) + Complex.I * v)‖ ≤
        20 * (Real.log 21600 + 2 * L) + 5520 * L + 5520 * L / delta := by
    have hbase := norm_logDeriv_LFunction_le_of_wide_clearance
      chi hprim hchi hr0 hr4 hdelta hdist
    have hlog := log_arithmeticScale_le_global (q := q)
      ((by norm_num : (0 : ℝ) ≤ 1).trans hH) hv
    have hdiv : 5520 * Real.log (arithmeticScale q v) / delta ≤
        5520 * L / delta := by
      apply div_le_div_of_nonneg_right _ hdelta.le
      exact mul_le_mul_of_nonneg_left hlog (by norm_num)
    dsimp [L] at hlog hdiv
    linarith
  have hlogLeft : ∀ u ∈ Set.Icc (-T) T,
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((sigma : ℂ) + Complex.I * u)‖ ≤ RLeft := by
    intro u hu
    have huabs : |u| ≤ H + 1 := by
      rw [abs_le]
      exact ⟨by linarith [hu.1, hTIoo.2], by linarith [hu.2, hTIoo.2]⟩
    simpa only [RLeft] using
      hlogBound dLeft u sigma hdLeft huabs hsigma.1 (by linarith)
        (hdistLeft u hu)
  have hlogTopCorner : ∀ r ∈ Set.Icc sigma (1 / 2 : ℝ),
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) + Complex.I * T)‖ ≤ RCorner := by
    intro r hr
    simpa only [RCorner] using
      hlogBound dCorner T r hdCorner hTabs
        (hsigma.1.trans_le hr.1) (hr.2.trans_lt (by linarith : (1 / 2 : ℝ) < 4))
        (hdistTopCorner r hr)
  have hlogBottomCorner : ∀ r ∈ Set.Icc sigma (1 / 2 : ℝ),
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) - Complex.I * T)‖ ≤ RCorner := by
    intro r hr
    have hbase := hlogBound dCorner (-T) r hdCorner hnegTabs
      (hsigma.1.trans_le hr.1)
      (hr.2.trans_lt (by linarith : (1 / 2 : ℝ) < 4)) (by
        intro rho hrho
        simpa only [Complex.ofReal_neg] using hdistBottomCorner r hr rho hrho)
    simpa only [Complex.ofReal_neg, mul_neg, sub_eq_add_neg] using hbase
  have hlogTopHigh : ∀ r ∈ Set.Icc (1 / 2 : ℝ) c,
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) + Complex.I * T)‖ ≤ RHorizontal := by
    intro r hr
    simpa only [RHorizontal] using
      hlogBound dHorizontal T r hdHorizontal hTabs
        (by linarith [hr.1]) (hr.2.trans_lt hc4) (hdistTopHigh r hr)
  have hlogBottomHigh : ∀ r ∈ Set.Icc (1 / 2 : ℝ) c,
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) - Complex.I * T)‖ ≤ RHorizontal := by
    intro r hr
    have hbase := hlogBound dHorizontal (-T) r hdHorizontal hnegTabs
      (by linarith [hr.1]) (hr.2.trans_lt hc4) (by
        intro rho hrho
        simpa only [Complex.ofReal_neg] using hdistBottomHigh r hr rho hrho)
    simpa only [Complex.ofReal_neg, mul_neg, sub_eq_add_neg] using hbase
  have hscaleOne : 1 ≤ (q : ℝ) * (H + 3) := by
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le (n := q)
    nlinarith
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg hscaleOne
  have hRCorner0 : 0 ≤ RCorner := by
    dsimp [RCorner]
    have hlogConst : 0 ≤ Real.log 21600 := Real.log_nonneg (by norm_num)
    positivity
  have hRHorizontal0 : 0 ≤ RHorizontal := by
    dsimp [RHorizontal]
    have hlogConst : 0 ≤ Real.log 21600 := Real.log_nonneg (by norm_num)
    positivity
  have hbase := norm_primitivePrefix_sub_characterMain_le_components
    chi ht hN hsigma.1 (hsigma.2.trans (by norm_num : (1 / 2 : ℝ) < 1)) hT
      hleftNonzero hbottomNonzero htopNonzero
  have hleft := norm_leftLineIntegral_le_of_logDeriv
    chi hx0 hsigma.1 hT.le hlogLeft
  have hhorizontal := norm_horizontalBoundaryIntegral_le_of_split_logDeriv
    chi hx hsigma.2.le
      ((by norm_num : (1 / 2 : ℝ) ≤ 1).trans hc1.le)
      hT hRCorner0 hRHorizontal0
      hlogTopCorner hlogBottomCorner hlogTopHigh hlogBottomHigh
  refine ⟨sigma, hsigma, T, hTIoo, ?_⟩
  dsimp only
  refine ⟨hdSigma, ?_⟩
  change ‖APFoundation.twistedMangoldtSum chi (Finset.Icc 1 N) -
      MAPSiegelWalfiszCharacterReduction.characterMain chi t‖ ≤ _
  exact hbase.trans (by
    dsimp only [x, c, N] at hleft hhorizontal ⊢
    gcongr)

#print axioms MAPKoukExercise12TwoPointwiseLocalFormula.exists_norm_primitivePrefix_sub_characterMain_le_zeroSum_add_local_contour

end

end MAPKoukExercise12TwoPointwiseLocalFormula
