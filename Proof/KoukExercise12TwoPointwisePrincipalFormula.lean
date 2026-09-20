import KoukExercise12TwoPointwiseFormula
import PrincipalLogDerivativeRemainderUnconditional
import PrimitiveContourComponentBounds

/-!
# Pointwise principal formula for Koukoulopoulos, Exercise 12.2(a)

This is the conductor-one companion to
`KoukExercise12TwoPointwiseFormula`.  The regularized zeta logarithmic
derivative is controlled by the certified principal Blaschke remainder, and
the pole at one is retained as an explicit bounded correction.
-/

namespace MAPKoukExercise12TwoPointwisePrincipalFormula

open Complex Set DirichletZeros PrimitiveExplicitFormulaSpine
open PrimitiveTruncatedExplicitFormulaBridge PaperEdgePrimitiveComponents
open MAPLocalZeroWindow MAPPrincipalLogDerivativeRemainderUnconditional
open MAPPrimitiveLogDerivativeRemainderUnconditional
open WideDiskLFunctionGrowth WideDiskBlaschkeAssembly
open MAPKoukExercise12TwoContourAperture PrimitiveContourComponentBounds

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩

private theorem mem_wide_of_zero_on_real_vertical
    {r t : ℝ} (hr0 : 0 < r) (hr4 : r < 4)
    (hzero : regularizedLFunction (1 : DirichletCharacter ℂ 1)
      ((r : ℂ) + Complex.I * t) = 0) :
    (r : ℂ) + Complex.I * t ∈
      wideZeroSupport (1 : DirichletCharacter ℂ 1) t := by
  apply mem_wideZeroSupport_of_eq_zero_of_mem_ball _ _ hzero
  rw [Metric.mem_ball, dist_eq_norm]
  have hdiff :
      ((r : ℂ) + Complex.I * t) - wideCenter t = ((r - 2 : ℝ) : ℂ) := by
    unfold wideCenter
    push_cast
    ring
  rw [hdiff, Complex.norm_real, Real.norm_eq_abs, wideRadius, abs_lt]
  constructor <;> linarith

private theorem log_arithmeticScale_le_global
    {H t : ℝ} (hH : 0 ≤ H) (ht : |t| ≤ H + 1) :
    Real.log (arithmeticScale 1 t) ≤ Real.log (H + 3) := by
  have hlocalPos : 0 < arithmeticScale 1 t := by
    linarith [two_le_arithmeticScale (q := 1) t]
  apply Real.log_le_log hlocalPos
  unfold arithmeticScale
  norm_num
  linarith

/-- Principal analogue of the wide-clearance logarithmic-derivative bound.
The additional constant `2` is the explicit pole-at-one correction. -/
theorem norm_logDeriv_principal_le_of_wide_clearance
    {t r d : ℝ} (hr0 : 0 < r) (hr4 : r < 4) (hd : 0 < d)
    (hspole : (r : ℂ) + Complex.I * t ≠ 1)
    (hpole : ‖(((r : ℂ) + Complex.I * t) - 1)⁻¹‖ ≤ 2)
    (hdist : ∀ rho ∈ wideZeroSupport (1 : DirichletCharacter ℂ 1) t,
      d ≤ ‖((r : ℂ) + Complex.I * t) - rho‖) :
    ‖logDeriv (DirichletCharacter.LFunction
        (1 : DirichletCharacter ℂ 1))
        ((r : ℂ) + Complex.I * t)‖ ≤
      2 +
        20 * (Real.log 223948800 +
          6 * Real.log (arithmeticScale 1 t)) +
        30300 * Real.log (arithmeticScale 1 t) +
        (30300 * Real.log (arithmeticScale 1 t)) / d := by
  let chi : DirichletCharacter ℂ 1 := 1
  let s : ℂ := (r : ℂ) + Complex.I * t
  have hsball : s ∈ Metric.ball (wideCenter t) 2 := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hdiff : s - wideCenter t = ((r - 2 : ℝ) : ℂ) := by
      dsimp [s, wideCenter]
      push_cast
      ring
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have hsF : s ∉ wideZeroSupport chi t := by
    intro hsupp
    have hz := hdist s (by simpa [chi, s] using hsupp)
    simp [s] at hz
    linarith
  have hlocal := norm_principal_localDeflatedLogDeriv_le hsball hsF
  have hmass := principal_wideZeroMultiplicity_mass_le_logScale t
  let P : ℂ := ∑ rho ∈ wideZeroSupport chi t,
    (wideZeroMultiplicity chi t rho : ℂ) / (s - rho)
  have hpoles : ‖P‖ ≤
      (∑ rho ∈ wideZeroSupport chi t,
        (wideZeroMultiplicity chi t rho : ℝ)) / d := by
    dsimp [P]
    calc
      ‖∑ rho ∈ wideZeroSupport chi t,
          (wideZeroMultiplicity chi t rho : ℂ) / (s - rho)‖ ≤
        ∑ rho ∈ wideZeroSupport chi t,
          ‖(wideZeroMultiplicity chi t rho : ℂ) / (s - rho)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ rho ∈ wideZeroSupport chi t,
          (wideZeroMultiplicity chi t rho : ℝ) / d := by
        apply Finset.sum_le_sum
        intro rho hrho
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hd
          (by simpa [chi, s] using hdist rho (by simpa [chi] using hrho))
      _ = (∑ rho ∈ wideZeroSupport chi t,
          (wideZeroMultiplicity chi t rho : ℝ)) / d := by
        rw [Finset.sum_div]
  have hpoles' : ‖P‖ ≤
      30300 * Real.log (arithmeticScale 1 t) / d :=
    hpoles.trans (div_le_div_of_nonneg_right (by simpa [chi] using hmass) hd.le)
  have hreg : regularizedLFunction chi s ≠ 0 := by
    intro hzero
    have hwide : s ∈ wideZeroSupport chi t := by
      dsimp [chi, s]
      exact mem_wide_of_zero_on_real_vertical hr0 hr4 (by simpa [chi, s] using hzero)
    exact hsF hwide
  have hs0 : s ≠ 0 := by
    intro hs
    have hre := congrArg Complex.re hs
    dsimp [s] at hre
    simp at hre
    linarith
  have hs1 : s ≠ 1 := by simpa [s] using hspole
  have hL : DirichletCharacter.LFunction chi s ≠ 0 := by
    classical
    intro hL
    apply hreg
    dsimp [chi]
    simp only [regularizedLFunction, if_pos]
    unfold DirichletCharacter.LFunctionTrivChar₁
    rw [Function.update_of_ne hs1]
    have hL' : DirichletCharacter.LFunctionTrivChar 1 s = 0 := by
      simpa [chi] using hL
    rw [hL', mul_zero]
  have hregBound : ‖logDeriv (regularizedLFunction chi) s‖ ≤
      20 * (Real.log 223948800 +
        6 * Real.log (arithmeticScale 1 t)) +
      30300 * Real.log (arithmeticScale 1 t) +
      (30300 * Real.log (arithmeticScale 1 t)) / d := by
    calc
      ‖logDeriv (regularizedLFunction chi) s‖ =
          ‖(logDeriv (regularizedLFunction chi) s - P) + P‖ := by
        congr 1
        ring
      _ ≤ ‖logDeriv (regularizedLFunction chi) s - P‖ + ‖P‖ :=
        norm_add_le _ _
      _ ≤ (20 * (Real.log 223948800 +
            6 * Real.log (arithmeticScale 1 t)) +
          ∑ rho ∈ wideZeroSupport chi t,
            (wideZeroMultiplicity chi t rho : ℝ)) +
          (30300 * Real.log (arithmeticScale 1 t) / d) :=
        add_le_add (by simpa only [P, s, chi] using hlocal) hpoles'
      _ ≤ 20 * (Real.log 223948800 +
            6 * Real.log (arithmeticScale 1 t)) +
          30300 * Real.log (arithmeticScale 1 t) +
          (30300 * Real.log (arithmeticScale 1 t)) / d := by
        linarith [hmass]
  have heq :=
    ZeroDistanceLogDerivativeBounds.neg_logDeriv_LFunction_eq_regularized_add_principalCorrection
      chi hs0 hs1 hL
  have hactual : ‖logDeriv (DirichletCharacter.LFunction chi) s‖ ≤
      ‖logDeriv (regularizedLFunction chi) s‖ + ‖(s - 1)⁻¹‖ := by
    rw [← norm_neg (logDeriv (DirichletCharacter.LFunction chi) s), heq]
    simpa [chi] using norm_add_le
      (-logDeriv (regularizedLFunction chi) s) ((s - 1)⁻¹)
  have hpole' : ‖(s - 1)⁻¹‖ ≤ 2 := by simpa [s] using hpole
  dsimp [chi, s] at hactual ⊢
  exact hactual.trans (by linarith)

/-- Selected-height pointwise principal prefix formula.  The only remaining
analytic term is the literal multiplicity-weighted zeta zero sum. -/
theorem exists_norm_principalPrefix_sub_main_le_zeroSum_add_contour
    {t H : ℝ} (ht : 0 ≤ t) (hN : 1 ≤ ⌊t⌋₊) (hH : 1 ≤ H) :
    ∃ sigma ∈ Set.Ioo (0 : ℝ) (1 / 2),
      ∃ T ∈ Set.Ioo H (H + 1),
        let d := exerciseContourClearance
          (1 : DirichletCharacter ℂ 1) H
        let L := Real.log (H + 3)
        let R := 2 + 20 * (Real.log 223948800 + 6 * L) +
          30300 * L + 30300 * L / d
        d ≤ sigma ∧
        ‖APFoundation.twistedMangoldtSum
              (1 : DirichletCharacter ℂ 1) (Finset.Icc 1 ⌊t⌋₊) -
            MAPSiegelWalfiszCharacterReduction.characterMain
              (1 : DirichletCharacter ℂ 1) t‖ ≤
          1 / 2 +
          ‖multiplicityWeightedPerronZeroSum
            (1 : DirichletCharacter ℂ 1) sigma T
            (halfIntegerPoint ⌊t⌋₊)‖ +
          T / Real.pi *
            (R * halfIntegerPoint ⌊t⌋₊ ^ sigma / sigma) +
          (standardEdge ⌊t⌋₊ - sigma) / Real.pi *
            (R * halfIntegerPoint ⌊t⌋₊ ^ standardEdge ⌊t⌋₊ / T) +
          insideMajorant ⌊t⌋₊ T + outsideMajorant ⌊t⌋₊ T := by
  let chi : DirichletCharacter ℂ 1 := 1
  let N := ⌊t⌋₊
  let x := halfIntegerPoint N
  let c := standardEdge N
  let d := exerciseContourClearance chi H
  let L := Real.log (H + 3)
  let R := 2 + 20 * (Real.log 223948800 + 6 * L) +
    30300 * L + 30300 * L / d
  obtain ⟨sigma, hsigma, T, hTIoo, hdSigma,
      hdistGlobalLeft, hdistGlobalBottom, hdistGlobalTop⟩ :=
    exists_exerciseContourAperture chi (H := H) (c := c)
  have hd : 0 < d := exerciseContourClearance_pos chi H
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
  have hc1 : 1 < c := standardEdge_gt_one N hN
  have hc4 : c < 4 := by
    dsimp [c, N]
    exact MAPKoukExercise12TwoPointwiseFormula.standardEdge_lt_four ⌊t⌋₊ hN
  have hsigmac : sigma ≤ c :=
    hsigma.2.le.trans ((by norm_num : (1 / 2 : ℝ) ≤ 1).trans hc1.le)
  have hdistLeft : ∀ u ∈ Set.Icc (-T) T,
      ∀ rho ∈ wideZeroSupport chi u,
        d ≤ ‖((sigma : ℂ) + Complex.I * u) - rho‖ := by
    intro u hu rho hrho
    have huabs : |u| ≤ H + 1 := by
      rw [abs_le]
      exact ⟨by linarith [hu.1, hTIoo.2], by linarith [hu.2, hTIoo.2]⟩
    apply exerciseClearance_le_norm_sub_wide chi huabs hdSigma hrho
    intro z hz
    simpa only [mul_comm] using hdistGlobalLeft u hu z hz
  have hdistTop : ∀ r ∈ Set.Icc sigma c,
      ∀ rho ∈ wideZeroSupport chi T,
        d ≤ ‖((r : ℂ) + Complex.I * T) - rho‖ := by
    intro r hr rho hrho
    apply exerciseClearance_le_norm_sub_wide chi hTabs
      (hdSigma.trans hr.1) hrho
    intro z hz
    simpa only [mul_comm] using hdistGlobalTop r hr z hz
  have hdistBottom : ∀ r ∈ Set.Icc sigma c,
      ∀ rho ∈ wideZeroSupport chi (-T),
        d ≤ ‖((r : ℂ) + Complex.I * (-T)) - rho‖ := by
    intro r hr rho hrho
    have hbase := exerciseClearance_le_norm_sub_wide chi hnegTabs
      (hdSigma.trans hr.1) hrho (by
        intro z hz
        simpa only [mul_comm] using hdistGlobalBottom r hr z hz)
    simpa only [Complex.ofReal_neg] using hbase
  have hleftNonzero : ∀ u ∈ Set.Icc (-T) T,
      regularizedLFunction chi
        ((sigma : ℂ) + (u : ℂ) * Complex.I) ≠ 0 := by
    intro u hu hzero
    have hwide : (sigma : ℂ) + Complex.I * u ∈ wideZeroSupport chi u :=
      mem_wide_of_zero_on_real_vertical hsigma.1 (by linarith) (by
        simpa only [chi, mul_comm] using hzero)
    have hz := hdistLeft u hu _ hwide
    simp at hz
    linarith
  have htopNonzero : ∀ r ∈ Set.Icc sigma c,
      regularizedLFunction chi ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0 := by
    intro r hr hzero
    have hwide : (r : ℂ) + Complex.I * T ∈ wideZeroSupport chi T :=
      mem_wide_of_zero_on_real_vertical (hsigma.1.trans_le hr.1)
        (hr.2.trans_lt hc4) (by simpa only [chi, mul_comm] using hzero)
    have hz := hdistTop r hr _ hwide
    simp at hz
    linarith
  have hbottomNonzero : ∀ r ∈ Set.Icc sigma c,
      regularizedLFunction chi
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro r hr hzero
    have hwide' : (r : ℂ) + Complex.I * ((-T : ℝ) : ℂ) ∈
        wideZeroSupport chi (-T) :=
      mem_wide_of_zero_on_real_vertical (hsigma.1.trans_le hr.1)
        (hr.2.trans_lt hc4) (by simpa only [chi, mul_comm] using hzero)
    have hwide : (r : ℂ) + Complex.I * (-T) ∈ wideZeroSupport chi (-T) := by
      simpa only [Complex.ofReal_neg] using hwide'
    have hz := hdistBottom r hr _ hwide
    simp at hz
    linarith
  have hlogBound (v r : ℝ) (hv : |v| ≤ H + 1)
      (hr0 : 0 < r) (hr4 : r < 4)
      (hpoleNe : (r : ℂ) + Complex.I * v ≠ 1)
      (hpole : ‖(((r : ℂ) + Complex.I * v) - 1)⁻¹‖ ≤ 2)
      (hdist : ∀ rho ∈ wideZeroSupport chi v,
        d ≤ ‖((r : ℂ) + Complex.I * v) - rho‖) :
      ‖logDeriv (DirichletCharacter.LFunction chi)
          ((r : ℂ) + Complex.I * v)‖ ≤ R := by
    have hbase := norm_logDeriv_principal_le_of_wide_clearance
      hr0 hr4 hd hpoleNe hpole (by simpa [chi] using hdist)
    have hlog := log_arithmeticScale_le_global
      ((by norm_num : (0 : ℝ) ≤ 1).trans hH) hv
    have hdiv : 30300 * Real.log (arithmeticScale 1 v) / d ≤
        30300 * L / d := by
      apply div_le_div_of_nonneg_right _ hd.le
      exact mul_le_mul_of_nonneg_left hlog (by norm_num)
    dsimp [R, L] at hlog hdiv ⊢
    linarith
  have hlogLeft : ∀ u ∈ Set.Icc (-T) T,
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((sigma : ℂ) + Complex.I * u)‖ ≤ R := by
    intro u hu
    have huabs : |u| ≤ H + 1 := by
      rw [abs_le]
      exact ⟨by linarith [hu.1, hTIoo.2], by linarith [hu.2, hTIoo.2]⟩
    have hpoleNe : (sigma : ℂ) + Complex.I * u ≠ 1 := by
      intro heq
      have hre := congrArg Complex.re heq
      simp at hre
      linarith [hsigma.2]
    have hpole : ‖(((sigma : ℂ) + Complex.I * u) - 1)⁻¹‖ ≤ 2 := by
      rw [norm_inv]
      have hden : (1 / 2 : ℝ) ≤
          ‖((sigma : ℂ) + Complex.I * u) - 1‖ := by
        calc
          (1 / 2 : ℝ) ≤ |sigma - 1| := by
            rw [abs_of_nonpos (by linarith [hsigma.2])]
            linarith [hsigma.2]
          _ = |((((sigma : ℂ) + Complex.I * u) - 1).re)| := by simp
          _ ≤ ‖((sigma : ℂ) + Complex.I * u) - 1‖ :=
            Complex.abs_re_le_norm _
      have hdenPos : 0 < ‖((sigma : ℂ) + Complex.I * u) - 1‖ :=
        (by norm_num : (0 : ℝ) < 1 / 2).trans_le hden
      calc
        ‖((sigma : ℂ) + Complex.I * u) - 1‖⁻¹ ≤ (1 / 2 : ℝ)⁻¹ :=
          (inv_le_inv₀ hdenPos (by norm_num)).2 hden
        _ = 2 := by norm_num
    exact hlogBound u sigma huabs hsigma.1 (by linarith)
      hpoleNe hpole (hdistLeft u hu)
  have hlogTop : ∀ r ∈ Set.Icc sigma c,
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) + Complex.I * T)‖ ≤ R := by
    intro r hr
    have hpoleNe : (r : ℂ) + Complex.I * T ≠ 1 := by
      intro heq
      have him := congrArg Complex.im heq
      simp at him
      linarith
    have hpole : ‖(((r : ℂ) + Complex.I * T) - 1)⁻¹‖ ≤ 2 := by
      rw [norm_inv]
      have hden : 1 ≤ ‖((r : ℂ) + Complex.I * T) - 1‖ := by
        calc
          1 ≤ |((((r : ℂ) + Complex.I * T) - 1).im)| := by
            simp
            rw [abs_of_pos hT]
            linarith [hH, hTIoo.1]
          _ ≤ ‖((r : ℂ) + Complex.I * T) - 1‖ := Complex.abs_im_le_norm _
      have hdenPos : 0 < ‖((r : ℂ) + Complex.I * T) - 1‖ :=
        zero_lt_one.trans_le hden
      calc
        ‖((r : ℂ) + Complex.I * T) - 1‖⁻¹ ≤ (1 : ℝ)⁻¹ :=
          (inv_le_inv₀ hdenPos zero_lt_one).2 hden
        _ ≤ 2 := by norm_num
    exact hlogBound T r hTabs (hsigma.1.trans_le hr.1)
      (hr.2.trans_lt hc4) hpoleNe hpole (hdistTop r hr)
  have hlogBottom : ∀ r ∈ Set.Icc sigma c,
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) - Complex.I * T)‖ ≤ R := by
    intro r hr
    have hpoleNeBase : (r : ℂ) + Complex.I * (-T) ≠ 1 := by
      intro heq
      have him := congrArg Complex.im heq
      simp at him
      linarith
    have hpoleBase : ‖(((r : ℂ) + Complex.I * (-T)) - 1)⁻¹‖ ≤ 2 := by
      rw [norm_inv]
      have hden : 1 ≤ ‖((r : ℂ) + Complex.I * (-T)) - 1‖ := by
        calc
          1 ≤ |((((r : ℂ) + Complex.I * (-T)) - 1).im)| := by
            simp
            rw [abs_of_pos hT]
            linarith [hH, hTIoo.1]
          _ ≤ ‖((r : ℂ) + Complex.I * (-T)) - 1‖ := Complex.abs_im_le_norm _
      have hdenPos : 0 < ‖((r : ℂ) + Complex.I * (-T)) - 1‖ :=
        zero_lt_one.trans_le hden
      calc
        ‖((r : ℂ) + Complex.I * (-T)) - 1‖⁻¹ ≤ (1 : ℝ)⁻¹ :=
          (inv_le_inv₀ hdenPos zero_lt_one).2 hden
        _ ≤ 2 := by norm_num
    have hpoleNe : (r : ℂ) + Complex.I * ((-T : ℝ) : ℂ) ≠ 1 := by
      simpa only [Complex.ofReal_neg] using hpoleNeBase
    have hpole : ‖(((r : ℂ) + Complex.I * ((-T : ℝ) : ℂ)) - 1)⁻¹‖ ≤ 2 := by
      simpa only [Complex.ofReal_neg] using hpoleBase
    have hbase := hlogBound (-T) r hnegTabs
      (hsigma.1.trans_le hr.1) (hr.2.trans_lt hc4) hpoleNe hpole (by
        intro rho hrho
        simpa only [Complex.ofReal_neg] using hdistBottom r hr rho hrho)
    simpa only [Complex.ofReal_neg, mul_neg, sub_eq_add_neg] using hbase
  have hbase := norm_primitivePrefix_sub_characterMain_le_components
    chi ht hN hsigma.1 (hsigma.2.trans (by norm_num : (1 / 2 : ℝ) < 1)) hT
      hleftNonzero hbottomNonzero htopNonzero
  have hleft := norm_leftLineIntegral_le_of_logDeriv
    chi hx0 hsigma.1 hT.le hlogLeft
  have hhorizontal := norm_horizontalBoundaryIntegral_le_of_logDeriv
    chi hx hsigmac hT hlogTop hlogBottom
  refine ⟨sigma, hsigma, T, hTIoo, ?_⟩
  dsimp only
  refine ⟨hdSigma, ?_⟩
  change ‖APFoundation.twistedMangoldtSum chi (Finset.Icc 1 N) -
      MAPSiegelWalfiszCharacterReduction.characterMain chi t‖ ≤ _
  exact hbase.trans (by
    dsimp only [x, c, N] at hleft hhorizontal ⊢
    gcongr)

end
end MAPKoukExercise12TwoPointwisePrincipalFormula

#print axioms MAPKoukExercise12TwoPointwisePrincipalFormula.norm_logDeriv_principal_le_of_wide_clearance
#print axioms MAPKoukExercise12TwoPointwisePrincipalFormula.exists_norm_principalPrefix_sub_main_le_zeroSum_add_contour
