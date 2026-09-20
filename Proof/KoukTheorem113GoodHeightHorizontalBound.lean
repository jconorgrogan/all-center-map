import KoukTheorem113PerCharacterGoodHeight
import KoukEndpointHorizontalAEBound
import KoukNegativeHorizontalLogDerivativeBound
import KoukPrincipalNegativeHorizontalLogDerivativeBound
import KoukGaussDigammaSeries
import LocalZeroCountSlice

/-!
# Good-height horizontal bound in Koukoulopoulos Theorem 11.3

This is the pointwise, per-character (not family-union) horizontal estimate.
The seam at `Re s = 0` is treated almost everywhere, exactly as required by
the contour integral.
-/

namespace KoukTheorem113GoodHeightHorizontalBound

open Set Complex MeasureTheory DirichletZeros
open WideDiskBlaschkeAssembly
open WideDiskLFunctionGrowth MAPLocalZeroWindow
open MAPKoukExercise12TwoContourAperture
open MAPKoukExercise12TwoLocalHorizontalAperture
open KoukTheorem113PerCharacterGoodHeight
open KoukNegativeHorizontalLogDerivativeBound
open KoukEndpointHorizontalAEBound
open KoukTheorem113ExactFormula

noncomputable section

private theorem ae_ne_zero : ∀ᵐ r : ℝ, r ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  have hzero : volume ({0} : Set ℝ) = 0 :=
    (Set.countable_singleton (0 : ℝ)).measure_zero volume
  simpa using hzero

private theorem log_arithmeticScale_le_goodHeightScale
    {q : ℕ} [NeZero q] {H v : ℝ} (hH : 0 ≤ H)
    (hv : |v| ≤ H + 1) :
    Real.log (arithmeticScale q v) ≤
      Real.log ((q : ℝ) * (H + 3)) := by
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hpos : 0 < arithmeticScale q v := by
    unfold arithmeticScale
    exact mul_pos (by exact_mod_cast NeZero.pos q)
      (by linarith [abs_nonneg v])
  apply Real.log_le_log hpos
  unfold arithmeticScale
  exact mul_le_mul_of_nonneg_left (by linarith) hq0

private theorem negativeGeometryLogSum_le
    {H T r : ℝ} (hH : 4 ≤ H) (hT : T ∈ Set.Ioo H (H + 1))
    (hr : r ∈ Set.Icc (-(1 / 2 : ℝ)) 0) :
    Real.log
        (‖(((1 - r : ℝ) : ℂ) + Complex.I * (-T))‖ + 3) +
      Real.log (‖((r : ℂ) + Complex.I * T)‖ + 3) ≤
        2 * Real.log (H + 8) := by
  have hTpos : 0 < T := by linarith [hH, hT.1]
  have hu : ‖(((1 - r : ℝ) : ℂ) + Complex.I * (-T))‖ + 3 ≤ H + 8 := by
    have htri := norm_add_le (((1 - r : ℝ) : ℂ)) (Complex.I * (-T : ℂ))
    have hreal : ‖((1 - r : ℝ) : ℂ)‖ = |1 - r| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    have himag : ‖Complex.I * (-T : ℂ)‖ = T := by
      rw [norm_mul, Complex.norm_I, one_mul, norm_neg,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hTpos]
    rw [hreal, himag] at htri
    have habs : |1 - r| = 1 - r := abs_of_nonneg (by linarith [hr.2])
    rw [habs] at htri
    calc
      ‖(((1 - r : ℝ) : ℂ) + Complex.I * (-T))‖ + 3 ≤
          (1 - r) + T + 3 := by linarith
      _ ≤ H + 8 := by linarith [hT.2, hr.1]
  have hz : ‖((r : ℂ) + Complex.I * T)‖ + 3 ≤ H + 8 := by
    have htri := norm_add_le (r : ℂ) (Complex.I * (T : ℂ))
    have hreal : ‖(r : ℂ)‖ = |r| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    have himag : ‖Complex.I * (T : ℂ)‖ = T := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hTpos]
    rw [hreal, himag] at htri
    have habs : |r| = -r := abs_of_nonpos hr.2
    rw [habs] at htri
    linarith [hT.2, hr.1]
  have hHpos : 0 < H + 8 := by linarith
  have hlogu := Real.log_le_log
    (show 0 < ‖(((1 - r : ℝ) : ℂ) + Complex.I * (-T))‖ + 3 by positivity) hu
  have hlogz := Real.log_le_log
    (show 0 < ‖((r : ℂ) + Complex.I * T)‖ + 3 by positivity) hz
  linarith

private theorem negativeGeometryBottomLogSum_le
    {H T r : ℝ} (hH : 4 ≤ H) (hT : T ∈ Set.Ioo H (H + 1))
    (hr : r ∈ Set.Icc (-(1 / 2 : ℝ)) 0) :
    Real.log
        (‖(((1 - r : ℝ) : ℂ) + Complex.I * T)‖ + 3) +
      Real.log (‖((r : ℂ) + Complex.I * (-T))‖ + 3) ≤
        2 * Real.log (H + 8) := by
  have hTpos : 0 < T := by linarith [hH, hT.1]
  have hu : ‖(((1 - r : ℝ) : ℂ) + Complex.I * T)‖ + 3 ≤ H + 8 := by
    have htri := norm_add_le (((1 - r : ℝ) : ℂ)) (Complex.I * (T : ℂ))
    have hreal : ‖((1 - r : ℝ) : ℂ)‖ = |1 - r| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    have himag : ‖Complex.I * (T : ℂ)‖ = T := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hTpos]
    rw [hreal, himag] at htri
    have habs : |1 - r| = 1 - r := abs_of_nonneg (by linarith [hr.2])
    rw [habs] at htri
    calc
      ‖(((1 - r : ℝ) : ℂ) + Complex.I * T)‖ + 3 ≤
          (1 - r) + T + 3 := by linarith
      _ ≤ H + 8 := by linarith [hT.2, hr.1]
  have hz : ‖((r : ℂ) + Complex.I * (-T))‖ + 3 ≤ H + 8 := by
    have htri := norm_add_le (r : ℂ) (Complex.I * (-T : ℂ))
    have hreal : ‖(r : ℂ)‖ = |r| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    have himag : ‖Complex.I * (-T : ℂ)‖ = T := by
      rw [norm_mul, Complex.norm_I, one_mul, norm_neg,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hTpos]
    rw [hreal, himag] at htri
    have habs : |r| = -r := abs_of_nonpos hr.2
    rw [habs] at htri
    calc
      ‖((r : ℂ) + Complex.I * (-T))‖ + 3 ≤ -r + T + 3 := by linarith
      _ ≤ H + 8 := by linarith [hT.2, hr.1]
  have hHpos : 0 < H + 8 := by linarith
  have hlogu := Real.log_le_log
    (show 0 < ‖(((1 - r : ℝ) : ℂ) + Complex.I * T)‖ + 3 by positivity) hu
  have hlogz := Real.log_le_log
    (show 0 < ‖((r : ℂ) + Complex.I * (-T))‖ + 3 by positivity) hz
  linarith

private theorem regularized_zero_of_L_zero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) {s : ℂ}
    (hL : DirichletCharacter.LFunction chi s = 0) :
    regularizedLFunction chi s = 0 := by
  simp [regularizedLFunction, hchi, hL]

private theorem LFunction_ne_zero_of_directWideClearance
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1)
    {v r d : ℝ} (hr0 : 0 < r) (hr4 : r < 4) (hd : 0 < d)
    (hdist : ∀ rho ∈ wideZeroSupport chi v,
      d ≤ ‖((r : ℂ) + Complex.I * v) - rho‖) :
    DirichletCharacter.LFunction chi
      ((r : ℂ) + Complex.I * v) ≠ 0 := by
  intro hzero
  let s : ℂ := (r : ℂ) + Complex.I * v
  have hsball : s ∈ Metric.ball (wideCenter v) 2 := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : s - wideCenter v = ((r - 2 : ℝ) : ℂ) := by
      dsimp [s, wideCenter]
      push_cast
      ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have hsupp : s ∈ wideZeroSupport chi v :=
    mem_wideZeroSupport_of_eq_zero_of_mem_ball chi
      (Metric.ball_subset_ball (by norm_num [wideRadius] :
        (2 : ℝ) ≤ wideRadius) hsball)
      (regularized_zero_of_L_zero chi hchi (by simpa [s] using hzero))
  have := hdist s hsupp
  simp [s] at this
  linarith

/-- Nonprincipal primitive selected-good-height horizontal estimate.  The
constant `M` is kept explicit; its inverse clearance has only one local-zero
logarithm by `inv_exerciseHorizontalClearance_le_uniform`. -/
theorem exists_goodHeight_horizontal_nonprincipal_fixed
    (Cg : ℝ) (hCg : 0 < Cg)
    (hDigamma : ∀ z : ℂ,
      (∀ m : ℕ, (1 / 4 : ℝ) ≤ ‖z + (m : ℂ)‖) →
      ‖Complex.digamma z‖ ≤ Cg * Real.log (‖z‖ + 2))
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {H x : ℝ} (hH : 4 ≤ H) (hx : Real.exp 2 ≤ x) :
    ∃ T ∈ Set.Ioo H (H + 1),
      (∀ a ∈ exerciseLocalImagCoordinates chi H,
        exerciseHorizontalClearance chi H ≤ |T - a|) ∧
      let d := exerciseHorizontalClearance chi H
      let L := Real.log ((q : ℝ) * (H + 3))
      let R := 20 * (Real.log 21600 + 2 * L) + 5520 * L + 5520 * L / d
      let M := ‖Complex.log (q : ℂ)‖ + R + 4 +
        2 * Cg * Real.log (H + 8)
      ‖endpointHorizontalBoundaryIntegral chi x (-(1 / 2 : ℝ))
          (1 + (Real.log x)⁻¹) T‖ ≤
        2 * ((1 + (Real.log x)⁻¹) - (-(1 / 2 : ℝ))) / Real.pi *
          (M * x ^ (1 + (Real.log x)⁻¹) / T) := by
  obtain ⟨T, hT, hclear⟩ := exists_goodHeight_with_localCoordinateClearance chi H
  let d := exerciseHorizontalClearance chi H
  let L := Real.log ((q : ℝ) * (H + 3))
  let R := 20 * (Real.log 21600 + 2 * L) + 5520 * L + 5520 * L / d
  let M := ‖Complex.log (q : ℂ)‖ + R + 4 + 2 * Cg * Real.log (H + 8)
  let c := 1 + (Real.log x)⁻¹
  have hd : 0 < d := exerciseHorizontalClearance_pos chi H
  have hlogx : 2 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le ((Real.exp_pos 2).trans_le hx)]
    exact hx
  have hc1 : 1 < c := by
    dsimp [c]
    exact lt_add_of_pos_right 1 (inv_pos.mpr (by linarith))
  have hc4 : c < 4 := by
    dsimp [c]
    have hinv : (Real.log x)⁻¹ ≤ (2 : ℝ)⁻¹ :=
      (inv_le_inv₀ (show (0 : ℝ) < Real.log x by linarith)
        (by norm_num)).2 hlogx
    norm_num at hinv
    linarith
  have hTpos : 0 < T := by linarith [hH, hT.1]
  have hTabs : |T| ≤ H + 1 := by rw [abs_of_pos hTpos]; exact hT.2.le
  have hnegTabs : |-T| ≤ H + 1 := by simpa using hTabs
  have hdirect := directWideClearance_of_goodHeight chi hprim hH hT hclear
  have hinverse := inverseWideClearance_of_goodHeight chi hprim hchi hH hT hclear
  have hinversePos := inverseWidePositiveClearance_of_goodHeight
    chi hprim hchi hH hT hclear
  have hdirectNeg : ∀ r : ℝ, ∀ rho ∈ wideZeroSupport chi (-T),
      d ≤ ‖((r : ℂ) + Complex.I * (-T : ℝ) - rho)‖ := by
    simpa only [Complex.ofReal_neg] using hdirect.1
  have hL0 : 0 ≤ L := by
    dsimp [L]
    apply Real.log_nonneg
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le (n := q)
    nlinarith
  have hR0 : 0 ≤ R := by
    dsimp [R]
    have hc : 0 ≤ Real.log 21600 := Real.log_nonneg (by norm_num)
    positivity
  have hM0 : 0 ≤ M := by
    dsimp [M]
    have hlogH : 0 ≤ Real.log (H + 8) := Real.log_nonneg (by linarith)
    positivity
  have hlogScaleTop := log_arithmeticScale_le_goodHeightScale
    (q := q) (show 0 ≤ H by linarith) hTabs
  have hlogScaleBottom := log_arithmeticScale_le_goodHeightScale
    (q := q) (show 0 ≤ H by linarith) hnegTabs
  have hpositive (v : ℝ) (hv : |v| ≤ H + 1)
      (hdirectv : ∀ r : ℝ, ∀ rho ∈ wideZeroSupport chi v,
        d ≤ ‖((r : ℂ) + Complex.I * v) - rho‖) :
      ∀ r ∈ Set.Ioc 0 c,
        ‖logDeriv (DirichletCharacter.LFunction chi)
          ((r : ℂ) + Complex.I * v)‖ ≤ M := by
    intro r hr
    have hbase := norm_logDeriv_LFunction_le_of_wide_clearance
      chi hprim hchi hr.1 (hr.2.trans_lt hc4) hd (hdirectv r)
    have hlog := log_arithmeticScale_le_goodHeightScale
      (q := q) (show 0 ≤ H by linarith) hv
    have hdiv : 5520 * Real.log (arithmeticScale q v) / d ≤
        5520 * L / d := by
      apply div_le_div_of_nonneg_right _ hd.le
      exact mul_le_mul_of_nonneg_left hlog (by norm_num)
    dsimp [M, R, L] at hbase hlog hdiv ⊢
    have hlogH : 0 ≤ Real.log (H + 8) := Real.log_nonneg (by linarith)
    nlinarith [norm_nonneg (Complex.log (q : ℂ))]
  have hnegTop : ∀ r ∈ Set.Icc (-(1 / 2 : ℝ)) 0, r < 0 →
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) + Complex.I * T)‖ ≤ M := by
    intro r hr hrneg
    have hbase := norm_logDeriv_LFunction_negativeHorizontal_le_fixed
      Cg hCg hDigamma chi hprim hchi hr hrneg
      (by rw [abs_of_pos hTpos]; linarith [hH, hT.1]) hd
      (hinverse r hr)
    have hgeom := negativeGeometryLogSum_le hH hT hr
    have hlog := hlogScaleBottom
    have hdiv : 5520 * Real.log (arithmeticScale q (-T)) / d ≤
        5520 * L / d := by
      apply div_le_div_of_nonneg_right _ hd.le
      exact mul_le_mul_of_nonneg_left hlog (by norm_num)
    dsimp [M, R, L] at hbase hlog hdiv ⊢
    nlinarith
  have hnegBottom : ∀ r ∈ Set.Icc (-(1 / 2 : ℝ)) 0, r < 0 →
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) - Complex.I * T)‖ ≤ M := by
    intro r hr hrneg
    have hbase := norm_logDeriv_LFunction_negativeHorizontal_le_fixed
      Cg hCg hDigamma chi hprim hchi hr hrneg
      (by rw [abs_neg, abs_of_pos hTpos]; linarith [hH, hT.1]) hd
      (by simpa only [neg_neg, Complex.ofReal_neg] using hinversePos r hr)
    have hgeom := negativeGeometryBottomLogSum_le hH hT hr
    have hlog := hlogScaleTop
    have hdiv : 5520 * Real.log (arithmeticScale q T) / d ≤
        5520 * L / d := by
      apply div_le_div_of_nonneg_right _ hd.le
      exact mul_le_mul_of_nonneg_left hlog (by norm_num)
    have hbase' :
        ‖logDeriv (DirichletCharacter.LFunction chi)
          ((r : ℂ) + Complex.I * (-T))‖ ≤
        ‖Complex.log (q : ℂ)‖ +
          (20 * (Real.log 21600 + 2 * Real.log (arithmeticScale q T)) +
            5520 * Real.log (arithmeticScale q T) +
            5520 * Real.log (arithmeticScale q T) / d) + 4 +
          Cg * (Real.log
            (‖(((1 - r : ℝ) : ℂ) + Complex.I * T)‖ + 3) +
            Real.log (‖((r : ℂ) + Complex.I * (-T))‖ + 3)) := by
      simpa only [neg_neg, Complex.ofReal_neg] using hbase
    dsimp [M, R, L] at hbase' hlog hdiv ⊢
    simpa only [Complex.ofReal_neg, mul_neg, sub_eq_add_neg] using (show
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) + Complex.I * (-T))‖ ≤ M by nlinarith)
  have htopAE : ∀ᵐ r : ℝ, r ∈ Set.uIoc (-(1 / 2 : ℝ)) c →
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) + Complex.I * T)‖ ≤ M := by
    filter_upwards [ae_ne_zero] with r hr0 hrange
    have hrIcc : r ∈ Set.Icc (-(1 / 2 : ℝ)) c := by
      have hu := Set.uIoc_subset_uIcc hrange
      rw [Set.uIcc_of_le (show (-(1 / 2 : ℝ)) ≤ c by linarith)] at hu
      exact hu
    rcases lt_or_gt_of_ne hr0 with hrneg | hrpos
    · exact hnegTop r ⟨hrIcc.1, hrneg.le⟩ hrneg
    · exact hpositive T hTabs hdirect.2 r ⟨hrpos, hrIcc.2⟩
  have hbottomAE : ∀ᵐ r : ℝ, r ∈ Set.uIoc (-(1 / 2 : ℝ)) c →
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) - Complex.I * T)‖ ≤ M := by
    filter_upwards [ae_ne_zero] with r hr0 hrange
    have hrIcc : r ∈ Set.Icc (-(1 / 2 : ℝ)) c := by
      have hu := Set.uIoc_subset_uIcc hrange
      rw [Set.uIcc_of_le (show (-(1 / 2 : ℝ)) ≤ c by linarith)] at hu
      exact hu
    rcases lt_or_gt_of_ne hr0 with hrneg | hrpos
    · exact hnegBottom r ⟨hrIcc.1, hrneg.le⟩ hrneg
    · have hp := hpositive (-T) hnegTabs hdirectNeg r ⟨hrpos, hrIcc.2⟩
      simpa only [Complex.ofReal_neg, mul_neg, sub_eq_add_neg] using hp
  have hLtopAE : ∀ᵐ r : ℝ, r ∈ Set.uIoc (-(1 / 2 : ℝ)) c →
      DirichletCharacter.LFunction chi ((r : ℂ) + Complex.I * T) ≠ 0 := by
    filter_upwards [ae_ne_zero] with r hr0 hrange
    have hrIcc : r ∈ Set.Icc (-(1 / 2 : ℝ)) c := by
      have hu := Set.uIoc_subset_uIcc hrange
      rw [Set.uIcc_of_le (show (-(1 / 2 : ℝ)) ≤ c by linarith)] at hu
      exact hu
    rcases lt_or_gt_of_ne hr0 with hrneg | hrpos
    · exact KoukNegativeHalfPlaneNonvanishing.LFunction_ne_zero_of_primitive_of_re_neg_of_gamma_ne_zero
        chi hprim (by simpa using hrneg)
        (KoukNegativeHalfPlaneNonvanishing.gammaFactor_ne_zero_of_im_ne_zero
          chi (by simp [hTpos.ne']))
    · exact LFunction_ne_zero_of_directWideClearance chi hchi hrpos
        (hrIcc.2.trans_lt hc4) hd (hdirect.2 r)
  have hLbottomAE : ∀ᵐ r : ℝ, r ∈ Set.uIoc (-(1 / 2 : ℝ)) c →
      DirichletCharacter.LFunction chi ((r : ℂ) - Complex.I * T) ≠ 0 := by
    filter_upwards [ae_ne_zero] with r hr0 hrange
    have hrIcc : r ∈ Set.Icc (-(1 / 2 : ℝ)) c := by
      have hu := Set.uIoc_subset_uIcc hrange
      rw [Set.uIcc_of_le (show (-(1 / 2 : ℝ)) ≤ c by linarith)] at hu
      exact hu
    rcases lt_or_gt_of_ne hr0 with hrneg | hrpos
    · exact KoukNegativeHalfPlaneNonvanishing.LFunction_ne_zero_of_primitive_of_re_neg_of_gamma_ne_zero
        chi hprim (by simpa using hrneg)
        (KoukNegativeHalfPlaneNonvanishing.gammaFactor_ne_zero_of_im_ne_zero
          chi (by simp [hTpos.ne']))
    · have hp := LFunction_ne_zero_of_directWideClearance chi hchi hrpos
        (hrIcc.2.trans_lt hc4) hd (hdirectNeg r)
      simpa only [Complex.ofReal_neg, mul_neg, sub_eq_add_neg] using hp
  refine ⟨T, hT, hclear, ?_⟩
  dsimp only [d, L, R, M, c]
  exact norm_endpointHorizontalBoundaryIntegral_le_of_logDeriv_ae
    chi (show 1 ≤ x by
      have he : 1 < Real.exp 2 := Real.one_lt_exp_iff.mpr (by norm_num)
      linarith)
      (show 0 ≤ c by linarith) (show (-(1 / 2 : ℝ)) ≤ c by linarith)
      hTpos hM0 hLtopAE hLbottomAE htopAE hbottomAE

/-- Source-sized nonprincipal horizontal estimate with one absolute constant.
This is the quantitative horizontal input in the proof of Theorem 11.3. -/
theorem uniform_goodHeight_horizontal_nonprincipal :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
        chi.IsPrimitive → chi ≠ 1 →
        ∀ H x : ℝ, 4 ≤ H → Real.exp 2 ≤ x →
          ∃ T ∈ Set.Ioo H (H + 1),
            (∀ a ∈ exerciseLocalImagCoordinates chi H,
              exerciseHorizontalClearance chi H ≤ |T - a|) ∧
            ‖endpointHorizontalBoundaryIntegral chi x (-(1 / 2 : ℝ))
                (1 + (Real.log x)⁻¹) T‖ ≤
              C * x * (Real.log ((q : ℝ) * (H + 8))) ^ 2 / T := by
  obtain ⟨Cg, hCg, hDigamma⟩ :=
    KoukGaussDigammaSeries.awayFromPolesDigammaLogBound
  let C0 : ℝ := 100000000 + 2 * Cg
  refine ⟨6 * C0, by dsimp [C0]; positivity, ?_⟩
  intro q _inst chi hprim hchi H x hH hx
  obtain ⟨T, hT, hclear, hraw⟩ :=
    exists_goodHeight_horizontal_nonprincipal_fixed
      Cg hCg hDigamma chi hprim hchi hH hx
  let d := exerciseHorizontalClearance chi H
  let L := Real.log ((q : ℝ) * (H + 3))
  let W := Real.log ((q : ℝ) * (H + 8))
  let R := 20 * (Real.log 21600 + 2 * L) + 5520 * L + 5520 * L / d
  let M := ‖Complex.log (q : ℂ)‖ + R + 4 + 2 * Cg * Real.log (H + 8)
  let c := 1 + (Real.log x)⁻¹
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le (n := q)
  have hW1 : 1 ≤ W := by
    dsimp [W]
    have hscale12 : (12 : ℝ) ≤ (q : ℝ) * (H + 8) := by
      have hm := mul_le_mul_of_nonneg_right hq (show 0 ≤ H + 8 by linarith)
      nlinarith
    have hscale : Real.exp 1 < (q : ℝ) * (H + 8) := by
      have he3 : Real.exp 1 < 3 := Real.exp_one_lt_three
      linarith
    exact (Real.lt_log_iff_exp_lt (by positivity)).2 hscale |>.le
  have hW0 : 0 ≤ W := zero_le_one.trans hW1
  have hLW : L ≤ W := by
    dsimp [L, W]
    apply Real.log_le_log
    · positivity
    · exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hlogqW : ‖Complex.log (q : ℂ)‖ ≤ W := by
    rw [← Complex.natCast_log, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_natCast_nonneg q)]
    dsimp [W]
    apply Real.log_le_log
    · positivity
    · have hq0 : (0 : ℝ) ≤ q := by positivity
      nlinarith [mul_le_mul_of_nonneg_left
        (show 1 ≤ H + 8 by linarith) hq0]
  have hlogHW : Real.log (H + 8) ≤ W := by
    dsimp [W]
    apply Real.log_le_log (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hq (show 0 ≤ H + 8 by linarith)]
  have hinvRaw := inv_exerciseHorizontalClearance_le_uniform
    chi hprim hchi (show 0 ≤ H by linarith)
  have hlogBig : Real.log ((q : ℝ) * (H + 8)) = W := rfl
  rw [hlogBig] at hinvRaw
  have hinv : d⁻¹ ≤ 8596 * W := by
    dsimp [d]
    exact hinvRaw.trans (by nlinarith)
  have hLd : L / d ≤ 8596 * W ^ 2 := by
    rw [div_eq_mul_inv]
    calc
      L * d⁻¹ ≤ W * (8596 * W) :=
        mul_le_mul hLW hinv (inv_nonneg.mpr
          (exerciseHorizontalClearance_pos chi H).le) hW0
      _ = 8596 * W ^ 2 := by ring
  have hWsq : W ≤ W ^ 2 := by nlinarith
  have hconst : Real.log 21600 ≤ 21599 := by
    convert Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 21600 by norm_num) using 1 <;> norm_num
  have hR : R ≤ 48000000 * W ^ 2 := by
    dsimp [R]
    have hscaled : 5520 * L / d ≤ 5520 * 8596 * W ^ 2 := by
      calc
        5520 * L / d = 5520 * (L / d) := by ring
        _ ≤ 5520 * (8596 * W ^ 2) :=
          mul_le_mul_of_nonneg_left hLd (by norm_num)
        _ = 5520 * 8596 * W ^ 2 := by ring
    nlinarith
  have hM : M ≤ C0 * W ^ 2 := by
    dsimp [M, C0]
    have hCgTerm : 2 * Cg * Real.log (H + 8) ≤
        2 * Cg * W ^ 2 := by
      exact mul_le_mul_of_nonneg_left (hlogHW.trans hWsq)
        (mul_nonneg (by norm_num) hCg.le)
    nlinarith
  have hlogx : 2 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le ((Real.exp_pos 2).trans_le hx)]
    exact hx
  have hc : c ≤ 3 / 2 := by
    dsimp [c]
    have hinvlog : (Real.log x)⁻¹ ≤ (2 : ℝ)⁻¹ :=
      (inv_le_inv₀ (show 0 < Real.log x by linarith) (by norm_num)).2 hlogx
    norm_num at hinvlog ⊢
    linarith
  have hpref : 2 * (c - (-(1 / 2 : ℝ))) / Real.pi ≤ 2 := by
    have hpi := Real.pi_gt_three
    have hpi0 := Real.pi_pos
    apply (div_le_iff₀ hpi0).2
    nlinarith
  have hx1 : 1 < x := by
    have he : 1 < Real.exp 2 := Real.one_lt_exp_iff.mpr (by norm_num)
    exact he.trans_le hx
  have hpow : x ^ c ≤ 3 * x := by
    have hbase := PaperEdgePerronRemainder.rpow_standardEdge_le
      hx1 (show 0 < x by linarith) le_rfl
    have he : Real.exp 1 < 3 := Real.exp_one_lt_three
    change x ^ (1 + (Real.log x)⁻¹) ≤ 3 * x
    exact hbase.trans (by nlinarith)
  have hTpos : 0 < T := by linarith [hH, hT.1]
  have hM0 : 0 ≤ M := by
    dsimp [M, R, L, d]
    have hscale1 : (1 : ℝ) ≤ (q : ℝ) * (H + 3) := by
      have hm := mul_le_mul_of_nonneg_right hq (show 0 ≤ H + 3 by linarith)
      nlinarith
    have hL0 : 0 ≤ Real.log ((q : ℝ) * (H + 3)) :=
      Real.log_nonneg hscale1
    have hlogc : 0 ≤ Real.log 21600 := Real.log_nonneg (by norm_num)
    have hlogH : 0 ≤ Real.log (H + 8) := Real.log_nonneg (by linarith)
    have hd0 := (exerciseHorizontalClearance_pos chi H).le
    positivity
  have hC00 : 0 ≤ C0 := by dsimp [C0]; positivity
  refine ⟨T, hT, hclear, ?_⟩
  calc
    ‖endpointHorizontalBoundaryIntegral chi x (-(1 / 2 : ℝ))
        (1 + (Real.log x)⁻¹) T‖ ≤
      2 * (c - (-(1 / 2 : ℝ))) / Real.pi * (M * x ^ c / T) := by
        simpa only [c, d, L, R, M] using hraw
    _ ≤ 2 * (M * (3 * x) / T) := by
      apply mul_le_mul hpref
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow hM0) hTpos.le
      · exact div_nonneg
          (mul_nonneg hM0 (Real.rpow_nonneg (by linarith) _)) hTpos.le
      · norm_num
    _ ≤ 6 * C0 * x * W ^ 2 / T := by
      have hmx : M * x ≤ (C0 * W ^ 2) * x :=
        mul_le_mul_of_nonneg_right hM (by linarith)
      have := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmx (by norm_num : (0 : ℝ) ≤ 6)) hTpos.le
      convert this using 1 <;> ring
    _ = (6 * C0) * x *
        (Real.log ((q : ℝ) * (H + 8))) ^ 2 / T := by rfl

private theorem principalLFunction_ne_zero_of_directWideClearance
    {v r d : ℝ} (hr0 : 0 < r) (hr4 : r < 4) (hv : v ≠ 0)
    (hd : 0 < d)
    (hdist : ∀ rho ∈ wideZeroSupport
        (1 : DirichletCharacter ℂ 1) v,
      d ≤ ‖((r : ℂ) + Complex.I * v) - rho‖) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)
      ((r : ℂ) + Complex.I * v) ≠ 0 := by
  let s : ℂ := (r : ℂ) + Complex.I * v
  have hsball : s ∈ Metric.ball (wideCenter v) 2 := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : s - wideCenter v = ((r - 2 : ℝ) : ℂ) := by
      dsimp [s, wideCenter]
      push_cast
      ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have hreg : regularizedLFunction
      (1 : DirichletCharacter ℂ 1) s ≠ 0 := by
    intro hzero
    have hsupp : s ∈ wideZeroSupport
        (1 : DirichletCharacter ℂ 1) v :=
      mem_wideZeroSupport_of_eq_zero_of_mem_ball _
        (Metric.ball_subset_ball (by norm_num [wideRadius] :
          (2 : ℝ) ≤ wideRadius) hsball) hzero
    have := hdist s hsupp
    simp [s] at this
    linarith
  apply KoukEndpointContourBounds.LFunction_ne_zero_of_regularized_ne_zero_of_im_ne_zero
    (1 : DirichletCharacter ℂ 1) (by simpa [s] using hv) hreg

/-- Principal conductor-one selected-good-height horizontal estimate.  It uses
the same per-character aperture as the nonprincipal case; self-duality turns
the reflected negative-half support into the two direct horizontal supports. -/
theorem exists_goodHeight_horizontal_principal_fixed
    (Cg : ℝ) (hCg : 0 < Cg)
    (hDigamma : ∀ z : ℂ,
      (∀ m : ℕ, (1 / 4 : ℝ) ≤ ‖z + (m : ℂ)‖) →
      ‖Complex.digamma z‖ ≤ Cg * Real.log (‖z‖ + 2))
    {H x : ℝ} (hH : 4 ≤ H) (hx : Real.exp 2 ≤ x) :
    ∃ T ∈ Set.Ioo H (H + 1),
      (∀ a ∈ exerciseLocalImagCoordinates
          (1 : DirichletCharacter ℂ 1) H,
        exerciseHorizontalClearance
          (1 : DirichletCharacter ℂ 1) H ≤ |T - a|) ∧
      let chi : DirichletCharacter ℂ 1 := 1
      let d := exerciseHorizontalClearance chi H
      let L := Real.log (H + 3)
      let R := 2 + 20 * (Real.log 223948800 + 6 * L) +
        30300 * L + 30300 * L / d
      let M := R + 4 + 2 * Cg * Real.log (H + 8)
      ‖endpointHorizontalBoundaryIntegral chi x (-(1 / 2 : ℝ))
          (1 + (Real.log x)⁻¹) T‖ ≤
        2 * ((1 + (Real.log x)⁻¹) - (-(1 / 2 : ℝ))) / Real.pi *
          (M * x ^ (1 + (Real.log x)⁻¹) / T) := by
  let chi : DirichletCharacter ℂ 1 := 1
  let d := exerciseHorizontalClearance chi H
  let L := Real.log (H + 3)
  let R := 2 + 20 * (Real.log 223948800 + 6 * L) +
    30300 * L + 30300 * L / d
  let M := R + 4 + 2 * Cg * Real.log (H + 8)
  let c := 1 + (Real.log x)⁻¹
  have hprim : chi.IsPrimitive := by
    dsimp [chi]
    rw [DirichletCharacter.isPrimitive_def,
      DirichletCharacter.conductor_one]
  obtain ⟨T, hT, hclear⟩ :=
    exists_goodHeight_with_localCoordinateClearance chi H
  have hd : 0 < d := exerciseHorizontalClearance_pos chi H
  have hlogx : 2 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le ((Real.exp_pos 2).trans_le hx)]
    exact hx
  have hc1 : 1 < c := by
    dsimp [c]
    exact lt_add_of_pos_right 1 (inv_pos.mpr (by linarith))
  have hc4 : c < 4 := by
    dsimp [c]
    have hinv : (Real.log x)⁻¹ ≤ (2 : ℝ)⁻¹ :=
      (inv_le_inv₀ (show (0 : ℝ) < Real.log x by linarith)
        (by norm_num)).2 hlogx
    norm_num at hinv
    linarith
  have hTpos : 0 < T := by linarith [hH, hT.1]
  have hTabs : |T| ≤ H + 1 := by rw [abs_of_pos hTpos]; exact hT.2.le
  have hnegTabs : |-T| ≤ H + 1 := by simpa using hTabs
  have hdirect := directWideClearance_of_goodHeight chi hprim hH hT hclear
  have hdirectNeg : ∀ r : ℝ, ∀ rho ∈ wideZeroSupport chi (-T),
      d ≤ ‖((r : ℂ) + Complex.I * (-T : ℝ) - rho)‖ := by
    simpa only [Complex.ofReal_neg] using hdirect.1
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg (by linarith)
  have hR0 : 0 ≤ R := by
    dsimp [R]
    have hc : 0 ≤ Real.log 223948800 := Real.log_nonneg (by norm_num)
    positivity
  have hM0 : 0 ≤ M := by
    dsimp [M]
    have hlogH : 0 ≤ Real.log (H + 8) := Real.log_nonneg (by linarith)
    positivity
  have hlogScaleTop : Real.log (arithmeticScale 1 T) ≤ L := by
    dsimp [L]
    have hp : 0 < arithmeticScale 1 T := by
      unfold arithmeticScale
      positivity
    apply Real.log_le_log hp
    unfold arithmeticScale
    norm_num
    linarith [hTabs]
  have hlogScaleBottom : Real.log (arithmeticScale 1 (-T)) ≤ L := by
    dsimp [L]
    have hp : 0 < arithmeticScale 1 (-T) := by
      unfold arithmeticScale
      positivity
    apply Real.log_le_log hp
    unfold arithmeticScale
    norm_num
    linarith [hnegTabs]
  have hpole (v r : ℝ) (hv : 1 ≤ |v|) :
      ‖(((r : ℂ) + Complex.I * v) - 1)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have hden : 1 ≤ ‖((r : ℂ) + Complex.I * v) - 1‖ := by
      exact hv.trans (by
        simpa using Complex.abs_im_le_norm
          (((r : ℂ) + Complex.I * v) - 1))
    have hdenPos : 0 < ‖((r : ℂ) + Complex.I * v) - 1‖ :=
      zero_lt_one.trans_le hden
    exact ((inv_le_inv₀ hdenPos zero_lt_one).2 hden).trans (by norm_num)
  have hpositive (v : ℝ) (hv : |v| ≤ H + 1) (hv1 : 1 ≤ |v|)
      (hdirectv : ∀ r : ℝ, ∀ rho ∈ wideZeroSupport chi v,
        d ≤ ‖((r : ℂ) + Complex.I * v) - rho‖) :
      ∀ r ∈ Set.Ioc 0 c,
        ‖logDeriv (DirichletCharacter.LFunction chi)
          ((r : ℂ) + Complex.I * v)‖ ≤ M := by
    intro r hr
    have hpoleNe : (r : ℂ) + Complex.I * v ≠ 1 := by
      intro heq
      have him := congrArg Complex.im heq
      simp at him
      have hvne : v ≠ 0 := abs_pos.mp (zero_lt_one.trans_le hv1)
      exact hvne him
    have hbase :=
      MAPKoukExercise12TwoPointwisePrincipalFormula.norm_logDeriv_principal_le_of_wide_clearance
        hr.1 (hr.2.trans_lt hc4) hd hpoleNe (hpole v r hv1)
          (by simpa [chi] using hdirectv r)
    have hlog : Real.log (arithmeticScale 1 v) ≤ L := by
      dsimp [L]
      have hp : 0 < arithmeticScale 1 v := by
        unfold arithmeticScale
        positivity
      apply Real.log_le_log hp
      unfold arithmeticScale
      norm_num
      linarith [hv]
    have hdiv : 30300 * Real.log (arithmeticScale 1 v) / d ≤
        30300 * L / d := by
      apply div_le_div_of_nonneg_right _ hd.le
      exact mul_le_mul_of_nonneg_left hlog (by norm_num)
    have hbase' :
        ‖logDeriv (DirichletCharacter.LFunction chi)
          ((r : ℂ) + Complex.I * v)‖ ≤
          2 + 20 * (Real.log 223948800 +
            6 * Real.log (arithmeticScale 1 v)) +
          30300 * Real.log (arithmeticScale 1 v) +
          30300 * Real.log (arithmeticScale 1 v) / d := by
      simpa [chi] using hbase
    have htail : 0 ≤ 4 + 2 * Cg * Real.log (H + 8) := by
      have hh : 0 ≤ Real.log (H + 8) := Real.log_nonneg (by linarith)
      positivity
    dsimp [M, R] at hbase' hdiv ⊢
    nlinarith
  have hnegTop : ∀ r ∈ Set.Icc (-(1 / 2 : ℝ)) 0, r < 0 →
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) + Complex.I * T)‖ ≤ M := by
    intro r hr hrneg
    have hbase :=
      KoukPrincipalNegativeHorizontalLogDerivativeBound.norm_logDeriv_principal_negativeHorizontal_le_fixed
        Cg hCg hDigamma hr hrneg
        (by rw [abs_of_pos hTpos]; linarith [hH, hT.1]) hd
        (by simpa [chi] using hdirect.1 (1 - r))
    have hgeom := negativeGeometryLogSum_le hH hT hr
    have hdiv : 30300 * Real.log (arithmeticScale 1 (-T)) / d ≤
        30300 * L / d := by
      apply div_le_div_of_nonneg_right _ hd.le
      exact mul_le_mul_of_nonneg_left hlogScaleBottom (by norm_num)
    dsimp [M, R] at hbase hdiv ⊢
    nlinarith
  have hnegBottom : ∀ r ∈ Set.Icc (-(1 / 2 : ℝ)) 0, r < 0 →
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) - Complex.I * T)‖ ≤ M := by
    intro r hr hrneg
    have hbase :=
      KoukPrincipalNegativeHorizontalLogDerivativeBound.norm_logDeriv_principal_negativeHorizontal_le_fixed
        Cg hCg hDigamma hr hrneg
        (by rw [abs_neg, abs_of_pos hTpos]; linarith [hH, hT.1]) hd
        (by simpa [chi, Complex.ofReal_neg] using hdirect.2 (1 - r))
    have hgeom := negativeGeometryBottomLogSum_le hH hT hr
    have hdiv : 30300 * Real.log (arithmeticScale 1 T) / d ≤
        30300 * L / d := by
      apply div_le_div_of_nonneg_right _ hd.le
      exact mul_le_mul_of_nonneg_left hlogScaleTop (by norm_num)
    have hbase' :
        ‖logDeriv (DirichletCharacter.LFunction chi)
          ((r : ℂ) + Complex.I * (-T))‖ ≤
          (2 + 20 * (Real.log 223948800 +
              6 * Real.log (arithmeticScale 1 T)) +
            30300 * Real.log (arithmeticScale 1 T) +
            30300 * Real.log (arithmeticScale 1 T) / d) + 4 +
          Cg * (Real.log
            (‖(((1 - r : ℝ) : ℂ) + Complex.I * T)‖ + 3) +
            Real.log (‖((r : ℂ) + Complex.I * (-T))‖ + 3)) := by
      simpa only [neg_neg, Complex.ofReal_neg] using hbase
    dsimp [M, R] at hbase' hdiv ⊢
    simpa only [Complex.ofReal_neg, mul_neg, sub_eq_add_neg] using (show
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) + Complex.I * (-T))‖ ≤ M by nlinarith)
  have htopAE : ∀ᵐ r : ℝ, r ∈ Set.uIoc (-(1 / 2 : ℝ)) c →
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) + Complex.I * T)‖ ≤ M := by
    filter_upwards [ae_ne_zero] with r hr0 hrange
    have hrIcc : r ∈ Set.Icc (-(1 / 2 : ℝ)) c := by
      have hu := Set.uIoc_subset_uIcc hrange
      rw [Set.uIcc_of_le (show (-(1 / 2 : ℝ)) ≤ c by linarith)] at hu
      exact hu
    rcases lt_or_gt_of_ne hr0 with hrneg | hrpos
    · exact hnegTop r ⟨hrIcc.1, hrneg.le⟩ hrneg
    · exact hpositive T hTabs (by rw [abs_of_pos hTpos]; linarith [hH, hT.1])
        hdirect.2 r ⟨hrpos, hrIcc.2⟩
  have hbottomAE : ∀ᵐ r : ℝ, r ∈ Set.uIoc (-(1 / 2 : ℝ)) c →
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) - Complex.I * T)‖ ≤ M := by
    filter_upwards [ae_ne_zero] with r hr0 hrange
    have hrIcc : r ∈ Set.Icc (-(1 / 2 : ℝ)) c := by
      have hu := Set.uIoc_subset_uIcc hrange
      rw [Set.uIcc_of_le (show (-(1 / 2 : ℝ)) ≤ c by linarith)] at hu
      exact hu
    rcases lt_or_gt_of_ne hr0 with hrneg | hrpos
    · exact hnegBottom r ⟨hrIcc.1, hrneg.le⟩ hrneg
    · have hp := hpositive (-T) hnegTabs
        (by rw [abs_neg, abs_of_pos hTpos]; linarith [hH, hT.1])
        hdirectNeg r ⟨hrpos, hrIcc.2⟩
      simpa only [Complex.ofReal_neg, mul_neg, sub_eq_add_neg] using hp
  have hLtopAE : ∀ᵐ r : ℝ, r ∈ Set.uIoc (-(1 / 2 : ℝ)) c →
      DirichletCharacter.LFunction chi ((r : ℂ) + Complex.I * T) ≠ 0 := by
    filter_upwards [ae_ne_zero] with r hr0 hrange
    have hrIcc : r ∈ Set.Icc (-(1 / 2 : ℝ)) c := by
      have hu := Set.uIoc_subset_uIcc hrange
      rw [Set.uIcc_of_le (show (-(1 / 2 : ℝ)) ≤ c by linarith)] at hu
      exact hu
    rcases lt_or_gt_of_ne hr0 with hrneg | hrpos
    · exact KoukNegativeHalfPlaneNonvanishing.LFunction_ne_zero_of_primitive_of_re_neg_of_gamma_ne_zero
        chi hprim (by simpa using hrneg)
        (KoukNegativeHalfPlaneNonvanishing.gammaFactor_ne_zero_of_im_ne_zero
          chi (by simp [hTpos.ne']))
    · exact principalLFunction_ne_zero_of_directWideClearance hrpos
        (hrIcc.2.trans_lt hc4) hTpos.ne' hd (by simpa [chi] using hdirect.2 r)
  have hLbottomAE : ∀ᵐ r : ℝ, r ∈ Set.uIoc (-(1 / 2 : ℝ)) c →
      DirichletCharacter.LFunction chi ((r : ℂ) - Complex.I * T) ≠ 0 := by
    filter_upwards [ae_ne_zero] with r hr0 hrange
    have hrIcc : r ∈ Set.Icc (-(1 / 2 : ℝ)) c := by
      have hu := Set.uIoc_subset_uIcc hrange
      rw [Set.uIcc_of_le (show (-(1 / 2 : ℝ)) ≤ c by linarith)] at hu
      exact hu
    rcases lt_or_gt_of_ne hr0 with hrneg | hrpos
    · exact KoukNegativeHalfPlaneNonvanishing.LFunction_ne_zero_of_primitive_of_re_neg_of_gamma_ne_zero
        chi hprim (by simpa using hrneg)
        (KoukNegativeHalfPlaneNonvanishing.gammaFactor_ne_zero_of_im_ne_zero
          chi (by simp [hTpos.ne']))
    · have hp := principalLFunction_ne_zero_of_directWideClearance hrpos
        (hrIcc.2.trans_lt hc4) (neg_ne_zero.mpr hTpos.ne') hd
        (by simpa [chi, Complex.ofReal_neg] using hdirect.1 r)
      simpa only [Complex.ofReal_neg, mul_neg, sub_eq_add_neg] using hp
  refine ⟨T, hT, by simpa [chi] using hclear, ?_⟩
  dsimp only [chi, d, L, R, M, c]
  exact norm_endpointHorizontalBoundaryIntegral_le_of_logDeriv_ae
    (1 : DirichletCharacter ℂ 1)
      (show 1 ≤ x by
        have he : 1 < Real.exp 2 := Real.one_lt_exp_iff.mpr (by norm_num)
        linarith)
      (show 0 ≤ c by linarith) (show (-(1 / 2 : ℝ)) ≤ c by linarith)
      hTpos hM0 (by simpa [chi] using hLtopAE)
      (by simpa [chi] using hLbottomAE)
      (by simpa [chi] using htopAE) (by simpa [chi] using hbottomAE)

/-- Source-sized conductor-one principal horizontal estimate with one absolute
constant. -/
theorem uniform_goodHeight_horizontal_principal :
    ∃ C : ℝ, 0 < C ∧
      ∀ H x : ℝ, 4 ≤ H → Real.exp 2 ≤ x →
        ∃ T ∈ Set.Ioo H (H + 1),
          (∀ a ∈ exerciseLocalImagCoordinates
              (1 : DirichletCharacter ℂ 1) H,
            exerciseHorizontalClearance
              (1 : DirichletCharacter ℂ 1) H ≤ |T - a|) ∧
          ‖endpointHorizontalBoundaryIntegral
              (1 : DirichletCharacter ℂ 1) x (-(1 / 2 : ℝ))
              (1 + (Real.log x)⁻¹) T‖ ≤
            C * x * (Real.log (H + 8)) ^ 2 / T := by
  obtain ⟨Cg, hCg, hDigamma⟩ :=
    KoukGaussDigammaSeries.awayFromPolesDigammaLogBound
  let C0 : ℝ := 12000000000 + 2 * Cg
  refine ⟨6 * C0, by dsimp [C0]; positivity, ?_⟩
  intro H x hH hx
  obtain ⟨T, hT, hclear, hraw⟩ :=
    exists_goodHeight_horizontal_principal_fixed Cg hCg hDigamma hH hx
  let chi : DirichletCharacter ℂ 1 := 1
  let d := exerciseHorizontalClearance chi H
  let L := Real.log (H + 3)
  let W := Real.log (H + 8)
  let R := 2 + 20 * (Real.log 223948800 + 6 * L) +
    30300 * L + 30300 * L / d
  let M := R + 4 + 2 * Cg * Real.log (H + 8)
  let c := 1 + (Real.log x)⁻¹
  have hW1 : 1 ≤ W := by
    dsimp [W]
    have he : Real.exp 1 < H + 8 := Real.exp_one_lt_three.trans (by linarith)
    exact (Real.lt_log_iff_exp_lt (by linarith)).2 he |>.le
  have hW0 : 0 ≤ W := zero_le_one.trans hW1
  have hLW : L ≤ W := by
    dsimp [L, W]
    exact Real.log_le_log (by linarith) (by linarith)
  have hinvRaw :=
    MAPKoukExercise12TwoLocalHorizontalAperture.inv_exerciseHorizontalClearance_le_principal
      (show 0 ≤ H by linarith)
  have hinv : d⁻¹ ≤ 121204 * W := by
    simpa [d, chi, W] using hinvRaw
  have hLd : L / d ≤ 121204 * W ^ 2 := by
    rw [div_eq_mul_inv]
    calc
      L * d⁻¹ ≤ W * (121204 * W) :=
        mul_le_mul hLW hinv (inv_nonneg.mpr
          (exerciseHorizontalClearance_pos chi H).le) hW0
      _ = 121204 * W ^ 2 := by ring
  have hWsq : W ≤ W ^ 2 := by nlinarith
  have hconst : Real.log 223948800 ≤ 223948799 := by
    convert Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 223948800 by norm_num) using 1 <;> norm_num
  have hR : R ≤ 10000000000 * W ^ 2 := by
    dsimp [R]
    have hscaled : 30300 * L / d ≤ 30300 * 121204 * W ^ 2 := by
      calc
        30300 * L / d = 30300 * (L / d) := by ring
        _ ≤ 30300 * (121204 * W ^ 2) :=
          mul_le_mul_of_nonneg_left hLd (by norm_num)
        _ = 30300 * 121204 * W ^ 2 := by ring
    nlinarith
  have hM : M ≤ C0 * W ^ 2 := by
    dsimp [M, C0]
    have hCgTerm : 2 * Cg * Real.log (H + 8) ≤
        2 * Cg * W ^ 2 := by
      exact mul_le_mul_of_nonneg_left hWsq
        (mul_nonneg (by norm_num) hCg.le)
    nlinarith
  have hlogx : 2 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le ((Real.exp_pos 2).trans_le hx)]
    exact hx
  have hc : c ≤ 3 / 2 := by
    dsimp [c]
    have hinvlog : (Real.log x)⁻¹ ≤ (2 : ℝ)⁻¹ :=
      (inv_le_inv₀ (show 0 < Real.log x by linarith) (by norm_num)).2 hlogx
    norm_num at hinvlog ⊢
    linarith
  have hpref : 2 * (c - (-(1 / 2 : ℝ))) / Real.pi ≤ 2 := by
    have hpi := Real.pi_gt_three
    have hpi0 := Real.pi_pos
    apply (div_le_iff₀ hpi0).2
    nlinarith
  have hx1 : 1 < x := by
    have he : 1 < Real.exp 2 := Real.one_lt_exp_iff.mpr (by norm_num)
    exact he.trans_le hx
  have hpow : x ^ c ≤ 3 * x := by
    have hbase := PaperEdgePerronRemainder.rpow_standardEdge_le
      hx1 (show 0 < x by linarith) le_rfl
    have he : Real.exp 1 < 3 := Real.exp_one_lt_three
    change x ^ (1 + (Real.log x)⁻¹) ≤ 3 * x
    exact hbase.trans (by nlinarith)
  have hTpos : 0 < T := by linarith [hH, hT.1]
  have hM0 : 0 ≤ M := by
    dsimp [M, R, L, d]
    have hL0 : 0 ≤ Real.log (H + 3) := Real.log_nonneg (by linarith)
    have hlogc : 0 ≤ Real.log 223948800 := Real.log_nonneg (by norm_num)
    have hlogH : 0 ≤ Real.log (H + 8) := Real.log_nonneg (by linarith)
    have hd0 := (exerciseHorizontalClearance_pos chi H).le
    positivity
  refine ⟨T, hT, hclear, ?_⟩
  calc
    ‖endpointHorizontalBoundaryIntegral
        (1 : DirichletCharacter ℂ 1) x (-(1 / 2 : ℝ))
        (1 + (Real.log x)⁻¹) T‖ ≤
      2 * (c - (-(1 / 2 : ℝ))) / Real.pi * (M * x ^ c / T) := by
        simpa only [chi, c, d, L, R, M] using hraw
    _ ≤ 2 * (M * (3 * x) / T) := by
      apply mul_le_mul hpref
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow hM0) hTpos.le
      · exact div_nonneg
          (mul_nonneg hM0 (Real.rpow_nonneg (by linarith) _)) hTpos.le
      · norm_num
    _ ≤ 6 * C0 * x * W ^ 2 / T := by
      have hmx : M * x ≤ (C0 * W ^ 2) * x :=
        mul_le_mul_of_nonneg_right hM (by linarith)
      have ht := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmx (by norm_num : (0 : ℝ) ≤ 6)) hTpos.le
      convert ht using 1 <;> ring
    _ = (6 * C0) * x * (Real.log (H + 8)) ^ 2 / T := by rfl

end

end KoukTheorem113GoodHeightHorizontalBound

#print axioms KoukTheorem113GoodHeightHorizontalBound.exists_goodHeight_horizontal_nonprincipal_fixed
#print axioms KoukTheorem113GoodHeightHorizontalBound.uniform_goodHeight_horizontal_nonprincipal
#print axioms KoukTheorem113GoodHeightHorizontalBound.exists_goodHeight_horizontal_principal_fixed
#print axioms KoukTheorem113GoodHeightHorizontalBound.uniform_goodHeight_horizontal_principal
