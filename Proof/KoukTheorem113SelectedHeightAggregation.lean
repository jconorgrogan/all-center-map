import KoukTheorem113GoodHeightHorizontalBound
import KoukUniformRealEndpointPerronBound
import KoukNegativeHalfLogDerivativeBound
import KoukRightReplacementCorrectionBound
import KoukTheorem113ZeroCutoffTransport
import KoukTheorem113ToCorrectedTail

/-!
# Selected-height aggregation for Koukoulopoulos Theorem 11.3

This module contains only the deterministic weld after the source analytic
components.  The zero divisor remains the complete primitive support.
-/

namespace KoukTheorem113SelectedHeightAggregation

set_option maxHeartbeats 1600000

open Set Complex DirichletZeros
open WideDiskBlaschkeAssembly WideDiskLFunctionGrowth
open MAPKoukExercise12TwoLocalHorizontalAperture
open KoukTheorem113PerCharacterGoodHeight
open KoukTheorem113ExactFormula KoukTheorem113FullSupportFormula
open KoukSelectedHeightRealEndpointFormula
open PrimitiveTruncatedExplicitFormulaBridge

noncomputable section

/-- A direct wide-disk clearance excludes every regularized zero on the
horizontal segment.  This includes `Re s = 0`, so the exact rectangle theorem
does not need an artificial seam convention. -/
theorem regularizedLFunction_ne_zero_of_directWideClearance
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {v r d : ℝ} (hrLower : -(1 : ℝ) < r) (hrUpper : r < 5)
    (hd : 0 < d)
    (hdist : ∀ rho ∈ wideZeroSupport chi v,
      d ≤ ‖((r : ℂ) + Complex.I * v) - rho‖) :
    regularizedLFunction chi ((r : ℂ) + Complex.I * v) ≠ 0 := by
  intro hzero
  let s : ℂ := (r : ℂ) + Complex.I * v
  have hsball : s ∈ Metric.ball (wideCenter v) wideRadius := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : s - wideCenter v = ((r - 2 : ℝ) : ℂ) := by
      dsimp [s, wideCenter]
      push_cast
      ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, wideRadius, abs_lt]
    constructor <;> linarith
  have hsupp : s ∈ wideZeroSupport chi v :=
    mem_wideZeroSupport_of_eq_zero_of_mem_ball chi hsball
      (by simpa [s] using hzero)
  have := hdist s hsupp
  simp [s] at this
  linarith

/-- Good-height clearance supplies the pointwise regularized nonvanishing
premises used by the exact real-endpoint rectangle. -/
theorem horizontal_regularized_nonzero_of_goodHeight
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) {H T c : ℝ}
    (hH : 4 ≤ H) (hT : T ∈ Set.Ioo H (H + 1))
    (hc : c < 4)
    (hclear : ∀ a ∈ exerciseLocalImagCoordinates chi H,
      exerciseHorizontalClearance chi H ≤ |T - a|) :
    (∀ r ∈ Set.Icc (-(1 / 2 : ℝ)) c,
      regularizedLFunction chi
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0) ∧
    (∀ r ∈ Set.Icc (-(1 / 2 : ℝ)) c,
      regularizedLFunction chi
        ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) := by
  have hdirect := directWideClearance_of_goodHeight chi hprim hH hT hclear
  have hd : 0 < exerciseHorizontalClearance chi H :=
    exerciseHorizontalClearance_pos chi H
  constructor
  · intro r hr
    have hdist : ∀ rho ∈ wideZeroSupport chi (-T),
        exerciseHorizontalClearance chi H ≤
          ‖((r : ℂ) + Complex.I * (-T : ℝ)) - rho‖ := by
      simpa only [Complex.ofReal_neg] using hdirect.1 r
    have hbase := regularizedLFunction_ne_zero_of_directWideClearance
      chi (v := -T) (r := r)
        (by linarith [hr.1]) (by linarith [hr.2, hc]) hd hdist
    simpa only [Complex.ofReal_neg, mul_comm] using hbase
  · intro r hr
    have hbase := regularizedLFunction_ne_zero_of_directWideClearance
      chi (v := T) (r := r)
        (by linarith [hr.1]) (by linarith [hr.2, hc]) hd (hdirect.2 r)
    simpa only [mul_comm] using hbase

/-- A primitive character equal to the principal character necessarily has
level one.  This isolates the dependent level transport needed to reuse the
literal conductor-one horizontal theorem. -/
private theorem principal_horizontal_of_eq_one
    {C : ℝ}
    (hHorizontal : ∀ H x : ℝ, 4 ≤ H → Real.exp 2 ≤ x →
      ∃ T ∈ Set.Ioo H (H + 1),
        (∀ a ∈ exerciseLocalImagCoordinates
            (1 : DirichletCharacter ℂ 1) H,
          exerciseHorizontalClearance
            (1 : DirichletCharacter ℂ 1) H ≤ |T - a|) ∧
        ‖endpointHorizontalBoundaryIntegral
            (1 : DirichletCharacter ℂ 1) x (-(1 / 2 : ℝ))
            (1 + (Real.log x)⁻¹) T‖ ≤
          C * x * (Real.log (H + 8)) ^ 2 / T)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi = 1)
    {H x : ℝ} (hH : 4 ≤ H) (hx : Real.exp 2 ≤ x) :
    ∃ T ∈ Set.Ioo H (H + 1),
      (∀ a ∈ exerciseLocalImagCoordinates chi H,
        exerciseHorizontalClearance chi H ≤ |T - a|) ∧
      ‖endpointHorizontalBoundaryIntegral chi x (-(1 / 2 : ℝ))
          (1 + (Real.log x)⁻¹) T‖ ≤
        C * x * (Real.log (H + 8)) ^ 2 / T := by
  have hlevel : q = 1 := by
    have hp := (DirichletCharacter.isPrimitive_def chi).mp hprim
    rw [hchi, DirichletCharacter.conductor_one] at hp
    exact hp.symm
  subst q
  obtain ⟨T, hT, hclear, hbound⟩ := hHorizontal H x hH hx
  refine ⟨T, hT, ?_, ?_⟩
  · simpa [hchi] using hclear
  · simpa [hchi] using hbound

/-- Literal triangle weld for the selected real-endpoint remainder.  No
component is dropped or renamed. -/
theorem norm_ambientSelectedRealEndpointRemainder_le_components
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    [NeZero chi.conductor]
    {t c T : ℝ} :
    ‖ambientSelectedRealEndpointRemainder chi t c T‖ ≤
      ‖realEndpointPerronError chi.primitiveCharacter t c T‖ +
      ‖endpointVerticalLineIntegral chi.primitiveCharacter t
        (-(1 / 2 : ℝ)) T‖ +
      ‖endpointHorizontalBoundaryIntegral chi.primitiveCharacter t
        (-(1 / 2 : ℝ)) c T‖ +
      ‖endpointRightReplacementCorrection chi.primitiveCharacter c T‖ +
      ‖principalEndpointUnit chi.primitiveCharacter‖ +
      ‖APFoundation.imprimitiveMangoldtCorrection chi
        (Finset.Icc 1 ⌊t⌋₊)‖ := by
  unfold ambientSelectedRealEndpointRemainder
  norm_num [KoukNegativeHalfPlaneNonvanishing.negativeHalfIntegerEdge]
  let A := realEndpointPerronError chi.primitiveCharacter t c T
  let B := endpointVerticalLineIntegral chi.primitiveCharacter t
    (-(1 / 2 : ℝ)) T
  let C := endpointHorizontalBoundaryIntegral chi.primitiveCharacter t
    (-(1 / 2 : ℝ)) c T
  let D := endpointRightReplacementCorrection chi.primitiveCharacter c T
  let E := principalEndpointUnit chi.primitiveCharacter
  let F := APFoundation.imprimitiveMangoldtCorrection chi
    (Finset.Icc 1 ⌊t⌋₊)
  change ‖A + B - C + D - E - F‖ ≤
    ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖E‖ + ‖F‖
  calc
    ‖A + B - C + D - E - F‖ ≤ ‖A + B - C + D - E‖ + ‖F‖ :=
      norm_sub_le _ _
    _ ≤ (‖A + B - C + D‖ + ‖E‖) + ‖F‖ := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ ((‖A + B - C‖ + ‖D‖) + ‖E‖) + ‖F‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (((‖A + B‖ + ‖C‖) + ‖D‖) + ‖E‖) + ‖F‖ := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ ((((‖A‖ + ‖B‖) + ‖C‖) + ‖D‖) + ‖E‖) + ‖F‖ := by
      gcongr
      exact norm_add_le _ _
    _ = ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖E‖ + ‖F‖ := by ring

/-- The range actually consumed by MAP: the requested zero cutoff is already
at least four, the arithmetic endpoint is beyond the selected unit height,
and the real-endpoint Perron estimate is in its certified range. -/
def KoukTheorem113MAPRangePointwise : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
      (T t : ℝ),
      4 ≤ T → T + 1 ≤ t → Real.exp 2 ≤ t →
        ‖MAPKoukTheorem113ToCorrectedTail.fullSupportEndpointResidual chi T t‖ ≤
          C * t * (Real.log (t * (q : ℝ) + 2)) ^ 2 / T

private theorem exp_two_gt_seven : (7 : ℝ) < Real.exp 2 := by
  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  nlinarith [Real.exp_one_gt_d9]

private theorem target_log_ge_one
    {q : ℕ} [NeZero q] {t : ℝ} (ht : Real.exp 2 ≤ t) :
    1 ≤ Real.log (t * (q : ℝ) + 2) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le (n := q)
  have ht0 : 0 < t := (Real.exp_pos 2).trans_le ht
  have hscale : Real.exp 1 < t * (q : ℝ) + 2 := by
    have he12 : Real.exp 1 < Real.exp 2 := Real.exp_lt_exp.mpr (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hq ht0.le]
  exact (Real.lt_log_iff_exp_lt ((Real.exp_pos 1).trans hscale)).2 hscale |>.le

private theorem log_t_add_two_le_target
    {q : ℕ} [NeZero q] {t : ℝ} (ht : 0 ≤ t) :
    Real.log (t + 2) ≤ Real.log (t * (q : ℝ) + 2) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le (n := q)
  apply Real.log_le_log (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hq ht]

private theorem log_conductor_height_le_two_target
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {H t : ℝ} (hH4 : 4 ≤ H) (hH : H + 1 ≤ t)
    (ht : Real.exp 2 ≤ t) :
    Real.log ((chi.conductor : ℝ) * (H + 8)) ≤
      2 * Real.log (t * (q : ℝ) + 2) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le (n := q)
  have ht7 : 7 < t := exp_two_gt_seven.trans_le ht
  have hcondNat : chi.conductor ≤ q :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) chi.conductor_dvd_level
  have hcond : (chi.conductor : ℝ) ≤ q := by exact_mod_cast hcondNat
  have hleft : (chi.conductor : ℝ) * (H + 8) ≤
      (t * (q : ℝ) + 2) ^ 2 := by
    have hH8 : H + 8 ≤ 2 * t := by linarith
    have hmul := mul_le_mul hcond hH8 (by linarith [hH4])
      (by positivity : (0 : ℝ) ≤ (q : ℝ))
    have hy : 2 * (q : ℝ) * t ≤ (t * (q : ℝ) + 2) ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ t by linarith) (show 0 ≤ (q : ℝ) by positivity)]
    nlinarith
  have hpos : 0 < (chi.conductor : ℝ) * (H + 8) := by
    exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero chi.conductor_ne_zero)
      (by linarith)
  have hlog := Real.log_le_log hpos hleft
  rw [Real.log_pow] at hlog
  norm_num at hlog ⊢
  exact hlog

private theorem log_height_le_two_target
    {q : ℕ} [NeZero q] {H t : ℝ}
    (hH4 : 4 ≤ H) (hH : H + 1 ≤ t) (ht : Real.exp 2 ≤ t) :
    Real.log (H + 8) ≤ 2 * Real.log (t * (q : ℝ) + 2) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le (n := q)
  have ht7 : 7 < t := exp_two_gt_seven.trans_le ht
  have hleft : H + 8 ≤ (t * (q : ℝ) + 2) ^ 2 := by
    have hH8 : H + 8 ≤ 2 * t := by linarith
    have hqt : t ≤ t * (q : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hq (show 0 ≤ t by linarith)]
    nlinarith
  have hlog := Real.log_le_log (by linarith : 0 < H + 8) hleft
  rw [Real.log_pow] at hlog
  norm_num at hlog ⊢
  exact hlog

/-- Transport the source's conductor-one band estimate across the only
possible primitive principal level.  The level equality is eliminated while
it is still an abstract index, avoiding dependent elimination on an ambient
character's `conductor` projection. -/
private theorem norm_residual_at_requestedCutoff_principal_of_eq_one
    {q : ℕ} [NeZero q] (psi : DirichletCharacter ℂ q)
    (hprim : psi.IsPrimitive) (hpsi : psi = 1)
    {T T' t E : ℝ} (hT : 2 ≤ T) (hTT' : T ≤ T')
    (hT' : T' ≤ T + 1) (hTt : T ≤ t) (hE : 0 ≤ E)
    {A P : ℂ}
    (hgood : ‖A - (P -
        MAPEndpointRegularizedZeroPrimitive.endpointMultiplicityWeightedZeroTerm
          psi 0 T' t)‖ ≤ E) :
    ‖A - (P -
        MAPEndpointRegularizedZeroPrimitive.endpointMultiplicityWeightedZeroTerm
          psi 0 T t)‖ ≤
      E + 13464 * t * Real.log (t + 2) / T := by
  subst psi
  have hlevel : q = 1 := by
    have hp := (DirichletCharacter.isPrimitive_def
      (1 : DirichletCharacter ℂ q)).mp hprim
    rw [DirichletCharacter.conductor_one] at hp
    exact hp.symm
  subst q
  exact KoukTheorem113ZeroCutoffTransport.norm_residual_at_requestedCutoff_principal_le
    hT hTT' hT' hTt hE hgood

private theorem selected_good_height_nonprincipal
    (CP CH Cg : ℝ) (hCP : 0 < CP) (hCH : 0 < CH) (hCg : 0 < Cg)
    (hDigamma : ∀ z : ℂ,
      (∀ m : ℕ, (1 / 4 : ℝ) ≤ ‖z + (m : ℂ)‖) →
      ‖Complex.digamma z‖ ≤ Cg * Real.log (‖z‖ + 2))
    (hPerron : ∀ (q : ℕ) [NeZero q]
      (psi : DirichletCharacter ℂ q) (t T : ℝ),
      Real.exp 2 ≤ t → 2 ≤ T → T ≤ t →
        ‖realEndpointPerronError psi t (1 + (Real.log t)⁻¹) T‖ ≤
          CP * t * (Real.log (t + 2)) ^ 2 / T)
    (hHorizontal : ∀ (q : ℕ) [NeZero q]
      (psi : DirichletCharacter ℂ q), psi.IsPrimitive → psi ≠ 1 →
      ∀ H x : ℝ, 4 ≤ H → Real.exp 2 ≤ x →
        ∃ T ∈ Set.Ioo H (H + 1),
          (∀ a ∈ exerciseLocalImagCoordinates psi H,
            exerciseHorizontalClearance psi H ≤ |T - a|) ∧
          ‖endpointHorizontalBoundaryIntegral psi x (-(1 / 2 : ℝ))
              (1 + (Real.log x)⁻¹) T‖ ≤
            CH * x * (Real.log ((q : ℝ) * (H + 8))) ^ 2 / T)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {H t : ℝ} (hH : 4 ≤ H) (hHt : H + 1 ≤ t)
    (ht : Real.exp 2 ≤ t)
    (hpsi : chi.primitiveCharacter ≠ 1) :
    ∃ T' ∈ Set.Ioo H (H + 1),
      ‖MAPKoukTheorem113ToCorrectedTail.fullSupportEndpointResidual chi T' t‖ ≤
        (CP + 4 * CH + 200 + 20 * Cg) *
          (t * (Real.log (t * (q : ℝ) + 2)) ^ 2 / T') := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let psi := chi.primitiveCharacter
  have hprim : psi.IsPrimitive := chi.primitiveCharacter_isPrimitive
  obtain ⟨T', hT', hclear, hhorizontal⟩ :=
    hHorizontal chi.conductor psi hprim hpsi H t hH ht
  let W := Real.log (t * (q : ℝ) + 2)
  let B := t * W ^ 2 / T'
  have ht0 : 0 < t := (Real.exp_pos 2).trans_le ht
  have hTpos : 0 < T' := by linarith [hH, hT'.1]
  have hTtwo : 2 ≤ T' := by linarith [hH, hT'.1]
  have hTt : T' ≤ t := hT'.2.le.trans hHt
  have hW1 : 1 ≤ W := by
    dsimp [W]
    exact target_log_ge_one ht
  have hW0 : 0 ≤ W := zero_le_one.trans hW1
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hWsqB : W ^ 2 ≤ B := by
    have hratio : 1 ≤ t / T' := by
      apply (le_div_iff₀ hTpos).2
      simpa using hTt
    calc
      W ^ 2 ≤ (t / T') * W ^ 2 :=
        (le_mul_iff_one_le_left (sq_pos_of_pos (zero_lt_one.trans_le hW1))).2 hratio
      _ = B := by dsimp [B]; ring
  have hp := hPerron chi.conductor psi t T' ht hTtwo hTt
  have hlogt : Real.log (t + 2) ≤ W := by
    dsimp [W]
    exact log_t_add_two_le_target ht0.le
  have hperron : ‖realEndpointPerronError psi t
      (1 + (Real.log t)⁻¹) T'‖ ≤ CP * B := by
    calc
      _ ≤ CP * t * (Real.log (t + 2)) ^ 2 / T' := hp
      _ ≤ CP * t * W ^ 2 / T' := by
        apply div_le_div_of_nonneg_right _ hTpos.le
        gcongr
        exact Real.log_nonneg (by linarith [ht0])
      _ = CP * B := by dsimp [B]; ring
  have hscale := log_conductor_height_le_two_target chi hH hHt ht
  have hscaleLog0 : 0 ≤ Real.log ((chi.conductor : ℝ) * (H + 8)) := by
    apply Real.log_nonneg
    have hc1 : (1 : ℝ) ≤ chi.conductor := by
      exact_mod_cast NeZero.one_le (n := chi.conductor)
    nlinarith [mul_le_mul_of_nonneg_left
      (show 1 ≤ H + 8 by linarith [hH]) (show (0 : ℝ) ≤ chi.conductor by positivity)]
  have hhorizontal' : ‖endpointHorizontalBoundaryIntegral psi t
      (-(1 / 2 : ℝ)) (1 + (Real.log t)⁻¹) T'‖ ≤ 4 * CH * B := by
    calc
      _ ≤ CH * t *
          (Real.log ((chi.conductor : ℝ) * (H + 8))) ^ 2 / T' := hhorizontal
      _ ≤ CH * t * (2 * W) ^ 2 / T' := by
        apply div_le_div_of_nonneg_right _ hTpos.le
        gcongr
      _ = 4 * CH * B := by dsimp [B]; ring
  have hleftRaw :=
    KoukNegativeHalfLogDerivativeBound.norm_endpointVerticalLineIntegral_negativeHalf_le_fixed
      Cg hCg hDigamma psi hprim (show 1 ≤ t by linarith) hTpos.le
  have hlogcond : ‖Complex.log (chi.conductor : ℂ)‖ ≤ W := by
    rw [← Complex.natCast_log, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_natCast_nonneg chi.conductor)]
    apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero chi.conductor_ne_zero
    · have hcondNat : chi.conductor ≤ q :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) chi.conductor_dvd_level
      have hcond : (chi.conductor : ℝ) ≤ q := by exact_mod_cast hcondNat
      have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le (n := q)
      nlinarith [mul_le_mul_of_nonneg_left hq ht0.le]
  have hlogHeight := log_height_le_two_target (q := q) hH hHt ht
  have hlogT5 : Real.log (T' + 5) ≤ 2 * W := by
    have harg : T' + 5 ≤ H + 8 := by linarith [hT'.2]
    exact (Real.log_le_log (by linarith [hTpos]) harg).trans hlogHeight
  have hlogT1 : Real.log (T' + 1) ≤ 2 * W := by
    have harg : T' + 1 ≤ H + 8 := by linarith [hT'.2]
    exact (Real.log_le_log (by linarith [hTpos]) harg).trans hlogHeight
  have hleft : ‖endpointVerticalLineIntegral psi t (-(1 / 2 : ℝ)) T'‖ ≤
      (100 + 20 * Cg) * B := by
    have hpi : 3 < Real.pi := Real.pi_gt_three
    have hrawFactor :
        6 * (‖Complex.log (chi.conductor : ℂ)‖ + 24 +
          2 * Cg * Real.log (T' + 5)) / Real.pi ≤
          (50 + 10 * Cg) * W := by
      apply (div_le_iff₀ Real.pi_pos).2
      have hCg0 : 0 ≤ Cg := hCg.le
      have hcglog : 2 * Cg * Real.log (T' + 5) ≤
          4 * Cg * W := by
        nlinarith [mul_le_mul_of_nonneg_left hlogT5 hCg0]
      have hparent : ‖Complex.log (chi.conductor : ℂ)‖ + 24 +
          2 * Cg * Real.log (T' + 5) ≤ (25 + 4 * Cg) * W := by
        nlinarith
      have hmul6 := mul_le_mul_of_nonneg_left hparent (by norm_num : (0 : ℝ) ≤ 6)
      have hpiTerm : (50 + 10 * Cg) * W * Real.pi ≥
          3 * ((50 + 10 * Cg) * W) := by
        let X := (50 + 10 * Cg) * W
        have hX0 : 0 ≤ X := by dsimp [X]; positivity
        have hx : 3 * X ≤ Real.pi * X :=
          mul_le_mul_of_nonneg_right hpi.le hX0
        simpa only [X, mul_comm] using hx
      nlinarith
    calc
      _ ≤ (6 * (‖Complex.log (chi.conductor : ℂ)‖ + 24 +
          2 * Cg * Real.log (T' + 5)) / Real.pi) *
            Real.log (T' + 1) := hleftRaw
      _ ≤ ((50 + 10 * Cg) * W) * (2 * W) :=
        mul_le_mul hrawFactor hlogT1
          (Real.log_nonneg (by linarith [hTpos]))
          (by positivity)
      _ = (100 + 20 * Cg) * W ^ 2 := by ring
      _ ≤ (100 + 20 * Cg) * B :=
        mul_le_mul_of_nonneg_left hWsqB (by positivity)
  have hdelta : 0 < (Real.log t)⁻¹ :=
    inv_pos.mpr (Real.log_pos (by linarith [ht0, exp_two_gt_seven.trans_le ht]))
  have hrightRaw :=
    KoukRightReplacementCorrectionBound.norm_endpointRightReplacementCorrection_le
      psi hdelta hTpos
  have hlogtW : Real.log t ≤ W := by
    exact Real.log_le_log ht0 (by
      have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le (n := q)
      nlinarith [mul_le_mul_of_nonneg_left hq ht0.le])
  have hright : ‖endpointRightReplacementCorrection psi
      (1 + (Real.log t)⁻¹) T'‖ ≤ 20 * B := by
    have hlogt0 : 0 < Real.log t := Real.log_pos (by linarith [exp_two_gt_seven.trans_le ht])
    have hformula :
        (2 / (Real.pi * T')) *
          ((2 / (Real.log t)⁻¹) *
            (1 + (((Real.log t)⁻¹ / 2)⁻¹))) =
          (4 * Real.log t * (1 + 2 * Real.log t)) / (Real.pi * T') := by
      field_simp [hlogt0.ne', Real.pi_ne_zero, hTpos.ne']
      ring
    rw [hformula] at hrightRaw
    calc
      _ ≤ (4 * Real.log t * (1 + 2 * Real.log t)) /
          (Real.pi * T') := hrightRaw
      _ ≤ 20 * W ^ 2 / T' := by
        have hnum : 4 * Real.log t * (1 + 2 * Real.log t) ≤
            20 * W ^ 2 := by nlinarith
        calc
          _ ≤ (20 * W ^ 2) / (Real.pi * T') :=
            div_le_div_of_nonneg_right hnum (mul_pos Real.pi_pos hTpos).le
          _ ≤ (20 * W ^ 2) / T' := by
            apply div_le_div_of_nonneg_left (by positivity) hTpos
            nlinarith [Real.pi_gt_three]
      _ ≤ 20 * B := by
        dsimp [B]
        have ht1 : 1 ≤ t := by linarith [exp_two_gt_seven.trans_le ht]
        calc
          20 * W ^ 2 / T' ≤ 20 * t * W ^ 2 / T' := by
            apply div_le_div_of_nonneg_right _ hTpos.le
            nlinarith [mul_le_mul_of_nonneg_right ht1 (sq_nonneg W)]
          _ = 20 * (t * W ^ 2 / T') := by ring
  have hunit : ‖principalEndpointUnit psi‖ ≤ 1 := by
    classical
    by_cases h : psi = 1 <;> simp [principalEndpointUnit, h]
  have himp := norm_imprimitiveMangoldtCorrection_prefix_le chi ⌊t⌋₊
  have himp' : ‖APFoundation.imprimitiveMangoldtCorrection chi
      (Finset.Icc 1 ⌊t⌋₊)‖ ≤ 2 * B := by
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    have hfloor : (⌊Real.log (⌊t⌋₊ : ℝ) / Real.log 2⌋₊ : ℝ) ≤ 2 * W := by
      have hNt : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0.le
      have hNpos : (0 : ℝ) < ⌊t⌋₊ := by
        exact_mod_cast (show 0 < ⌊t⌋₊ by
          apply Nat.floor_pos.mpr
          linarith [exp_two_gt_seven.trans_le ht])
      have hNone : (1 : ℝ) ≤ ⌊t⌋₊ := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by
          intro hz
          rw [hz] at hNpos
          norm_num at hNpos))
      have hlogN0 : 0 ≤ Real.log (⌊t⌋₊ : ℝ) := Real.log_nonneg hNone
      have hlog2nonneg : 0 ≤ Real.log 2 :=
        Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
      have hfloorle := Nat.floor_le (div_nonneg hlogN0 hlog2nonneg)
      have hfloorlog : (⌊Real.log (⌊t⌋₊ : ℝ) / Real.log 2⌋₊ : ℝ) ≤
          Real.log (⌊t⌋₊ : ℝ) / Real.log 2 := by exact_mod_cast hfloorle
      have hlogN : Real.log (⌊t⌋₊ : ℝ) ≤ Real.log t := by
        exact Real.log_le_log hNpos hNt
      have hquot : Real.log (⌊t⌋₊ : ℝ) / Real.log 2 ≤ 2 * W := by
        apply (div_le_iff₀ (show 0 < Real.log 2 by linarith)).2
        nlinarith [hlogtW]
      exact hfloorlog.trans hquot
    have hlogq : Real.log q ≤ W := by
      dsimp [W]
      apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q))
      have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le (n := q)
      nlinarith [mul_le_mul_of_nonneg_left hq ht0.le]
    calc
      _ ≤ (⌊Real.log (⌊t⌋₊ : ℝ) / Real.log 2⌋₊ : ℝ) * Real.log q := himp
      _ ≤ (2 * W) * W :=
        mul_le_mul hfloor hlogq (Real.log_natCast_nonneg q) (by positivity)
      _ = 2 * W ^ 2 := by ring
      _ ≤ 2 * B := mul_le_mul_of_nonneg_left hWsqB (by norm_num)
  have hnonzero := horizontal_regularized_nonzero_of_goodHeight
    psi hprim (c := 1 + (Real.log t)⁻¹) hH hT' (by
      have hlogt : 0 < Real.log t := Real.log_pos (by linarith [exp_two_gt_seven.trans_le ht])
      have hlogt2 : 2 ≤ Real.log t :=
        (Real.le_log_iff_exp_le ht0).2 ht
      have hinv0 := (inv_le_inv₀ hlogt (by norm_num : (0 : ℝ) < 2)).2 hlogt2
      have hinv : (Real.log t)⁻¹ ≤ (1 / 2 : ℝ) := by
        norm_num at hinv0 ⊢
        exact hinv0
      linarith) hclear
  have hbottom : ∀ r ∈ Set.Icc
      (KoukNegativeHalfPlaneNonvanishing.negativeHalfIntegerEdge 0)
        (1 + (Real.log t)⁻¹),
      regularizedLFunction chi.primitiveCharacter
        ((r : ℂ) + ((-T' : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    simpa [psi, KoukNegativeHalfPlaneNonvanishing.negativeHalfIntegerEdge]
      using hnonzero.1
  have htop : ∀ r ∈ Set.Icc
      (KoukNegativeHalfPlaneNonvanishing.negativeHalfIntegerEdge 0)
        (1 + (Real.log t)⁻¹),
      regularizedLFunction chi.primitiveCharacter
        ((r : ℂ) + (T' : ℂ) * Complex.I) ≠ 0 := by
    simpa [psi, KoukNegativeHalfPlaneNonvanishing.negativeHalfIntegerEdge]
      using hnonzero.2
  have heq := ambientSelectedRealEndpointRemainder_eq_fullSupportResidual
    chi (t := t) (c := 1 + (Real.log t)⁻¹) (T := T') ht0 (by
      exact lt_add_of_pos_right 1
        (inv_pos.mpr (Real.log_pos (by linarith [exp_two_gt_seven.trans_le ht]))))
      hTpos hbottom htop
  refine ⟨T', hT', ?_⟩
  change ‖APExplicitFormulaMajorantAdapter.ambientTwistedPsi chi t -
      (APExplicitFormulaMajorantAdapter.principalCoefficient chi * t -
        MAPEndpointRegularizedZeroPrimitive.endpointMultiplicityWeightedZeroTerm
          chi.primitiveCharacter 0 T' t)‖ ≤ _
  rw [← heq]
  have hcomp := norm_ambientSelectedRealEndpointRemainder_le_components
    chi (t := t) (c := 1 + (Real.log t)⁻¹) (T := T')
  exact hcomp.trans (by
    calc
      _ ≤ CP * B + (100 + 20 * Cg) * B + 4 * CH * B +
          20 * B + 1 + 2 * B := by gcongr
      _ ≤ (CP + 4 * CH + 200 + 20 * Cg) * B := by
        have hB1 : 1 ≤ B := hWsqB.trans' (by nlinarith [hW1])
        nlinarith
      _ = _ := by ring)


private theorem selected_good_height_principal
    (CP CH Cg : ℝ) (hCP : 0 < CP) (hCH : 0 < CH) (hCg : 0 < Cg)
    (hDigamma : ∀ z : ℂ,
      (∀ m : ℕ, (1 / 4 : ℝ) ≤ ‖z + (m : ℂ)‖) →
      ‖Complex.digamma z‖ ≤ Cg * Real.log (‖z‖ + 2))
    (hPerron : ∀ (q : ℕ) [NeZero q]
      (psi : DirichletCharacter ℂ q) (t T : ℝ),
      Real.exp 2 ≤ t → 2 ≤ T → T ≤ t →
        ‖realEndpointPerronError psi t (1 + (Real.log t)⁻¹) T‖ ≤
          CP * t * (Real.log (t + 2)) ^ 2 / T)
    (hHorizontal : ∀ H x : ℝ, 4 ≤ H → Real.exp 2 ≤ x →
        ∃ T ∈ Set.Ioo H (H + 1),
          (∀ a ∈ exerciseLocalImagCoordinates
              (1 : DirichletCharacter ℂ 1) H,
            exerciseHorizontalClearance
              (1 : DirichletCharacter ℂ 1) H ≤ |T - a|) ∧
          ‖endpointHorizontalBoundaryIntegral
              (1 : DirichletCharacter ℂ 1) x (-(1 / 2 : ℝ))
              (1 + (Real.log x)⁻¹) T‖ ≤
            CH * x * (Real.log (H + 8)) ^ 2 / T)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {H t : ℝ} (hH : 4 ≤ H) (hHt : H + 1 ≤ t)
    (ht : Real.exp 2 ≤ t)
    (hpsi : chi.primitiveCharacter = 1) :
    ∃ T' ∈ Set.Ioo H (H + 1),
      ‖MAPKoukTheorem113ToCorrectedTail.fullSupportEndpointResidual chi T' t‖ ≤
        (CP + 4 * CH + 200 + 20 * Cg) *
          (t * (Real.log (t * (q : ℝ) + 2)) ^ 2 / T') := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let psi := chi.primitiveCharacter
  have hprim : psi.IsPrimitive := chi.primitiveCharacter_isPrimitive
  obtain ⟨T', hT', hclear, hhorizontal⟩ :=
    principal_horizontal_of_eq_one hHorizontal psi hprim hpsi hH ht
  let W := Real.log (t * (q : ℝ) + 2)
  let B := t * W ^ 2 / T'
  have ht0 : 0 < t := (Real.exp_pos 2).trans_le ht
  have hTpos : 0 < T' := by linarith [hH, hT'.1]
  have hTtwo : 2 ≤ T' := by linarith [hH, hT'.1]
  have hTt : T' ≤ t := hT'.2.le.trans hHt
  have hW1 : 1 ≤ W := by
    dsimp [W]
    exact target_log_ge_one ht
  have hW0 : 0 ≤ W := zero_le_one.trans hW1
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hWsqB : W ^ 2 ≤ B := by
    have hratio : 1 ≤ t / T' := by
      apply (le_div_iff₀ hTpos).2
      simpa using hTt
    calc
      W ^ 2 ≤ (t / T') * W ^ 2 :=
        (le_mul_iff_one_le_left (sq_pos_of_pos (zero_lt_one.trans_le hW1))).2 hratio
      _ = B := by dsimp [B]; ring
  have hp := hPerron chi.conductor psi t T' ht hTtwo hTt
  have hlogt : Real.log (t + 2) ≤ W := by
    dsimp [W]
    exact log_t_add_two_le_target ht0.le
  have hperron : ‖realEndpointPerronError psi t
      (1 + (Real.log t)⁻¹) T'‖ ≤ CP * B := by
    calc
      _ ≤ CP * t * (Real.log (t + 2)) ^ 2 / T' := hp
      _ ≤ CP * t * W ^ 2 / T' := by
        apply div_le_div_of_nonneg_right _ hTpos.le
        gcongr
        exact Real.log_nonneg (by linarith [ht0])
      _ = CP * B := by dsimp [B]; ring
  have hscale := log_height_le_two_target (q := q) hH hHt ht
  have hscaleLog0 : 0 ≤ Real.log (H + 8) := by
    exact Real.log_nonneg (by linarith [hH])
  have hhorizontal' : ‖endpointHorizontalBoundaryIntegral psi t
      (-(1 / 2 : ℝ)) (1 + (Real.log t)⁻¹) T'‖ ≤ 4 * CH * B := by
    calc
      _ ≤ CH * t * (Real.log (H + 8)) ^ 2 / T' := hhorizontal
      _ ≤ CH * t * (2 * W) ^ 2 / T' := by
        apply div_le_div_of_nonneg_right _ hTpos.le
        gcongr
      _ = 4 * CH * B := by dsimp [B]; ring
  have hleftRaw :=
    KoukNegativeHalfLogDerivativeBound.norm_endpointVerticalLineIntegral_negativeHalf_le_fixed
      Cg hCg hDigamma psi hprim (show 1 ≤ t by linarith) hTpos.le
  have hlogcond : ‖Complex.log (chi.conductor : ℂ)‖ ≤ W := by
    rw [← Complex.natCast_log, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_natCast_nonneg chi.conductor)]
    apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero chi.conductor_ne_zero
    · have hcondNat : chi.conductor ≤ q :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) chi.conductor_dvd_level
      have hcond : (chi.conductor : ℝ) ≤ q := by exact_mod_cast hcondNat
      have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le (n := q)
      nlinarith [mul_le_mul_of_nonneg_left hq ht0.le]
  have hlogHeight := log_height_le_two_target (q := q) hH hHt ht
  have hlogT5 : Real.log (T' + 5) ≤ 2 * W := by
    have harg : T' + 5 ≤ H + 8 := by linarith [hT'.2]
    exact (Real.log_le_log (by linarith [hTpos]) harg).trans hlogHeight
  have hlogT1 : Real.log (T' + 1) ≤ 2 * W := by
    have harg : T' + 1 ≤ H + 8 := by linarith [hT'.2]
    exact (Real.log_le_log (by linarith [hTpos]) harg).trans hlogHeight
  have hleft : ‖endpointVerticalLineIntegral psi t (-(1 / 2 : ℝ)) T'‖ ≤
      (100 + 20 * Cg) * B := by
    have hpi : 3 < Real.pi := Real.pi_gt_three
    have hrawFactor :
        6 * (‖Complex.log (chi.conductor : ℂ)‖ + 24 +
          2 * Cg * Real.log (T' + 5)) / Real.pi ≤
          (50 + 10 * Cg) * W := by
      apply (div_le_iff₀ Real.pi_pos).2
      have hCg0 : 0 ≤ Cg := hCg.le
      have hcglog : 2 * Cg * Real.log (T' + 5) ≤
          4 * Cg * W := by
        nlinarith [mul_le_mul_of_nonneg_left hlogT5 hCg0]
      have hparent : ‖Complex.log (chi.conductor : ℂ)‖ + 24 +
          2 * Cg * Real.log (T' + 5) ≤ (25 + 4 * Cg) * W := by
        nlinarith
      have hmul6 := mul_le_mul_of_nonneg_left hparent (by norm_num : (0 : ℝ) ≤ 6)
      have hpiTerm : (50 + 10 * Cg) * W * Real.pi ≥
          3 * ((50 + 10 * Cg) * W) := by
        let X := (50 + 10 * Cg) * W
        have hX0 : 0 ≤ X := by dsimp [X]; positivity
        have hx : 3 * X ≤ Real.pi * X :=
          mul_le_mul_of_nonneg_right hpi.le hX0
        simpa only [X, mul_comm] using hx
      nlinarith
    calc
      _ ≤ (6 * (‖Complex.log (chi.conductor : ℂ)‖ + 24 +
          2 * Cg * Real.log (T' + 5)) / Real.pi) *
            Real.log (T' + 1) := hleftRaw
      _ ≤ ((50 + 10 * Cg) * W) * (2 * W) :=
        mul_le_mul hrawFactor hlogT1
          (Real.log_nonneg (by linarith [hTpos]))
          (by positivity)
      _ = (100 + 20 * Cg) * W ^ 2 := by ring
      _ ≤ (100 + 20 * Cg) * B :=
        mul_le_mul_of_nonneg_left hWsqB (by positivity)
  have hdelta : 0 < (Real.log t)⁻¹ :=
    inv_pos.mpr (Real.log_pos (by linarith [ht0, exp_two_gt_seven.trans_le ht]))
  have hrightRaw :=
    KoukRightReplacementCorrectionBound.norm_endpointRightReplacementCorrection_le
      psi hdelta hTpos
  have hlogtW : Real.log t ≤ W := by
    exact Real.log_le_log ht0 (by
      have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le (n := q)
      nlinarith [mul_le_mul_of_nonneg_left hq ht0.le])
  have hright : ‖endpointRightReplacementCorrection psi
      (1 + (Real.log t)⁻¹) T'‖ ≤ 20 * B := by
    have hlogt0 : 0 < Real.log t := Real.log_pos (by linarith [exp_two_gt_seven.trans_le ht])
    have hformula :
        (2 / (Real.pi * T')) *
          ((2 / (Real.log t)⁻¹) *
            (1 + (((Real.log t)⁻¹ / 2)⁻¹))) =
          (4 * Real.log t * (1 + 2 * Real.log t)) / (Real.pi * T') := by
      field_simp [hlogt0.ne', Real.pi_ne_zero, hTpos.ne']
      ring
    rw [hformula] at hrightRaw
    calc
      _ ≤ (4 * Real.log t * (1 + 2 * Real.log t)) /
          (Real.pi * T') := hrightRaw
      _ ≤ 20 * W ^ 2 / T' := by
        have hnum : 4 * Real.log t * (1 + 2 * Real.log t) ≤
            20 * W ^ 2 := by nlinarith
        calc
          _ ≤ (20 * W ^ 2) / (Real.pi * T') :=
            div_le_div_of_nonneg_right hnum (mul_pos Real.pi_pos hTpos).le
          _ ≤ (20 * W ^ 2) / T' := by
            apply div_le_div_of_nonneg_left (by positivity) hTpos
            nlinarith [Real.pi_gt_three]
      _ ≤ 20 * B := by
        dsimp [B]
        have ht1 : 1 ≤ t := by linarith [exp_two_gt_seven.trans_le ht]
        calc
          20 * W ^ 2 / T' ≤ 20 * t * W ^ 2 / T' := by
            apply div_le_div_of_nonneg_right _ hTpos.le
            nlinarith [mul_le_mul_of_nonneg_right ht1 (sq_nonneg W)]
          _ = 20 * (t * W ^ 2 / T') := by ring
  have hunit : ‖principalEndpointUnit psi‖ ≤ 1 := by
    classical
    by_cases h : psi = 1 <;> simp [principalEndpointUnit, h]
  have himp := norm_imprimitiveMangoldtCorrection_prefix_le chi ⌊t⌋₊
  have himp' : ‖APFoundation.imprimitiveMangoldtCorrection chi
      (Finset.Icc 1 ⌊t⌋₊)‖ ≤ 2 * B := by
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    have hfloor : (⌊Real.log (⌊t⌋₊ : ℝ) / Real.log 2⌋₊ : ℝ) ≤ 2 * W := by
      have hNt : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0.le
      have hNpos : (0 : ℝ) < ⌊t⌋₊ := by
        exact_mod_cast (show 0 < ⌊t⌋₊ by
          apply Nat.floor_pos.mpr
          linarith [exp_two_gt_seven.trans_le ht])
      have hNone : (1 : ℝ) ≤ ⌊t⌋₊ := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by
          intro hz
          rw [hz] at hNpos
          norm_num at hNpos))
      have hlogN0 : 0 ≤ Real.log (⌊t⌋₊ : ℝ) := Real.log_nonneg hNone
      have hlog2nonneg : 0 ≤ Real.log 2 :=
        Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
      have hfloorle := Nat.floor_le (div_nonneg hlogN0 hlog2nonneg)
      have hfloorlog : (⌊Real.log (⌊t⌋₊ : ℝ) / Real.log 2⌋₊ : ℝ) ≤
          Real.log (⌊t⌋₊ : ℝ) / Real.log 2 := by exact_mod_cast hfloorle
      have hlogN : Real.log (⌊t⌋₊ : ℝ) ≤ Real.log t := by
        exact Real.log_le_log hNpos hNt
      have hquot : Real.log (⌊t⌋₊ : ℝ) / Real.log 2 ≤ 2 * W := by
        apply (div_le_iff₀ (show 0 < Real.log 2 by linarith)).2
        nlinarith [hlogtW]
      exact hfloorlog.trans hquot
    have hlogq : Real.log q ≤ W := by
      dsimp [W]
      apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q))
      have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le (n := q)
      nlinarith [mul_le_mul_of_nonneg_left hq ht0.le]
    calc
      _ ≤ (⌊Real.log (⌊t⌋₊ : ℝ) / Real.log 2⌋₊ : ℝ) * Real.log q := himp
      _ ≤ (2 * W) * W :=
        mul_le_mul hfloor hlogq (Real.log_natCast_nonneg q) (by positivity)
      _ = 2 * W ^ 2 := by ring
      _ ≤ 2 * B := mul_le_mul_of_nonneg_left hWsqB (by norm_num)
  have hnonzero := horizontal_regularized_nonzero_of_goodHeight
    psi hprim (c := 1 + (Real.log t)⁻¹) hH hT' (by
      have hlogt : 0 < Real.log t := Real.log_pos (by linarith [exp_two_gt_seven.trans_le ht])
      have hlogt2 : 2 ≤ Real.log t :=
        (Real.le_log_iff_exp_le ht0).2 ht
      have hinv0 := (inv_le_inv₀ hlogt (by norm_num : (0 : ℝ) < 2)).2 hlogt2
      have hinv : (Real.log t)⁻¹ ≤ (1 / 2 : ℝ) := by
        norm_num at hinv0 ⊢
        exact hinv0
      linarith) hclear
  have hbottom : ∀ r ∈ Set.Icc
      (KoukNegativeHalfPlaneNonvanishing.negativeHalfIntegerEdge 0)
        (1 + (Real.log t)⁻¹),
      regularizedLFunction chi.primitiveCharacter
        ((r : ℂ) + ((-T' : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    simpa [psi, KoukNegativeHalfPlaneNonvanishing.negativeHalfIntegerEdge]
      using hnonzero.1
  have htop : ∀ r ∈ Set.Icc
      (KoukNegativeHalfPlaneNonvanishing.negativeHalfIntegerEdge 0)
        (1 + (Real.log t)⁻¹),
      regularizedLFunction chi.primitiveCharacter
        ((r : ℂ) + (T' : ℂ) * Complex.I) ≠ 0 := by
    simpa [psi, KoukNegativeHalfPlaneNonvanishing.negativeHalfIntegerEdge]
      using hnonzero.2
  have heq := ambientSelectedRealEndpointRemainder_eq_fullSupportResidual
    chi (t := t) (c := 1 + (Real.log t)⁻¹) (T := T') ht0 (by
      exact lt_add_of_pos_right 1
        (inv_pos.mpr (Real.log_pos (by linarith [exp_two_gt_seven.trans_le ht]))))
      hTpos hbottom htop
  refine ⟨T', hT', ?_⟩
  change ‖APExplicitFormulaMajorantAdapter.ambientTwistedPsi chi t -
      (APExplicitFormulaMajorantAdapter.principalCoefficient chi * t -
        MAPEndpointRegularizedZeroPrimitive.endpointMultiplicityWeightedZeroTerm
          chi.primitiveCharacter 0 T' t)‖ ≤ _
  rw [← heq]
  have hcomp := norm_ambientSelectedRealEndpointRemainder_le_components
    chi (t := t) (c := 1 + (Real.log t)⁻¹) (T := T')
  exact hcomp.trans (by
    calc
      _ ≤ CP * B + (100 + 20 * Cg) * B + 4 * CH * B +
          20 * B + 1 + 2 * B := by gcongr
      _ ≤ (CP + 4 * CH + 200 + 20 * Cg) * B := by
        have hB1 : 1 ≤ B := hWsqB.trans' (by nlinarith [hW1])
        nlinarith
      _ = _ := by ring)

/-- The complete source-facing Koukoulopoulos endpoint estimate in the range
used by MAP.  A nearby per-character good height is selected, all six exact
contour corrections are aggregated there, and the complete primitive zero
cutoff is then transported back to the requested height. -/
theorem certifiedKoukTheorem113MAPRangePointwise :
    KoukTheorem113MAPRangePointwise := by
  obtain ⟨CP, hCP, hPerron⟩ :=
    KoukUniformRealEndpointPerronBound.uniformRealEndpointPerronBound
  obtain ⟨CHn, hCHn, hHorizontalNonprincipal⟩ :=
    KoukTheorem113GoodHeightHorizontalBound.uniform_goodHeight_horizontal_nonprincipal
  obtain ⟨CHp, hCHp, hHorizontalPrincipal⟩ :=
    KoukTheorem113GoodHeightHorizontalBound.uniform_goodHeight_horizontal_principal
  obtain ⟨Cg, hCg, hDigamma⟩ :=
    KoukGaussDigammaSeries.awayFromPolesDigammaLogBound
  let C := CP + 4 * CHn + 4 * CHp + 30000 + 40 * Cg
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro q _inst chi T t hT hTt ht
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let psi := chi.primitiveCharacter
  have hprim : psi.IsPrimitive := chi.primitiveCharacter_isPrimitive
  let W := Real.log (t * (q : ℝ) + 2)
  let B := t * W ^ 2 / T
  have ht0 : 0 < t := (Real.exp_pos 2).trans_le ht
  have hTpos : 0 < T := by linarith
  have hTtwo : 2 ≤ T := by linarith
  have hW1 : 1 ≤ W := by
    dsimp [W]
    exact target_log_ge_one ht
  have hW0 : 0 ≤ W := zero_le_one.trans hW1
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hlogt : Real.log (t + 2) ≤ W := by
    dsimp [W]
    exact log_t_add_two_le_target ht0.le
  have hWleSq : W ≤ W ^ 2 := by nlinarith
  change ‖APExplicitFormulaMajorantAdapter.ambientTwistedPsi chi t -
      (APExplicitFormulaMajorantAdapter.principalCoefficient chi * t -
        MAPEndpointRegularizedZeroPrimitive.endpointMultiplicityWeightedZeroTerm
          chi.primitiveCharacter 0 T t)‖ ≤ C * t * W ^ 2 / T
  by_cases hpsi : psi = 1
  · obtain ⟨T', hT', hgood⟩ := selected_good_height_principal
      CP CHp Cg hCP hCHp hCg hDigamma hPerron hHorizontalPrincipal
      chi hT hTt ht (by simpa only [psi] using hpsi)
    let Kp := CP + 4 * CHp + 200 + 20 * Cg
    let E := Kp * (t * W ^ 2 / T')
    have hT'pos : 0 < T' := by linarith [hT, hT'.1]
    have hTT' : T ≤ T' := hT'.1.le
    have hT'le : T' ≤ T + 1 := hT'.2.le
    have hE0 : 0 ≤ E := by dsimp [E, Kp]; positivity
    change ‖APExplicitFormulaMajorantAdapter.ambientTwistedPsi chi t -
        (APExplicitFormulaMajorantAdapter.principalCoefficient chi * t -
          MAPEndpointRegularizedZeroPrimitive.endpointMultiplicityWeightedZeroTerm
            chi.primitiveCharacter 0 T' t)‖ ≤ E at hgood
    have htransport :=
      norm_residual_at_requestedCutoff_principal_of_eq_one
        psi hprim hpsi (T := T) (T' := T') (t := t) (E := E)
        hTtwo hTT' hT'le (by linarith) hE0
        (A := APExplicitFormulaMajorantAdapter.ambientTwistedPsi chi t)
        (P := APExplicitFormulaMajorantAdapter.principalCoefficient chi * t)
        (by simpa only [psi] using hgood)
    have hselected : E ≤ Kp * B := by
      dsimp [E, B]
      apply mul_le_mul_of_nonneg_left _ (by dsimp [Kp]; positivity)
      exact div_le_div_of_nonneg_left (mul_nonneg ht0.le (sq_nonneg W))
        hTpos hTT'
    have hband : 13464 * t * Real.log (t + 2) / T ≤ 13464 * B := by
      calc
        _ ≤ 13464 * t * W ^ 2 / T := by
          apply div_le_div_of_nonneg_right _ hTpos.le
          nlinarith [mul_le_mul_of_nonneg_left hlogt ht0.le,
            mul_le_mul_of_nonneg_left hWleSq ht0.le]
        _ = 13464 * B := by dsimp [B]; ring
    calc
      _ ≤ E + 13464 * t * Real.log (t + 2) / T := by
        simpa only [psi] using htransport
      _ ≤ Kp * B + 13464 * B := add_le_add hselected hband
      _ ≤ C * B := by
        rw [← add_mul]
        apply mul_le_mul_of_nonneg_right _ hB0
        dsimp [Kp, C]
        nlinarith [hCHn, hCg]
      _ = C * t * W ^ 2 / T := by dsimp [B]; ring
  · obtain ⟨T', hT', hgood⟩ := selected_good_height_nonprincipal
      CP CHn Cg hCP hCHn hCg hDigamma hPerron hHorizontalNonprincipal
      chi hT hTt ht (by simpa only [psi] using hpsi)
    let Kn := CP + 4 * CHn + 200 + 20 * Cg
    let E := Kn * (t * W ^ 2 / T')
    have hT'pos : 0 < T' := by linarith [hT, hT'.1]
    have hTT' : T ≤ T' := hT'.1.le
    have hT'le : T' ≤ T + 1 := hT'.2.le
    have hE0 : 0 ≤ E := by dsimp [E, Kn]; positivity
    change ‖APExplicitFormulaMajorantAdapter.ambientTwistedPsi chi t -
        (APExplicitFormulaMajorantAdapter.principalCoefficient chi * t -
          MAPEndpointRegularizedZeroPrimitive.endpointMultiplicityWeightedZeroTerm
            chi.primitiveCharacter 0 T' t)‖ ≤ E at hgood
    have htransport :=
      KoukTheorem113ZeroCutoffTransport.norm_residual_at_requestedCutoff_nonprincipal_le
        psi hprim hpsi (T := T) (T' := T') (t := t) (E := E)
        hTtwo hTT' hT'le (by linarith) hE0
        (A := APExplicitFormulaMajorantAdapter.ambientTwistedPsi chi t)
        (P := APExplicitFormulaMajorantAdapter.principalCoefficient chi * t)
        (by simpa only [psi] using hgood)
    have hselected : E ≤ Kn * B := by
      dsimp [E, B]
      apply mul_le_mul_of_nonneg_left _ (by dsimp [Kn]; positivity)
      exact div_le_div_of_nonneg_left (mul_nonneg ht0.le (sq_nonneg W))
        hTpos hTT'
    have hcondNat : chi.conductor ≤ q :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) chi.conductor_dvd_level
    have hcond : (chi.conductor : ℝ) ≤ q := by exact_mod_cast hcondNat
    have hlogcond : Real.log (t * (chi.conductor : ℝ) + 2) ≤ W := by
      dsimp [W]
      apply Real.log_le_log (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left hcond ht0.le]
    have hband : 2456 * t * Real.log (t * (chi.conductor : ℝ) + 2) / T ≤
        2456 * B := by
      calc
        _ ≤ 2456 * t * W ^ 2 / T := by
          apply div_le_div_of_nonneg_right _ hTpos.le
          nlinarith [mul_le_mul_of_nonneg_left hlogcond ht0.le,
            mul_le_mul_of_nonneg_left hWleSq ht0.le]
        _ = 2456 * B := by dsimp [B]; ring
    calc
      _ ≤ E + 2456 * t * Real.log (t * (chi.conductor : ℝ) + 2) / T := by
        simpa only [psi] using htransport
      _ ≤ Kn * B + 2456 * B := add_le_add hselected hband
      _ ≤ C * B := by
        rw [← add_mul]
        apply mul_le_mul_of_nonneg_right _ hB0
        dsimp [Kn, C]
        nlinarith [hCHp, hCg]
      _ = C * t * W ^ 2 / T := by dsimp [B]; ring

#print axioms regularizedLFunction_ne_zero_of_directWideClearance
#print axioms horizontal_regularized_nonzero_of_goodHeight
#print axioms norm_ambientSelectedRealEndpointRemainder_le_components
#print axioms certifiedKoukTheorem113MAPRangePointwise

end
end KoukTheorem113SelectedHeightAggregation
