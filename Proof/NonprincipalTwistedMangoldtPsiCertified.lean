import NonprincipalKoukSiegelFormula
import KoukExercise12TwoLocalContourRBounds
import KoukExercise12TwoFinalScalarTrades
import WeakVKNearDecay
import PrimitiveTwistedMangoldtSourceSplit

/-! Final scalar collapse for primitive nonprincipal characters. -/

namespace MAPNonprincipalTwistedMangoldtPsiCertified

open Filter Set DirichletZeros
open PrimitiveTruncatedExplicitFormulaBridge PaperEdgePrimitiveComponents
open MAPKoukExercise12TwoContourAperture
open MAPKoukExercise12TwoLocalHorizontalAperture
open MAPKoukExercise12TwoZeroSum

noncomputable section

theorem primitiveNonprincipalTwistedMangoldtPsi :
    MAPPrimitiveTwistedMangoldtSourceSplit.PrimitiveNonprincipalTwistedMangoldtPsi := by
  intro A B
  let D : ℕ := A + B + 10
  let p : ℕ := B + 3 * D
  let c : ℝ := 1 /
    (100000000000 * (((B + D : ℕ) : ℝ) + Real.log 4))
  let K : ℝ := (((B + D : ℕ) : ℝ) + 4)
  let Cinv : ℝ := 40000016
  let Ch : ℝ := 28 * (1 + 306 * K)
  let CLeft : ℝ := 20 * 21599 + 5560 * K + 5520 * K * Cinv
  let CHorizontal : ℝ := 20 * 21599 + 5560 * K + 5520 * K * Ch
  let CCorner : ℝ := 20 * 21599 + 5560 * K + 5520 * K * (Cinv + Ch)
  let CZero : ℝ := 3 * 5000000 * Cinv
  let CExceptional : ℝ := 6 * Cinv
  let CTotal : ℝ := 1 + CZero + CExceptional +
    2 * CLeft * Cinv + 2 * CCorner + 18 * CHorizontal + 3000 + 9000
  have hc : 0 < c := by
    dsimp [c]
    have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    positivity
  have hCTotal : 0 < CTotal := by
    dsimp [CTotal, CZero, CExceptional, CLeft, CCorner, CHorizontal,
      Cinv, Ch, K]
    positivity
  have hCLeft0 : 0 ≤ CLeft := by
    dsimp [CLeft, Cinv, K]
    positivity
  have hCHorizontal0 : 0 ≤ CHorizontal := by
    dsimp [CHorizontal, Ch, K]
    positivity
  have hCCorner0 : 0 ≤ CCorner := by
    dsimp [CCorner, Cinv, Ch, K]
    positivity
  have hformula :=
    MAPNonprincipalKoukSiegelFormula.exists_eventually_nonprincipal_formula B D A
  have hdecay := WeakVKNear.weakGap_nearFactor_beats_polylog
    (1 / 4 : ℝ) c ((2 * p : ℕ) : ℝ) (A : ℝ)
    (by norm_num) hc (by positivity) (by positivity)
  have hpolyLarge := SupportBoundaryQuantitative.polylog_absorption
    ((D + 2 * p + 1 + A : ℕ) : ℝ) (1 / 4 : ℝ) (by norm_num)
  have hpolyTarget := SupportBoundaryQuantitative.polylog_absorption
    (A : ℝ) 1 (by norm_num)
  have hall : ∀ᶠ X : ℝ in atTop,
      ∀ (q : ℕ), 1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B →
      ∀ chi : DirichletCharacter ℂ q, chi.IsPrimitive → chi ≠ 1 →
      ∀ t : ℝ, t ∈ Set.Icc X (2 * X) →
        ‖APFoundation.twistedMangoldtSum chi (Finset.Icc 1 ⌊t⌋₊) -
            MAPSiegelWalfiszCharacterReduction.characterMain chi t‖ ≤
          CTotal * X / (Real.log X) ^ A := by
    filter_upwards [hformula, hdecay, hpolyLarge, hpolyTarget,
        eventually_ge_atTop (Real.exp 2), eventually_ge_atTop 9] with
        X hformulaX hdecayX hpolyLargeX hpolyTargetX hXexp hX9
    intro q hqNat hq chi hprim hchi t ht
    letI : NeZero q := ⟨Nat.ne_of_gt hqNat⟩
    have hXpos : 0 < X := (Real.exp_pos 2).trans_le hXexp
    have hlogTwo : 2 ≤ Real.log X := by
      rw [Real.le_log_iff_exp_le hXpos]
      exact hXexp
    have hlogOne : 1 ≤ Real.log X := by linarith
    have hlogPos : 0 < Real.log X := zero_lt_one.trans_le hlogOne
    have hRange := MAPKoukExercise12TwoEndpointScalars.halfIntegerPoint_floor_range
      (by linarith : 2 ≤ X) ht
    obtain ⟨hN, hxLower, hxUpper, hNX⟩ := hRange
    obtain ⟨sigma, hsigma, T, hT, hpoint⟩ :=
      hformulaX q hq chi hprim hchi t ht
    dsimp only at hpoint
    have hTpos : 0 < T := by
      exact (pow_pos hlogPos D).trans hT.1
    have hlogPowOne : 1 ≤ (Real.log X) ^ D := one_le_pow₀ hlogOne
    have hqReal : (1 : ℝ) ≤ q := by exact_mod_cast hqNat
    have hscale : 0 ≤ Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) := by
      apply Real.log_nonneg
      nlinarith
    have hRealClearPos :
        0 < exerciseRealClearance chi ((Real.log X) ^ D) :=
      exerciseRealClearance_pos chi ((Real.log X) ^ D)
    have hHorizontalClearPos :
        0 < exerciseHorizontalClearance chi ((Real.log X) ^ D) :=
      exerciseHorizontalClearance_pos chi ((Real.log X) ^ D)
    have hCornerClearPos : 0 <
        min (exerciseRealClearance chi ((Real.log X) ^ D))
          (exerciseHorizontalClearance chi ((Real.log X) ^ D)) :=
      lt_min hRealClearPos hHorizontalClearPos
    have hGap : c * Real.rpow (Real.log X) (-(1 / 4 : ℝ)) ≤
        exercise12TwoGap q T := by simpa only [c] using hpoint.2.1
    have hGap0 : 0 ≤ exercise12TwoGap q T :=
      (exercise12TwoGap_pos (q := q) (T := T) hTpos.le).le
    have hWeakFactor :=
      MAPKoukExercise12TwoEndpointScalars.halfIntegerPoint_rpow_one_sub_le_weakFactor
        (by linarith : 4 ≤ X) ht hGap0
    have hdecayGap := hdecayX (exercise12TwoGap q T) hGap
    have hInv :=
      MAPKoukExercise12TwoLocalPolylogScalars.inv_exerciseRealClearance_polylogHeight_le
        B D hlogTwo chi hprim hq
    have hInvSigma : sigma⁻¹ ≤ Cinv * (Real.log X) ^ p := by
      have hinvds : sigma⁻¹ ≤
          (exerciseRealClearance chi ((Real.log X) ^ D))⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le
          (exerciseRealClearance_pos chi ((Real.log X) ^ D)) hpoint.1
      exact hinvds.trans (by simpa only [Cinv, p] using hInv)
    have hCountMono := MAPMellinDetectorLeaf.dirichletZeroCount_mono chi
      (show (0 : ℝ) ≤ sigma from hsigma.1.le)
      (show T ≤ (Real.log X) ^ D + 4 by linarith [hT.2])
    have hCountBase :=
      MAPKoukExercise12TwoPolylogScalars.dirichletZeroCount_polylogHeight_le
        B D hlogTwo chi hprim hq
    have hCount : (dirichletZeroCount chi sigma T : ℝ) ≤
        5000000 * (Real.log X) ^ p := by
      have hCountMonoReal : (dirichletZeroCount chi sigma T : ℝ) ≤
          (dirichletZeroCount chi 0 ((Real.log X) ^ D + 4) : ℝ) := by
        exact_mod_cast hCountMono
      exact hCountMonoReal.trans (by simpa only [p] using hCountBase)
    have hZeroTerm :
        ((dirichletZeroCount chi sigma T : ℝ) / sigma) *
            Real.rpow (halfIntegerPoint ⌊t⌋₊)
              (1 - exercise12TwoGap q T) ≤
          CZero * (X / (Real.log X) ^ A) := by
      have hraw :
          ((dirichletZeroCount chi sigma T : ℝ) / sigma) *
              Real.rpow (halfIntegerPoint ⌊t⌋₊)
                (1 - exercise12TwoGap q T) ≤
            CZero * X *
              ((Real.log X) ^ (2 * p) *
                Real.rpow X (-(exercise12TwoGap q T / 12))) := by
        rw [div_eq_mul_inv]
        dsimp [CZero, Cinv]
        calc
          ((dirichletZeroCount chi sigma T : ℝ) * sigma⁻¹) *
              Real.rpow (halfIntegerPoint ⌊t⌋₊)
                (1 - exercise12TwoGap q T) ≤
            (5000000 * (Real.log X) ^ p) *
              (40000016 * (Real.log X) ^ p) *
                (3 * X * Real.rpow X (-(exercise12TwoGap q T / 12))) := by
              gcongr
              · exact Real.rpow_nonneg (halfIntegerPoint_pos _).le _
              · exact inv_nonneg.mpr hsigma.1.le
          _ = (3 * 5000000 * 40000016) * X *
              ((Real.log X) ^ (2 * p) *
                Real.rpow X (-(exercise12TwoGap q T / 12))) := by
              rw [show 2 * p = p + p by omega, pow_add]
              ring
      calc
        _ ≤ CZero * X *
            ((Real.log X) ^ (2 * p) *
              Real.rpow X (-(exercise12TwoGap q T / 12))) := hraw
        _ ≤ CZero * X * Real.rpow (Real.log X) (-(A : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [← Real.rpow_natCast]
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using! hdecayGap
        _ = CZero * (X / (Real.log X) ^ A) := by
          rw [MAPKoukExercise12TwoFinalScalarTrades.rpow_neg_nat_eq_one_div_pow hlogPos]
          ring
    have hRLeft := MAPKoukExercise12TwoLocalContourRBounds.realContourR_le
      B D hlogTwo chi hprim hq
    have hRHorizontal :=
      MAPKoukExercise12TwoLocalContourRBounds.horizontalContourR_le
        B D hlogTwo chi hprim hchi hq
    have hRCorner := MAPKoukExercise12TwoLocalContourRBounds.cornerContourR_le
      B D (by dsimp [D]; omega) hlogTwo chi hprim hchi hq
    have hRLeft0 : 0 ≤
        20 * (Real.log 21600 +
            2 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))) +
          5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) +
          5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) /
            exerciseRealClearance chi ((Real.log X) ^ D) := by positivity
    have hRHorizontal0 : 0 ≤
        20 * (Real.log 21600 +
            2 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))) +
          5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) +
          5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) /
            exerciseHorizontalClearance chi ((Real.log X) ^ D) := by positivity
    have hRCorner0 : 0 ≤
        20 * (Real.log 21600 +
            2 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))) +
          5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) +
          5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) /
            min (exerciseRealClearance chi ((Real.log X) ^ D))
              (exerciseHorizontalClearance chi ((Real.log X) ^ D)) := by positivity
    have hxSigma :=
      MAPKoukExercise12TwoPowerGeometry.halfIntegerPoint_rpow_sigma_le_threeQuarter
        hX9 ht hsigma.2.le
    have hxHalf :=
      MAPKoukExercise12TwoPowerGeometry.halfIntegerPoint_rpow_half_le_threeQuarter
        hX9 ht
    have hpolyNat : (Real.log X) ^ (D + 2 * p + 1 + A) ≤
        Real.rpow X (1 / 4 : ℝ) := by
      rw [← Real.rpow_natCast]
      exact hpolyLargeX
    have hleftTrade :=
      MAPKoukExercise12TwoFinalScalarTrades.threeQuarter_mul_polylog_le_div
        hXpos hlogPos hpolyNat
    have hLeftTerm :
        T / Real.pi *
          ((20 * (Real.log 21600 +
              2 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))) +
            5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) +
            5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) /
              exerciseRealClearance chi ((Real.log X) ^ D)) *
            Real.rpow (halfIntegerPoint ⌊t⌋₊) sigma / sigma) ≤
          (2 * CLeft * Cinv) * (X / (Real.log X) ^ A) := by
      have hRLeft' :
          20 * (Real.log 21600 +
              2 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))) +
            5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) +
            5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) /
              exerciseRealClearance chi ((Real.log X) ^ D) ≤
            CLeft * (Real.log X) ^ (p + 1) := by
        simpa only [CLeft, K, Cinv, p] using hRLeft
      have hInnerLeft0 : 0 ≤
          ((20 * (Real.log 21600 +
              2 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))) +
            5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) +
            5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) /
              exerciseRealClearance chi ((Real.log X) ^ D)) *
            Real.rpow (halfIntegerPoint ⌊t⌋₊) sigma / sigma) := by
        exact div_nonneg
          (mul_nonneg hRLeft0
            (Real.rpow_nonneg (halfIntegerPoint_pos _).le _))
          hsigma.1.le
      have hInnerLeft :
          ((20 * (Real.log 21600 +
              2 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))) +
            5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) +
            5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) /
              exerciseRealClearance chi ((Real.log X) ^ D)) *
            Real.rpow (halfIntegerPoint ⌊t⌋₊) sigma / sigma) ≤
          (CLeft * (Real.log X) ^ (p + 1)) *
            Real.rpow X (3 / 4 : ℝ) *
              (Cinv * (Real.log X) ^ p) := by
        rw [div_eq_mul_inv]
        have hfirst :
            (20 * (Real.log 21600 +
                2 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))) +
              5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) +
              5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) /
                exerciseRealClearance chi ((Real.log X) ^ D)) *
              Real.rpow (halfIntegerPoint ⌊t⌋₊) sigma ≤
            (CLeft * (Real.log X) ^ (p + 1)) *
              Real.rpow X (3 / 4 : ℝ) :=
          mul_le_mul hRLeft' hxSigma
            (Real.rpow_nonneg (halfIntegerPoint_pos _).le _)
            (mul_nonneg hCLeft0 (pow_nonneg hlogPos.le _))
        exact mul_le_mul hfirst hInvSigma (inv_nonneg.mpr hsigma.1.le)
          (mul_nonneg (mul_nonneg hCLeft0 (pow_nonneg hlogPos.le _))
            (Real.rpow_nonneg hXpos.le _))
      have hTupper : T / Real.pi ≤ 2 * (Real.log X) ^ D := by
        calc
          T / Real.pi ≤ T := div_le_self hTpos.le (by linarith [Real.pi_gt_three])
          _ ≤ 2 * (Real.log X) ^ D := by linarith [hT.2, hlogPowOne]
      calc
        _ ≤ (2 * (Real.log X) ^ D) *
            ((CLeft * (Real.log X) ^ (p + 1)) *
              Real.rpow X (3 / 4 : ℝ) *
                (Cinv * (Real.log X) ^ p)) := by
          exact mul_le_mul hTupper hInnerLeft hInnerLeft0
            (by positivity)
        _ = (2 * CLeft * Cinv) *
            (Real.rpow X (3 / 4 : ℝ) *
              (Real.log X) ^ (D + 2 * p + 1)) := by
          dsimp [CLeft]
          rw [show D + 2 * p + 1 = D + (p + 1) + p by omega,
            pow_add, pow_add]
          ring
        _ ≤ (2 * CLeft * Cinv) * (X / (Real.log X) ^ A) :=
          mul_le_mul_of_nonneg_left hleftTrade (by positivity)
    have hpolyCorner : (Real.log X) ^ (p + 1 + A) ≤
        Real.rpow X (1 / 4 : ℝ) := by
      exact (pow_le_pow_right₀ hlogOne (by omega : p + 1 + A ≤ D + 2 * p + 1 + A)).trans
        hpolyNat
    have hcornerTrade :=
      MAPKoukExercise12TwoFinalScalarTrades.threeQuarter_mul_polylog_le_div
        hXpos hlogPos hpolyCorner
    have hOuter :=
      MAPKoukExercise12TwoFinalScalarTrades.standardEdge_sub_sigma_div_pi_le_two
        hN hsigma.1
    have hCornerInner :
        ((20 * (Real.log 21600 +
              2 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))) +
            5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) +
            5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) /
              min (exerciseRealClearance chi ((Real.log X) ^ D))
                (exerciseHorizontalClearance chi ((Real.log X) ^ D))) *
          Real.rpow (halfIntegerPoint ⌊t⌋₊) (1 / 2 : ℝ) / T) ≤
        CCorner * (X / (Real.log X) ^ A) := by
      have hTone : 1 ≤ T := hlogPowOne.trans hT.1.le
      have hTinv : 1 / T ≤ 1 := by
        simpa only [one_div] using (inv_le_one₀ hTpos).2 hTone
      rw [div_eq_mul_inv]
      have hRCorner' :
          20 * (Real.log 21600 +
              2 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))) +
            5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) +
            5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) /
              min (exerciseRealClearance chi ((Real.log X) ^ D))
                (exerciseHorizontalClearance chi ((Real.log X) ^ D)) ≤
            CCorner * (Real.log X) ^ (p + 1) := by
        simpa only [CCorner, K, Cinv, Ch, p] using hRCorner
      calc
        _ ≤ (CCorner * (Real.log X) ^ (p + 1)) *
            Real.rpow X (3 / 4 : ℝ) * 1 := by
          have hfirst :
              (20 * (Real.log 21600 +
                  2 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))) +
                5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) +
                5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) /
                  min (exerciseRealClearance chi ((Real.log X) ^ D))
                    (exerciseHorizontalClearance chi ((Real.log X) ^ D))) *
                Real.rpow (halfIntegerPoint ⌊t⌋₊) (1 / 2 : ℝ) ≤
              (CCorner * (Real.log X) ^ (p + 1)) *
                Real.rpow X (3 / 4 : ℝ) :=
            mul_le_mul hRCorner' hxHalf
              (Real.rpow_nonneg (halfIntegerPoint_pos _).le _)
              (mul_nonneg hCCorner0 (pow_nonneg hlogPos.le _))
          exact mul_le_mul hfirst (by simpa only [one_div] using hTinv)
            (inv_nonneg.mpr hTpos.le)
            (mul_nonneg (mul_nonneg hCCorner0 (pow_nonneg hlogPos.le _))
              (Real.rpow_nonneg hXpos.le _))
        _ = CCorner *
            (Real.rpow X (3 / 4 : ℝ) * (Real.log X) ^ (p + 1)) := by ring
        _ ≤ CCorner * (X / (Real.log X) ^ A) :=
          mul_le_mul_of_nonneg_left hcornerTrade (by positivity)
    have hxEdge :=
      MAPKoukExercise12TwoFinalScalarTrades.halfIntegerPoint_rpow_standardEdge_le_nine_mul
        (by linarith : 2 ≤ X) ht
    have hheightTrade :=
      MAPKoukExercise12TwoFinalScalarTrades.polylog_div_selectedHeight_le
        hlogOne hT.1 (by dsimp [D]; omega : 2 + A ≤ D)
    have hHorizontalInner :
        ((20 * (Real.log 21600 +
              2 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))) +
            5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) +
            5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) /
              exerciseHorizontalClearance chi ((Real.log X) ^ D)) *
          Real.rpow (halfIntegerPoint ⌊t⌋₊) (standardEdge ⌊t⌋₊) / T) ≤
        (9 * CHorizontal) * (X / (Real.log X) ^ A) := by
      have hRHorizontal' :
          20 * (Real.log 21600 +
              2 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))) +
            5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) +
            5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) /
              exerciseHorizontalClearance chi ((Real.log X) ^ D) ≤
            CHorizontal * (Real.log X) ^ 2 := by
        simpa only [CHorizontal, K, Ch] using hRHorizontal
      calc
        _ ≤ (CHorizontal * (Real.log X) ^ 2) * (9 * X) / T := by
          apply div_le_div_of_nonneg_right _ hTpos.le
          exact mul_le_mul hRHorizontal' hxEdge
            (Real.rpow_nonneg (halfIntegerPoint_pos _).le _)
            (mul_nonneg hCHorizontal0 (pow_nonneg hlogPos.le _))
        _ = (9 * CHorizontal) * X * ((Real.log X) ^ 2 / T) := by ring
        _ ≤ (9 * CHorizontal) * X * (1 / (Real.log X) ^ A) :=
          mul_le_mul_of_nonneg_left hheightTrade (by positivity)
        _ = (9 * CHorizontal) * (X / (Real.log X) ^ A) := by ring
    have hHorizontal :
        (standardEdge ⌊t⌋₊ - sigma) / Real.pi *
          (((20 * (Real.log 21600 +
                2 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))) +
              5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) +
              5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) /
                min (exerciseRealClearance chi ((Real.log X) ^ D))
                  (exerciseHorizontalClearance chi ((Real.log X) ^ D))) *
            Real.rpow (halfIntegerPoint ⌊t⌋₊) (1 / 2 : ℝ) / T) +
           ((20 * (Real.log 21600 +
                2 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))) +
              5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) +
              5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) /
                exerciseHorizontalClearance chi ((Real.log X) ^ D)) *
            Real.rpow (halfIntegerPoint ⌊t⌋₊) (standardEdge ⌊t⌋₊) / T)) ≤
          (2 * CCorner + 18 * CHorizontal) *
            (X / (Real.log X) ^ A) := by
      have hCornerInner0 : 0 ≤
          ((20 * (Real.log 21600 +
                2 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))) +
              5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) +
              5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) /
                min (exerciseRealClearance chi ((Real.log X) ^ D))
                  (exerciseHorizontalClearance chi ((Real.log X) ^ D))) *
            Real.rpow (halfIntegerPoint ⌊t⌋₊) (1 / 2 : ℝ) / T) := by
        exact div_nonneg
          (mul_nonneg hRCorner0
            (Real.rpow_nonneg (halfIntegerPoint_pos _).le _)) hTpos.le
      have hHorizontalInner0 : 0 ≤
          ((20 * (Real.log 21600 +
                2 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))) +
              5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) +
              5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) /
                exerciseHorizontalClearance chi ((Real.log X) ^ D)) *
            Real.rpow (halfIntegerPoint ⌊t⌋₊) (standardEdge ⌊t⌋₊) / T) := by
        exact div_nonneg
          (mul_nonneg hRHorizontal0
            (Real.rpow_nonneg (halfIntegerPoint_pos _).le _)) hTpos.le
      have hinners0 : 0 ≤
          ((20 * (Real.log 21600 +
                2 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))) +
              5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) +
              5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) /
                min (exerciseRealClearance chi ((Real.log X) ^ D))
                  (exerciseHorizontalClearance chi ((Real.log X) ^ D))) *
            Real.rpow (halfIntegerPoint ⌊t⌋₊) (1 / 2 : ℝ) / T) +
           ((20 * (Real.log 21600 +
                2 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))) +
              5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) +
              5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) /
                exerciseHorizontalClearance chi ((Real.log X) ^ D)) *
            Real.rpow (halfIntegerPoint ⌊t⌋₊) (standardEdge ⌊t⌋₊) / T) :=
        add_nonneg hCornerInner0 hHorizontalInner0
      calc
        _ ≤ 2 *
          (((20 * (Real.log 21600 +
                2 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))) +
              5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) +
              5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) /
                min (exerciseRealClearance chi ((Real.log X) ^ D))
                  (exerciseHorizontalClearance chi ((Real.log X) ^ D))) *
            Real.rpow (halfIntegerPoint ⌊t⌋₊) (1 / 2 : ℝ) / T) +
           ((20 * (Real.log 21600 +
                2 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))) +
              5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) +
              5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) /
                exerciseHorizontalClearance chi ((Real.log X) ^ D)) *
            Real.rpow (halfIntegerPoint ⌊t⌋₊) (standardEdge ⌊t⌋₊) / T)) :=
          mul_le_mul_of_nonneg_right hOuter hinners0
        _ ≤ 2 * (CCorner * (X / (Real.log X) ^ A) +
              (9 * CHorizontal) * (X / (Real.log X) ^ A)) := by gcongr
        _ = (2 * CCorner + 18 * CHorizontal) *
            (X / (Real.log X) ^ A) := by ring
    have hInside := MAPKoukExercise12TwoEndpointScalars.insideMajorant_le
      hN (hNX.trans (by linarith : 2 * X ≤ 5 * X))
      (by exact (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans hXexp)
      hTpos
    have hOutside := MAPKoukExercise12TwoEndpointScalars.outsideMajorant_le
      hN (hNX.trans (by linarith : 2 * X ≤ 5 * X))
      (by exact (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans hXexp)
      hTpos
    have hInsideFinal : insideMajorant ⌊t⌋₊ T ≤
        3000 * (X / (Real.log X) ^ A) := by
      calc
        _ ≤ 3000 * X * (Real.log X) ^ 2 / T := hInside
        _ = 3000 * X * ((Real.log X) ^ 2 / T) := by ring
        _ ≤ 3000 * X * (1 / (Real.log X) ^ A) :=
          mul_le_mul_of_nonneg_left hheightTrade (by positivity)
        _ = _ := by ring
    have hOutsideFinal : outsideMajorant ⌊t⌋₊ T ≤
        9000 * (X / (Real.log X) ^ A) := by
      calc
        _ ≤ 9000 * X * (Real.log X) ^ 2 / T := hOutside
        _ = 9000 * X * ((Real.log X) ^ 2 / T) := by ring
        _ ≤ 9000 * X * (1 / (Real.log X) ^ A) :=
          mul_le_mul_of_nonneg_left hheightTrade (by positivity)
        _ = _ := by ring
    have hTarget : 1 ≤ X / (Real.log X) ^ A := by
      rw [le_div_iff₀ (pow_pos hlogPos A)]
      have hpolyA : (Real.log X) ^ A ≤ X := by
        calc
          _ = Real.rpow (Real.log X) (A : ℝ) :=
            (Real.rpow_natCast _ _).symm
          _ ≤ Real.rpow X 1 := hpolyTargetX
          _ = X := Real.rpow_one X
      simpa using hpolyA
    have hExceptional : (6 * 40000016) * X *
        Real.rpow (Real.log X) (-(A : ℝ)) ≤
          CExceptional * (X / (Real.log X) ^ A) := by
      dsimp [CExceptional, Cinv]
      have hrpow :=
        MAPKoukExercise12TwoFinalScalarTrades.rpow_neg_nat_eq_one_div_pow
          hlogPos A
      calc
        6 * 40000016 * X * Real.rpow (Real.log X) (-(A : ℝ)) =
            6 * 40000016 * X * (1 / (Real.log X) ^ A) := by rw [hrpow]
        _ = 6 * 40000016 * (X / (Real.log X) ^ A) := by ring
        _ ≤ 6 * 40000016 * (X / (Real.log X) ^ A) := le_rfl
    have hFormulaBound := hpoint.2.2
    have hhalf : (1 / 2 : ℝ) ≤ X / (Real.log X) ^ A :=
      (by norm_num : (1 / 2 : ℝ) ≤ 1).trans hTarget
    calc
      ‖APFoundation.twistedMangoldtSum chi (Finset.Icc 1 ⌊t⌋₊) -
          MAPSiegelWalfiszCharacterReduction.characterMain chi t‖ ≤
        1 / 2 +
          ((dirichletZeroCount chi sigma T : ℝ) / sigma) *
            Real.rpow (halfIntegerPoint ⌊t⌋₊) (1 - exercise12TwoGap q T) +
          (6 * 40000016) * X * Real.rpow (Real.log X) (-(A : ℝ)) +
          T / Real.pi *
            ((20 * (Real.log 21600 +
                2 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))) +
              5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) +
              5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) /
                exerciseRealClearance chi ((Real.log X) ^ D)) *
              Real.rpow (halfIntegerPoint ⌊t⌋₊) sigma / sigma) +
          (standardEdge ⌊t⌋₊ - sigma) / Real.pi *
            (((20 * (Real.log 21600 +
                  2 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))) +
                5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) +
                5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) /
                  min (exerciseRealClearance chi ((Real.log X) ^ D))
                    (exerciseHorizontalClearance chi ((Real.log X) ^ D))) *
              Real.rpow (halfIntegerPoint ⌊t⌋₊) (1 / 2 : ℝ) / T) +
             ((20 * (Real.log 21600 +
                  2 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))) +
                5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) +
                5520 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) /
                  exerciseHorizontalClearance chi ((Real.log X) ^ D)) *
              Real.rpow (halfIntegerPoint ⌊t⌋₊) (standardEdge ⌊t⌋₊) / T)) +
          insideMajorant ⌊t⌋₊ T + outsideMajorant ⌊t⌋₊ T := hFormulaBound
      _ ≤ CTotal * (X / (Real.log X) ^ A) := by
        have hExpand :
            CTotal * (X / (Real.log X) ^ A) =
              (X / (Real.log X) ^ A) +
              CZero * (X / (Real.log X) ^ A) +
              CExceptional * (X / (Real.log X) ^ A) +
              (2 * CLeft * Cinv) * (X / (Real.log X) ^ A) +
              (2 * CCorner + 18 * CHorizontal) *
                (X / (Real.log X) ^ A) +
              3000 * (X / (Real.log X) ^ A) +
              9000 * (X / (Real.log X) ^ A) := by
          dsimp [CTotal]
          ring
        rw [hExpand]
        gcongr
      _ = CTotal * X / (Real.log X) ^ A := by ring
  obtain ⟨X0, hX0⟩ := eventually_atTop.1 hall
  refine ⟨CTotal, max 2 X0, hCTotal, le_max_left _ _, ?_⟩
  intro X hX q hq hqcap chi hprim hchi t ht
  exact hX0 X ((le_max_right 2 X0).trans hX) q hq hqcap chi hprim hchi t ht

end
end MAPNonprincipalTwistedMangoldtPsiCertified

#print axioms MAPNonprincipalTwistedMangoldtPsiCertified.primitiveNonprincipalTwistedMangoldtPsi
