import PrincipalKoukLocalAppendixBFormula
import PrincipalKoukLocalKhaleHighFormula
import PrincipalKoukLocalTheorem12ThreeFormula
import KoukExercise12TwoPrincipalLocalContourRBounds
import KoukExercise12TwoFinalScalarTrades
import KoukExercise12TwoPolylogScalars
import PrimitiveTwistedMangoldtSourceSplit

/-!
# Principal Exercise 12.2 endpoint from Appendix B

This file performs the deterministic scalar collapse of the split local
principal contour.  In particular, the horizontal segment next to the pole is
controlled with the local horizontal aperture; the older global-clearance
formula is deliberately not used here.
-/

namespace MAPPrincipalKoukSiegelFormula

open Filter Set DirichletZeros
open PrimitiveTruncatedExplicitFormulaBridge PaperEdgePrimitiveComponents
open MAPKoukExercise12TwoContourAperture
open MAPKoukExercise12TwoLocalHorizontalAperture

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩

/-- Exact local principal contour formula source consumed by the final scalar
collapse, with the zero-free saving exponent kept explicit. -/
def PrincipalLocalFormulaSourceAt (theta : ℝ) : Prop :=
  ∀ D : ℕ,
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ X : ℝ in atTop,
        ∀ t : ℝ, t ∈ Set.Icc X (2 * X) →
          ∃ sigma ∈ Set.Ioo (0 : ℝ) (1 / 2),
            ∃ T ∈ Set.Ioo ((Real.log X) ^ D) ((Real.log X) ^ D + 1),
              let x := halfIntegerPoint ⌊t⌋₊
              let dLeft := exerciseRealClearance
                (1 : DirichletCharacter ℂ 1) ((Real.log X) ^ D)
              let dHorizontal := exerciseHorizontalClearance
                (1 : DirichletCharacter ℂ 1) ((Real.log X) ^ D)
              let dCorner := min dLeft dHorizontal
              let L := Real.log ((Real.log X) ^ D + 3)
              let RLeft := 2 + 20 * (Real.log 223948800 + 6 * L) +
                30300 * L + 30300 * L / dLeft
              let RHorizontal := 2 + 20 * (Real.log 223948800 + 6 * L) +
                30300 * L + 30300 * L / dHorizontal
              let RCorner := 2 + 20 * (Real.log 223948800 + 6 * L) +
                30300 * L + 30300 * L / dCorner
              dLeft ≤ sigma ∧
              ‖APFoundation.twistedMangoldtSum
                    (1 : DirichletCharacter ℂ 1) (Finset.Icc 1 ⌊t⌋₊) -
                  MAPSiegelWalfiszCharacterReduction.characterMain
                    (1 : DirichletCharacter ℂ 1) t‖ ≤
                1 / 2 +
                ((dirichletZeroCount
                    (1 : DirichletCharacter ℂ 1) sigma T : ℝ) / sigma) *
                  x ^ (1 - c * Real.rpow (Real.log X) (-theta)) +
                T / Real.pi * (RLeft * x ^ sigma / sigma) +
                (standardEdge ⌊t⌋₊ - sigma) / Real.pi *
                  (RCorner * x ^ (1 / 2 : ℝ) / T +
                    RHorizontal * x ^ standardEdge ⌊t⌋₊ / T) +
                insideMajorant ⌊t⌋₊ T + outsideMajorant ⌊t⌋₊ T

/-- Backward-compatible weak-VK source shape. -/
abbrev PrincipalLocalFormulaSource : Prop :=
  PrincipalLocalFormulaSourceAt (3 / 4 : ℝ)

theorem primitivePrincipalOneTwistedMangoldtPsi_of_localFormulaSourceAt
    (theta : ℝ) (htheta : theta < 1)
    (hSource : PrincipalLocalFormulaSourceAt theta) :
    MAPPrimitiveTwistedMangoldtSourceSplit.PrimitivePrincipalOneTwistedMangoldtPsi := by
  intro A
  let D : ℕ := A + 4
  let K : ℝ := (D : ℝ) + 4
  let CReal : ℝ :=
    2 + 20 * 223948800 + 30420 * K + 30300 * K * 40000016
  let CHorizontal : ℝ :=
    2 + 20 * 223948800 + 30420 * K + 30300 * K * (121204 * K)
  let CCorner : ℝ :=
    2 + 20 * 223948800 + 30420 * K +
      30300 * K * (40000016 + 121204 * K)
  let C : ℝ :=
    1 + 3 * 5000000 * 40000016 +
      2 * CReal * 40000016 + 2 * CCorner + 18 * CHorizontal + 12000
  obtain ⟨c, hc, hformula⟩ := hSource D
  have hdecay := WeakVKNear.weakGap_nearFactor_beats_polylog
    theta c ((6 * D : ℕ) : ℝ) (A : ℝ)
    htheta hc (by positivity) (by positivity)
  have hpolyLeft := SupportBoundaryQuantitative.polylog_absorption
    (((7 * D + 1 + A : ℕ) : ℝ)) (1 / 4 : ℝ) (by norm_num)
  have hpolyCorner := SupportBoundaryQuantitative.polylog_absorption
    (((3 * D + 1 + A : ℕ) : ℝ)) (1 / 4 : ℝ) (by norm_num)
  have hpolyHalf := SupportBoundaryQuantitative.polylog_absorption
    (A : ℝ) 1 (by norm_num)
  have hall : ∀ᶠ X : ℝ in atTop,
      ∀ t : ℝ, t ∈ Set.Icc X (2 * X) →
        ‖APFoundation.twistedMangoldtSum
              (1 : DirichletCharacter ℂ 1) (Finset.Icc 1 ⌊t⌋₊) -
            MAPSiegelWalfiszCharacterReduction.characterMain
              (1 : DirichletCharacter ℂ 1) t‖ ≤
          C * X / (Real.log X) ^ A := by
    filter_upwards [hformula, hdecay, hpolyLeft, hpolyCorner, hpolyHalf,
        eventually_ge_atTop (Real.exp 2), eventually_ge_atTop 9] with
        X hformulaX hdecayX hpolyLeftX hpolyCornerX hpolyHalfX hXexp hX9
    intro t ht
    have hXpos : 0 < X := (Real.exp_pos 2).trans_le hXexp
    have hX2 : 2 ≤ X := by linarith
    have hL2 : 2 ≤ Real.log X := by
      rw [Real.le_log_iff_exp_le hXpos]
      exact hXexp
    have hL1 : 1 ≤ Real.log X := by linarith
    have hLpos : 0 < Real.log X := by linarith
    have hCReal0 : 0 ≤ CReal := by dsimp only [CReal, K]; positivity
    have hCHorizontal0 : 0 ≤ CHorizontal := by
      dsimp only [CHorizontal, K]
      positivity
    have hCCorner0 : 0 ≤ CCorner := by dsimp only [CCorner, K]; positivity
    obtain ⟨hN, _hxLower, hxUpper, hNX⟩ :=
      MAPKoukExercise12TwoEndpointScalars.halfIntegerPoint_floor_range hX2 ht
    obtain ⟨sigma, hsigma, T, hT, hleftSigma, hpoint⟩ := hformulaX t ht
    let x := halfIntegerPoint ⌊t⌋₊
    let dLeft := exerciseRealClearance
      (1 : DirichletCharacter ℂ 1) ((Real.log X) ^ D)
    let dHorizontal := exerciseHorizontalClearance
      (1 : DirichletCharacter ℂ 1) ((Real.log X) ^ D)
    let dCorner := min dLeft dHorizontal
    let LH := Real.log ((Real.log X) ^ D + 3)
    let RLeft := 2 + 20 * (Real.log 223948800 + 6 * LH) +
      30300 * LH + 30300 * LH / dLeft
    let RHorizontal := 2 + 20 * (Real.log 223948800 + 6 * LH) +
      30300 * LH + 30300 * LH / dHorizontal
    let RCorner := 2 + 20 * (Real.log 223948800 + 6 * LH) +
      30300 * LH + 30300 * LH / dCorner
    have hTpos : 0 < T := (pow_pos hLpos D).trans hT.1
    have hTupper : T ≤ 2 * (Real.log X) ^ D := by
      have hpowOne : 1 ≤ (Real.log X) ^ D := one_le_pow₀ hL1
      linarith [hT.2]
    have hInvSigma : sigma⁻¹ ≤ 40000016 * (Real.log X) ^ (3 * D) := by
      have hdPos := exerciseRealClearance_pos
        (1 : DirichletCharacter ℂ 1) ((Real.log X) ^ D)
      have hfirst : sigma⁻¹ ≤ dLeft⁻¹ := by
        simpa only [dLeft, one_div] using
          one_div_le_one_div_of_le hdPos hleftSigma
      exact hfirst.trans (by
        simpa only [Nat.zero_add, dLeft] using
          MAPKoukExercise12TwoLocalPolylogScalars.inv_exerciseRealClearance_polylogHeight_le
            0 D hL2 (1 : DirichletCharacter ℂ 1)
            (by rw [DirichletCharacter.isPrimitive_def,
              DirichletCharacter.conductor_one]) (by simp))
    have hCount :
        (dirichletZeroCount (1 : DirichletCharacter ℂ 1) sigma T : ℝ) ≤
          5000000 * (Real.log X) ^ (3 * D) := by
      have hmono := MAPMellinDetectorLeaf.dirichletZeroCount_mono
        (1 : DirichletCharacter ℂ 1) hsigma.1.le
        (show T ≤ (Real.log X) ^ D + 4 by linarith [hT.2])
      have hcast :
          (dirichletZeroCount (1 : DirichletCharacter ℂ 1) sigma T : ℝ) ≤
            (dirichletZeroCount (1 : DirichletCharacter ℂ 1) 0
              ((Real.log X) ^ D + 4) : ℝ) := by exact_mod_cast hmono
      exact hcast.trans (by
        simpa only [Nat.zero_add] using
          MAPKoukExercise12TwoPolylogScalars.dirichletZeroCount_polylogHeight_le
            0 D hL2 (1 : DirichletCharacter ℂ 1)
            (by rw [DirichletCharacter.isPrimitive_def,
              DirichletCharacter.conductor_one]) (by simp))
    have hRLeft : RLeft ≤ CReal * (Real.log X) ^ (3 * D + 1) := by
      simpa only [K, CReal, RLeft, LH, dLeft] using
        MAPKoukExercise12TwoPrincipalLocalContourRBounds.realContourR_le D hL2
    have hRHorizontal : RHorizontal ≤ CHorizontal * (Real.log X) ^ 2 := by
      simpa only [K, CHorizontal, RHorizontal, LH, dHorizontal] using
        MAPKoukExercise12TwoPrincipalLocalContourRBounds.horizontalContourR_le D hL2
    have hRCorner : RCorner ≤ CCorner * (Real.log X) ^ (3 * D + 1) := by
      simpa only [K, CCorner, RCorner, LH, dCorner, dLeft, dHorizontal] using
        MAPKoukExercise12TwoPrincipalLocalContourRBounds.cornerContourR_le
          D (by dsimp [D]; omega) hL2
    have hLHpos : 0 < LH := by
      dsimp only [LH]
      apply Real.log_pos
      have : 1 ≤ (Real.log X) ^ D := one_le_pow₀ hL1
      linarith
    have hRLeft0 : 0 ≤ RLeft := by
      dsimp only [RLeft]
      have hd := exerciseRealClearance_pos
        (1 : DirichletCharacter ℂ 1) ((Real.log X) ^ D)
      have hlogc : 0 ≤ Real.log (223948800 : ℝ) := Real.log_nonneg (by norm_num)
      positivity
    have hRHorizontal0 : 0 ≤ RHorizontal := by
      dsimp only [RHorizontal]
      have hd := exerciseHorizontalClearance_pos
        (1 : DirichletCharacter ℂ 1) ((Real.log X) ^ D)
      have hlogc : 0 ≤ Real.log (223948800 : ℝ) := Real.log_nonneg (by norm_num)
      positivity
    have hRCorner0 : 0 ≤ RCorner := by
      dsimp only [RCorner, dCorner, dLeft, dHorizontal]
      have hdR := exerciseRealClearance_pos
        (1 : DirichletCharacter ℂ 1) ((Real.log X) ^ D)
      have hdH := exerciseHorizontalClearance_pos
        (1 : DirichletCharacter ℂ 1) ((Real.log X) ^ D)
      have hlogc : 0 ≤ Real.log (223948800 : ℝ) := Real.log_nonneg (by norm_num)
      positivity
    have hxSigma : Real.rpow x sigma ≤ Real.rpow X (3 / 4 : ℝ) := by
      simpa only [x] using
        MAPKoukExercise12TwoPowerGeometry.halfIntegerPoint_rpow_sigma_le_threeQuarter
          hX9 ht hsigma.2.le
    have hxHalf : Real.rpow x (1 / 2 : ℝ) ≤ Real.rpow X (3 / 4 : ℝ) := by
      simpa only [x] using
        MAPKoukExercise12TwoPowerGeometry.halfIntegerPoint_rpow_half_le_threeQuarter
          hX9 ht
    have hxEdge : Real.rpow x (standardEdge ⌊t⌋₊) ≤ 9 * X := by
      simpa only [x] using
        MAPKoukExercise12TwoFinalScalarTrades.halfIntegerPoint_rpow_standardEdge_le_nine_mul
          hX2 ht
    have hfront : (standardEdge ⌊t⌋₊ - sigma) / Real.pi ≤ 2 :=
      MAPKoukExercise12TwoFinalScalarTrades.standardEdge_sub_sigma_div_pi_le_two
        hN hsigma.1
    have hfront0 : 0 ≤ (standardEdge ⌊t⌋₊ - sigma) / Real.pi := by
      apply div_nonneg
      · have hedge := PaperEdgePrimitiveComponents.standardEdge_gt_one ⌊t⌋₊ hN
        linarith [hsigma.2]
      · exact Real.pi_pos.le
    have hpowWeak : Real.rpow x
        (1 - c * Real.rpow (Real.log X) (-theta)) ≤
        3 * X * Real.rpow X
          (-((c * Real.rpow (Real.log X) (-theta)) / 12)) := by
      simpa only [x] using
        MAPKoukExercise12TwoEndpointScalars.halfIntegerPoint_rpow_one_sub_le_weakFactor
          (by linarith) ht (mul_nonneg hc.le (Real.rpow_nonneg hLpos.le _))
    have hdecayNow : (Real.log X) ^ (6 * D) *
        Real.rpow X
          (-((c * Real.rpow (Real.log X) (-theta)) / 12)) ≤
        1 / (Real.log X) ^ A := by
      have hd := hdecayX (c * Real.rpow (Real.log X) (-theta)) le_rfl
      rw [MAPKoukExercise12TwoFinalScalarTrades.rpow_neg_nat_eq_one_div_pow
        hLpos A] at hd
      calc
        (Real.log X) ^ (6 * D) *
            Real.rpow X
              (-((c * Real.rpow (Real.log X) (-theta)) / 12)) =
          Real.rpow (Real.log X) ((6 * D : ℕ) : ℝ) *
            Real.rpow X
              (-((c * Real.rpow (Real.log X) (-theta)) / 12)) := by
                exact congrArg
                  (fun y : ℝ => y * Real.rpow X
                    (-((c * Real.rpow (Real.log X) (-theta)) / 12)))
                  (Real.rpow_natCast (Real.log X) (6 * D)).symm
        _ ≤ _ := hd
    have hZero :
        ((dirichletZeroCount (1 : DirichletCharacter ℂ 1) sigma T : ℝ) / sigma) *
            Real.rpow x
              (1 - c * Real.rpow (Real.log X) (-theta)) ≤
          (3 * 5000000 * 40000016) * X / (Real.log X) ^ A := by
      rw [div_eq_mul_inv]
      calc
        _ ≤ (5000000 * (Real.log X) ^ (3 * D)) *
              (40000016 * (Real.log X) ^ (3 * D)) *
              (3 * X * Real.rpow X
                (-((c * Real.rpow (Real.log X) (-theta)) / 12))) := by
            have hfirst :
                (dirichletZeroCount (1 : DirichletCharacter ℂ 1) sigma T : ℝ) *
                    sigma⁻¹ ≤
                  (5000000 * (Real.log X) ^ (3 * D)) *
                    (40000016 * (Real.log X) ^ (3 * D)) :=
              mul_le_mul hCount hInvSigma (inv_nonneg.mpr hsigma.1.le)
                (by positivity)
            exact mul_le_mul hfirst hpowWeak
              (Real.rpow_nonneg (halfIntegerPoint_pos ⌊t⌋₊).le _)
              (mul_nonneg (by positivity) (by positivity))
        _ = (3 * 5000000 * 40000016) * X *
              ((Real.log X) ^ (6 * D) * Real.rpow X
                (-((c * Real.rpow (Real.log X) (-theta)) / 12))) := by
            rw [show (Real.log X) ^ (6 * D) =
              (Real.log X) ^ (3 * D) * (Real.log X) ^ (3 * D) by
                rw [← pow_add]; congr 1 <;> omega]
            ring
        _ ≤ (3 * 5000000 * 40000016) * X *
              (1 / (Real.log X) ^ A) := by gcongr
        _ = _ := by ring
    have hpolyLeft' : (Real.log X) ^ (7 * D + 1 + A) ≤
        Real.rpow X (1 / 4 : ℝ) := by
      calc
        (Real.log X) ^ (7 * D + 1 + A) =
            Real.rpow (Real.log X) ((7 * D + 1 + A : ℕ) : ℝ) := by
              exact (Real.rpow_natCast (Real.log X) (7 * D + 1 + A)).symm
        _ ≤ _ := hpolyLeftX
    have hpolyCorner' : (Real.log X) ^ (3 * D + 1 + A) ≤
        Real.rpow X (1 / 4 : ℝ) := by
      calc
        (Real.log X) ^ (3 * D + 1 + A) =
            Real.rpow (Real.log X) ((3 * D + 1 + A : ℕ) : ℝ) := by
              exact (Real.rpow_natCast (Real.log X) (3 * D + 1 + A)).symm
        _ ≤ _ := hpolyCornerX
    have hLeftTrade :=
      MAPKoukExercise12TwoFinalScalarTrades.threeQuarter_mul_polylog_le_div
        hXpos hLpos (P := 7 * D + 1) (A := A) (by
          simpa only [Nat.add_assoc] using hpolyLeft')
    have hCornerTrade :=
      MAPKoukExercise12TwoFinalScalarTrades.threeQuarter_mul_polylog_le_div
        hXpos hLpos (P := 3 * D + 1) (A := A) (by
          simpa only [Nat.add_assoc] using hpolyCorner')
    have hLeft :
        T / Real.pi * (RLeft * Real.rpow x sigma / sigma) ≤
          (2 * CReal * 40000016) * X / (Real.log X) ^ A := by
      have hpiInv : Real.pi⁻¹ ≤ 1 := by
        have : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
        exact (inv_le_one₀ Real.pi_pos).2 this
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have hOuter : T * Real.pi⁻¹ ≤ (2 * (Real.log X) ^ D) * 1 :=
        mul_le_mul hTupper hpiInv (inv_nonneg.mpr Real.pi_pos.le) (by positivity)
      have hInnerPower : RLeft * Real.rpow x sigma ≤
          (CReal * (Real.log X) ^ (3 * D + 1)) *
            Real.rpow X (3 / 4 : ℝ) :=
        mul_le_mul hRLeft hxSigma (Real.rpow_nonneg (halfIntegerPoint_pos ⌊t⌋₊).le _)
          (mul_nonneg hCReal0 (pow_nonneg hLpos.le _))
      have hInner : RLeft * Real.rpow x sigma * sigma⁻¹ ≤
          (CReal * (Real.log X) ^ (3 * D + 1) *
              Real.rpow X (3 / 4 : ℝ)) *
            (40000016 * (Real.log X) ^ (3 * D)) :=
        mul_le_mul hInnerPower hInvSigma (inv_nonneg.mpr hsigma.1.le)
          (mul_nonneg (mul_nonneg hCReal0 (pow_nonneg hLpos.le _))
            (Real.rpow_nonneg hXpos.le _))
      calc
        _ ≤ (2 * (Real.log X) ^ D) * 1 *
              (CReal * (Real.log X) ^ (3 * D + 1) *
                Real.rpow X (3 / 4 : ℝ) *
                (40000016 * (Real.log X) ^ (3 * D))) :=
          mul_le_mul hOuter hInner
            (mul_nonneg
              (mul_nonneg hRLeft0
                (Real.rpow_nonneg (halfIntegerPoint_pos ⌊t⌋₊).le _))
              (inv_nonneg.mpr hsigma.1.le))
            (mul_nonneg (by positivity) (by positivity))
        _ = (2 * CReal * 40000016) *
              (Real.rpow X (3 / 4 : ℝ) *
                (Real.log X) ^ (7 * D + 1)) := by
            rw [show (Real.log X) ^ (7 * D + 1) =
              (Real.log X) ^ D * (Real.log X) ^ (3 * D + 1) *
                (Real.log X) ^ (3 * D) by
              rw [← pow_add, ← pow_add]; congr 1 <;> omega]
            ring
        _ ≤ (2 * CReal * 40000016) * (X / (Real.log X) ^ A) := by gcongr
        _ = _ := by ring
    have hCornerLow :
        (standardEdge ⌊t⌋₊ - sigma) / Real.pi *
            (RCorner * Real.rpow x (1 / 2 : ℝ) / T) ≤
          (2 * CCorner) * X / (Real.log X) ^ A := by
      have hTinv : T⁻¹ ≤ 1 := by
        have hTone : 1 ≤ T := (one_le_pow₀ hL1).trans hT.1.le
        exact (inv_le_one₀ hTpos).2 hTone
      rw [div_eq_mul_inv]
      have hCornerInnerPower : RCorner * Real.rpow x (1 / 2 : ℝ) ≤
          (CCorner * (Real.log X) ^ (3 * D + 1)) *
            Real.rpow X (3 / 4 : ℝ) :=
        mul_le_mul hRCorner hxHalf (Real.rpow_nonneg (halfIntegerPoint_pos ⌊t⌋₊).le _)
          (mul_nonneg hCCorner0 (pow_nonneg hLpos.le _))
      have hCornerInner : RCorner * Real.rpow x (1 / 2 : ℝ) * T⁻¹ ≤
          (CCorner * (Real.log X) ^ (3 * D + 1) *
              Real.rpow X (3 / 4 : ℝ)) * 1 :=
        mul_le_mul hCornerInnerPower hTinv (inv_nonneg.mpr hTpos.le)
          (mul_nonneg (mul_nonneg hCCorner0 (pow_nonneg hLpos.le _))
            (Real.rpow_nonneg hXpos.le _))
      calc
        _ ≤ 2 * (CCorner * (Real.log X) ^ (3 * D + 1) *
              Real.rpow X (3 / 4 : ℝ) * 1) :=
          mul_le_mul hfront hCornerInner
            (mul_nonneg
              (mul_nonneg hRCorner0
                (Real.rpow_nonneg (halfIntegerPoint_pos ⌊t⌋₊).le _))
              (inv_nonneg.mpr hTpos.le)) (by norm_num)
        _ = (2 * CCorner) *
              (Real.rpow X (3 / 4 : ℝ) *
                (Real.log X) ^ (3 * D + 1)) := by ring
        _ ≤ (2 * CCorner) * (X / (Real.log X) ^ A) := by gcongr
        _ = _ := by ring
    have hHeightTrade :=
      MAPKoukExercise12TwoFinalScalarTrades.polylog_div_selectedHeight_le
        hL1 hT.1 (P := 2) (A := A) (D := D) (by dsimp [D]; omega)
    have hCornerHigh :
        (standardEdge ⌊t⌋₊ - sigma) / Real.pi *
            (RHorizontal * Real.rpow x (standardEdge ⌊t⌋₊) / T) ≤
          (18 * CHorizontal) * X / (Real.log X) ^ A := by
      have hHighNum : RHorizontal * Real.rpow x (standardEdge ⌊t⌋₊) ≤
          (CHorizontal * (Real.log X) ^ 2) * (9 * X) :=
        mul_le_mul hRHorizontal hxEdge
          (Real.rpow_nonneg (halfIntegerPoint_pos ⌊t⌋₊).le _)
          (mul_nonneg hCHorizontal0 (pow_nonneg hLpos.le _))
      have hHighDiv : RHorizontal * Real.rpow x (standardEdge ⌊t⌋₊) / T ≤
          CHorizontal * (Real.log X) ^ 2 * (9 * X) / T :=
        div_le_div_of_nonneg_right hHighNum hTpos.le
      calc
        _ ≤ 2 * (CHorizontal * (Real.log X) ^ 2 * (9 * X) / T) :=
          mul_le_mul hfront hHighDiv
            (div_nonneg (mul_nonneg hRHorizontal0
              (Real.rpow_nonneg (halfIntegerPoint_pos ⌊t⌋₊).le _)) hTpos.le)
            (by norm_num)
        _ = (18 * CHorizontal) * X * ((Real.log X) ^ 2 / T) := by ring
        _ ≤ (18 * CHorizontal) * X * (1 / (Real.log X) ^ A) := by gcongr
        _ = _ := by ring
    have hNX5 : (⌊t⌋₊ : ℝ) ≤ 5 * X := by linarith [hNX]
    have hExpOne : Real.exp 1 ≤ X :=
      (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans hXexp
    have hInside := MAPKoukExercise12TwoEndpointScalars.insideMajorant_le
      (X := X) (T := T) hN hNX5 hExpOne hTpos
    have hOutside := MAPKoukExercise12TwoEndpointScalars.outsideMajorant_le
      (X := X) (T := T) hN hNX5 hExpOne hTpos
    have hPerron : insideMajorant ⌊t⌋₊ T + outsideMajorant ⌊t⌋₊ T ≤
        12000 * X / (Real.log X) ^ A := by
      calc
        _ ≤ 12000 * X * ((Real.log X) ^ 2 / T) := by
          calc
            _ ≤ 3000 * X * (Real.log X) ^ 2 / T +
                9000 * X * (Real.log X) ^ 2 / T := add_le_add hInside hOutside
            _ = _ := by ring
        _ ≤ 12000 * X * (1 / (Real.log X) ^ A) := by gcongr
        _ = _ := by ring
    have hpolyHalf' : (Real.log X) ^ A ≤ X := by
      calc
        (Real.log X) ^ A = Real.rpow (Real.log X) (A : ℝ) := by
          exact (Real.rpow_natCast (Real.log X) A).symm
        _ ≤ Real.rpow X 1 := hpolyHalfX
        _ = X := Real.rpow_one X
    have hHalf : (1 / 2 : ℝ) ≤ X / (Real.log X) ^ A := by
      have hOne : (1 : ℝ) ≤ X / (Real.log X) ^ A := by
        rw [le_div_iff₀ (pow_pos hLpos A)]
        simpa using hpolyHalf'
      exact (by norm_num : (1 / 2 : ℝ) ≤ 1).trans hOne
    have hcornerSplit :
        (standardEdge ⌊t⌋₊ - sigma) / Real.pi *
            (RCorner * Real.rpow x (1 / 2 : ℝ) / T +
              RHorizontal * Real.rpow x (standardEdge ⌊t⌋₊) / T) ≤
          ((2 * CCorner) + (18 * CHorizontal)) * X /
            (Real.log X) ^ A := by
      rw [mul_add]
      calc
        _ ≤ (2 * CCorner) * X / (Real.log X) ^ A +
            (18 * CHorizontal) * X / (Real.log X) ^ A :=
          add_le_add hCornerLow hCornerHigh
        _ = _ := by ring
    have hsum :
        1 / 2 +
          ((dirichletZeroCount (1 : DirichletCharacter ℂ 1) sigma T : ℝ) / sigma) *
            Real.rpow x
              (1 - c * Real.rpow (Real.log X) (-theta)) +
          T / Real.pi * (RLeft * Real.rpow x sigma / sigma) +
          (standardEdge ⌊t⌋₊ - sigma) / Real.pi *
            (RCorner * Real.rpow x (1 / 2 : ℝ) / T +
              RHorizontal * Real.rpow x (standardEdge ⌊t⌋₊) / T) +
          insideMajorant ⌊t⌋₊ T + outsideMajorant ⌊t⌋₊ T ≤
            C * X / (Real.log X) ^ A := by
      calc
        _ = 1 / 2 +
              ((dirichletZeroCount (1 : DirichletCharacter ℂ 1) sigma T : ℝ) /
                sigma) *
                Real.rpow x
                  (1 - c * Real.rpow (Real.log X) (-theta)) +
              T / Real.pi * (RLeft * Real.rpow x sigma / sigma) +
              (standardEdge ⌊t⌋₊ - sigma) / Real.pi *
                (RCorner * Real.rpow x (1 / 2 : ℝ) / T +
                  RHorizontal * Real.rpow x (standardEdge ⌊t⌋₊) / T) +
              (insideMajorant ⌊t⌋₊ T + outsideMajorant ⌊t⌋₊ T) := by ring
        _ ≤ X / (Real.log X) ^ A +
              (3 * 5000000 * 40000016) * X / (Real.log X) ^ A +
              (2 * CReal * 40000016) * X / (Real.log X) ^ A +
              ((2 * CCorner) + (18 * CHorizontal)) * X /
                (Real.log X) ^ A +
              12000 * X / (Real.log X) ^ A := by
            gcongr
        _ = C * X / (Real.log X) ^ A := by
          dsimp only [C]
          ring
    exact hpoint.trans (by simpa only [x, dLeft, dHorizontal, dCorner,
      LH, RLeft, RHorizontal, RCorner] using hsum)
  rcases eventually_atTop.1 hall with ⟨X1, hX1⟩
  let X0 := max 2 X1
  refine ⟨C, X0, ?_, le_max_left 2 X1, ?_⟩
  · dsimp only [C, CReal, CHorizontal, CCorner, K, D]
    positivity
  intro X hX t ht
  exact hX1 X ((le_max_right 2 X1).trans hX) t ht

/-- The original exponent-`3/4` scalar constructor. -/
theorem primitivePrincipalOneTwistedMangoldtPsi_of_localFormulaSource
    (hSource : PrincipalLocalFormulaSource) :
    MAPPrimitiveTwistedMangoldtSourceSplit.PrimitivePrincipalOneTwistedMangoldtPsi :=
  primitivePrincipalOneTwistedMangoldtPsi_of_localFormulaSourceAt
    (3 / 4 : ℝ) (by norm_num) hSource

/-- Premise-free conductor-one endpoint.  Its high-zero input is the
principal zeta `3-4-1` collar, and its bounded-zero input is compactness. -/
theorem primitivePrincipalOneTwistedMangoldtPsi :
    MAPPrimitiveTwistedMangoldtSourceSplit.PrimitivePrincipalOneTwistedMangoldtPsi :=
  primitivePrincipalOneTwistedMangoldtPsi_of_localFormulaSourceAt
    (1 / 4 : ℝ) (by norm_num)
    (fun D =>
      MAPPrincipalKoukLocalTheorem12ThreeFormula.exists_eventually_principal_local_formula D)


/-- Original Appendix-B-facing constructor. -/
theorem primitivePrincipalOneTwistedMangoldtPsi_of_appendixB
    (hKhale104 : MAPKhaleAppendixBSource.AppendixBCorollary104) :
    MAPPrimitiveTwistedMangoldtSourceSplit.PrimitivePrincipalOneTwistedMangoldtPsi :=
  primitivePrincipalOneTwistedMangoldtPsi_of_localFormulaSource
    (fun D =>
      MAPPrincipalKoukLocalAppendixBFormula.exists_eventually_principal_local_formula_of_appendixB
        hKhale104 D)

/-- Principal endpoint avoiding McCurley's finite-height theorem: compactness
handles bounded zeros, while the high Khale argument is supplied by Ford's
Hurwitz estimate and the raw Lemma-4.1 input. -/
theorem primitivePrincipalOneTwistedMangoldtPsi_of_ford_raw
    (hFord : MAPKhaleAppendixBSource.FordHurwitzEquation12 76.2 4.45)
    (hRaw : MAPKhaleAppendixBFirstPartAnalyticReduction.AppendixBFirstPartRawEstimate) :
    MAPPrimitiveTwistedMangoldtSourceSplit.PrimitivePrincipalOneTwistedMangoldtPsi :=
  primitivePrincipalOneTwistedMangoldtPsi_of_localFormulaSource
    (fun D =>
      MAPPrincipalKoukLocalKhaleHighFormula.exists_eventually_principal_local_formula_of_ford_raw
        hFord hRaw D)

end
end MAPPrincipalKoukSiegelFormula

#print axioms MAPPrincipalKoukSiegelFormula.primitivePrincipalOneTwistedMangoldtPsi_of_localFormulaSource
#print axioms MAPPrincipalKoukSiegelFormula.primitivePrincipalOneTwistedMangoldtPsi
#print axioms MAPPrincipalKoukSiegelFormula.primitivePrincipalOneTwistedMangoldtPsi_of_appendixB
#print axioms MAPPrincipalKoukSiegelFormula.primitivePrincipalOneTwistedMangoldtPsi_of_ford_raw
