import PostA5HighStripSplitAssembly
import CGLDetectorStructuredLargeValue
import BHPFixedCharacterFromDyadicAFE
import PostA5RecenteredSourceBudget
import ZeroDensityArithmetic
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# High-strip split reduction from the nonprincipal fourth moment

This module discharges the eventual scale and exponent ledgers around the
finite source-faithful Type-I/Type-II weld.  Its public endpoint has the exact
nonprincipal discrete fourth moment as its only input.
-/

namespace PostA5HighStripSplitReductionFromFourthMoment

open Filter Set
open scoped BigOperators FourierTransform
open CGLProofDAG DirichletZeros MAPAppendixA4PostA5SetAdapter
open MAPAppendixA4DetectorDichotomy
open MAPAppendixA4RecenteredGammaRepair
open PostA5TypeIFourierAssembly PostA5TypeIFourierTailAbsorption
open PostA5RecenteredSourceBudget PostA5LongSpacingAssembly
open PostA5CrowdingDeterministic PostA5HighStripSplitAssembly
open PostA5RecenteredSourceSplit PostA5RecenteredTypeIExtractor
open PostA5TypeIIFourthMoment PostA5TypeICoefficientProvenance
open CGLDetectorStructuredLargeValue
open SchwartzMap

noncomputable section

/-- The collar window has an exact linear cardinality at an integral radius. -/
theorem shiftedFloorWindowCount_natCast (C : ℕ) :
    shiftedFloorWindowCount (C : ℝ) = 2 * C + 2 := by
  have hneg : Int.floor (-(C : ℝ)) = -((C : ℤ)) := by
    rw [show (-(C : ℝ)) = ((-((C : ℤ)) : ℤ) : ℝ) by push_cast; ring]
    exact Int.floor_intCast _
  simp [shiftedFloorWindowCount, shiftedFloorWindow, Int.card_Icc, hneg]
  omega

/-- A selected dyadic block below the mollifier cutoff vanishes literally. -/
theorem arithmeticDetectorDyadicBlock_eq_zero_of_two_pow_le_mollifier
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {U N : ℕ} (hU : 1 ≤ U) (rho : ℂ) (Y : ℝ)
    (j : Fin (detectorDyadicCount N))
    (hbelow : 2 * 2 ^ (j : ℕ) ≤ U) :
    arithmeticDetectorDyadicBlock chi U N rho Y j = 0 := by
  classical
  unfold arithmeticDetectorDyadicBlock
  apply Finset.sum_eq_zero
  intro n hn
  rw [Finset.mem_filter] at hn
  have hnIco := Finset.mem_Ico.mp hn.1
  have hn2 : 2 ≤ n := by omega
  have hshell := (log2_sub_one_eq_iff_mem_Ioc hn2).mp hn.2
  have hnupper := (Finset.mem_Ioc.mp hshell).2
  omega

/-- Positivity of the detector threshold forces the selected shell above half
of the mollifier cutoff. -/
theorem mollifier_lt_two_pow_of_positive_selected_block
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {U N : ℕ} (hU : 1 ≤ U) {V : ℝ} (hV : 0 < V)
    (rho : ℂ) (Y : ℝ) (j : Fin (detectorDyadicCount N))
    (hlarge : V ≤ (detectorDyadicCount N : ℝ) *
      ‖arithmeticDetectorDyadicBlock chi U N rho Y j‖) :
    U < 2 * 2 ^ (j : ℕ) := by
  by_contra h
  have hzero := arithmeticDetectorDyadicBlock_eq_zero_of_two_pow_le_mollifier
    chi hU rho Y j (by omega)
  rw [hzero, norm_zero, mul_zero] at hlarge
  linarith

/-- The elementary dyadic-index upper bound used simultaneously for the
Fourier tail and the public polynomial length. -/
theorem two_pow_fin_detectorDyadicCount_le_sub_one
    {N : ℕ} (hN : 2 ≤ N) (j : Fin (detectorDyadicCount N)) :
    2 ^ (j : ℕ) ≤ N - 1 := by
  have hm : 0 < N - 1 := by omega
  apply (Nat.le_log2 (Nat.ne_of_gt hm)).mp
  have hj := j.isLt
  simp only [detectorDyadicCount] at hj
  omega

/-- The dyadic shell count is at most the arithmetic cutoff itself. -/
theorem detectorDyadicCount_le_self {N : ℕ} (hN : 1 ≤ N) :
    detectorDyadicCount N ≤ N := by
  unfold detectorDyadicCount
  by_cases hm0 : N - 1 = 0
  · simp [hm0]
    omega
  · have hlt : (N - 1).log2 < (N - 1) + 1 := by
      rw [Nat.log2_lt hm0]
      exact (Nat.lt_two_pow_self.trans_le
        (Nat.pow_le_pow_right (by omega) (Nat.le_succ (N - 1))))
    omega

/-! ## Fixed reserve parameters -/

def splitOutputKappa (loss : ℝ) : ℝ := min (loss / 1000) (1 / 1000)

def splitDetectorKappa (loss : ℝ) : ℝ := 2 * splitOutputKappa loss

def splitOutputEta (loss : ℝ) : ℝ := loss / 2

def splitDetectorEta (loss : ℝ) : ℝ :=
  splitOutputEta loss *
    ((powerCap (splitDetectorKappa loss) : ℝ) + 1) /
      (256 * ((powerCap (splitOutputKappa loss) : ℝ) + 1))

def splitSmallExponent (loss : ℝ) : ℝ :=
  min (inputLoss (splitOutputKappa loss) (splitOutputEta loss) / 1000)
    (1 / 1000)

def splitFourthEpsilon (loss : ℝ) : ℝ := min (loss / 1000) (1 / 1000)

theorem split_parameters_pos {loss : ℝ} (hloss : 0 < loss) :
    0 < splitOutputKappa loss ∧
    0 < splitDetectorKappa loss ∧
    0 < splitOutputEta loss ∧
    0 < splitDetectorEta loss ∧
    0 < splitSmallExponent loss ∧
    0 < splitFourthEpsilon loss := by
  have hkout : 0 < splitOutputKappa loss := by
    dsimp [splitOutputKappa]
    exact lt_min (by positivity) (by norm_num)
  have hkdet : 0 < splitDetectorKappa loss := by
    dsimp [splitDetectorKappa]
    positivity
  have heout : 0 < splitOutputEta loss := by
    dsimp [splitOutputEta]
    positivity
  have hpcOut : 0 < (powerCap (splitOutputKappa loss) : ℝ) + 1 := by
    positivity
  have hpcDet : 0 < (powerCap (splitDetectorKappa loss) : ℝ) + 1 := by
    positivity
  have hedet : 0 < splitDetectorEta loss := by
    dsimp [splitDetectorEta]
    positivity
  have hsmall : 0 < splitSmallExponent loss := by
    dsimp [splitSmallExponent]
    exact lt_min (div_pos (inputLoss_pos hkout heout) (by norm_num))
      (by norm_num)
  have hfourth : 0 < splitFourthEpsilon loss := by
    dsimp [splitFourthEpsilon]
    exact lt_min (by positivity) (by norm_num)
  exact ⟨hkout, hkdet, heout, hedet, hsmall, hfourth⟩

theorem split_output_kappa_ledger {loss : ℝ} (hloss : 0 < loss) :
    splitOutputKappa loss ≤ 1 / 2 ∧
    2 * splitOutputKappa loss ≤ loss ∧
    splitDetectorKappa loss < 1 / 20 := by
  have hkLoss : splitOutputKappa loss ≤ loss / 1000 :=
    min_le_left _ _
  have hkFixed : splitOutputKappa loss ≤ 1 / 1000 :=
    min_le_right _ _
  constructor
  · linarith
  constructor
  · nlinarith
  · dsimp [splitDetectorKappa]
    linarith

theorem split_inputLoss_relation (loss : ℝ) :
    inputLoss (splitDetectorKappa loss) (splitDetectorEta loss) =
      inputLoss (splitOutputKappa loss) (splitOutputEta loss) / 256 := by
  unfold splitDetectorEta inputLoss
  have hOut : (0 : ℝ) <
      (powerCap (splitOutputKappa loss) : ℝ) + 1 := by positivity
  have hDet : (0 : ℝ) <
      (powerCap (splitDetectorKappa loss) : ℝ) + 1 := by positivity
  field_simp

theorem inputLoss_le_eta_div_64
    {kappa eta : ℝ} (heta : 0 ≤ eta) :
    inputLoss kappa eta ≤ eta / 64 := by
  unfold inputLoss
  have hpc : (1 : ℝ) ≤ (powerCap kappa : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (powerCap kappa))
  have hden : 0 < 64 * ((powerCap kappa : ℝ) + 1) := by positivity
  exact div_le_div_of_nonneg_left heta (by norm_num) (by nlinarith)

/-- The fixed choices leave simultaneous reserves for the Type-I collar,
normalization, and direct Type-II fourth-moment ledgers. -/
theorem split_reserve_ledgers {loss : ℝ} (hloss : 0 < loss) :
    let kOut := splitOutputKappa loss
    let kDet := splitDetectorKappa loss
    let etaOut := splitOutputEta loss
    let etaDet := splitDetectorEta loss
    let dOut := inputLoss kOut etaOut
    let dDet := inputLoss kDet etaDet
    let a := splitSmallExponent loss
    let eps := splitFourthEpsilon loss
    6 * a ≤ etaOut ∧
    4 * a ≤ dOut - dDet ∧
    2 * kDet + 4 * dDet + eps + a * (5 + eps) ≤
      2 * kOut + etaOut := by
  dsimp only
  have hp := split_parameters_pos hloss
  have hetaOut : 0 < splitOutputEta loss := hp.2.2.1
  have hdOut : 0 < inputLoss (splitOutputKappa loss)
      (splitOutputEta loss) := inputLoss_pos hp.1 hetaOut
  have hdDetEq := split_inputLoss_relation loss
  have hdOutUpper := inputLoss_le_eta_div_64
    (kappa := splitOutputKappa loss) hetaOut.le
  have haOut : splitSmallExponent loss ≤
      inputLoss (splitOutputKappa loss) (splitOutputEta loss) / 1000 :=
    min_le_left _ _
  have haFixed : splitSmallExponent loss ≤ 1 / 1000 := min_le_right _ _
  have hepsLoss : splitFourthEpsilon loss ≤ loss / 1000 := min_le_left _ _
  have hepsFixed : splitFourthEpsilon loss ≤ 1 / 1000 := min_le_right _ _
  have hkLoss : splitOutputKappa loss ≤ loss / 1000 := min_le_left _ _
  have haPos := hp.2.2.2.2.1
  have hepsPos := hp.2.2.2.2.2
  have haLoss : splitSmallExponent loss ≤
      (loss / 2 / 64) / 1000 :=
    haOut.trans (div_le_div_of_nonneg_right (by
      simpa [splitOutputEta] using hdOutUpper) (by norm_num))
  have hdLoss : inputLoss (splitOutputKappa loss)
      (splitOutputEta loss) ≤ loss / 128 := by
    convert hdOutUpper using 1 <;> simp [splitOutputEta] <;> ring
  have haLoss' : splitSmallExponent loss ≤ loss / 128 / 1000 := by
    convert haLoss using 1 <;> ring
  rw [hdDetEq]
  constructor
  · dsimp [splitOutputEta] at hdOutUpper ⊢
    nlinarith
  constructor
  · nlinarith
  · dsimp [splitDetectorKappa, splitOutputEta]
    have haeps : splitSmallExponent loss *
        splitFourthEpsilon loss ≤ splitSmallExponent loss / 1000 := by
      nlinarith
    have haepsLoss : splitSmallExponent loss * splitFourthEpsilon loss ≤
        loss / 128 / 1000 / 1000 := by
      exact haeps.trans (div_le_div_of_nonneg_right haLoss' (by norm_num))
    have hdDetLoss :
        inputLoss (splitOutputKappa loss) (splitOutputEta loss) / 256 ≤
          loss / 128 / 256 := by
      exact div_le_div_of_nonneg_right hdLoss (by norm_num)
    have hfiveA : 5 * splitSmallExponent loss ≤
        5 * (loss / 128 / 1000) := by linarith
    dsimp [splitOutputEta] at hdDetLoss hdLoss haLoss' haepsLoss
    linarith

/-! ## Uniform subpower bookkeeping -/

/-- A fixed nonnegative constant times one fixed power of `log T` is absorbed
by any prescribed positive power of `T`. -/
theorem eventually_const_mul_polylog_le_rpow
    (C K a : ℝ) (hC : 0 ≤ C) (ha : 0 < a) :
    ∀ᶠ T : ℝ in Filter.atTop,
      C * Real.rpow (Real.log T) K ≤ Real.rpow T a := by
  have hpoly := ZeroDensityArithmetic.polylog_absorption K (a / 2) (by
    positivity)
  have hconst := (tendsto_rpow_atTop (by positivity : 0 < a / 2)).eventually
    (eventually_ge_atTop C)
  filter_upwards [hpoly, hconst, eventually_ge_atTop 1] with T hpolyT hconstT hT
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  calc
    C * Real.rpow (Real.log T) K ≤
        Real.rpow T (a / 2) * Real.rpow T (a / 2) :=
      mul_le_mul hconstT hpolyT
        (Real.rpow_nonneg (Real.log_nonneg hT) _)
        (Real.rpow_nonneg (zero_le_one.trans hT) _)
    _ = Real.rpow T a := by
      calc
        Real.rpow T (a / 2) * Real.rpow T (a / 2) =
            Real.rpow T (a / 2 + a / 2) :=
          (Real.rpow_add hTpos _ _).symm
        _ = Real.rpow T a := by congr 1 <;> ring

def crowdingLinearConstant : ℝ :=
  (Real.log 3 + Real.log 3200 + 2 * Real.log 4 + 4) /
    Real.log (17 / 16)

theorem crowdingLinearConstant_pos : 0 < crowdingLinearConstant := by
  unfold crowdingLinearConstant
  apply div_pos
  · have h3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
    have h3200 := Real.log_pos (by norm_num : (1 : ℝ) < 3200)
    have h4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
    linarith
  · exact Real.log_pos (by norm_num)

/-- The natural A.5 multiplicity/crowding cap is uniformly subpower in a
polylogarithmic conductor range. -/
theorem eventually_crowdingNatCap_le_rpow
    (K a : ℝ) (ha : 0 < a) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ (q : ℕ) [NeZero q],
        (q : ℝ) ≤ Real.rpow (Real.log T) K →
        (certifiedA5CrowdingNatCap q T : ℝ) ≤ Real.rpow T a := by
  have hqpower := ZeroDensityArithmetic.polylog_absorption K 1 (by norm_num)
  have hcapPower := eventually_const_mul_polylog_le_rpow
    (crowdingLinearConstant + 1) 1 a
    (by have := crowdingLinearConstant_pos; positivity) ha
  filter_upwards [hqpower, hcapPower, eventually_ge_atTop (Real.exp 1),
    eventually_ge_atTop 3] with T hqpowerT hcapPowerT hTexp hTthree
  intro q _inst hq
  have hT : 1 ≤ T := by linarith
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hlog : 1 ≤ Real.log T := by
    rw [← Real.exp_le_exp]
    simpa [Real.exp_log hTpos] using hTexp
  have hqT : (q : ℝ) ≤ T := hq.trans (by
    simpa [Real.rpow_one] using hqpowerT)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hscalePos : 0 < (q : ℝ) * (T + 3) := by positivity
  have hscale : (q : ℝ) * (T + 3) ≤ 4 * T ^ 2 := by
    calc
      (q : ℝ) * (T + 3) ≤ T * (T + 3) := by
        exact mul_le_mul_of_nonneg_right hqT (by linarith)
      _ ≤ T * (4 * T) := by gcongr <;> linarith
      _ = 4 * T ^ 2 := by ring
  have htargetPos : 0 < 4 * T ^ 2 := by positivity
  have hlogScale : Real.log ((q : ℝ) * (T + 3)) ≤
      Real.log 4 + 2 * Real.log T := by
    calc
      Real.log ((q : ℝ) * (T + 3)) ≤ Real.log (4 * T ^ 2) :=
        Real.log_le_log hscalePos hscale
      _ = Real.log 4 + 2 * Real.log T := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        norm_num
  have henv0 : 0 ≤ certifiedA5CrowdingEnvelope q T := by
    unfold certifiedA5CrowdingEnvelope
    apply div_nonneg
    · have h3 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
      have h3200 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3200)
      have hs := Real.log_nonneg (by
        have hqone : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
        exact one_le_mul_of_one_le_of_one_le hqone
          (show (1 : ℝ) ≤ T + 3 by linarith))
      linarith
    · exact Real.log_nonneg (by norm_num)
  have henv : certifiedA5CrowdingEnvelope q T ≤
      crowdingLinearConstant * Real.log T := by
    unfold certifiedA5CrowdingEnvelope crowdingLinearConstant
    have hden : 0 < Real.log (17 / 16 : ℝ) := Real.log_pos (by norm_num)
    rw [div_mul_eq_mul_div]
    apply (div_le_div_iff_of_pos_right hden).2
    nlinarith [mul_nonneg
      (show 0 ≤ Real.log 3 + Real.log 3200 + 2 * Real.log 4 by
        positivity)
      (sub_nonneg.mpr hlog)]
  have hceil := Nat.ceil_lt_add_one (show
    0 ≤ max 0 (certifiedA5CrowdingEnvelope q T) by positivity)
  have hcapLinear : (certifiedA5CrowdingNatCap q T : ℝ) ≤
      (crowdingLinearConstant + 1) * Real.log T := by
    unfold certifiedA5CrowdingNatCap
    rw [max_eq_right henv0]
    rw [max_eq_right henv0] at hceil
    calc
      (⌈certifiedA5CrowdingEnvelope q T⌉₊ : ℝ) ≤
          certifiedA5CrowdingEnvelope q T + 1 := hceil.le
      _ ≤ crowdingLinearConstant * Real.log T + 1 := by linarith
      _ ≤ (crowdingLinearConstant + 1) * Real.log T := by
        nlinarith
  exact hcapLinear.trans (by simpa [Real.rpow_one] using hcapPowerT)

theorem eventually_longSpacingColorCount_le_rpow
    (a : ℝ) (ha : 0 < a) :
    ∀ᶠ T : ℝ in Filter.atTop,
      (longSpacingColorCount (detectorVerticalCutoff T) : ℝ) ≤
        Real.rpow T a := by
  have hpoly := eventually_const_mul_polylog_le_rpow 5 2 a
    (by norm_num) ha
  filter_upwards [hpoly, eventually_ge_atTop (Real.exp 1)]
    with T hpolyT hTexp
  have hTpos : 0 < T := lt_of_lt_of_le (Real.exp_pos 1) hTexp
  have hlog : 1 ≤ Real.log T := by
    rw [← Real.exp_le_exp]
    simpa [Real.exp_log hTpos] using hTexp
  have hceil := Nat.ceil_lt_add_one
    (show 0 ≤ 3 * detectorVerticalCutoff T + 1 by
      unfold detectorVerticalCutoff
      positivity)
  unfold longSpacingColorCount at hceil ⊢
  calc
    (⌈3 * detectorVerticalCutoff T + 1⌉₊ : ℝ) ≤
        3 * detectorVerticalCutoff T + 2 := by
      convert hceil.le using 1 <;> ring
    _ ≤ 5 * Real.rpow (Real.log T) 2 := by
      unfold detectorVerticalCutoff
      rw [show Real.rpow (Real.log T) 2 = (Real.log T) ^ 2 by
        norm_num [Real.rpow_natCast]]
      nlinarith [sq_nonneg (Real.log T - 1)]
    _ ≤ Real.rpow T a := hpolyT

def dyadicLinearConstant : ℝ :=
  (Real.log 2 + 1) / Real.log 2 + 1

theorem dyadicLinearConstant_pos : 0 < dyadicLinearConstant := by
  unfold dyadicLinearConstant
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- At the paper cutoff `ceil(T^(1/2)(log T)^2)`, the number of dyadic
blocks is uniformly subpower. -/
theorem eventually_project_detectorDyadicCount_le_rpow
    (a : ℝ) (ha : 0 < a) :
    ∀ᶠ T : ℝ in Filter.atTop,
      (detectorDyadicCount (detectorArithmeticCutoff
        (Real.rpow T (1 / 2)) T) : ℝ) ≤ Real.rpow T a := by
  have hlogSq := ZeroDensityArithmetic.polylog_absorption 2 (1 / 2)
    (by norm_num)
  have hpoly := eventually_const_mul_polylog_le_rpow
    dyadicLinearConstant 1 a dyadicLinearConstant_pos.le ha
  filter_upwards [hlogSq, hpoly, eventually_ge_atTop (Real.exp 1),
    eventually_ge_atTop 2] with T hlogSqT hpolyT hTexp hTtwo
  have hT : 1 ≤ T := by linarith
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hlog : 1 ≤ Real.log T := by
    rw [← Real.exp_le_exp]
    simpa [Real.exp_log hTpos] using hTexp
  let x : ℝ := Real.rpow T (1 / 2) * (Real.log T) ^ 2
  let N : ℕ := detectorArithmeticCutoff (Real.rpow T (1 / 2)) T
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxT : x ≤ T := by
    dsimp [x]
    have hhalf : Real.rpow T (1 / 2) * Real.rpow T (1 / 2) = T := by
      calc
        Real.rpow T (1 / 2) * Real.rpow T (1 / 2) =
            Real.rpow T (1 / 2 + 1 / 2) :=
          (Real.rpow_add hTpos _ _).symm
        _ = T := by norm_num [Real.rpow_one]
    calc
      Real.rpow T (1 / 2) * (Real.log T) ^ 2 ≤
          Real.rpow T (1 / 2) * Real.rpow T (1 / 2) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa [Real.rpow_natCast] using hlogSqT)
          (Real.rpow_nonneg (zero_le_one.trans hT) _)
      _ = T := hhalf
  have hNupper : (N : ℝ) ≤ 2 * T := by
    have hceil : (N : ℝ) < x + 1 := by
      dsimp [N, detectorArithmeticCutoff, x]
      exact Nat.ceil_lt_add_one hx0
    exact hceil.le.trans (by linarith)
  have hNpos : 1 ≤ N := by
    have hxone : 1 ≤ x := by
      dsimp [x]
      have hhalfOne : 1 ≤ Real.rpow T (1 / 2) :=
        Real.one_le_rpow hT (by norm_num)
      have hlogSqOne : 1 ≤ (Real.log T) ^ 2 := by nlinarith
      exact one_le_mul_of_one_le_of_one_le hhalfOne hlogSqOne
    have hceil : x ≤ (N : ℝ) := by
      dsimp [N, detectorArithmeticCutoff, x]
      exact Nat.le_ceil _
    exact_mod_cast hxone.trans hceil
  have hJlinear : (detectorDyadicCount N : ℝ) ≤
      dyadicLinearConstant * Real.log T := by
    by_cases hN1 : N = 1
    · simp [detectorDyadicCount, hN1]
      unfold dyadicLinearConstant
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hratio : 0 < (Real.log 2 + 1) / Real.log 2 :=
        div_pos (by linarith) hlog2
      nlinarith
    · have hmNat : 0 < N - 1 := by omega
      have hmR : (0 : ℝ) < N - 1 := by exact_mod_cast hmNat
      have hmUpper : ((N - 1 : ℕ) : ℝ) ≤ 2 * T := by
        have hsub : N - 1 ≤ N := Nat.sub_le N 1
        exact (by exact_mod_cast hsub :
          ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ)).trans hNupper
      have hlogb := Real.log2_le_logb (N - 1)
      have hlogbMono : Real.logb 2 ((N - 1 : ℕ) : ℝ) ≤
          Real.logb 2 (2 * T) :=
        (Real.logb_le_logb (b := 2) (by norm_num) (by
          exact_mod_cast hmNat) (by positivity)).2 hmUpper
      have hlogbEval : Real.logb 2 (2 * T) =
          (Real.log 2 + Real.log T) / Real.log 2 := by
        unfold Real.logb
        rw [Real.log_mul (by norm_num) hTpos.ne']
      unfold detectorDyadicCount dyadicLinearConstant
      push_cast
      rw [hlogbEval] at hlogbMono
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have heval : (Real.log 2 + Real.log T) / Real.log 2 =
          1 + Real.log T / Real.log 2 := by
        field_simp
      rw [heval] at hlogbMono
      have hconst : (Real.log 2 + 1) / Real.log 2 + 1 =
          2 + 1 / Real.log 2 := by
        field_simp
        ring
      rw [hconst]
      have hlogPos : 0 < Real.log T := by linarith
      have hlogNat := hlogb.trans hlogbMono
      have hdivEq : Real.log T / Real.log 2 =
          (1 / Real.log 2) * Real.log T := by ring
      rw [hdivEq] at hlogNat
      nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (sub_nonneg.mpr hlog)]
  change (detectorDyadicCount N : ℝ) ≤ Real.rpow T a
  exact hJlinear.trans (by simpa [Real.rpow_one] using hpolyT)

/-- Exact eventual Type-I multiplicity, dyadic, and collar ledger. -/
theorem eventually_typeI_project_cost_le
    (K h a : ℝ) (hh : 0 < h) (ha : 0 < a) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ (q : ℕ) [NeZero q],
        (q : ℝ) ≤ Real.rpow (Real.log T) K →
        let C : ℕ := ⌈2 * Real.pi * Real.rpow T h⌉₊
        let P : ℕ := longSpacingColorCount (detectorVerticalCutoff T) *
          certifiedA5CrowdingNatCap q T ^ 2
        ((P * detectorDyadicCount (detectorArithmeticCutoff
          (Real.rpow T (1 / 2)) T) *
          (4 * shiftedFloorWindowCount (C : ℝ) + 2 * (C + 1)) : ℕ) : ℝ) ≤
          Real.rpow T (h + 5 * a) := by
  have hcolor := eventually_longSpacingColorCount_le_rpow a ha
  have hcap := eventually_crowdingNatCap_le_rpow K a ha
  have hJ := eventually_project_detectorDyadicCount_le_rpow a ha
  have hconst := eventually_const_mul_polylog_le_rpow
    (20 * Real.pi + 20) 0 a (by nlinarith [Real.pi_pos.le]) ha
  filter_upwards [hcolor, hcap, hJ, hconst, eventually_ge_atTop 1]
    with T hcolorT hcapT hJT hconstT hT
  intro q _inst hq
  let C : ℕ := ⌈2 * Real.pi * Real.rpow T h⌉₊
  let P : ℕ := longSpacingColorCount (detectorVerticalCutoff T) *
    certifiedA5CrowdingNatCap q T ^ 2
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hcapq := hcapT q hq
  have hCceil := Nat.ceil_lt_add_one
    (show 0 ≤ 2 * Real.pi * Real.rpow T h by
      exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
        (Real.rpow_nonneg (zero_le_one.trans hT) _))
  have hThOne : 1 ≤ Real.rpow T h := Real.one_le_rpow hT hh.le
  have hCcast : (C : ℝ) ≤ (2 * Real.pi + 1) * Real.rpow T h := by
    dsimp [C]
    calc
      (⌈2 * Real.pi * Real.rpow T h⌉₊ : ℝ) ≤
          2 * Real.pi * Real.rpow T h + 1 := hCceil.le
      _ ≤ (2 * Real.pi + 1) * Real.rpow T h := by nlinarith
  have hbase : ((4 * shiftedFloorWindowCount (C : ℝ) +
      2 * (C + 1) : ℕ) : ℝ) ≤
      (20 * Real.pi + 20) * Real.rpow T h := by
    rw [shiftedFloorWindowCount_natCast]
    push_cast
    nlinarith
  have hconstT' : 20 * Real.pi + 20 ≤ Real.rpow T a := by
    simpa [Real.rpow_zero, mul_one] using hconstT
  have hbasePow : ((4 * shiftedFloorWindowCount (C : ℝ) +
      2 * (C + 1) : ℕ) : ℝ) ≤ Real.rpow T (h + a) := by
    calc
      ((4 * shiftedFloorWindowCount (C : ℝ) +
        2 * (C + 1) : ℕ) : ℝ) ≤
          (20 * Real.pi + 20) * Real.rpow T h := hbase
      _ ≤ Real.rpow T a * Real.rpow T h := by
        gcongr
      _ = Real.rpow T (h + a) := by
        calc
          Real.rpow T a * Real.rpow T h = Real.rpow T (a + h) :=
            (Real.rpow_add hTpos _ _).symm
          _ = Real.rpow T (h + a) := by congr 1 <;> ring
  have hPpow : (P : ℝ) ≤ Real.rpow T (3 * a) := by
    dsimp [P]
    push_cast
    calc
      (longSpacingColorCount (detectorVerticalCutoff T) : ℝ) *
          (certifiedA5CrowdingNatCap q T : ℝ) ^ 2 ≤
          Real.rpow T a * (Real.rpow T a) ^ 2 := by
        have hcapSq : (certifiedA5CrowdingNatCap q T : ℝ) ^ 2 ≤
            (Real.rpow T a) ^ 2 := by nlinarith
        exact mul_le_mul hcolorT hcapSq (by positivity)
          (Real.rpow_nonneg (zero_le_one.trans hT) _)
      _ = Real.rpow T (3 * a) := by
        calc
          Real.rpow T a * (Real.rpow T a) ^ 2 =
          Real.rpow T a * (Real.rpow T a * Real.rpow T a) := by ring
          _ = Real.rpow T a * Real.rpow T (a + a) := by
            exact congrArg (fun z : ℝ => Real.rpow T a * z)
              (Real.rpow_add hTpos a a).symm
          _ = Real.rpow T (a + (a + a)) :=
            (Real.rpow_add hTpos _ _).symm
          _ = Real.rpow T (3 * a) := by congr 1 <;> ring
  have hPJ : (P : ℝ) * detectorDyadicCount
      (detectorArithmeticCutoff (Real.rpow T (1 / 2)) T) ≤
      Real.rpow T (3 * a) * Real.rpow T a :=
    mul_le_mul hPpow hJT (Nat.cast_nonneg _)
      (Real.rpow_nonneg (zero_le_one.trans hT) _)
  have hmul : (P : ℝ) * detectorDyadicCount
      (detectorArithmeticCutoff (Real.rpow T (1 / 2)) T) *
      ((4 * shiftedFloorWindowCount (C : ℝ) + 2 * (C + 1) : ℕ) : ℝ) ≤
      Real.rpow T (3 * a) * Real.rpow T a * Real.rpow T (h + a) :=
    mul_le_mul hPJ hbasePow (Nat.cast_nonneg _)
      (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hT) _)
        (Real.rpow_nonneg (zero_le_one.trans hT) _))
  have hpowEq : Real.rpow T (3 * a) * Real.rpow T a *
      Real.rpow T (h + a) = Real.rpow T (h + 5 * a) := by
    calc
      Real.rpow T (3 * a) * Real.rpow T a * Real.rpow T (h + a) =
          Real.rpow T (3 * a + a) * Real.rpow T (h + a) := by
        exact congrArg (fun z : ℝ => z * Real.rpow T (h + a))
          (Real.rpow_add hTpos (3 * a) a).symm
      _ = Real.rpow T ((3 * a + a) + (h + a)) :=
        (Real.rpow_add hTpos _ _).symm
      _ = Real.rpow T (h + 5 * a) := by congr 1 <;> ring
  exact (by simpa [P, C] using hmul.trans_eq hpowEq)

/-- Eventual normalization reserve for every selected shell `D≤T`. -/
theorem eventually_typeI_normalization_cost_le
    (Kd e h a gap : ℝ) (hKd : 0 < Kd) (he : 0 < e)
    (hh : 0 < h) (ha : 0 < a) (hledger : h + e + 2 * a ≤ gap) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ D J : ℝ, 1 ≤ T → 0 < D → D ≤ T → 0 ≤ J →
        J ≤ Real.rpow T a →
        96 * Real.rpow T h * J * Kd * Real.rpow (2 * D) e ≤
          Real.rpow T gap := by
  have hconst := eventually_const_mul_polylog_le_rpow
    (96 * Kd * Real.rpow 2 e) 0 a
      (mul_nonneg (mul_nonneg (by norm_num) hKd.le)
        (Real.rpow_nonneg (by norm_num) _)) ha
  filter_upwards [hconst, eventually_ge_atTop 1] with T hconstT hT
  intro D J hTone hDpos hDT hJ0 hJ
  have hTpos : 0 < T := zero_lt_one.trans_le hTone
  have hconstT' : 96 * Kd * Real.rpow 2 e ≤ Real.rpow T a := by
    simpa [Real.rpow_zero, mul_one] using hconstT
  have htwo : Real.rpow (2 * D) e = Real.rpow 2 e * Real.rpow D e :=
    Real.mul_rpow (by norm_num) hDpos.le
  have hDpow : Real.rpow D e ≤ Real.rpow T e :=
    Real.rpow_le_rpow hDpos.le hDT he.le
  have hraw : 96 * Real.rpow T h * J * Kd * Real.rpow (2 * D) e ≤
      Real.rpow T h * Real.rpow T a * Real.rpow T a * Real.rpow T e := by
    rw [htwo]
    calc
      96 * Real.rpow T h * J * Kd *
          (Real.rpow 2 e * Real.rpow D e) =
          Real.rpow T h * J * (96 * Kd * Real.rpow 2 e) *
            Real.rpow D e := by ring
      _ ≤ Real.rpow T h * Real.rpow T a * Real.rpow T a *
          Real.rpow T e := by
        have hTh0 := Real.rpow_nonneg (zero_le_one.trans hTone) h
        have hTa0 := Real.rpow_nonneg (zero_le_one.trans hTone) a
        have hAJ : Real.rpow T h * J ≤
            Real.rpow T h * Real.rpow T a :=
          mul_le_mul_of_nonneg_left hJ hTh0
        have hAJC : Real.rpow T h * J *
            (96 * Kd * Real.rpow 2 e) ≤
            (Real.rpow T h * Real.rpow T a) * Real.rpow T a :=
          mul_le_mul hAJ hconstT'
            (mul_nonneg (mul_nonneg (by norm_num) hKd.le)
              (Real.rpow_nonneg (by norm_num) _))
            (mul_nonneg hTh0 hTa0)
        exact mul_le_mul hAJC hDpow (Real.rpow_nonneg hDpos.le _)
          (mul_nonneg (mul_nonneg hTh0 hTa0) hTa0)
  have hpowEq : Real.rpow T h * Real.rpow T a * Real.rpow T a *
      Real.rpow T e = Real.rpow T (h + e + 2 * a) := by
    calc
      Real.rpow T h * Real.rpow T a * Real.rpow T a * Real.rpow T e =
          ((Real.rpow T h * Real.rpow T a) * Real.rpow T a) *
            Real.rpow T e := by ring
      _ = (Real.rpow T (h + a) * Real.rpow T a) * Real.rpow T e := by
        exact congrArg (fun z : ℝ => (z * Real.rpow T a) * Real.rpow T e)
          (Real.rpow_add hTpos h a).symm
      _ = Real.rpow T ((h + a) + a) * Real.rpow T e := by
        exact congrArg (fun z : ℝ => z * Real.rpow T e)
          (Real.rpow_add hTpos (h + a) a).symm
      _ = Real.rpow T (((h + a) + a) + e) :=
        (Real.rpow_add hTpos _ _).symm
      _ = Real.rpow T (h + e + 2 * a) := by congr 1 <;> ring
  exact hraw.trans_eq hpowEq |>.trans
    (Real.rpow_le_rpow_of_exponent_le hTone hledger)

/-- Direct source-normalized Type-II ledger.  The exact denominator from the
detector is retained; only the stated subpower bounds are used. -/
theorem eventually_typeII_source_ledger
    (Cfourth eps kDet dDet kOut eta a : ℝ)
    (hC : 0 < Cfourth) (heps : 0 < eps) (hkDet : 0 < kDet)
    (hdDet : 0 < dDet) (hkOut : 0 < kOut) (heta : 0 < eta)
    (ha : 0 < a)
    (hledger : 2 * kDet + 4 * dDet + eps + a * (5 + eps) ≤
      2 * kOut + eta) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ (P r U : ℕ) (sigma : ℝ),
        1 ≤ T → 1 ≤ U →
        (P : ℝ) ≤ Real.rpow T (3 * a) →
        (r : ℝ) ≤ Real.rpow T a →
        (U : ℝ) ≤ Real.rpow T kDet →
        7 / 10 ≤ sigma → sigma ≤ 4 / 5 →
        (P : ℝ) *
          ((Cfourth * Real.rpow ((r : ℝ) * (2 * T)) (1 + eps)) /
            (Real.rpow T (-dDet) /
              (29 * Real.rpow (Real.rpow T (1 / 2)) (1 / 2 - sigma) *
                (2 * Real.sqrt U))) ^ 4) ≤
          Real.rpow T (2 * (1 - sigma) + 2 * kOut + eta) := by
  let C0 : ℝ := Cfourth * Real.rpow 2 (1 + eps) * 29 ^ 4 * 16
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hconst := eventually_const_mul_polylog_le_rpow C0 0 a hC0 ha
  filter_upwards [hconst, eventually_ge_atTop 1] with T hconstT hTone
  intro P r U sigma hT hU hP hr hUupper hsigmaLow hsigmaHigh
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hUpos : (0 : ℝ) < U := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hU)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hconstT' : C0 ≤ Real.rpow T a := by
    simpa [Real.rpow_zero, mul_one] using hconstT
  have hrexp : 0 ≤ 1 + eps := by linarith
  have hrpow : Real.rpow (r : ℝ) (1 + eps) ≤
      Real.rpow T (a * (1 + eps)) := by
    have h := Real.rpow_le_rpow hr0 hr hrexp
    exact h.trans_eq (Real.rpow_mul (zero_le_one.trans hT) a (1 + eps)).symm
  have hUpow : ((U : ℝ) ^ 2) ≤ Real.rpow T (2 * kDet) := by
    have hsquare : ((U : ℝ) ^ 2) ≤ (Real.rpow T kDet) ^ 2 := by
      nlinarith
    calc
      ((U : ℝ) ^ 2) ≤ (Real.rpow T kDet) ^ 2 := hsquare
      _ = Real.rpow T (2 * kDet) := by
        rw [show (Real.rpow T kDet) ^ 2 =
          Real.rpow T kDet * Real.rpow T kDet by ring]
        calc
          Real.rpow T kDet * Real.rpow T kDet =
              Real.rpow T (kDet + kDet) :=
            (Real.rpow_add hTpos _ _).symm
          _ = Real.rpow T (2 * kDet) := by congr 1 <;> ring
  have hYpow : (Real.rpow (Real.rpow T (1 / 2))
      (1 / 2 - sigma)) ^ 4 = Real.rpow T (1 - 2 * sigma) := by
    calc
      (Real.rpow (Real.rpow T (1 / 2)) (1 / 2 - sigma)) ^ 4 =
          Real.rpow (Real.rpow T (1 / 2)) (1 / 2 - sigma) ^ (4 : ℝ) := by
        exact (Real.rpow_natCast _ 4).symm
      _ = Real.rpow (Real.rpow T (1 / 2)) ((1 / 2 - sigma) * 4) :=
        (Real.rpow_mul (Real.rpow_nonneg (zero_le_one.trans hT) _)
          (1 / 2 - sigma) 4).symm
      _ = Real.rpow T ((1 / 2) * ((1 / 2 - sigma) * 4)) :=
        (Real.rpow_mul (zero_le_one.trans hT) (1 / 2)
          ((1 / 2 - sigma) * 4)).symm
      _ = Real.rpow T (1 - 2 * sigma) := by congr 1 <;> ring
  have hsqrt : (2 * Real.sqrt U) ^ 4 = 16 * (U : ℝ) ^ 2 := by
    have hsqrtSq : (Real.sqrt (U : ℝ)) ^ 2 = U :=
      Real.sq_sqrt (Nat.cast_nonneg _)
    nlinarith
  have hVinv : (Real.rpow T (-dDet)) ^ 4 = Real.rpow T (-4 * dDet) := by
    calc
      (Real.rpow T (-dDet)) ^ 4 =
          Real.rpow (Real.rpow T (-dDet)) (4 : ℝ) := by
        exact (Real.rpow_natCast _ 4).symm
      _ = Real.rpow T ((-dDet) * 4) :=
        (Real.rpow_mul (zero_le_one.trans hT) (-dDet) 4).symm
      _ = Real.rpow T (-4 * dDet) := by congr 1 <;> ring
  have hsourceEq :
      (P : ℝ) *
          ((Cfourth * Real.rpow ((r : ℝ) * (2 * T)) (1 + eps)) /
            (Real.rpow T (-dDet) /
              (29 * Real.rpow (Real.rpow T (1 / 2)) (1 / 2 - sigma) *
                (2 * Real.sqrt U))) ^ 4) =
        (P : ℝ) * C0 * Real.rpow (r : ℝ) (1 + eps) *
          Real.rpow T (1 + eps) * Real.rpow T (1 - 2 * sigma) *
          ((U : ℝ) ^ 2) * Real.rpow T (4 * dDet) := by
    have hdenpos : 0 < 29 * Real.rpow (Real.rpow T (1 / 2))
        (1 / 2 - sigma) * (2 * Real.sqrt U) := by
      exact mul_pos
        (mul_pos (by norm_num) (Real.rpow_pos_of_pos
          (Real.rpow_pos_of_pos hTpos _) _))
        (mul_pos (by norm_num) (Real.sqrt_pos.2 hUpos))
    have hVpos : 0 < Real.rpow T (-dDet) := Real.rpow_pos_of_pos hTpos _
    have hRT : Real.rpow ((r : ℝ) * (2 * T)) (1 + eps) =
        Real.rpow (r : ℝ) (1 + eps) * Real.rpow 2 (1 + eps) *
          Real.rpow T (1 + eps) := by
      calc
        Real.rpow ((r : ℝ) * (2 * T)) (1 + eps) =
        Real.rpow (r : ℝ) (1 + eps) *
              Real.rpow (2 * T) (1 + eps) :=
          Real.mul_rpow hr0 (by positivity)
        _ = Real.rpow (r : ℝ) (1 + eps) *
            (Real.rpow 2 (1 + eps) * Real.rpow T (1 + eps)) := by
          exact congrArg (fun z : ℝ => Real.rpow (r : ℝ) (1 + eps) * z)
            (Real.mul_rpow (by norm_num) hTpos.le)
        _ = _ := by ring
    rw [hRT]
    rw [div_pow]
    rw [show (29 * Real.rpow (Real.rpow T (1 / 2))
        (1 / 2 - sigma) * (2 * Real.sqrt U)) ^ 4 =
      29 ^ 4 * (Real.rpow (Real.rpow T (1 / 2))
        (1 / 2 - sigma)) ^ 4 * (2 * Real.sqrt U) ^ 4 by ring]
    rw [hYpow, hsqrt, hVinv]
    dsimp [C0]
    have hcancel : Real.rpow T (-4 * dDet) * Real.rpow T (4 * dDet) = 1 := by
      calc
        Real.rpow T (-4 * dDet) * Real.rpow T (4 * dDet) =
            Real.rpow T ((-4 * dDet) + 4 * dDet) :=
          (Real.rpow_add hTpos _ _).symm
        _ = 1 := by simp
    field_simp
    ring_nf at hcancel ⊢
    change (P : ℝ) * Real.rpow (r : ℝ) (1 + eps) =
      (P : ℝ) * Real.rpow (r : ℝ) (1 + eps) *
        Real.rpow T (-(dDet * 4)) * Real.rpow T (dDet * 4)
    calc
      (P : ℝ) * Real.rpow (r : ℝ) (1 + eps) =
          (P : ℝ) * Real.rpow (r : ℝ) (1 + eps) * 1 := by ring
      _ = (P : ℝ) * Real.rpow (r : ℝ) (1 + eps) *
          (Real.rpow T (-(dDet * 4)) * Real.rpow T (dDet * 4)) := by
        rw [hcancel]
      _ = _ := by ring
  rw [hsourceEq]
  have hraw :
      (P : ℝ) * C0 * Real.rpow (r : ℝ) (1 + eps) *
          Real.rpow T (1 + eps) * Real.rpow T (1 - 2 * sigma) *
          ((U : ℝ) ^ 2) * Real.rpow T (4 * dDet) ≤
        Real.rpow T (3 * a) * Real.rpow T a *
          Real.rpow T (a * (1 + eps)) * Real.rpow T (1 + eps) *
          Real.rpow T (1 - 2 * sigma) * Real.rpow T (2 * kDet) *
          Real.rpow T (4 * dDet) := by
    gcongr
    all_goals
      repeat' apply mul_nonneg
      all_goals first
        | exact Real.rpow_nonneg hTpos.le _
        | exact Real.rpow_nonneg hr0 _
        | positivity
  have hpowEq :
      Real.rpow T (3 * a) * Real.rpow T a *
          Real.rpow T (a * (1 + eps)) * Real.rpow T (1 + eps) *
          Real.rpow T (1 - 2 * sigma) * Real.rpow T (2 * kDet) *
          Real.rpow T (4 * dDet) =
        Real.rpow T (2 * (1 - sigma) + 2 * kDet + 4 * dDet + eps +
          a * (5 + eps)) := by
    have hadd : ∀ x y : ℝ,
        Real.rpow T x * Real.rpow T y = Real.rpow T (x + y) :=
      fun x y => (Real.rpow_add hTpos x y).symm
    repeat' rw [hadd]
    congr 1
    ring
  exact hraw.trans_eq hpowEq |>.trans
    (Real.rpow_le_rpow_of_exponent_le hT (by linarith))

/-! ## Project-scale geometry -/

/-- All floor, ceiling, dyadic-shell, and collar inequalities at the literal
paper scales, packaged independently of the analytic detector inputs. -/
theorem eventually_project_scale_geometry
    (kOut kDet h : ℝ) (hkOut : 0 < kOut)
    (hkRel : kDet = 2 * kOut) (hkDetHalf : kDet ≤ 1 / 2)
    (hh : 0 < h) :
    ∀ᶠ T : ℝ in Filter.atTop,
      let U : ℕ := ⌊Real.rpow T kDet⌋₊
      let Y : ℝ := Real.rpow T (1 / 2)
      let N : ℕ := detectorArithmeticCutoff Y T
      let B : ℝ := detectorVerticalCutoff T
      let C : ℕ := ⌈2 * Real.pi * Real.rpow T h⌉₊
      4 ≤ T ∧ 1 ≤ U ∧ 2 * Real.rpow T kOut ≤ U ∧
      (U : ℝ) ≤ Y * (Real.log T) ^ 2 ∧ U ≤ N ∧
      1 ≤ B ∧ 2 ≤ N ∧
      (∀ j : Fin (detectorDyadicCount N),
        ((2 ^ (j : ℕ) : ℕ) : ℝ) ≤ T) ∧
      (∀ j : Fin (detectorDyadicCount N),
        ((2 ^ (j : ℕ) : ℕ) : ℝ) ≤ Y * (Real.log T) ^ 2) ∧
      (detectorDyadicCount N : ℝ) ≤ 2 * T ∧
      2 * Real.pi * Real.rpow T h ≤ C := by
  have hgrow := (tendsto_rpow_atTop hkOut).eventually
    (eventually_ge_atTop 3)
  have hlogSq := ZeroDensityArithmetic.polylog_absorption 2 (1 / 2)
    (by norm_num)
  filter_upwards [hgrow, hlogSq, eventually_ge_atTop (Real.exp 1),
    eventually_ge_atTop 4] with T hgrowT hlogSqT hTexp hTfour
  let U : ℕ := ⌊Real.rpow T kDet⌋₊
  let Y : ℝ := Real.rpow T (1 / 2)
  let N : ℕ := detectorArithmeticCutoff Y T
  let B : ℝ := detectorVerticalCutoff T
  let C : ℕ := ⌈2 * Real.pi * Real.rpow T h⌉₊
  have hT : 1 ≤ T := by linarith
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hlog : 1 ≤ Real.log T := by
    rw [← Real.exp_le_exp]
    simpa [Real.exp_log hTpos] using hTexp
  have hYpos : 0 < Y := by dsimp [Y]; positivity
  have hYone : 1 ≤ Y := Real.one_le_rpow hT (by norm_num)
  have hYsq : Y * Y = T := by
    dsimp [Y]
    rw [← Real.rpow_add hTpos]
    norm_num [Real.rpow_one]
  have hxT : Y * (Real.log T) ^ 2 ≤ T := by
    calc
      Y * (Real.log T) ^ 2 ≤ Y * Y := by
        gcongr
        simpa [Y, Real.rpow_natCast] using hlogSqT
      _ = T := hYsq
  have hkpow : Real.rpow T kDet = Real.rpow T kOut * Real.rpow T kOut := by
    rw [hkRel, show 2 * kOut = kOut + kOut by ring]
    exact Real.rpow_add hTpos _ _
  have hxquad :
      2 * Real.rpow T kOut + 1 ≤
        Real.rpow T kOut * Real.rpow T kOut := by
    have hx0 : 0 ≤ Real.rpow T kOut := Real.rpow_nonneg hTpos.le _
    have h3x : 3 * Real.rpow T kOut ≤
        Real.rpow T kOut * Real.rpow T kOut :=
      mul_le_mul_of_nonneg_right hgrowT hx0
    have hxone : 1 ≤ Real.rpow T kOut := by
      calc
        (1 : ℝ) ≤ 3 := by norm_num
        _ ≤ Real.rpow T kOut := by simpa only using! hgrowT
    have hxlin : 2 * Real.rpow T kOut + 1 ≤
        3 * Real.rpow T kOut := by
      linarith
    exact hxlin.trans h3x
  have hfloor : Real.rpow T kDet < (U : ℝ) + 1 := by
    dsimp [U]
    exact Nat.lt_floor_add_one (Real.rpow T kDet)
  rw [hkpow] at hfloor
  have hUgt : 2 * Real.rpow T kOut < (U : ℝ) := by
    linarith
  have hUone : 1 ≤ U := by
    have hUposR : (0 : ℝ) < U :=
      (mul_pos (by norm_num) (Real.rpow_pos_of_pos hTpos _)).trans hUgt
    exact_mod_cast hUposR
  have hUlow : 2 * Real.rpow T kOut ≤ (U : ℝ) := hUgt.le
  have hUbase : (U : ℝ) ≤ Real.rpow T kDet := by
    dsimp [U]
    exact Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hT) _)
  have hkpowY : Real.rpow T kDet ≤ Y := by
    dsimp [Y]
    exact Real.rpow_le_rpow_of_exponent_le hT hkDetHalf
  have hUhigh : (U : ℝ) ≤ Y * (Real.log T) ^ 2 :=
    hUbase.trans (hkpowY.trans (by
      nlinarith [sq_nonneg (Real.log T - 1)]))
  have hx0 : 0 ≤ Y * (Real.log T) ^ 2 := by positivity
  have hxceil : Y * (Real.log T) ^ 2 ≤ (N : ℝ) := by
    dsimp [N, detectorArithmeticCutoff]
    exact Nat.le_ceil _
  have hUN : U ≤ N := by exact_mod_cast hUhigh.trans hxceil
  have hNone : 1 ≤ N := hUone.trans hUN
  have hNtwo : 2 ≤ N := by
    have hYlogTwo : 2 ≤ Y * (Real.log T) ^ 2 := by
      have hYtwo : 2 ≤ Y := by
        dsimp [Y]
        have : Real.rpow 4 (1 / 2) ≤ Real.rpow T (1 / 2) :=
          Real.rpow_le_rpow (by norm_num) hTfour (by norm_num)
        norm_num at this ⊢
        exact this
      nlinarith [sq_nonneg (Real.log T - 1)]
    exact_mod_cast hYlogTwo.trans hxceil
  have hNupper : (N : ℝ) < Y * (Real.log T) ^ 2 + 1 := by
    dsimp [N, detectorArithmeticCutoff]
    exact Nat.ceil_lt_add_one hx0
  have hDhigh : ∀ j : Fin (detectorDyadicCount N),
      ((2 ^ (j : ℕ) : ℕ) : ℝ) ≤ Y * (Real.log T) ^ 2 := by
    intro j
    have hd := two_pow_fin_detectorDyadicCount_le_sub_one hNtwo j
    have hdR : (((2 ^ (j : ℕ) : ℕ) : ℝ)) ≤ ((N - 1 : ℕ) : ℝ) := by
      exact_mod_cast hd
    have hNm : (((N - 1 : ℕ) : ℝ)) < Y * (Real.log T) ^ 2 := by
      have hcast : (((N - 1 : ℕ) : ℝ)) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub hNone]
        norm_num
      rw [hcast]
      linarith
    exact hdR.trans hNm.le
  have hDtime : ∀ j : Fin (detectorDyadicCount N),
      ((2 ^ (j : ℕ) : ℕ) : ℝ) ≤ T := fun j => (hDhigh j).trans hxT
  have hJtime : (detectorDyadicCount N : ℝ) ≤ 2 * T := by
    have hJN := detectorDyadicCount_le_self hNone
    have hNle : (N : ℝ) ≤ 2 * T := hNupper.le.trans (by linarith)
    exact (by exact_mod_cast hJN : (detectorDyadicCount N : ℝ) ≤ N).trans hNle
  have hB : 1 ≤ B := by
    dsimp [B, detectorVerticalCutoff]
    nlinarith [sq_nonneg (Real.log T - 1)]
  have hC : 2 * Real.pi * Real.rpow T h ≤ (C : ℝ) := by
    dsimp [C]
    exact Nat.le_ceil _
  exact ⟨hTfour, hUone, hUlow, hUhigh, hUN, hB, hNtwo,
    hDtime, hDhigh, hJtime, hC⟩

/-! ## Public one-moment constructor -/

set_option maxHeartbeats 800000

/-- The source-faithful high-strip split follows from exactly the canonical
nonprincipal discrete fourth moment.  All detector, recentering, spacing,
multiplicity, Fourier-tail, and exponent losses are discharged internally. -/
theorem postA5HighStripStructuredSplitReduction_of_nonprincipalFourthMoment
    (hfourth :
      FixedCharacterFourthMomentFromAFE.NonprincipalFixedCharacterDiscreteFourthMoment) :
    CGLDetectorStructuredLargeValue.PostA5HighStripStructuredSplitReduction := by
  intro K delta loss hK hdelta hloss
  let kOut := splitOutputKappa loss
  let kDet := splitDetectorKappa loss
  let etaOut := splitOutputEta loss
  let etaDet := splitDetectorEta loss
  let dOut := inputLoss kOut etaOut
  let dDet := inputLoss kDet etaDet
  let a := splitSmallExponent loss
  let eps := splitFourthEpsilon loss
  let e := a
  let h := a
  obtain ⟨hkOut, hkDet, hetaOut, hetaDet, ha, heps⟩ :=
    split_parameters_pos hloss
  have he : 0 < e := by simpa [e] using ha
  have hh : 0 < h := by simpa [h] using ha
  obtain ⟨hkOutHalf, hkOutLoss, hkDetCap⟩ := split_output_kappa_ledger hloss
  obtain ⟨hZIexp, hNormExp, hIIexp⟩ := split_reserve_ledgers hloss
  obtain ⟨Kd, hKd, hdiv⟩ :=
    FixedCharacterPoweredBridge.orderedDivisorCount_subpolynomial
      2 (by norm_num) e he
  obtain ⟨Cfourth, Tfourth, hCfourth, hTfourth, hsourceMoment⟩ :=
    sourceTypeII_shifted_moment_of_nonprincipalFourthMoment hfourth eps heps
  have hsource := eventually_recentered_source_budget_floor_inputLoss
    K kDet etaDet hkDet hkDetCap hetaDet
  have htail :=
    eventually_exists_fourierMoment_detectorCommonCoefficient_mul_fourierTail_le_inputLoss
      kDet etaDet e h hkDet hetaDet he hh
  have hgeom := eventually_project_scale_geometry kOut kDet h hkOut
    (by simp [kDet, kOut, splitDetectorKappa])
    (by
      dsimp [kDet]
      exact hkDetCap.le.trans (by norm_num)) hh
  have hZIcost := eventually_typeI_project_cost_le K h a hh ha
  have hNorm := eventually_typeI_normalization_cost_le Kd e h a
    (dOut - dDet) hKd he hh ha (by
      dsimp [e, h, dOut, dDet]
      nlinarith [hNormExp])
  have hII := eventually_typeII_source_ledger Cfourth eps kDet dDet
    kOut etaOut a hCfourth heps hkDet
    (by dsimp [dDet]; exact inputLoss_pos hkDet hetaDet)
    hkOut hetaOut ha (by
      dsimp [dDet, dOut, kDet, kOut, etaOut, etaDet, a, eps]
      exact hIIexp)
  have hcolor := eventually_longSpacingColorCount_le_rpow a ha
  have hcap := eventually_crowdingNatCap_le_rpow K a ha
  have hJsub := eventually_project_detectorDyadicCount_le_rpow a ha
  have hqsub := ZeroDensityArithmetic.polylog_absorption K a ha
  have hlogSq := ZeroDensityArithmetic.polylog_absorption 2 (1 / 2)
    (by norm_num)
  have hTfourthEv : ∀ᶠ T : ℝ in Filter.atTop, Tfourth ≤ 2 * T :=
    eventually_ge_atTop (Tfourth / 2) |>.mono (by
      intro T hT
      linarith)
  have hAll := hsource.and
    (htail.and
      (hgeom.and
        (hZIcost.and
          (hNorm.and
            (hII.and
              (hcolor.and
                (hcap.and
                  (hJsub.and
                    (hqsub.and
                      (hlogSq.and hTfourthEv))))))))))
  obtain ⟨Tbase, hTbase⟩ := Filter.eventually_atTop.1 hAll
  let T₀ : ℝ := max (4 : ℝ) Tbase
  refine ⟨kOut, 1, T₀, hkOut, hkOutHalf, hkOutLoss, by norm_num,
    by
      dsimp [T₀]
      exact (by norm_num : (2 : ℝ) ≤ 4).trans (le_max_left _ _), ?_⟩
  intro T Q sigma hT0 hQ hsigmaLow hsigmaHigh r _inst chi
    hprimitive hchi hrQ
  have hTb : Tbase ≤ T := (le_max_right 4 Tbase).trans hT0
  obtain ⟨hsourceT, htailT, hgeomT, hZIcostT, hNormT, hIIT,
    hcolorT, hcapT, hJsubT, hqsubT, hlogSqT, hTfourthT⟩ := hTbase T hTb
  let U : ℕ := ⌊Real.rpow T kDet⌋₊
  let Y : ℝ := Real.rpow T (1 / 2)
  let Ncut : ℕ := detectorArithmeticCutoff Y T
  let B : ℝ := detectorVerticalCutoff T
  let C : ℕ := ⌈2 * Real.pi * Real.rpow T h⌉₊
  let V : ℝ := Real.rpow T (-dDet)
  let P : ℕ := longSpacingColorCount B * certifiedA5CrowdingNatCap r T ^ 2
  let Mfourth : ℝ := Cfourth * Real.rpow ((r : ℝ) * (2 * T)) (1 + eps)
  dsimp only at hgeomT
  obtain ⟨hTfour, hUone, hUtwolow, hUhigh, hUN, hBone, hNtwo,
    hDtime, hNhigh, hJtime, hC⟩ := hgeomT
  have hTone : 1 ≤ T := by linarith
  have hTpos : 0 < T := zero_lt_one.trans_le hTone
  have hTnonneg : 0 ≤ T := hTpos.le
  have hYone : 1 ≤ Y := by dsimp [Y]; exact Real.one_le_rpow hTone (by norm_num)
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hYone
  have hVpos : 0 < V := by dsimp [V]; positivity
  have hq : (r : ℝ) ≤ Real.rpow (Real.log T) K := by
    have hrQR : (r : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hrQ
    exact hrQR.trans hQ
  have hrpow : (r : ℝ) ≤ Real.rpow T a := hq.trans hqsubT
  have hsigmaHalf : 1 / 2 ≤ sigma := by
    norm_num at hsigmaLow ⊢
    linarith
  obtain ⟨Z0, hZ0, hsep, hcountThin⟩ :=
    exists_threeBSeparated_zeroSupport_natWeighted chi hchi
      (B := B) hsigmaHalf hTnonneg (zero_le_one.trans hBone)
  have hrect : ∀ rho ∈ Z0, rho ∈ zeroRectangle sigma T := by
    intro rho hrho
    exact (zeroDivisor chi sigma T).supportWithinDomain
      ((zeroSupport_mem_iff chi sigma T rho).mp (hZ0 hrho))
  have hzero : ∀ rho ∈ Z0, DirichletCharacter.LFunction chi rho = 0 := by
    intro rho hrho
    exact MAPMcCurleyPrimitiveLowPredicate.LFunction_eq_zero_of_mem_zeroSupport
      chi (hZ0 hrho)
  have hbetaLow : ∀ rho ∈ Z0, sigma ≤ rho.re := by
    intro rho hrho
    exact (Complex.mem_reProdIm.mp (hrect rho hrho)).1.1
  have hbetaHigh : ∀ rho ∈ Z0, rho.re ≤ 1 := by
    intro rho hrho
    exact (Complex.mem_reProdIm.mp (hrect rho hrho)).1.2
  have hheight : ∀ rho ∈ Z0, |rho.im| ≤ T := by
    intro rho hrho
    exact abs_le.mpr (Complex.mem_reProdIm.mp (hrect rho hrho)).2
  have hbudget : ∀ rho ∈ Z0,
      detectorTruncationErrorEnvelopePolynomialHeight r U rho Y T + V + V ≤
        Real.exp (-(1 / Y)) := by
    intro rho hrho
    simpa [U, Y, V, dDet] using hsourceT r rho hq (hheight rho hrho)
  have hVlower : Real.rpow T (-inputLoss kDet etaDet) ≤ V := by
    simp [V, dDet]
  have htail' : ∀ (j : Fin (detectorDyadicCount Ncut)) (rho : ℂ),
      sigma ≤ rho.re → rho.re ≤ 1 →
      (∑ n ∈ Finset.Ioc (2 ^ (j : ℕ)) (2 * 2 ^ (j : ℕ)),
          ‖detectorCommonCoefficient chi U Ncut Y sigma n‖) *
        (∫ xi in (Set.Icc (-(Real.rpow T h)) (Real.rpow T h))ᶜ,
          ‖((𝓕 (detectorRealPartCutoff
            (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤
        (V / (detectorDyadicCount Ncut : ℝ)) / 2 := by
    intro j rho hbLo hbHi
    exact htailT r chi U Ncut Y sigma rho j V hTfour hYpos
      hsigmaLow hsigmaHigh hbLo hbHi (by simpa [Ncut, Y] using hDtime j)
      (by simpa [Ncut, Y] using hJtime) hVlower
  have hNlow : ∀ (j : Fin (detectorDyadicCount Ncut)) (rho : ℂ),
      rho ∈ Z0 →
      V ≤ (detectorDyadicCount Ncut : ℝ) *
        ‖arithmeticDetectorDyadicBlock chi U Ncut rho Y j‖ →
      Real.rpow T kOut ≤ (2 ^ (j : ℕ) : ℕ) := by
    intro j rho hrho hlarge
    have hUD := mollifier_lt_two_pow_of_positive_selected_block
      chi hUone hVpos rho Y j hlarge
    have hUDR : (U : ℝ) < 2 * ((2 ^ (j : ℕ) : ℕ) : ℝ) := by exact_mod_cast hUD
    linarith
  have hthreshold : ∀ j : Fin (detectorDyadicCount Ncut),
      let D : ℕ := 2 ^ (j : ℕ)
      let L : ℝ := Real.rpow D (-sigma) * (Kd * Real.rpow (2 * D) e)
      Real.rpow D sigma * Real.rpow T (-inputLoss kOut etaOut) ≤
        L⁻¹ * (V / (4 * (24 * Real.rpow T h) * detectorDyadicCount Ncut)) := by
    intro j
    dsimp only
    have hcost := hNormT (2 ^ (j : ℕ) : ℝ) (detectorDyadicCount Ncut : ℝ)
      hTone (by positivity) (by simpa [Ncut, Y] using hDtime j)
      (Nat.cast_nonneg _) (by simpa [Ncut, Y] using hJsubT)
    simpa [V, dDet, dOut] using
      normalized_typeI_threshold_of_cost (sigma := sigma) hTpos
        (by positivity) (by unfold detectorDyadicCount; positivity) hKd hcost
  have hZIledger : ∀ (j : Fin (detectorDyadicCount Ncut)) (W : Finset ℝ),
      ((P * detectorDyadicCount Ncut *
        (4 * (shiftedFloorWindowCount C * 1) * W.card +
          2 * (C + 1) * 1) : ℕ) : ℝ) ≤
        Real.rpow T etaOut * (1 + (W.card : ℝ)) := by
    intro j W
    have hbase := hZIcostT r hq
    have hpow : Real.rpow T (h + 5 * a) ≤ Real.rpow T etaOut :=
      Real.rpow_le_rpow_of_exponent_le hTone (by
        dsimp [h]
        linarith)
    have hnatural := typeI_natural_ledger_of_cost
      (P := P) (J := detectorDyadicCount Ncut) (C := C)
      (T := T) (eta := etaOut) (A := 1) (W := W)
      (by simpa [P, C, Ncut, Y] using hbase.trans hpow)
    simpa using hnatural
  have hBT : B ≤ T := by
    dsimp [B, detectorVerticalCutoff]
    have hYle : Real.rpow T (1 / 2) ≤ T := by
      have hraw := Real.rpow_le_rpow_of_exponent_le hTone
        (by norm_num : (1 / 2 : ℝ) ≤ 1)
      simpa only [Real.rpow_one] using! hraw
    have hlogSqY : (Real.log T) ^ 2 ≤ Real.rpow T (1 / 2) := by
      simpa [Real.rpow_natCast] using hlogSqT
    exact hlogSqY.trans hYle
  have hmoment : ∀ (shift : ℂ → ℝ) (SII : Finset ℂ),
      SII ⊆ postA5SourceTypeIISet chi U Y T V Z0 →
      (∀ rho ∈ SII, shift rho ∈ Set.Icc (-B) B) →
      (∑ t ∈ SII.image (fun rho => rho.im + shift rho),
        ‖DirichletCharacter.LFunction chi
          (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 4) ≤ Mfourth := by
    intro shift SII hSII hshift
    apply hsourceMoment T B r chi hprimitive hchi SII shift hTnonneg hBone
      hBT hTfourthT
    · intro rho hrho
      apply hheight rho
      exact (mem_postA5SourceTypeIISet_iff chi U Y T V Z0 rho).mp
        (hSII hrho) |>.1
    · intro rho hrho
      exact abs_le.mpr (hshift rho hrho)
    · intro rho hrho rho' hrho' hne
      apply hsep rho
      · exact (mem_postA5SourceTypeIISet_iff chi U Y T V Z0 rho).mp
          (hSII hrho) |>.1
      · exact (mem_postA5SourceTypeIISet_iff chi U Y T V Z0 rho').mp
          (hSII hrho') |>.1
      · exact hne
  have hPpow : (P : ℝ) ≤ Real.rpow T (3 * a) := by
    have hc := hcolorT
    have hcapr := hcapT r hq
    dsimp [P, B]
    push_cast
    calc
      (longSpacingColorCount (detectorVerticalCutoff T) : ℝ) *
          (certifiedA5CrowdingNatCap r T : ℝ) ^ 2 ≤
          Real.rpow T a * (Real.rpow T a) ^ 2 := by
        have hcapSq : (certifiedA5CrowdingNatCap r T : ℝ) ^ 2 ≤
            (Real.rpow T a) ^ 2 := by
          exact (sq_le_sq₀
            (Nat.cast_nonneg (certifiedA5CrowdingNatCap r T))
            (Real.rpow_nonneg hTnonneg a)).2 hcapr
        exact mul_le_mul hc hcapSq (sq_nonneg _)
          (Real.rpow_nonneg hTnonneg a)
      _ = Real.rpow T (3 * a) := by
        rw [show (Real.rpow T a) ^ 2 = Real.rpow T a * Real.rpow T a by ring]
        calc
          Real.rpow T a * (Real.rpow T a * Real.rpow T a) =
              Real.rpow T a * Real.rpow T (a + a) := by
            congr 1
            exact (Real.rpow_add hTpos a a).symm
          _ = Real.rpow T (a + (a + a)) :=
            (Real.rpow_add hTpos _ _).symm
          _ = Real.rpow T (3 * a) := by congr 1 <;> ring
  have hUupper : (U : ℝ) ≤ Real.rpow T kDet := by
    dsimp [U]
    exact Nat.floor_le (Real.rpow_nonneg hTnonneg _)
  have hZIIledger : (P : ℝ) *
      (Mfourth / (V / (29 * Real.rpow Y (1 / 2 - sigma) *
        (2 * Real.sqrt U))) ^ 4) ≤
      Real.rpow T (2 * (1 - sigma) + 2 * kOut + etaOut) := by
    simpa [Mfourth, V, dDet, Y] using
      hIIT P r U sigma hTone hUone hPpow hrpow hUupper
        hsigmaLow hsigmaHigh
  obtain ⟨Nout, b, W, ZI, ZII, hNoutLow, hNoutHigh, hb, hWsep,
    hWheight, hWlarge, hcount, hZI, hZII,
    Uout, NcutOut, Yout, scaleOut, hprovenance⟩ :=
    finite_highStrip_structured_split_witness
      (kappaDet := kDet) (etaDet := etaDet)
      (kappaOut := kOut) (etaOut := etaOut)
      (e := e) (h := h) (T := T) (sigma := sigma)
      (Y := Y) (R := T) (V := V) (Kd := Kd) (Mfourth := Mfourth)
      (AZI := 1) (AZII := 1) (U := U) (P := P) (C := C)
      chi hchi Z0 hTfour hYone
      (by exact hTpos)
      hUone hVpos he hKd hkDet hetaDet hkOut hetaOut hh hzero hbetaLow
      hsigmaLow hsigmaHigh hbetaHigh hheight
      (by simpa [B] using hsep) (by simpa [P] using hcountThin)
      (by simpa [U, Ncut, Y] using hUN) (by simpa [B] using hBone)
      hbudget (by simp [V, dDet, kDet, etaDet]) hVlower
      (by simpa [Ncut, Y] using hDtime) (by simpa [Ncut, Y] using hJtime)
      (by simpa [C] using hC) htail' hdiv
      (by linarith) hUhigh hNlow (by simpa [Ncut, Y] using hNhigh)
      hthreshold hmoment
      (by simpa only [Ncut, one_mul] using hZIledger)
      (by simpa only [one_mul] using hZIIledger)
  refine ⟨Nout, b, W, ZI, ZII, hNoutLow, hNoutHigh, hb, hWsep,
    hWheight, ?_, hcount, ?_, ?_, Uout, NcutOut, Yout, scaleOut,
    hprovenance⟩
  · simpa [etaOut, splitOutputEta] using hWlarge
  · have hpow : Real.rpow T etaOut ≤ Real.rpow T loss :=
      Real.rpow_le_rpow_of_exponent_le hTone (by
        dsimp [etaOut, splitOutputEta]
        linarith)
    have hZI' : (ZI : ℝ) ≤
        Real.rpow T etaOut * (1 + (W.card : ℝ)) := by
      simpa only [one_mul] using hZI
    have hout := hZI'.trans
      (mul_le_mul_of_nonneg_right hpow (by positivity))
    simpa only [one_mul] using hout
  · have hpow : Real.rpow T
        (2 * (1 - sigma) + 2 * kOut + etaOut) ≤
        Real.rpow T (2 * (1 - sigma) + 2 * kOut + loss) :=
      Real.rpow_le_rpow_of_exponent_le hTone (by
        dsimp [etaOut, splitOutputEta]
        linarith)
    have hZII' : (ZII : ℝ) ≤ Real.rpow T
        (2 * (1 - sigma) + 2 * kOut + etaOut) := by
      simpa only [one_mul] using hZII
    have hout := hZII'.trans hpow
    simpa only [one_mul] using hout

/-- Source-facing A.4 adapter: the one Ramachandra Lemmas 3--6 dyadic AFE
witness shared with the BHP/MRT route supplies the fixed-character fourth
moment, hence the complete provenance-preserving high-strip split. -/
theorem postA5HighStripStructuredSplitReduction_of_ramachandraDyadicAFE
    (hAFE :
      BHPRamachandraMeanValueFromDyadicAFE.RamachandraLemma3To6AllCharacterDyadicAFE) :
    CGLDetectorStructuredLargeValue.PostA5HighStripStructuredSplitReduction :=
  postA5HighStripStructuredSplitReduction_of_nonprincipalFourthMoment
    (BHPFixedCharacterFromDyadicAFE.nonprincipalFixedCharacterDiscreteFourthMoment_of_dyadicAFE
      hAFE)

end
end PostA5HighStripSplitReductionFromFourthMoment

#print axioms PostA5HighStripSplitReductionFromFourthMoment.shiftedFloorWindowCount_natCast
#print axioms PostA5HighStripSplitReductionFromFourthMoment.arithmeticDetectorDyadicBlock_eq_zero_of_two_pow_le_mollifier
#print axioms PostA5HighStripSplitReductionFromFourthMoment.mollifier_lt_two_pow_of_positive_selected_block
#print axioms PostA5HighStripSplitReductionFromFourthMoment.two_pow_fin_detectorDyadicCount_le_sub_one
#print axioms PostA5HighStripSplitReductionFromFourthMoment.detectorDyadicCount_le_self
#print axioms PostA5HighStripSplitReductionFromFourthMoment.split_parameters_pos
#print axioms PostA5HighStripSplitReductionFromFourthMoment.split_output_kappa_ledger
#print axioms PostA5HighStripSplitReductionFromFourthMoment.split_inputLoss_relation
#print axioms PostA5HighStripSplitReductionFromFourthMoment.eventually_const_mul_polylog_le_rpow
#print axioms PostA5HighStripSplitReductionFromFourthMoment.eventually_crowdingNatCap_le_rpow
#print axioms PostA5HighStripSplitReductionFromFourthMoment.eventually_longSpacingColorCount_le_rpow
#print axioms PostA5HighStripSplitReductionFromFourthMoment.eventually_project_detectorDyadicCount_le_rpow
#print axioms PostA5HighStripSplitReductionFromFourthMoment.eventually_typeI_project_cost_le
#print axioms PostA5HighStripSplitReductionFromFourthMoment.eventually_typeI_normalization_cost_le
#print axioms PostA5HighStripSplitReductionFromFourthMoment.eventually_typeII_source_ledger
#print axioms PostA5HighStripSplitReductionFromFourthMoment.postA5HighStripStructuredSplitReduction_of_nonprincipalFourthMoment
#print axioms PostA5HighStripSplitReductionFromFourthMoment.postA5HighStripStructuredSplitReduction_of_ramachandraDyadicAFE
