import PostA5HighStripSplitReductionFromFourthMoment
import MAPNearOneBulkBypassDetectorTail
import MAPNearOneBulkBypassDetectorFinite

namespace MAPNearOneBulkBypassDetectorNonprincipal
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

open PostA5HighStripSplitReductionFromFourthMoment
noncomputable section
set_option maxHeartbeats 1000000

def PostA5HighStripStructuredSplitReduction : Prop :=
  ∀ K delta loss : ℝ, 0 < K → 0 < delta → 0 < loss →
    ∃ κ A T₀ : ℝ,
      0 < κ ∧ κ ≤ 1 / 2 ∧ 2 * κ ≤ loss ∧ 0 < A ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (Q : ℕ) (sigma : ℝ), T₀ ≤ T →
        (Q : ℝ) ≤ Real.rpow (Real.log T) K →
        7 / 10 ≤ sigma → sigma ≤ 1 →
        ∀ (r : ℕ) [NeZero r] (chi : DirichletCharacter ℂ r),
          chi.IsPrimitive → chi ≠ 1 → r ≤ Q →
          ∃ (D : ℕ) (b : ℕ → ℂ) (W : Finset ℝ) (ZI ZII : ℕ),
            Real.rpow T κ ≤ D ∧
            (D : ℝ) ≤ Real.rpow T (1 / 2) * (Real.log T) ^ 2 ∧
            (∀ n, ‖b n‖ ≤ 1) ∧
            OneSeparated W ∧
            (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) ∧
            (∀ t ∈ W,
              Real.rpow D sigma *
                  Real.rpow T (-inputLoss κ (loss / 2)) ≤
                ‖dirichletPolynomial b D t‖) ∧
            dirichletZeroCount chi sigma T ≤ ZI + ZII ∧
            (ZI : ℝ) ≤ A * Real.rpow T loss * (1 + (W.card : ℝ)) ∧
            (ZII : ℝ) ≤
              A * Real.rpow T
                (2 * (1 - sigma) + 2 * κ + loss) ∧
            ∃ (U Ncut : ℕ) (Y scale : ℝ),
              IsNormalizedDetectorCoefficient
                chi U Ncut Y sigma D scale T b


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
        7 / 10 ≤ sigma → sigma ≤ 1 →
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


theorem postA5HighStripStructuredSplitReduction_of_nonprincipalFourthMoment
    (hfourth :
      FixedCharacterFourthMomentFromAFE.NonprincipalFixedCharacterDiscreteFourthMoment) :
    PostA5HighStripStructuredSplitReduction := by
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
    MAPNearOneBulkBypassDetectorTail.eventually_exists_fourierMoment_detectorCommonCoefficient_mul_fourierTail_le_inputLoss
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
      simpa only [Real.rpow_one] using hraw
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
    MAPNearOneBulkBypassDetectorFinite.finite_highStrip_structured_split_witness
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


end
end MAPNearOneBulkBypassDetectorNonprincipal
#print axioms MAPNearOneBulkBypassDetectorNonprincipal.postA5HighStripStructuredSplitReduction_of_nonprincipalFourthMoment
