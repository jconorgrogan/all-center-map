import PrincipalZetaStructuredSplitFromFourthMoment
import PrincipalHighOrdinateDetectorBudgetProof
import MAPNearOneBulkBypassDetectorTail
import MAPNearOneBulkBypassDetectorPrincipalFinite
import MAPNearOneBulkBypassDetectorNonprincipal

/-!
# Principal structured detector split through sigma = 1

This extends the exact principal post-A.5 contract while retaining the
normalized detector coefficient provenance. The cap-one Fourier tail,
finite split, and Type-II source ledger are used explicitly. The low-ordinate
exception is absorbed by the reserved small exponent even at sigma = 1;
no positive lower bound for 1-sigma is assumed.
-/
namespace MAPNearOneBulkBypassDetectorPrincipal
open Filter
open scoped BigOperators FourierTransform
open CGLProofDAG DirichletZeros MAPAppendixA4PostA5SetAdapter SchwartzMap
open MAPAppendixA4DetectorDichotomy MAPAppendixA4RecenteredGammaRepair
open PostA5RecenteredSourceSplit PostA5RecenteredTypeIExtractor
open PostA5TypeIIFourthMoment PostA5LongSpacingAssembly
open PostA5CrowdingDeterministic PostA5TypeIFourierAssembly
open PostA5TypeIOrdinateRecentering PostA5HighStripSplitAssembly
open PostA5TypeICoefficientProvenance
open PostA5HighStripSplitReductionFromFourthMoment
open PostA5TypeIFourierTailAbsorption MAPLocalZeroWindow
open MAPPrincipalZetaCompactCrowding MAPPrincipalZetaDetectorDichotomy
open MAPPrincipalZetaFiniteStructuredSplit MAPPrincipalZetaStructuredDensity

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)
local notation "principalF" => MAPPrincipalZetaFixedStrip.principalRegularized

open MAPPrincipalZetaStructuredSplitFromFourthMoment

def PrincipalPostA5StructuredSplitReduction : Prop :=
  ∀ loss : ℝ, 0 < loss →
    ∃ kappa A Tdet : ℝ,
      0 < kappa ∧ kappa ≤ 1 / 2 ∧ 2 * kappa ≤ loss ∧
      0 < A ∧ 2 ≤ Tdet ∧
      ∀ (T sigma : ℝ), Tdet ≤ T →
        7 / 10 ≤ sigma → sigma ≤ 1 →
        ∃ (D : ℕ) (b : ℕ → ℂ) (W : Finset ℝ) (ZI ZII : ℕ)
            (U Ncut : ℕ) (Y scale : ℝ),
          Real.rpow T kappa ≤ D ∧
          (D : ℝ) ≤ Real.rpow T (1 / 2) * (Real.log T) ^ 2 ∧
          (∀ n, ‖b n‖ ≤ 1) ∧
          OneSeparated W ∧
          (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) ∧
          (∀ t ∈ W,
            Real.rpow D sigma *
                Real.rpow T (-inputLoss kappa (loss / 2)) ≤
              ‖dirichletPolynomial b D t‖) ∧
          (zeroSupport chiOne sigma T).card ≤ ZI + ZII ∧
          (ZI : ℝ) ≤ A * Real.rpow T loss * (1 + (W.card : ℝ)) ∧
          (ZII : ℝ) ≤ A * Real.rpow T
            (2 * (1 - sigma) + 2 * kappa + loss) ∧
          IsNormalizedDetectorCoefficient
            chiOne U Ncut Y sigma D scale T b

set_option maxHeartbeats 1000000

theorem principalPostA5StructuredSplitReduction_of_principalFourthMoment
    (hbudget : PrincipalHighOrdinateDetectorBudget)
    (hfourth : PrincipalZetaDiscreteFourthMoment) :
    PrincipalPostA5StructuredSplitReduction := by
  intro loss hloss
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
    sourceTypeII_shifted_moment_of_principalFourthMoment hfourth eps heps
  have hsource := hbudget kDet etaDet hkDet hkDetCap hetaDet
  have htail :=
    MAPNearOneBulkBypassDetectorTail.eventually_exists_fourierMoment_detectorCommonCoefficient_mul_fourierTail_le_inputLoss
      kDet etaDet e h hkDet hetaDet he hh
  have hgeom := eventually_project_scale_geometry kOut kDet h hkOut
    (by simp [kDet, kOut, splitDetectorKappa])
    (by
      dsimp [kDet]
      exact hkDetCap.le.trans (by norm_num)) hh
  have hZIcost := eventually_principal_typeI_project_cost_le h a hh ha
  have hNorm := eventually_typeI_normalization_cost_le Kd e h a
    (dOut - dDet) hKd he hh ha (by
      dsimp [e, h, dOut, dDet]
      nlinarith [hNormExp])
  have hII := MAPNearOneBulkBypassDetectorNonprincipal.eventually_typeII_source_ledger Cfourth eps kDet dDet
    kOut etaOut a hCfourth heps hkDet
    (by dsimp [dDet]; exact inputLoss_pos hkDet hetaDet)
    hkOut hetaOut ha (by
      dsimp [dDet, dOut, kDet, kOut, etaOut, etaDet, a, eps]
      exact hIIexp)
  have hcolor := eventually_longSpacingColorCount_le_rpow a ha
  have hcap := eventually_two_principal_crowdingCap_le_rpow a ha
  have hJsub := eventually_project_detectorDyadicCount_le_rpow a ha
  have hqsub := ZeroDensityArithmetic.polylog_absorption 1 a ha
  have hlogSq := ZeroDensityArithmetic.polylog_absorption 2 (1 / 2)
    (by norm_num)
  have hlow := eventually_principal_lowOrdinateSupport_card_le_rpow a ha
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
                      (hlogSq.and (hlow.and hTfourthEv)))))))))))
  obtain ⟨Tbase, hTbase⟩ := Filter.eventually_atTop.1 hAll
  let T₀ : ℝ := max (Real.exp 1) (max 4 Tbase)
  refine ⟨kOut, 2, T₀, hkOut, hkOutHalf, hkOutLoss, by norm_num,
    by
      dsimp [T₀]
      exact (by norm_num : (2 : ℝ) ≤ 4).trans
        ((le_max_left 4 Tbase).trans (le_max_right _ _)), ?_⟩
  intro T sigma hT0 hsigmaLow hsigmaHigh
  have hTb : Tbase ≤ T :=
    ((le_max_right 4 Tbase).trans (le_max_right (Real.exp 1) _)).trans hT0
  have hTexp : Real.exp 1 ≤ T := (le_max_left _ _).trans hT0
  obtain ⟨hsourceT, htailT, hgeomT, hZIcostT, hNormT, hIIT,
    hcolorT, hcapT, hJsubT, hqsubT, hlogSqT, hlowT, hTfourthT⟩ :=
    hTbase T hTb
  let U : ℕ := ⌊Real.rpow T kDet⌋₊
  let Y : ℝ := Real.rpow T (1 / 2)
  let Ncut : ℕ := detectorArithmeticCutoff Y T
  let B : ℝ := detectorVerticalCutoff T
  let C : ℕ := ⌈2 * Real.pi * Real.rpow T h⌉₊
  let V : ℝ := Real.rpow T (-dDet)
  let P : ℕ := 2 * ⌈1683 * Real.log (T + 3)⌉₊ *
    longSpacingColorCount B
  let Mfourth : ℝ := Cfourth * Real.rpow (2 * T) (1 + eps)
  dsimp only at hgeomT
  obtain ⟨hTfour, hUone, hUtwolow, hUhigh, hUN, hBone, hNtwo,
    hDtime, hNhigh, hJtime, hC⟩ := hgeomT
  have hTone : 1 ≤ T := by linarith
  have hTpos : 0 < T := zero_lt_one.trans_le hTone
  have hTnonneg : 0 ≤ T := hTpos.le
  have hYone : 1 ≤ Y := by dsimp [Y]; exact Real.one_le_rpow hTone (by norm_num)
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hYone
  have hVpos : 0 < V := by dsimp [V]; positivity
  have hlog : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hTexp
  have hq : (1 : ℝ) ≤ Real.rpow (Real.log T) 1 := by simpa using hlog
  have hrpow : (1 : ℝ) ≤ Real.rpow T a :=
    Real.one_le_rpow hTone ha.le
  have hsigmaHalf : 1 / 2 ≤ sigma := by
    norm_num at hsigmaLow ⊢
    linarith
  let Zhigh := (zeroSupport chiOne sigma T).filter fun rho => B ≤ |rho.im|
  let Zlow := (zeroSupport chiOne sigma T).filter fun rho => |rho.im| < B
  obtain ⟨Z0, hZ0, hsep, hcountThin⟩ :=
    exists_threeBSeparated_principal_subset (sigma := sigma) (T := T)
      (B := B) (by linarith) hTnonneg (zero_le_one.trans hBone) Zhigh
      (Finset.filter_subset _ _)
  have hZ0Full : ∀ rho ∈ Z0, rho ∈ zeroSupport chiOne sigma T := by
    intro rho hrho
    exact Finset.filter_subset _ _ (hZ0 hrho)
  have hrect : ∀ rho ∈ Z0, rho ∈ zeroRectangle sigma T := by
    intro rho hrho
    exact (zeroDivisor chiOne sigma T).supportWithinDomain
      ((zeroSupport_mem_iff chiOne sigma T rho).mp (hZ0Full rho hrho))
  have hzero : ∀ rho ∈ Z0, principalF rho = 0 := by
    intro rho hrho
    simpa [MAPPrincipalZetaFixedStrip.principalRegularized,
      DirichletZeros.regularizedLFunction] using
      (regularizedLFunction_eq_zero_of_mem_zeroSupport
        chiOne sigma T (hZ0Full rho hrho))
  have hbetaLow : ∀ rho ∈ Z0, sigma ≤ rho.re := by
    intro rho hrho
    exact (Complex.mem_reProdIm.mp (hrect rho hrho)).1.1
  have hbetaHigh : ∀ rho ∈ Z0, rho.re ≤ 1 := by
    intro rho hrho
    exact (Complex.mem_reProdIm.mp (hrect rho hrho)).1.2
  have hheight : ∀ rho ∈ Z0, |rho.im| ≤ T := by
    intro rho hrho
    exact abs_le.mpr (Complex.mem_reProdIm.mp (hrect rho hrho)).2
  have hbudget' : ∀ rho ∈ Z0,
      principalPaperScaleTruncationError U rho Y T + V + V ≤
        Real.exp (-(1 / Y)) := by
    intro rho hrho
    have hhigh : detectorVerticalCutoff T ≤ |rho.im| :=
      (Finset.mem_filter.mp (hZ0 hrho)).2
    simpa [U, Y, V, dDet] using hsourceT rho (hzero rho hrho)
      (hbetaLow rho hrho |> hsigmaLow.trans) (hbetaHigh rho hrho)
      hhigh (hheight rho hrho)
  have hVlower : Real.rpow T (-inputLoss kDet etaDet) ≤ V := by
    simp [V, dDet]
  have htail' : ∀ (j : Fin (detectorDyadicCount Ncut)) (rho : ℂ),
      sigma ≤ rho.re → rho.re ≤ 1 →
      (∑ n ∈ Finset.Ioc (2 ^ (j : ℕ)) (2 * 2 ^ (j : ℕ)),
          ‖detectorCommonCoefficient chiOne U Ncut Y sigma n‖) *
        (∫ xi in (Set.Icc (-(Real.rpow T h)) (Real.rpow T h))ᶜ,
          ‖((𝓕 (detectorRealPartCutoff
            (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤
        (V / (detectorDyadicCount Ncut : ℝ)) / 2 := by
    intro j rho hbLo hbHi
    exact htailT 1 chiOne U Ncut Y sigma rho j V hTfour hYpos
      hsigmaLow hsigmaHigh hbLo hbHi (by simpa [Ncut, Y] using hDtime j)
      (by simpa [Ncut, Y] using hJtime) hVlower
  have hNlow : ∀ (j : Fin (detectorDyadicCount Ncut)) (rho : ℂ),
      rho ∈ Z0 →
      V ≤ (detectorDyadicCount Ncut : ℝ) *
        ‖arithmeticDetectorDyadicBlock chiOne U Ncut rho Y j‖ →
      Real.rpow T kOut ≤ (2 ^ (j : ℕ) : ℕ) := by
    intro j rho hrho hlarge
    have hUD := mollifier_lt_two_pow_of_positive_selected_block
      chiOne hUone hVpos rho Y j hlarge
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
    have hbase := hZIcostT
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
      SII ⊆ postA5SourceTypeIISet chiOne U Y T V Z0 →
      (∀ rho ∈ SII, shift rho ∈ Set.Icc (-B) B) →
      (∑ t ∈ SII.image (fun rho => rho.im + shift rho),
        ‖DirichletCharacter.LFunction chiOne
          (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 4) ≤ Mfourth := by
    intro shift SII hSII hshift
    apply hsourceMoment T B SII shift hTnonneg hBone hBT hTfourthT
    · intro rho hrho
      apply hheight rho
      exact (mem_postA5SourceTypeIISet_iff chiOne U Y T V Z0 rho).mp
        (hSII hrho) |>.1
    · intro rho hrho
      exact abs_le.mpr (hshift rho hrho)
    · intro rho hrho rho' hrho' hne
      apply hsep rho
      · exact (mem_postA5SourceTypeIISet_iff chiOne U Y T V Z0 rho).mp
          (hSII hrho) |>.1
      · exact (mem_postA5SourceTypeIISet_iff chiOne U Y T V Z0 rho').mp
          (hSII hrho') |>.1
      · exact hne
  have hPpow : (P : ℝ) ≤ Real.rpow T (3 * a) := by
    dsimp [P, B]
    push_cast
    push_cast at hcapT
    calc
      2 * (⌈1683 * Real.log (T + 3)⌉₊ : ℝ) *
          (longSpacingColorCount (detectorVerticalCutoff T) : ℝ) ≤
          Real.rpow T (2 * a) * Real.rpow T a :=
        mul_le_mul hcapT hcolorT (by positivity)
          (Real.rpow_nonneg hTnonneg _)
      _ = Real.rpow T (3 * a) := by
        calc
          Real.rpow T (2 * a) * Real.rpow T a =
              Real.rpow T (2 * a + a) := (Real.rpow_add hTpos _ _).symm
          _ = Real.rpow T (3 * a) := by congr 1 <;> ring
  have hUupper : (U : ℝ) ≤ Real.rpow T kDet := by
    dsimp [U]
    exact Nat.floor_le (Real.rpow_nonneg hTnonneg _)
  have hZIIledger : (P : ℝ) *
      (Mfourth / (V / (29 * Real.rpow Y (1 / 2 - sigma) *
        (2 * Real.sqrt U))) ^ 4) ≤
      Real.rpow T (2 * (1 - sigma) + 2 * kOut + etaOut) := by
    simpa [Mfourth, V, dDet, Y] using
      hIIT P 1 U sigma hTone hUone hPpow (by simpa using hrpow) hUupper
        hsigmaLow hsigmaHigh
  obtain ⟨Nout, b, W, ZI, ZII, hNoutLow, hNoutHigh, hb, hWsep,
    hWheight, hWlarge, hcount, hZI, hZII,
    Uout, NcutOut, Yout, scaleOut, hprovenance⟩ :=
    MAPNearOneBulkBypassDetectorPrincipalFinite.principal_finite_highStrip_structured_split_witness
      (Ztarget := Zhigh.card) (kappaDet := kDet) (etaDet := etaDet)
      (kappaOut := kOut) (etaOut := etaOut)
      (e := e) (h := h) (T := T) (sigma := sigma)
      (Y := Y) (R := T) (V := V) (Kd := Kd) (Mfourth := Mfourth)
      (AZI := 1) (AZII := 1) (U := U) (P := P) (C := C)
      Z0 hTfour hYone (by exact hTpos)
      hUone hVpos he hKd hkDet hetaDet hkOut hetaOut hh hzero hbetaLow
      hsigmaLow hsigmaHigh hbetaHigh hheight
      (by simpa [B] using hsep) (by simpa [P] using hcountThin)
      (by simpa [U, Ncut, Y] using hUN) (by simpa [B] using hBone)
      hbudget'  (by simp [V, dDet, kDet, etaDet]) hVlower
      (by simpa [Ncut, Y] using hDtime) (by simpa [Ncut, Y] using hJtime)
      (by simpa [C] using hC) htail' hdiv
      (by linarith) hUhigh hNlow (by simpa [Ncut, Y] using hNhigh)
      hthreshold hmoment
      (by simpa only [Ncut, one_mul] using hZIledger)
      (by simpa only [one_mul] using hZIIledger)
  let ZIIout : ℕ := ZII + Zlow.card
  have hsupportSplit : (zeroSupport chiOne sigma T).card ≤
      Zhigh.card + Zlow.card := by
    apply (Finset.card_le_card ?_).trans (Finset.card_union_le Zhigh Zlow)
    intro rho hrho
    by_cases hlowOrd : |rho.im| < B
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hrho, hlowOrd⟩)
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hrho, le_of_not_gt hlowOrd⟩)
  have hcountAll : (zeroSupport chiOne sigma T).card ≤ ZI + ZIIout := by
    calc
      (zeroSupport chiOne sigma T).card ≤ Zhigh.card + Zlow.card :=
        hsupportSplit
      _ ≤ (ZI + ZII) + Zlow.card := Nat.add_le_add_right hcount _
      _ = ZI + ZIIout := by simp [ZIIout, Nat.add_assoc]
  refine ⟨Nout, b, W, ZI, ZIIout, Uout, NcutOut, Yout, scaleOut,
    hNoutLow, hNoutHigh, hb, hWsep, hWheight, ?_, hcountAll, ?_, ?_,
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
    have hnonneg : 0 ≤ Real.rpow T loss * (1 + (W.card : ℝ)) :=
      mul_nonneg (Real.rpow_nonneg hTnonneg _) (by positivity)
    simpa only using hout.trans (by nlinarith)
  · let targetExp : ℝ := 2 * (1 - sigma) + 2 * kOut + loss
    have hpow : Real.rpow T
        (2 * (1 - sigma) + 2 * kOut + etaOut) ≤
        Real.rpow T targetExp :=
      Real.rpow_le_rpow_of_exponent_le hTone (by
        dsimp [targetExp, etaOut, splitOutputEta]
        linarith)
    have hZII' : (ZII : ℝ) ≤ Real.rpow T
        (2 * (1 - sigma) + 2 * kOut + etaOut) := by
      simpa only [one_mul] using hZII
    have hZIIbound : (ZII : ℝ) ≤ Real.rpow T targetExp := hZII'.trans hpow
    have hlowBound : (Zlow.card : ℝ) ≤ Real.rpow T a := by
      simpa [Zlow, B] using hlowT sigma (by linarith)
    have haCap : a ≤ 1 / 1000 := by
      dsimp [a, splitSmallExponent]
      exact min_le_right _ _
    have haTarget : a ≤ targetExp := by
      dsimp [targetExp]
      have hbase : (2 : ℝ) * (1 - sigma) ≥ 0 := by linarith
      have hk0 : 0 ≤ kOut := hkOut.le
      have haLoss : 6*a ≤ loss/2 := by
        simpa only [a,etaOut,splitOutputEta] using hZIexp
      linarith
    have hlowTarget : (Zlow.card : ℝ) ≤ Real.rpow T targetExp :=
      hlowBound.trans (Real.rpow_le_rpow_of_exponent_le hTone haTarget)
    have hcast : (ZIIout : ℝ) = (ZII : ℝ) + Zlow.card := by
      simp [ZIIout]
    rw [hcast]
    have htarget0 : 0 ≤ Real.rpow T targetExp := Real.rpow_nonneg hTnonneg _
    exact (add_le_add hZIIbound hlowTarget).trans (by nlinarith)


/-- The high-ordinate principal truncation budget is already unconditional;
only the independent principal fourth-moment source remains an argument. -/
theorem principalPostA5StructuredSplitReduction_of_fourthMoment
    (hfourth : PrincipalZetaDiscreteFourthMoment) :
    PrincipalPostA5StructuredSplitReduction :=
  principalPostA5StructuredSplitReduction_of_principalFourthMoment
    MAPPrincipalHighOrdinateDetectorBudgetProof.principalHighOrdinateDetectorBudget_unconditional
    hfourth

end
end MAPNearOneBulkBypassDetectorPrincipal

#print axioms MAPNearOneBulkBypassDetectorPrincipal.principalPostA5StructuredSplitReduction_of_principalFourthMoment
#print axioms MAPNearOneBulkBypassDetectorPrincipal.principalPostA5StructuredSplitReduction_of_fourthMoment
