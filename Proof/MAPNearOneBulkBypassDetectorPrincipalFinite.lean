import PrincipalZetaFiniteStructuredSplit
import PrincipalZetaDetectorDichotomy
import PostA5TypeICoefficientProvenance

/-!
# Honest finite principal structured split

This module reuses the certified post-A.5 Type-I provenance and Type-II
fourth-moment machinery, but obtains the detector partition from the
residue-aware principal A.4 theorem.  The two branches remain separate.
-/

namespace MAPNearOneBulkBypassDetectorPrincipalFinite

open scoped BigOperators FourierTransform
open CGLProofDAG DirichletZeros MAPAppendixA4PostA5SetAdapter SchwartzMap
open MAPAppendixA4DetectorDichotomy MAPAppendixA4RecenteredGammaRepair
open PostA5RecenteredSourceSplit PostA5RecenteredTypeIExtractor
open PostA5TypeIIFourthMoment PostA5LongSpacingAssembly
open PostA5CrowdingDeterministic PostA5TypeIFourierAssembly
open PostA5TypeIOrdinateRecentering PostA5HighStripSplitAssembly
open PostA5TypeICoefficientProvenance
open MAPPrincipalZetaDetectorDichotomy

noncomputable section
local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)
local notation "principalF" => MAPPrincipalZetaFixedStrip.principalRegularized

theorem principal_finite_highStrip_structured_split_witness
    {kappaDet etaDet kappaOut etaOut e h T sigma Y R V Kd Mfourth AZI AZII : ℝ}
    {U P C Ztarget : ℕ} (Z0 : Finset ℂ)
    (hT : 4 ≤ T) (hY : 1 ≤ Y) (hR : 0 < R)
    (hU : 1 ≤ U) (hV : 0 < V) (he : 0 < e) (hKd : 0 < Kd)
    (hkappaDet : 0 < kappaDet) (hetaDet : 0 < etaDet)
    (hkappaOut : 0 < kappaOut) (hetaOut : 0 < etaOut) (hh : 0 < h)
    (hzero : ∀ rho ∈ Z0, principalF rho = 0)
    (hbetaLow : ∀ rho ∈ Z0, sigma ≤ rho.re)
    (hbetaSeven : 7 / 10 ≤ sigma) (hbetaFour : sigma ≤ 1)
    (hbetaHigh : ∀ rho ∈ Z0, rho.re ≤ 1)
    (hheight : ∀ rho ∈ Z0, |rho.im| ≤ T)
    (hsep : ∀ rho ∈ Z0, ∀ rho' ∈ Z0, rho ≠ rho' →
      3 * detectorVerticalCutoff R ≤ |rho.im - rho'.im|)
    (hcountThin : Ztarget ≤ P * Z0.card)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R)
    (hbudget : ∀ rho ∈ Z0,
      principalPaperScaleTruncationError U rho Y R + V + V ≤
        Real.exp (-(1 / Y)))
    (hVR : V = Real.rpow R (-inputLoss kappaDet etaDet))
    (hVlower : Real.rpow T (-inputLoss kappaDet etaDet) ≤ V)
    (hDtime : ∀ j : Fin (detectorDyadicCount
      (detectorArithmeticCutoff Y R)), ((2 ^ (j : ℕ) : ℕ) : ℝ) ≤ T)
    (hJtime : (detectorDyadicCount
      (detectorArithmeticCutoff Y R) : ℝ) ≤ 2 * T)
    (hC : 2 * Real.pi * Real.rpow T h ≤ C)
    (htail : ∀ (j : Fin (detectorDyadicCount
        (detectorArithmeticCutoff Y R))) (rho : ℂ),
      sigma ≤ rho.re → rho.re ≤ 1 →
      (∑ n ∈ Finset.Ioc (2 ^ (j : ℕ)) (2 * 2 ^ (j : ℕ)),
          ‖detectorCommonCoefficient chiOne U
            (detectorArithmeticCutoff Y R) Y sigma n‖) *
        (∫ xi in (Set.Icc (-(Real.rpow T h)) (Real.rpow T h))ᶜ,
          ‖((𝓕 (detectorRealPartCutoff
            (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤
        (V / (detectorDyadicCount
          (detectorArithmeticCutoff Y R) : ℝ)) / 2)
    (hdiv : ∀ n : ℕ, 0 < n →
      (orderedDivisorCount 2 n : ℝ) ≤ Kd * Real.rpow n e)
    (hUoutLow : Real.rpow T kappaOut ≤ U)
    (hUoutHigh : (U : ℝ) ≤
      Real.rpow T (1 / 2) * (Real.log T) ^ 2)
    (hNlow : ∀ (j : Fin (detectorDyadicCount
        (detectorArithmeticCutoff Y R))) (rho : ℂ),
      rho ∈ Z0 →
      V ≤ (detectorDyadicCount (detectorArithmeticCutoff Y R) : ℝ) *
        ‖arithmeticDetectorDyadicBlock chiOne U
          (detectorArithmeticCutoff Y R) rho Y j‖ →
      Real.rpow T kappaOut ≤ (2 ^ (j : ℕ) : ℕ))
    (hNhigh : ∀ j : Fin (detectorDyadicCount
      (detectorArithmeticCutoff Y R)),
      ((2 ^ (j : ℕ) : ℕ) : ℝ) ≤
        Real.rpow T (1 / 2) * (Real.log T) ^ 2)
    (hthreshold : ∀ j : Fin (detectorDyadicCount
      (detectorArithmeticCutoff Y R)),
      let D : ℕ := 2 ^ (j : ℕ)
      let L : ℝ := Real.rpow D (-sigma) *
        (Kd * Real.rpow (2 * D) e)
      Real.rpow D sigma * Real.rpow T (-inputLoss kappaOut etaOut) ≤
        L⁻¹ * (V /
          (4 * (24 * Real.rpow T h) *
            detectorDyadicCount (detectorArithmeticCutoff Y R))))
    (hmoment : ∀ (shift : ℂ → ℝ) (SII : Finset ℂ),
      SII ⊆ postA5SourceTypeIISet chiOne U Y R V Z0 →
      (∀ rho ∈ SII,
        shift rho ∈ Set.Icc (-(detectorVerticalCutoff R))
          (detectorVerticalCutoff R)) →
      (∑ t ∈ SII.image (fun rho => rho.im + shift rho),
        ‖DirichletCharacter.LFunction chiOne
          (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 4) ≤ Mfourth)
    (hZIledger : ∀ (j : Fin (detectorDyadicCount
        (detectorArithmeticCutoff Y R))) (W : Finset ℝ),
      ((P * detectorDyadicCount (detectorArithmeticCutoff Y R) *
        (4 * (shiftedFloorWindowCount C * 1) * W.card +
          2 * (C + 1) * 1) : ℕ) : ℝ) ≤
        AZI * Real.rpow T etaOut * (1 + (W.card : ℝ)))
    (hZIIledger : (P : ℝ) *
      (Mfourth /
        (V / (29 * Real.rpow Y (1 / 2 - sigma) *
          (2 * Real.sqrt U))) ^ 4) ≤
      AZII * Real.rpow T
        (2 * (1 - sigma) + 2 * kappaOut + etaOut)) :
    ∃ (Nout : ℕ) (b : ℕ → ℂ) (W : Finset ℝ) (ZI ZII : ℕ),
      Real.rpow T kappaOut ≤ Nout ∧
      (Nout : ℝ) ≤ Real.rpow T (1 / 2) * (Real.log T) ^ 2 ∧
      (∀ n, ‖b n‖ ≤ 1) ∧
      OneSeparated W ∧
      (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) ∧
      (∀ t ∈ W,
        Real.rpow Nout sigma * Real.rpow T (-inputLoss kappaOut etaOut) ≤
          ‖dirichletPolynomial b Nout t‖) ∧
      Ztarget ≤ ZI + ZII ∧
      (ZI : ℝ) ≤ AZI * Real.rpow T etaOut * (1 + (W.card : ℝ)) ∧
      (ZII : ℝ) ≤ AZII * Real.rpow T
        (2 * (1 - sigma) + 2 * kappaOut + etaOut) ∧
      ∃ (Uout NcutOut : ℕ) (Yout scaleOut : ℝ),
        IsNormalizedDetectorCoefficient chiOne Uout NcutOut Yout sigma
          Nout scaleOut T b := by
  classical
  let Ncut := detectorArithmeticCutoff Y R
  let ZIset := postA5TypeISet chiOne U Y R V Z0
  let ZIIset := postA5SourceTypeIISet chiOne U Y R V Z0
  have hbudget' : ∀ rho ∈ Z0,
      principalPaperScaleTruncationError U rho Y R +
          Real.rpow R (-inputLoss kappaDet etaDet) +
          Real.rpow R (-inputLoss kappaDet etaDet) ≤
        Real.exp (-(1 / Y)) := by
    intro rho hrho
    rw [← hVR]
    exact hbudget rho hrho
  have hbetaLow' : ∀ rho ∈ Z0, 7 / 10 ≤ rho.re := by
    intro rho hrho
    exact hbetaSeven.trans (hbetaLow rho hrho)
  obtain ⟨j, S1, hS1, hcardI, hblock, hcardSplit⟩ :=
    principal_post_A5_budgeted_zeroSet_common_dyadic_or_sourceTypeII
      hkappaDet hetaDet hU hY hR hzero hbetaLow' hbetaHigh hUN hB hbudget'
  have hS1Z0 : S1 ⊆ Z0 := by
    intro rho hrho
    have hziset : rho ∈ postA5TypeISet chiOne U Y R
        (Real.rpow R (-inputLoss kappaDet etaDet)) Z0 := hS1 hrho
    exact (Finset.mem_filter.mp hziset).1
  have hS1source : ∀ m : ℤ,
      ∑ rho ∈ S1 with Int.floor rho.im = m, (1 : ℕ) ≤ 1 := by
    intro m
    simp only [Finset.sum_const, Nat.smul_one_eq_cast]
    exact floorBin_card_le_one_of_threeSeparated S1 hB
      (fun rho hrho rho' hrho' hne =>
        hsep rho (hS1Z0 hrho) rho' (hS1Z0 hrho') hne) m
  have hD : 1 ≤ 2 ^ (j : ℕ) := Nat.one_le_two_pow
  have hmass : ∀ rho ∈ endpointInterior S1 T C,
      (∫ xi in Set.Icc (-(Real.rpow T h)) (Real.rpow T h),
        ‖((𝓕 (detectorRealPartCutoff
          (rho.re - sigma) (2 ^ (j : ℕ))) : 𝓢(ℝ, ℂ)) xi)‖) ≤
        24 * Real.rpow T h := by
    intro rho hrho
    have hrhoS : rho ∈ S1 := Finset.filter_subset _ _ hrho
    have hrhoZ : rho ∈ Z0 := hS1Z0 hrhoS
    apply integral_norm_fourier_detectorRealPartCutoff_Icc_le hD
    · exact sub_nonneg.mpr (hbetaLow rho hrhoZ)
    · linarith [hbetaHigh rho hrhoZ]
    · exact Real.rpow_nonneg (by linarith : 0 ≤ T) _
  obtain ⟨braw, W, hbraw, hWsep, hWheight, hWlarge, hS1card⟩ :=
    exists_typeI_commonPolynomial_recentered_with_collar_provenance
      chiOne hU Y sigma j S1 (fun _ => 1) hC
      (fun rho hrho => hheight rho (hS1Z0 hrho))
      (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by linarith) _)) hV
      hmass
      (fun rho hrho => htail j rho
        (hbetaLow rho (hS1Z0 (Finset.filter_subset _ _ hrho)))
        (hbetaHigh rho (hS1Z0 (Finset.filter_subset _ _ hrho))))
      (fun rho hrho => by
        rw [hVR]
        exact hblock rho hrho)
      hS1source
  let D : ℕ := 2 ^ (j : ℕ)
  let L : ℝ := Real.rpow D (-sigma) *
    (Kd * Real.rpow (2 * D) e)
  have hDpos : (0 : ℝ) < D := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hLpos : 0 < L := by
    dsimp [L]
    exact mul_pos (Real.rpow_pos_of_pos hDpos _)
      (mul_pos hKd (Real.rpow_pos_of_pos (by positivity) _))
  let scale : ℝ := L⁻¹
  have hscale : 0 ≤ scale := inv_nonneg.mpr hLpos.le
  have hscaleL : scale * L ≤ 1 := by
    dsimp [scale]
    rw [inv_mul_cancel₀ hLpos.ne']
  let b : ℕ → ℂ := shellNormalizedCoefficient braw D scale
  have hbrawNorm : ∀ n,
      ‖braw n‖ = ‖detectorCommonCoefficient chiOne U Ncut Y sigma n‖ := by
    intro n
    rcases hbraw with hbraw | hbraw
    · rw [hbraw]
    · rw [hbraw, norm_translatedCoefficient]
  have hb : ∀ n, ‖b n‖ ≤ 1 := by
    apply norm_shellNormalizedCoefficient_le_one braw hscale hLpos.le hscaleL
    intro n hn
    rw [hbrawNorm n]
    dsimp [L, D, Ncut]
    exact detectorCommonCoefficient_shell_bound chiOne (by linarith) hD
      (by linarith) he.le hKd.le hdiv n hn
  have hprovenance :
      IsNormalizedDetectorCoefficient chiOne U Ncut Y sigma D scale T b := by
    exact isNormalizedDetectorCoefficient_of_recentered
      chiOne U Ncut Y sigma D scale T hbraw
  have hWlarge' : ∀ t ∈ W,
      Real.rpow D sigma * Real.rpow T (-inputLoss kappaOut etaOut) ≤
        ‖dirichletPolynomial b D t‖ := by
    intro t ht
    calc
      Real.rpow D sigma * Real.rpow T (-inputLoss kappaOut etaOut) ≤
          scale * (V / (4 * (24 * Real.rpow T h) *
            detectorDyadicCount (detectorArithmeticCutoff Y R))) := by
        simpa [D, L, scale] using hthreshold j
      _ ≤ scale * ‖dirichletPolynomial braw D t‖ := by
        exact mul_le_mul_of_nonneg_left (by simpa [D] using hWlarge t ht) hscale
      _ = ‖dirichletPolynomial b D t‖ := by
        symm
        exact dirichletPolynomial_shellNormalizedCoefficient braw D hscale t
  have hZIIsetSub : ZIIset ⊆
      postA5SourceTypeIISet chiOne U Y R V Z0 := by
    intro rho hrho
    simpa [ZIIset] using hrho
  obtain ⟨shift, hshiftChoice⟩ :=
    exists_sourceTypeII_shift_assignment chiOne hZIIsetSub
  have hshiftAbs : ∀ rho ∈ ZIIset,
      |shift rho| ≤ detectorVerticalCutoff R := by
    intro rho hrho
    exact abs_le.mpr (hshiftChoice rho hrho).1
  have hZIIbeta : ∀ rho ∈ ZIIset, sigma ≤ rho.re := by
    intro rho hrho
    have hrhoZ : rho ∈ Z0 := by
      have hz := (mem_postA5SourceTypeIISet_iff chiOne U Y R V Z0 rho).mp
        (hZIIsetSub hrho)
      exact hz.1
    exact hbetaLow rho hrhoZ
  have hZIIsep : ∀ rho ∈ ZIIset, ∀ rho' ∈ ZIIset, rho ≠ rho' →
      3 * detectorVerticalCutoff R ≤ |rho.im - rho'.im| := by
    intro rho hrho rho' hrho' hne
    apply hsep rho
    · exact (mem_postA5SourceTypeIISet_iff chiOne U Y R V Z0 rho).mp
        (hZIIsetSub hrho) |>.1
    · exact (mem_postA5SourceTypeIISet_iff chiOne U Y R V Z0 rho').mp
        (hZIIsetSub hrho') |>.1
    · exact hne
  have hmoment' := hmoment shift ZIIset hZIIsetSub
    (fun rho hrho => (hshiftChoice rho hrho).1)
  have hZIIcard : (ZIIset.card : ℝ) ≤
      Mfourth / (V / (29 * Real.rpow Y (1 / 2 - sigma) *
        (2 * Real.sqrt U))) ^ 4 :=
    typeII_card_le_of_shifted_fourthMoment chiOne ZIIset shift hB hU hY hV
      hshiftAbs hZIIsep hZIIbeta
      (fun rho hrho => (hshiftChoice rho hrho).2) hmoment'
  let typeICost : ℕ :=
    4 * (shiftedFloorWindowCount C * 1) * W.card + 2 * (C + 1) * 1
  let ZIout : ℕ :=
    P * detectorDyadicCount (detectorArithmeticCutoff Y R) * typeICost
  let ZIIout : ℕ := P * ZIIset.card
  have hS1card' : S1.card ≤ typeICost := by
    simpa [typeICost] using hS1card
  have hcardI' : ZIset.card ≤
      detectorDyadicCount (detectorArithmeticCutoff Y R) * S1.card := by
    dsimp [ZIset]
    rw [hVR]
    exact hcardI
  have hcardSplit' : Z0.card ≤ ZIset.card + ZIIset.card := by
    dsimp [ZIset, ZIIset]
    rw [hVR]
    exact hcardSplit
  have hcount : Ztarget ≤ ZIout + ZIIout := by
    calc
      Ztarget ≤ P * Z0.card := hcountThin
      _ ≤ P * (ZIset.card + ZIIset.card) :=
        Nat.mul_le_mul_left P hcardSplit'
      _ ≤ P *
          (detectorDyadicCount (detectorArithmeticCutoff Y R) * S1.card +
            ZIIset.card) := by
        exact Nat.mul_le_mul_left P (Nat.add_le_add_right hcardI' _)
      _ ≤ P *
          (detectorDyadicCount (detectorArithmeticCutoff Y R) * typeICost +
            ZIIset.card) := by
        gcongr
      _ = ZIout + ZIIout := by
        dsimp [ZIout, ZIIout]
        ring
  have hZIIoutBound : (ZIIout : ℝ) ≤ AZII * Real.rpow T
      (2 * (1 - sigma) + 2 * kappaOut + etaOut) := by
    have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
    dsimp [ZIIout]
    push_cast
    exact (mul_le_mul_of_nonneg_left hZIIcard hP0).trans hZIIledger
  by_cases hS1ne : S1.Nonempty
  · obtain ⟨rho, hrho⟩ := hS1ne
    refine ⟨D, b, W, ZIout, ZIIout, ?_, ?_, hb, hWsep, hWheight,
      hWlarge', hcount, ?_, hZIIoutBound, U, Ncut, Y, scale, hprovenance⟩
    · simpa [D] using hNlow j rho (hS1Z0 hrho) (by
        rw [hVR]
        exact hblock rho hrho)
    · simpa [D] using hNhigh j
    · simpa [ZIout, typeICost] using hZIledger j W
  · have hS1empty : S1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS1ne
    have hZIempty : ZIset.card = 0 := by
      have hcardI'' := hcardI'
      rw [hS1empty] at hcardI''
      simp only [Finset.card_empty, mul_zero] at hcardI''
      omega
    have hZ0toII : Z0.card ≤ ZIIset.card := by
      rw [hZIempty, zero_add] at hcardSplit'
      exact hcardSplit'
    have hcountEmpty : Ztarget ≤ ZIIout := by
      calc
        Ztarget ≤ P * Z0.card := hcountThin
        _ ≤ P * ZIIset.card := Nat.mul_le_mul_left P hZ0toII
        _ = ZIIout := rfl
    let Lempty : ℝ := Real.rpow U (-sigma) *
      (Kd * Real.rpow (2 * U) e)
    have hUpos : (0 : ℝ) < U := by exact_mod_cast hU
    have hLemptyPos : 0 < Lempty := by
      dsimp [Lempty]
      exact mul_pos (Real.rpow_pos_of_pos hUpos _)
        (mul_pos hKd (Real.rpow_pos_of_pos (by positivity) _))
    let scaleEmpty : ℝ := Lempty⁻¹
    have hscaleEmpty : 0 ≤ scaleEmpty := inv_nonneg.mpr hLemptyPos.le
    have hscaleEmptyL : scaleEmpty * Lempty ≤ 1 := by
      dsimp [scaleEmpty]
      rw [inv_mul_cancel₀ hLemptyPos.ne']
    let bEmpty : ℕ → ℂ := normalizedDetectorCoefficient
      chiOne U Ncut Y sigma U scaleEmpty
    have hbEmpty : ∀ n, ‖bEmpty n‖ ≤ 1 := by
      apply norm_shellNormalizedCoefficient_le_one
        (detectorCommonCoefficient chiOne U Ncut Y sigma)
        hscaleEmpty hLemptyPos.le hscaleEmptyL
      intro n hn
      dsimp [Lempty, Ncut]
      exact detectorCommonCoefficient_shell_bound chiOne (by linarith) hU
        (by linarith) he.le hKd.le hdiv n hn
    have hprovenanceEmpty :
        IsNormalizedDetectorCoefficient chiOne U Ncut Y sigma U scaleEmpty T
          bEmpty := Or.inl rfl
    refine ⟨U, bEmpty, ∅, 0, ZIIout, hUoutLow, hUoutHigh,
      hbEmpty, ?_, ?_, ?_, ?_, ?_, hZIIoutBound,
      U, Ncut, Y, scaleEmpty, hprovenanceEmpty⟩
    · intro t ht
      simp at ht
    · intro t ht
      simp at ht
    · intro t ht
      simp at ht
    · simpa using hcountEmpty
    · have hzeroLedger := hZIledger j (∅ : Finset ℝ)
      norm_num at hzeroLedger ⊢
      have hlhs : (0 : ℝ) ≤
          (P : ℝ) * detectorDyadicCount (detectorArithmeticCutoff Y R) *
            (2 * ((C : ℝ) + 1)) := by positivity
      exact hlhs.trans hzeroLedger

end
end MAPNearOneBulkBypassDetectorPrincipalFinite
#print axioms MAPNearOneBulkBypassDetectorPrincipalFinite.principal_finite_highStrip_structured_split_witness
