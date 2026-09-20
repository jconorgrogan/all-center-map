import MontgomeryFullScaleDetectorPartition
import MontgomeryFullScaleDetectorBudgets
namespace MAPMontgomeryFullScaleNonprincipalCounts
open scoped BigOperators
open Complex DirichletZeros
open MAPMontgomeryFullScaleTypeIFamily MAPMontgomeryMixedMomentTypeII
open MAPMontgomeryFullScaleDetectorPartition MAPMontgomeryLowStripNonprincipalSelection
open MAPMontgomeryTheorem12SourceDAG PostA5LongSpacingAssembly PostA5CrowdingDeterministic
open MAPAppendixA4DetectorDichotomy MAPAppendixA4RecenteredGammaRepair MAPAppendixA4PostA5SetAdapter
open MAPMontgomeryMixedMomentIntegral MAPMRTCorollary25Minkowski
noncomputable section
set_option maxHeartbeats 1000000

/-- Complete finite nonprincipal zero-count reduction with both analytic
branches instantiated. Only literal scalar parameter inequalities remain. -/
theorem exists_constant_nonprincipal_fullScale_counts :
    ∃ C₆ : ℝ, 0 < C₆ ∧
    ∀ {q : ℕ} [NeZero q] {U : ℕ} {delta sigma Y R V C T H Bthin : ℝ},
      1 ≤ U → 0 < delta → 1/2+delta ≤ sigma → sigma ≤ 7/10 →
      1 ≤ Y → 0 < V → 0 ≤ T → 0 < H → 2*Real.pi*H ≤ C →
      0 ≤ Bthin → detectorVerticalCutoff R ≤ Bthin → 2*C+1 ≤ 3*Bthin →
      1 ≤ detectorVerticalCutoff R → 3 ≤ T+detectorVerticalCutoff R →
      U ≤ detectorArithmeticCutoff Y R →
      (q : ℝ)*(2*(T+C)+1) ≤ (U : ℝ) →
      ∀ k : ℕ,
      2*(detectorArithmeticCutoff Y R : ℝ)^2 * ((H^k)⁻¹ *
        MAPMontgomeryFullStripFourier.detectorFourierMomentConstant k) ≤
        (V/(detectorDyadicCount (detectorArithmeticCutoff Y R) : ℝ))/2 →
      (∀ rho : ℂ, |rho.im| ≤ T →
        detectorTruncationErrorEnvelopePolynomialHeight q U rho Y R + V+V ≤
          Real.exp (-(1/Y))) →
      ∃ RI RII : ℝ, 0 ≤ RI ∧ 0 ≤ RII ∧
        (nonprincipalAmbientZeroCountAtLevel q sigma T : ℝ) ≤
          certifiedA5CrowdingEnvelope q T *
            (longSpacingColorCount Bthin * certifiedA5CrowdingNatCap q T) * (RI+RII) ∧
        RI * (V/(4*fullStripFourierMass*detectorDyadicCount (detectorArithmeticCutoff Y R)))^2 ≤
          (detectorDyadicCount (detectorArithmeticCutoff Y R) : ℝ)^2 * 3*(2+8*Real.pi) *
            Real.rpow (detectorArithmeticCutoff Y R) (2*(1-sigma)) *
              (1+Real.log (2*(detectorArithmeticCutoff Y R : ℝ)))^4 ∧
        RII^3 * V^4 ≤
          ((mixedStripGammaConstant delta / Real.pi)*Real.rpow Y (1/2-sigma))^4 *
            (∫ u in (-detectorVerticalCutoff R)..detectorVerticalCutoff R, perronWeight u) *
            (C₆ * RamachandraTheorem6ShiftedStripSource.ramachandraTheorem6K2Scale q
              (T+detectorVerticalCutoff R)) *
            (((q : ℝ)*(2*(T+detectorVerticalCutoff R))+8*Real.pi*(U : ℝ)) *
              (1+Real.log U))^2 := by
  obtain ⟨C₆,hC₆,hII⟩ := exists_constant_mixed_typeII_family_budget
  refine ⟨C₆,hC₆,?_⟩
  intro q _ U delta sigma Y R V C T H Bthin hU hdelta hsigmaLow hsigmaHigh hY hV hT hH hHC
    hthin hBthin hCthin hB hTB hUN hfull k htail herror
  classical
  obtain ⟨W,hprincipal,hsub,hsep,hcount⟩ := exists_simultaneous_nonprincipal_threeBSeparated
    (q := q) (sigma := sigma) (by linarith) hT hthin
  have hchi : ∀ chi rho, rho ∈ W chi → chi ≠ 1 := by
    intro chi rho hrho heq
    subst chi
    rw [hprincipal] at hrho
    exact Finset.notMem_empty _ hrho
  have hrect : ∀ chi rho, rho ∈ W chi → rho ∈ zeroRectangle sigma T := by
    intro chi rho hrho
    have hs := hsub chi (hchi chi rho hrho) hrho
    exact (zeroDivisor chi sigma T).supportWithinDomain ((zeroSupport_mem_iff chi sigma T rho).mp hs)
  have hbeta : ∀ chi rho, rho ∈ W chi → sigma ≤ rho.re ∧ rho.re ≤ 1 := by
    intro chi rho hrho
    exact (Complex.mem_reProdIm.mp (hrect chi rho hrho)).1
  have hheight : ∀ chi rho, rho ∈ W chi → |rho.im| ≤ T := by
    intro chi rho hrho
    exact abs_le.mpr (Complex.mem_reProdIm.mp (hrect chi rho hrho)).2
  have hzero : ∀ chi rho, rho ∈ W chi → DirichletCharacter.LFunction chi rho = 0 := by
    intro chi rho hrho
    have hz := regularizedLFunction_eq_zero_of_mem_zeroSupport chi sigma T
      (hsub chi (hchi chi rho hrho) hrho)
    simpa [regularizedLFunction,hchi chi rho hrho] using hz
  let WI := arithmeticFamily W U (detectorArithmeticCutoff Y R) Y V
  let WII := centralFamily W U Y (detectorVerticalCutoff R) V
  have hI_sub : ∀ chi, WI chi ⊆ W chi := fun chi => Finset.filter_subset _ _
  have hII_sub : ∀ chi, WII chi ⊆ W chi := fun chi => Finset.filter_subset _ _
  have hcover := nonprincipal_fullScale_detector_family_cover W hU hY hUN hB hchi hzero
    (fun chi rho hrho => by linarith [(hbeta chi rho hrho).1])
    (fun chi rho hrho => (hbeta chi rho hrho).2)
    (fun chi rho hrho => herror rho (hheight chi rho hrho))
  let RI : ℝ := ∑ chi : DirichletCharacter ℂ q, ((WI chi).card : ℝ)
  let RII : ℝ := ∑ chi : DirichletCharacter ℂ q, ((WII chi).card : ℝ)
  have hIcount := fullScale_typeI_family_budget hU hUN WI (by linarith) (by linarith)
    (by linarith : sigma ≤ 1) hH hV hHC hT hfull k
    (fun chi rho hrho rho' hrho' hne => hCthin.trans
      (hsep chi rho (hI_sub chi hrho) rho' (hI_sub chi hrho') hne))
    (fun chi rho hrho => (hbeta chi rho (hI_sub chi hrho)).1)
    (fun chi rho hrho => (hbeta chi rho (hI_sub chi hrho)).2)
    (fun chi rho hrho => hheight chi rho (hI_sub chi hrho)) htail
    (fun chi rho hrho => (Finset.mem_filter.mp hrho).2)
  have hIIcount := hII WII hU hdelta hY (show 0 < detectorVerticalCutoff R by linarith)
    hT hTB hV.le
    (fun chi rho hrho => hsigmaLow.trans (hbeta chi rho (hII_sub chi hrho)).1)
    (fun chi rho hrho => (hbeta chi rho (hII_sub chi hrho)).2)
    (fun chi rho hrho => (hbeta chi rho (hII_sub chi hrho)).1)
    (fun chi rho hrho => hheight chi rho (hII_sub chi hrho))
    (fun chi rho hrho rho' hrho' hne =>
      (show 3*detectorVerticalCutoff R ≤ 3*Bthin by linarith).trans
        (hsep chi rho (hII_sub chi hrho) rho' (hII_sub chi hrho') hne))
    (fun chi rho hrho => (Finset.mem_filter.mp hrho).2)
  have hRI : 0 ≤ RI := Finset.sum_nonneg (fun chi hchi => Nat.cast_nonneg _)
  have hRII : 0 ≤ RII := Finset.sum_nonneg (fun chi hchi => Nat.cast_nonneg _)
  refine ⟨RI,RII,hRI,hRII,?_,hIcount,hIIcount⟩
  have henv : 0 ≤ certifiedA5CrowdingEnvelope q T := by
    have hqone : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
    have hs : 1 ≤ (q : ℝ)*(T+3) := one_le_mul_of_one_le_of_one_le hqone (by linarith)
    unfold certifiedA5CrowdingEnvelope
    exact div_nonneg (by
      have := Real.log_nonneg hs
      have := Real.log_nonneg (by norm_num : (1:ℝ)≤3)
      have := Real.log_nonneg (by norm_num : (1:ℝ)≤3200)
      linarith) (Real.log_nonneg (by norm_num))
  apply hcount.trans
  exact mul_le_mul_of_nonneg_left hcover (mul_nonneg henv (by positivity))
end
end MAPMontgomeryFullScaleNonprincipalCounts
#print axioms MAPMontgomeryFullScaleNonprincipalCounts.exists_constant_nonprincipal_fullScale_counts
