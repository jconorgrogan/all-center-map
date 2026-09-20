import MontgomeryFullScaleDetectorPartition
import MontgomeryPrincipalFullScaleThinning
namespace MAPMontgomeryFullScalePrincipalCounts
open scoped BigOperators
open Complex DirichletZeros
open MAPMontgomeryFullScaleTypeIFamily MAPMontgomeryMixedMomentTypeII
open MAPMontgomeryFullScaleDetectorPartition MAPMontgomeryPrincipalFullScaleThinning
open MAPAppendixA4DetectorDichotomy MAPAppendixA4PostA5SetAdapter
open MAPPrincipalZetaDetectorDichotomy MAPPrincipalZetaDetectorPoleRemoval
open MAPMontgomeryMixedMomentIntegral MAPMRTCorollary25Minkowski
noncomputable section
local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)
set_option maxHeartbeats 800000

/-- Complete finite conductor-one count, including every multiplicity and
an explicit additive representative for the principal low-height exception. -/
theorem exists_constant_principal_fullScale_counts :
    ∃ C₆ : ℝ, 0 < C₆ ∧
    ∀ {U : ℕ} {delta sigma Y R V c C T H Bthin : ℝ},
      1 ≤ U → 0 < delta → 1/2+delta ≤ sigma → sigma ≤ 7/10 →
      1 ≤ Y → 0 < V → 0 ≤ T → 0 < H → 2*Real.pi*H ≤ C →
      1 ≤ Bthin → detectorVerticalCutoff R ≤ Bthin → 2*C+1 ≤ 3*Bthin →
      1 ≤ detectorVerticalCutoff R → 3 ≤ T+detectorVerticalCutoff R →
      U ≤ detectorArithmeticCutoff Y R → 2*(T+C)+1 ≤ (U : ℝ) →
      ∀ k : ℕ,
      2*(detectorArithmeticCutoff Y R : ℝ)^2 * ((H^k)⁻¹ *
        MAPMontgomeryFullStripFourier.detectorFourierMomentConstant k) ≤
        (V/(detectorDyadicCount (detectorArithmeticCutoff Y R) : ℝ))/2 →
      (∀ rho : ℂ, |rho.im| ≤ T →
        principalPoleSubtractedPaperScaleError U rho Y R + c+V+V ≤ Real.exp (-(1/Y))) →
      (∀ rho : ℂ, |rho.im| ≤ T → MAPPrincipalZetaFixedStrip.principalRegularized rho = 0 →
        sigma ≤ rho.re → rho.re ≤ 1 → detectorVerticalCutoff R ≤ |rho.im| →
        ‖principalDetectorResidue rho U Y‖ ≤ c) →
      ∃ RI RII : ℝ, 0 ≤ RI ∧ 0 ≤ RII ∧
        (dirichletZeroCount chiOne sigma T : ℝ) ≤
          (principalThinningFactor T Bthin : ℝ) * (RI+RII+1) ∧
        RI * (V/(4*fullStripFourierMass*detectorDyadicCount (detectorArithmeticCutoff Y R)))^2 ≤
          (detectorDyadicCount (detectorArithmeticCutoff Y R) : ℝ)^2 * 3*(2+8*Real.pi) *
            Real.rpow (detectorArithmeticCutoff Y R) (2*(1-sigma)) *
              (1+Real.log (2*(detectorArithmeticCutoff Y R : ℝ)))^4 ∧
        RII^3 * V^4 ≤
          ((mixedStripGammaConstant delta / Real.pi)*Real.rpow Y (1/2-sigma))^4 *
            (∫ u in (-detectorVerticalCutoff R)..detectorVerticalCutoff R, perronWeight u) *
            (C₆ * RamachandraTheorem6ShiftedStripSource.ramachandraTheorem6K2Scale 1
              (T+detectorVerticalCutoff R)) *
            ((2*(T+detectorVerticalCutoff R)+8*Real.pi*(U : ℝ)) * (1+Real.log U))^2 := by
  obtain ⟨C₆,hC₆,hII⟩ := exists_constant_mixed_typeII_family_budget
  refine ⟨C₆,hC₆,?_⟩
  intro U delta sigma Y R V c C T H Bthin hU hdelta hsigmaLow hsigmaHigh hY hV hT hH hHC
    hthin hBthin hCthin hB hTB hUN hfull k htail herror hresidue
  classical
  obtain ⟨S,hsub,hhigh,hsep,himage,hcount⟩ := exists_principal_high_threeBSeparated
    (T := T) (sigma := sigma) (by linarith) hthin
  have hrect : ∀ rho ∈ S, rho ∈ zeroRectangle sigma T := by
    intro rho hrho
    exact (zeroDivisor chiOne sigma T).supportWithinDomain
      ((zeroSupport_mem_iff chiOne sigma T rho).mp (hsub hrho))
  have hbeta : ∀ rho ∈ S, sigma ≤ rho.re ∧ rho.re ≤ 1 := by
    intro rho hrho; exact (Complex.mem_reProdIm.mp (hrect rho hrho)).1
  have hheight : ∀ rho ∈ S, |rho.im| ≤ T := by
    intro rho hrho; exact abs_le.mpr (Complex.mem_reProdIm.mp (hrect rho hrho)).2
  have hzero : ∀ rho ∈ S, MAPPrincipalZetaFixedStrip.principalRegularized rho = 0 := by
    intro rho hrho
    have h := regularizedLFunction_eq_zero_of_mem_zeroSupport chiOne sigma T (hsub hrho)
    simpa [regularizedLFunction, MAPPrincipalZetaFixedStrip.principalRegularized] using h
  let SI := S.filter (fun rho => V ≤ ‖arithmeticDetectorBlock chiOne U (detectorArithmeticCutoff Y R) rho Y‖)
  let SII := S.filter (fun rho => V ≤ ‖normalizedCentralGammaIntegral chiOne U rho Y (detectorVerticalCutoff R)‖)
  have hIsub : SI ⊆ S := Finset.filter_subset _ _
  have hIIsub : SII ⊆ S := Finset.filter_subset _ _
  have hcover : S.card ≤ SI.card+SII.card := principal_fullScale_detector_cover S hU hY hUN hB
    hzero (fun rho hrho => by linarith [(hbeta rho hrho).1])
    (fun rho hrho => (hbeta rho hrho).2)
    (fun rho hrho => hresidue rho (hheight rho hrho) (hzero rho hrho) (hbeta rho hrho).1 (hbeta rho hrho).2
      (hBthin.trans (hhigh rho hrho)))
    (fun rho hrho => herror rho (hheight rho hrho))
  let WI : DirichletCharacter ℂ 1 → Finset ℂ := fun _ => SI
  let WII : DirichletCharacter ℂ 1 → Finset ℂ := fun _ => SII
  have hIsum : (∑ chi : DirichletCharacter ℂ 1, ((WI chi).card : ℝ)) = (SI.card : ℝ) := by simp [WI]
  have hIIsum : (∑ chi : DirichletCharacter ℂ 1, ((WII chi).card : ℝ)) = (SII.card : ℝ) := by simp [WII]
  have hIcount := fullScale_typeI_family_budget (Y := Y) (sigma := sigma) hU hUN WI (by linarith) (by linarith)
    (by linarith : sigma ≤ 1) hH hV hHC hT (by simpa using hfull) k
    (fun chi rho hrho rho' hrho' hne => hCthin.trans (hsep rho (hIsub hrho) rho' (hIsub hrho') hne))
    (fun chi rho hrho => (hbeta rho (hIsub hrho)).1)
    (fun chi rho hrho => (hbeta rho (hIsub hrho)).2)
    (fun chi rho hrho => hheight rho (hIsub hrho)) htail
    (by intro chi rho hrho; have heq : chi=chiOne := Subsingleton.elim _ _; subst chi
        exact (Finset.mem_filter.mp hrho).2)
  rw [hIsum] at hIcount
  have hIIcount := hII WII hU hdelta hY (show 0 < detectorVerticalCutoff R by linarith)
    hT hTB hV.le
    (fun chi rho hrho => hsigmaLow.trans (hbeta rho (hIIsub hrho)).1)
    (fun chi rho hrho => (hbeta rho (hIIsub hrho)).2)
    (fun chi rho hrho => (hbeta rho (hIIsub hrho)).1)
    (fun chi rho hrho => hheight rho (hIIsub hrho))
    (fun chi rho hrho rho' hrho' hne =>
      (show 3*detectorVerticalCutoff R ≤ 3*Bthin by linarith).trans
        (hsep rho (hIIsub hrho) rho' (hIIsub hrho') hne))
    (by intro chi rho hrho; have heq : chi=chiOne := Subsingleton.elim _ _; subst chi
        exact (Finset.mem_filter.mp hrho).2)
  rw [hIIsum] at hIIcount
  refine ⟨SI.card,SII.card,Nat.cast_nonneg _,Nat.cast_nonneg _,?_,hIcount,?_⟩
  · have h := hcount.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hcover 1))
    exact_mod_cast h
  · simpa only [Nat.cast_one,one_mul] using hIIcount
end
end MAPMontgomeryFullScalePrincipalCounts
#print axioms MAPMontgomeryFullScalePrincipalCounts.exists_constant_principal_fullScale_counts
