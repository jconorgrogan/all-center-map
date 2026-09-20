import MontgomeryFullScaleNonprincipalDensity
import MontgomeryFullScalePrincipalCounts
namespace MAPMontgomeryFullScalePrincipalDensity
open Filter
open scoped BigOperators
open Complex DirichletZeros ZeroDensityArithmetic MAPMontgomeryLowStrip
open MAPMontgomeryFullScaleNonprincipalDensity MAPMontgomeryFullScalePrincipalCounts
open MAPMontgomeryFullScaleDensityAbsorption MAPMontgomeryFullScaleDetectorBudgets
open MAPMontgomeryFullScaleTypeIFamily MAPMontgomeryMixedMomentIntegral
open MAPMontgomeryPoweredSourceExponentLedger MAPAppendixA4DetectorDichotomy
open MAPAppendixA4PostA5SetAdapter
noncomputable section
local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)
set_option maxHeartbeats 1000000

theorem principal_fullScale_low_strip_density :
    ∀ delta eta : ℝ, 0 < delta → 0 < eta →
      ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
        ∀ (T sigma : ℝ), T₀ ≤ T → 1/2+delta ≤ sigma → sigma ≤ 7/10 →
          (dirichletZeroCount chiOne sigma T : ℝ) ≤
            C*Real.rpow T (uniformCoeff*(1-sigma)+eta) := by
  intro delta eta hdelta heta
  obtain ⟨C₆,hC₆,hfinite⟩ := exists_constant_principal_fullScale_counts
  let A := fullStripFourierMass
  let G := mixedStripGammaConstant delta / Real.pi
  let kappa := min (eta/4) (1/4)
  have hkappa : 0 < kappa := lt_min (by linarith) (by norm_num)
  have hkappahalf : kappa ≤ 1/2 := (min_le_right _ _).trans (by norm_num)
  have hkappaeta : kappa ≤ eta/2 := (min_le_left _ _).trans (by linarith)
  have hA : 0 < A := by
    dsimp [A,fullStripFourierMass]
    linarith [MAPMontgomeryFullStripFourier.detectorFourierMomentConstant_nonneg 0]
  have hG : 0 < G := div_pos (mixedStripGammaConstant_pos hdelta) Real.pi_pos
  obtain ⟨k,htail⟩ := exists_eventually_fullScale_fourier_tail (K:=1) (by norm_num) hkappa
  let Cfinal := principalScaleCountConstant A G C₆ * 3^139
  have hCfinal : 0 < Cfinal := mul_pos (principalScaleCountConstant_pos hC₆.le) (by positivity)
  have hevent : ∀ᶠ T : ℝ in atTop, ∀ sigma : ℝ,
      1/2+delta ≤ sigma → sigma ≤ 7/10 →
      (dirichletZeroCount chiOne sigma T : ℝ) ≤
        Cfinal*Real.rpow T (uniformCoeff*(1-sigma)+eta) := by
    filter_upwards [eventually_fullScale_detector_budgets,
      eventually_fullScale_window_le_height (K:=1) (by norm_num),
      eventually_fullScale_principal_count_envelope_absorption (A:=A) (G:=G) heta hC₆.le,
      htail, eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (3:ℝ),
      eventually_ge_atTop ((2*Real.pi)^2)] with T hbudgetT hwindowT habsorbT htailT hTexp hTthree hTpi
    intro sigma hslo hshi
    have hT : 0 ≤ T := by linarith
    have hslo' : 1/2 ≤ sigma := by linarith
    have hlog1 : 1 ≤ Real.log T := by
      have h := Real.log_le_log (Real.exp_pos 1) hTexp
      simpa using h
    have hqpoly : (1:ℝ) ≤ Real.rpow (Real.log T) 1 := by simpa using hlog1
    let U := fullScaleMollifier T
    let Y := fullScaleY T sigma
    let B := detectorVerticalCutoff T
    let H := Real.rpow T kappa
    let C := 2*Real.pi*H
    let Bthin := B+2*C+1
    have hH : 0 < H := Real.rpow_pos_of_pos (by linarith) _
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hB0 : 0 ≤ B := by dsimp [B,detectorVerticalCutoff]; positivity
    have hp0 := hbudgetT 1 sigma (0:ℂ) (by norm_num) hslo' hshi (by simpa using hT)
    simp only [Nat.cast_one,one_mul] at hp0
    change 1 ≤ U ∧ 1 ≤ Y ∧ U ≤ detectorArithmeticCutoff Y T ∧ 1 ≤ B ∧ _ at hp0
    obtain ⟨hU,hY,hUN,hB,hrest⟩ := hp0
    have herror : ∀ rho : ℂ, |rho.im| ≤ T →
        MAPPrincipalZetaDetectorDichotomy.principalPoleSubtractedPaperScaleError U rho Y T +
          1/8+1/8+1/8 ≤ Real.exp (-(1/Y)) := by
      intro rho hrho
      simpa only [Nat.cast_one,one_mul] using
        (hbudgetT 1 sigma rho (by norm_num) hslo' hshi hrho).2.2.2.2.2.1
    have hresidue : ∀ rho : ℂ, |rho.im| ≤ T →
        MAPPrincipalZetaFixedStrip.principalRegularized rho = 0 → sigma ≤ rho.re → rho.re ≤ 1 →
        B ≤ |rho.im| → ‖MAPPrincipalZetaDetectorPoleRemoval.principalDetectorResidue rho U Y‖ ≤ 1/8 := by
      intro rho hrheight hz hβlo hβhi hγ
      have h := (hbudgetT 1 sigma rho (by norm_num) hslo' hshi hrheight).2.2.2.2.2.2
      simp only [Nat.cast_one,one_mul] at h
      exact h hz (by linarith) hβhi hγ
    have hfull : 2*(T+C)+1 ≤ (U : ℝ) := by
      simpa only [Nat.cast_one,one_mul] using
        (fullScale_collar_and_mollifier_cover (q:=1) (by linarith) hTpi hkappahalf).2
    have htail' : 2*(detectorArithmeticCutoff Y T : ℝ)^2 *
        ((H^k)⁻¹ * MAPMontgomeryFullStripFourier.detectorFourierMomentConstant k) ≤
        ((1/8)/(detectorDyadicCount (detectorArithmeticCutoff Y T) : ℝ))/2 := by
      simpa only [Y,H,fullScaleY_eq_source,detectorArithmeticCutoff,Nat.cast_one,one_mul,mul_assoc] using
        htailT 1 sigma (by simpa using hqpoly) hslo' hshi
    obtain ⟨RI,RII,hRI,hRII,hcount,hI,hII⟩ := hfinite (c:=1/8) hU hdelta hslo hshi hY
      (by norm_num : (0:ℝ)<1/8) hT hH (le_rfl : 2*Real.pi*H ≤ C)
      (show 1 ≤ Bthin by dsimp [Bthin]; linarith)
      (show B ≤ Bthin by dsimp [Bthin]; linarith)
      (show 2*C+1 ≤ 3*Bthin by dsimp [Bthin]; linarith)
      hB (show 3 ≤ T+B by linarith) hUN hfull k htail' herror hresidue
    have hnorm := fullScale_finite_principal_count_envelope (T:=T) (sigma:=sigma) (kappa:=kappa)
      (A:=A) (G:=G) (C6:=C₆) (RI:=RI) (RII:=RII) hTexp hslo' hshi
      hkappa.le hA hG.le hC₆.le hRI hRII (by simpa only [Nat.cast_one,one_mul] using hwindowT 1 (by simpa using hqpoly))
    have hnorm' := hnorm
      (by simpa only [Y,fullScaleY_eq_source,detectorArithmeticCutoff,A,mul_assoc] using hI)
      (by simpa only [Y,U,B,G,fullScaleY_eq_source,fullScaleMollifier,detectorVerticalCutoff,
          RamachandraTheorem6ShiftedStripSource.ramachandraTheorem6K2Scale,mul_assoc,
          Nat.cast_one,one_mul,Real.log_one,Real.sqrt_zero,Real.exp_zero,mul_one] using hII)
    have hcount' : (dirichletZeroCount chiOne sigma T : ℝ) ≤
        principalScaleCountConstant A G C₆ * Real.rpow T kappa *
          Real.rpow T (inghamExponent sigma) * (1+Real.log T)^139 := by
      apply hcount.trans
      simpa only [B,H,C,Bthin,detectorVerticalCutoff] using hnorm'
    exact hcount'.trans (habsorbT sigma kappa hkappaeta hslo' hshi)
  obtain ⟨T₁,hT₁⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨Cfinal,max 2 T₁,hCfinal,le_max_left _ _,?_⟩
  intro T sigma hT hslo hshi
  exact hT₁ T ((le_max_right _ _).trans hT) sigma hslo hshi
end
end MAPMontgomeryFullScalePrincipalDensity
#print axioms MAPMontgomeryFullScalePrincipalDensity.principal_fullScale_low_strip_density
