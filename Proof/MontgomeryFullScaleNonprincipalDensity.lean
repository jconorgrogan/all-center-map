import MontgomeryFullScaleNonprincipalCounts
import MontgomeryFullScaleDensityAbsorption
namespace MAPMontgomeryFullScaleNonprincipalDensity
open Filter
open scoped BigOperators
open Complex DirichletZeros ZeroDensityArithmetic
open MAPMontgomeryFullScaleNonprincipalCounts MAPMontgomeryFullScaleDensityAbsorption
open MAPMontgomeryFullScaleDetectorBudgets MAPMontgomeryFullScaleTypeIFamily
open MAPMontgomeryMixedMomentIntegral MAPMontgomeryPoweredSourceExponentLedger
open MAPMontgomeryTheorem12SourceDAG MAPMontgomeryLowStrip MAPAppendixA4DetectorDichotomy
open MAPAppendixA4PostA5SetAdapter MAPMRTCorollary25Minkowski
noncomputable section
set_option maxHeartbeats 1000000

theorem fullScaleY_eq_source (S sigma : ℝ) :
    fullScaleY S sigma = Real.rpow S (sourceYExponent sigma) := by
  unfold fullScaleY sourceYExponent
  rw [show 4-2*sigma=2*(2-sigma) by ring]

/-- Actual low-strip density with arbitrary positive slack, uniformly for
polylogarithmic conductors. This is derived from zero supports and analytic
moments; it does not assume a Montgomery zero-density source proposition. -/
theorem nonprincipal_fullScale_low_strip_density :
    ∀ K delta eta : ℝ, 0<K → 0<delta → 0<eta →
      ∃ C T₀ : ℝ, 0<C ∧ 2≤ T₀ ∧
        ∀ (T : ℝ) (q : ℕ) [NeZero q] (sigma : ℝ), T₀≤ T →
          (q : ℝ)≤ Real.rpow (Real.log T) K →
          1/2+delta≤ sigma → sigma≤7/10 →
          (nonprincipalAmbientZeroCountAtLevel q sigma T : ℝ) ≤
            C*Real.rpow T (uniformCoeff*(1-sigma)+eta) := by
  intro K delta eta hK hdelta heta
  obtain ⟨C₆,hC₆,hfinite⟩ := exists_constant_nonprincipal_fullScale_counts
  let A := fullStripFourierMass
  let G := mixedStripGammaConstant delta / Real.pi
  let kappa := min (eta/4) (1/4)
  have hkappa : 0<kappa := lt_min (by linarith) (by norm_num)
  have hkappahalf : kappa≤1/2 := (min_le_right _ _).trans (by norm_num)
  have hkappaeta : kappa≤ eta/2 := (min_le_left _ _).trans (by linarith)
  have hA : 0<A := by
    dsimp [A,fullStripFourierMass]
    linarith [MAPMontgomeryFullStripFourier.detectorFourierMomentConstant_nonneg 0]
  have hG : 0<G := div_pos (mixedStripGammaConstant_pos hdelta) Real.pi_pos
  obtain ⟨k,htail⟩ := exists_eventually_fullScale_fourier_tail hK hkappa
  let Cfinal := fullScaleCountConstant A G C₆ * (K+2)^139
  have hCfinal : 0<Cfinal := mul_pos (fullScaleCountConstant_pos hC₆.le) (by positivity)
  have hevent : ∀ᶠ T : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (sigma : ℝ),
      (q : ℝ)≤ Real.rpow (Real.log T) K → 1/2+delta≤ sigma → sigma≤7/10 →
      (nonprincipalAmbientZeroCountAtLevel q sigma T : ℝ) ≤
        Cfinal*Real.rpow T (uniformCoeff*(1-sigma)+eta) := by
    filter_upwards [eventually_fullScale_detector_budgets,
      eventually_fullScale_window_le_height hK,
      eventually_fullScale_count_envelope_absorption hK heta hA.le hG.le hC₆.le,
      htail, eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (3:ℝ),
      eventually_ge_atTop ((2*Real.pi)^2)] with T hbudgetT hwindowT habsorbT htailT hTexp hTthree hTpi
    intro q _ sigma hq hslo hshi
    have hT : 0≤ T := by linarith
    have hslo' : 1/2≤ sigma := by linarith
    let S := (q : ℝ)*T
    let U := fullScaleMollifier S
    let Y := fullScaleY S sigma
    let B := detectorVerticalCutoff S
    let H := Real.rpow T kappa
    let C := 2*Real.pi*H
    let Bthin := B+2*C+1
    have hH : 0<H := Real.rpow_pos_of_pos (by linarith) _
    have hC : 0≤ C := by dsimp [C]; positivity
    have hB0 : 0≤ B := by dsimp [B,detectorVerticalCutoff]; positivity
    have hp0 := hbudgetT q sigma (0:ℂ) (NeZero.pos q) hslo' hshi (by simpa using hT)
    change 1≤ U ∧ 1≤ Y ∧ U≤ detectorArithmeticCutoff Y S ∧ 1≤ B ∧ _ at hp0
    obtain ⟨hU,hY,hUN,hB,hrest⟩ := hp0
    have herror : ∀ rho : ℂ, |rho.im|≤ T →
        MAPAppendixA4RecenteredGammaRepair.detectorTruncationErrorEnvelopePolynomialHeight q U rho Y S +
          1/8+1/8≤ Real.exp (-(1/Y)) := by
      intro rho hrho
      exact (hbudgetT q sigma rho (NeZero.pos q) hslo' hshi hrho).2.2.2.2.1
    have hfull : (q : ℝ)*(2*(T+C)+1)≤(U : ℝ) := by
      exact (fullScale_collar_and_mollifier_cover (q:=q) (by linarith) hTpi hkappahalf).2
    have htail' : 2*(detectorArithmeticCutoff Y S : ℝ)^2 *
        ((H^k)⁻¹ * MAPMontgomeryFullStripFourier.detectorFourierMomentConstant k) ≤
        ((1/8)/(detectorDyadicCount (detectorArithmeticCutoff Y S) : ℝ))/2 := by
      simpa only [S,Y,H,fullScaleY_eq_source,detectorArithmeticCutoff,mul_assoc] using
        htailT q sigma hq hslo' hshi
    obtain ⟨RI,RII,hRI,hRII,hcount,hI,hII⟩ := hfinite hU hdelta hslo hshi hY
      (by norm_num : (0:ℝ)<1/8) hT hH (le_rfl : 2*Real.pi*H≤ C)
      (show 0≤ Bthin by dsimp [Bthin]; linarith)
      (show B≤ Bthin by dsimp [Bthin]; linarith)
      (show 2*C+1≤3*Bthin by dsimp [Bthin]; linarith)
      hB (show 3≤ T+B by linarith) hUN hfull k htail' herror
    have hnorm := fullScale_finite_count_envelope (q:=q) (T:=T) (sigma:=sigma) (kappa:=kappa)
      (A:=A) (G:=G) (C6:=C₆) (RI:=RI) (RII:=RII) hTexp hslo' hshi
      hkappa.le hA hG.le hC₆.le hRI hRII (hwindowT q hq)
    have hnorm' := hnorm
      (by simpa only [S,Y,fullScaleY_eq_source,detectorArithmeticCutoff,A,mul_assoc] using hI)
      (by simpa only [S,Y,U,B,G,fullScaleY_eq_source,fullScaleMollifier,detectorVerticalCutoff,
          RamachandraTheorem6ShiftedStripSource.ramachandraTheorem6K2Scale,mul_assoc,mul_left_comm,mul_comm] using hII)
    have hcount' : (nonprincipalAmbientZeroCountAtLevel q sigma T : ℝ) ≤
        fullScaleCountConstant A G C₆ * Real.rpow T kappa *
          Real.rpow ((q : ℝ)*T) (inghamExponent sigma) *
          (1+Real.log ((q : ℝ)*T))^139 * Real.exp (Real.sqrt (Real.log (q : ℝ))) := by
      apply hcount.trans
      simpa only [S,B,H,C,Bthin,detectorVerticalCutoff,Nat.cast_mul] using hnorm'
    exact hcount'.trans (habsorbT q sigma kappa hq hkappaeta hslo' hshi)
  obtain ⟨T₁,hT₁⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨Cfinal,max 2 T₁,hCfinal,le_max_left _ _,?_⟩
  intro T q _ sigma hT hq hslo hshi
  exact hT₁ T ((le_max_right _ _).trans hT) q sigma hq hslo hshi
end
end MAPMontgomeryFullScaleNonprincipalDensity
#print axioms MAPMontgomeryFullScaleNonprincipalDensity.nonprincipal_fullScale_low_strip_density
