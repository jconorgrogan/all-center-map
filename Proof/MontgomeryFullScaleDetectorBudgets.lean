import PostA5RecenteredDetectorAbsorption
import PrincipalZetaDetectorDichotomy

/-! Uniform literal detector budgets for the full hybrid mollifier.
The conductor and ordinate costs remain in the repaired polynomial-height
envelope; the conductor-one residue is bounded separately at high ordinates. -/
namespace MAPMontgomeryFullScaleDetectorBudgets
open Filter MeasureTheory Set
open MAPAppendixA4DetectorDichotomy MAPAppendixA4RecenteredGammaRepair
open MAPPrincipalZetaDetectorDichotomy MAPPrincipalZetaDetectorPoleRemoval
open PostA5RecenteredDetectorAbsorption
noncomputable section
set_option maxHeartbeats 800000

def fullScaleMollifier (S : ℝ) : ℕ := ⌈10 * S⌉₊
def fullScaleY (S sigma : ℝ) : ℝ := Real.rpow S (3 / (4 - 2 * sigma))

def nonprincipalVerticalConstant : ℝ :=
  (1 / (2 * Real.pi)) * (460800 * 36 * Real.exp (1 / 2))
def principalVerticalConstant : ℝ :=
  (1 / (2 * Real.pi)) *
    (4 * (12 * 3200 * 5 ^ 6 * (2 : ℝ) ^ 7 *
      (Nat.factorial 7 : ℝ) * Real.exp (1 / 2)))

theorem fullScaleY_bounds {S sigma : ℝ} (hS : 1 ≤ S)
    (hslo : 1 / 2 ≤ sigma) (hshi : sigma ≤ 7 / 10) :
    S ≤ fullScaleY S sigma ∧ fullScaleY S sigma ≤ S ^ 2 := by
  have hd : 0 < 4 - 2 * sigma := by linarith
  have hlo : 1 ≤ 3 / (4 - 2 * sigma) := (le_div_iff₀ hd).2 (by linarith)
  have hhi : 3 / (4 - 2 * sigma) ≤ 2 := (div_le_iff₀ hd).2 (by linarith)
  constructor
  · simpa [fullScaleY, Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hS hlo
  · simpa [fullScaleY, Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hS hhi

theorem fullScaleMollifier_bounds {S : ℝ} (hS : 12 ≤ S) :
    1 ≤ fullScaleMollifier S ∧ (fullScaleMollifier S + 1 : ℝ) ≤ S ^ 2 := by
  have hc : (fullScaleMollifier S : ℝ) < 10 * S + 1 := by
    exact Nat.ceil_lt_add_one (by linarith)
  have hl : 10 * S ≤ (fullScaleMollifier S : ℝ) := Nat.le_ceil _
  constructor
  · have : (1 : ℝ) ≤ (fullScaleMollifier S : ℝ) := by linarith
    exact_mod_cast this
  · nlinarith [sq_nonneg (S - 12)]

theorem arithmetic_tail_le_gaussian {S Y : ℝ} {U : ℕ} (hY : 1 ≤ Y) :
    (U + 1 : ℝ) * (Real.exp (-(1 / Y))) ^ (detectorArithmeticCutoff Y S + 1) *
      (1 - Real.exp (-(1 / Y)))⁻¹ ≤
    (U + 1 : ℝ) * Real.exp 1 * Y * Real.exp (-(Real.log S) ^ 2) := by
  have hYpos : 0 < Y := zero_lt_one.trans_le hY
  have hcut : Y * (Real.log S) ^ 2 ≤ (detectorArithmeticCutoff Y S + 1 : ℕ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ (detectorArithmeticCutoff Y S))
  have hdiv : (Real.log S) ^ 2 ≤ (detectorArithmeticCutoff Y S + 1 : ℕ) / Y := by
    rw [le_div_iff₀ hYpos]
    simpa [mul_comm] using hcut
  have hpow : (Real.exp (-(1 / Y))) ^ (detectorArithmeticCutoff Y S + 1) ≤
      Real.exp (-(Real.log S) ^ 2) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    convert neg_le_neg hdiv using 1 <;> ring
  have hinv := one_sub_exp_neg_inv_le_exp_mul hY
  have hinv0 : 0 ≤ (1 - Real.exp (-(1 / Y)))⁻¹ := by
    apply inv_nonneg.mpr
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))
  calc
    _ ≤ (U + 1 : ℝ) * Real.exp (-(Real.log S) ^ 2) * (Real.exp 1 * Y) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity)) hinv hinv0 (by positivity)
    _ = _ := by ring

theorem arithmetic_tail_le_inv {S Y : ℝ} {U : ℕ}
    (hS : 1 ≤ S) (hlog : 20 ≤ Real.log S)
    (hconst : Real.exp 1 ≤ S) (hU : (U + 1 : ℝ) ≤ S ^ 2)
    (hY : 1 ≤ Y) (hYhi : Y ≤ S ^ 2) :
    (U + 1 : ℝ) * (Real.exp (-(1 / Y))) ^ (detectorArithmeticCutoff Y S + 1) *
      (1 - Real.exp (-(1 / Y)))⁻¹ ≤ 1 / S := by
  have hSp : 0 < S := zero_lt_one.trans_le hS
  have hg := rpow_mul_exp_neg_log_sq_le_rpow_neg
    (a := 5) (d := 1) hSp (by linarith) (by linarith)
  calc
    _ ≤ (U + 1 : ℝ) * Real.exp 1 * Y * Real.exp (-(Real.log S) ^ 2) :=
      arithmetic_tail_le_gaussian hY
    _ ≤ S ^ 2 * S * S ^ 2 * Real.exp (-(Real.log S) ^ 2) := by gcongr
    _ = S ^ 5 * Real.exp (-(Real.log S) ^ 2) := by ring
    _ ≤ 1 / S := by simpa [Real.rpow_neg_one, Real.rpow_natCast, one_div] using hg

/-- Polynomial-height nonprincipal envelope: all conductor and ordinate
factors are paid before the logarithmic Gaussian is absorbed. -/
theorem nonprincipal_error_le_two_inv {S Y : ℝ} {q U : ℕ} {rho : ℂ}
    (hS : 1 ≤ S) (hlog : 20 ≤ Real.log S)
    (hconst : Real.exp 1 ≤ S) (hvert : nonprincipalVerticalConstant ≤ S)
    (hq : (q : ℝ) ≤ S) (hU : (U + 1 : ℝ) ≤ S ^ 2)
    (hheight : |rho.im| ≤ S) (hY : 1 ≤ Y) (hYhi : Y ≤ S ^ 2) :
    detectorTruncationErrorEnvelopePolynomialHeight q U rho Y S ≤ 2 / S := by
  have hSp : 0 < S := zero_lt_one.trans_le hS
  have hh : (5 + |rho.im|) ^ 2 ≤ 36 * S ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 5 + |rho.im|)
      (by linarith : 5 + |rho.im| ≤ 6 * S) 2
    nlinarith
  have hv0 : 0 ≤ nonprincipalVerticalConstant := by unfold nonprincipalVerticalConstant; positivity
  have hv : (1 / (2 * Real.pi)) *
      (460800 * (q : ℝ) ^ 2 * (U + 1) * (5 + |rho.im|) ^ 2 *
        Real.exp (1 / 2) * Real.exp (-(detectorVerticalCutoff S) / 2)) ≤ 1 / S := by
    calc
      _ ≤ nonprincipalVerticalConstant * S ^ 2 * S ^ 2 * S ^ 2 *
          Real.exp (-(Real.log S) ^ 2 / 2) := by
        calc
          _ ≤ (1 / (2 * Real.pi)) *
              (460800 * S ^ 2 * S ^ 2 * (36 * S ^ 2) *
                Real.exp (1 / 2) * Real.exp (-(detectorVerticalCutoff S) / 2)) := by
            gcongr
          _ = _ := by unfold nonprincipalVerticalConstant detectorVerticalCutoff; ring
      _ ≤ S ^ 7 * Real.exp (-(Real.log S) ^ 2 / 2) := by
        calc
          _ ≤ S * S ^ 2 * S ^ 2 * S ^ 2 * Real.exp (-(Real.log S) ^ 2 / 2) := by gcongr
          _ = _ := by ring
      _ ≤ 1 / S := by
        simpa [Real.rpow_neg_one, Real.rpow_natCast, one_div] using
          rpow_mul_exp_neg_half_log_sq_le_rpow_neg (a := 7) (d := 1)
            hSp (by linarith) (by linarith)
  unfold detectorTruncationErrorEnvelopePolynomialHeight
  have ha := arithmetic_tail_le_inv hS hlog hconst hU hY hYhi
  exact (add_le_add ha hv).trans_eq (by ring)

theorem principal_error_le_two_inv {S Y : ℝ} {U : ℕ} {rho : ℂ}
    (hS : 1 ≤ S) (hlog : 20 ≤ Real.log S)
    (hconst : Real.exp 1 ≤ S) (hvert : principalVerticalConstant ≤ S)
    (hU : (U + 1 : ℝ) ≤ S ^ 2) (hheight : |rho.im| ≤ S)
    (hY : 1 ≤ Y) (hYhi : Y ≤ S ^ 2) :
    principalPoleSubtractedPaperScaleError U rho Y S ≤ 2 / S := by
  have hSp : 0 < S := zero_lt_one.trans_le hS
  have hh : (4 + |rho.im|) ^ 6 ≤ 5 ^ 6 * S ^ 6 := by
    simpa [mul_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ 4 + |rho.im|)
      (by linarith : 4 + |rho.im| ≤ 5 * S) 6
  have hv : (1 / (2 * Real.pi)) *
      (4 * (12 * 3200 * (U + 1) * (4 + |rho.im|) ^ 6 *
        (2 : ℝ) ^ 7 * (Nat.factorial 7 : ℝ) * Real.exp (1 / 2)) *
          Real.exp (-(detectorVerticalCutoff S) / 2)) ≤ 1 / S := by
    calc
      _ ≤ principalVerticalConstant * S ^ 2 * S ^ 6 *
          Real.exp (-(Real.log S) ^ 2 / 2) := by
        calc
          _ ≤ (1 / (2 * Real.pi)) *
              (4 * (12 * 3200 * S ^ 2 * (5 ^ 6 * S ^ 6) *
                (2 : ℝ) ^ 7 * (Nat.factorial 7 : ℝ) * Real.exp (1 / 2)) *
                  Real.exp (-(detectorVerticalCutoff S) / 2)) := by gcongr
          _ = _ := by unfold principalVerticalConstant detectorVerticalCutoff; ring
      _ ≤ S ^ 9 * Real.exp (-(Real.log S) ^ 2 / 2) := by
        calc
          _ ≤ S * S ^ 2 * S ^ 6 * Real.exp (-(Real.log S) ^ 2 / 2) := by gcongr
          _ = _ := by ring
      _ ≤ 1 / S := by
        simpa [Real.rpow_neg_one, Real.rpow_natCast, one_div] using
          rpow_mul_exp_neg_half_log_sq_le_rpow_neg (a := 9) (d := 1)
            hSp (by linarith) (by linarith)
  unfold principalPoleSubtractedPaperScaleError principalPoleSubtractedTruncationError
  have ha := arithmetic_tail_le_inv hS hlog hconst hU hY hYhi
  exact (add_le_add ha hv).trans_eq (by ring)

theorem principal_residue_le_inv {S Y : ℝ} {U : ℕ} {rho : ℂ}
    (hS : 24 ≤ S) (hlog : 20 ≤ Real.log S)
    (hU : (U + 1 : ℝ) ≤ S ^ 2) (hY : 1 ≤ Y) (hYhi : Y ≤ S ^ 2)
    (hrho : MAPPrincipalZetaFixedStrip.principalRegularized rho = 0)
    (hbetaLow : 1 / 2 ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    (hgamma : (Real.log S) ^ 2 ≤ |rho.im|) :
    ‖principalDetectorResidue rho U Y‖ ≤ 1 / S := by
  have hSone : 1 ≤ S := by linarith
  have hSp : 0 < S := by linarith
  have himOne : 1 ≤ |rho.im| := by nlinarith [sq_nonneg (Real.log S - 20)]
  have himpos : 0 < |rho.im| := zero_lt_one.trans_le himOne
  have hrhoOne : rho ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.one_im] at hi
    rw [hi, abs_zero] at himOne
    norm_num at himOne
  have hYpos : 0 < Y := zero_lt_one.trans_le hY
  have hres := norm_principalDetectorResidue_le (U := U) hrho hrhoOne hbetaLow hbetaHigh himOne hYpos
  have hratio : (1 + |rho.im|) * (1 / |rho.im|) ≤ 2 := by
    rw [one_div, ← div_eq_mul_inv, div_le_iff₀ himpos]
    linarith
  have hpow : Real.rpow Y (1 - rho.re) ≤ S := by
    calc
      _ ≤ Real.rpow Y (1 / 2) := Real.rpow_le_rpow_of_exponent_le hY (by linarith)
      _ ≤ Real.rpow (S ^ 2) (1 / 2) := Real.rpow_le_rpow (by positivity) hYhi (by norm_num)
      _ = S := by
        change (S ^ 2 : ℝ) ^ (1 / 2 : ℝ) = S
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hSp.le]
  have hexp : Real.exp (-|rho.im|) ≤ Real.exp (-(Real.log S) ^ 2) :=
    Real.exp_le_exp.mpr (neg_le_neg hgamma)
  calc
    _ ≤ 24 * Real.exp (-(Real.log S) ^ 2) * S * S ^ 2 := by
      apply hres.trans
      calc
        _ = 12 * ((1 + |rho.im|) * (1 / |rho.im|)) *
            Real.exp (-|rho.im|) * Real.rpow Y (1 - rho.re) * (U + 1) := by ring
        _ ≤ 12 * 2 * Real.exp (-(Real.log S) ^ 2) * S * S ^ 2 := by
          gcongr
          exact Real.rpow_nonneg hYpos.le _
        _ = _ := by ring
    _ ≤ S ^ 4 * Real.exp (-(Real.log S) ^ 2) := by
      calc
        _ ≤ S * Real.exp (-(Real.log S) ^ 2) * S * S ^ 2 := by gcongr
        _ = _ := by ring
    _ ≤ 1 / S := by
      simpa [Real.rpow_neg_one, Real.rpow_natCast, one_div] using
        rpow_mul_exp_neg_log_sq_le_rpow_neg (a := 4) (d := 1)
          hSp (by linarith) (by linarith)

/-- The budget threshold is independent of conductor, sigma, and zero. -/
def fullScaleReady (S : ℝ) : Prop :=
  24 ≤ S ∧ 20 ≤ Real.log S ∧ Real.exp 1 ≤ S ∧
    nonprincipalVerticalConstant ≤ S ∧ principalVerticalConstant ≤ S

theorem eventually_fullScaleReady : ∀ᶠ S : ℝ in atTop, fullScaleReady S := by
  filter_upwards [eventually_ge_atTop 24,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 20),
    eventually_ge_atTop (Real.exp 1), eventually_ge_atTop nonprincipalVerticalConstant,
    eventually_ge_atTop principalVerticalConstant] with S h1 h2 h3 h4 h5
  exact ⟨h1,h2,h3,h4,h5⟩

theorem fullScaleReady_mono {S T : ℝ} (hT : fullScaleReady T) (hTS : T ≤ S) :
    fullScaleReady S := by
  exact ⟨hT.1.trans hTS,
    hT.2.1.trans (Real.log_le_log (by linarith [hT.1]) hTS),
    hT.2.2.1.trans hTS, hT.2.2.2.1.trans hTS, hT.2.2.2.2.trans hTS⟩

/-- Literal scale admissibility and small tail budgets. Uniformity even
holds for every q≥1, hence in particular for q≤(log T)^K. Sigma's upper
bound controls Y; no restriction to low beta is made for the detected zero. -/
theorem eventually_fullScale_detector_budgets :
    ∀ᶠ T : ℝ in atTop, ∀ (q : ℕ) (sigma : ℝ) (rho : ℂ),
      1 ≤ q → 1 / 2 ≤ sigma → sigma ≤ 7 / 10 → |rho.im| ≤ T →
      let S := (q : ℝ) * T
      let U := fullScaleMollifier S
      let Y := fullScaleY S sigma
      1 ≤ U ∧ 1 ≤ Y ∧ U ≤ detectorArithmeticCutoff Y S ∧
        1 ≤ detectorVerticalCutoff S ∧
        detectorTruncationErrorEnvelopePolynomialHeight q U rho Y S + 1 / 8 + 1 / 8 ≤
          Real.exp (-(1 / Y)) ∧
        principalPoleSubtractedPaperScaleError U rho Y S + 1 / 8 + 1 / 8 + 1 / 8 ≤
          Real.exp (-(1 / Y)) ∧
        (MAPPrincipalZetaFixedStrip.principalRegularized rho = 0 →
          1 / 2 ≤ rho.re → rho.re ≤ 1 →
          detectorVerticalCutoff S ≤ |rho.im| →
          ‖principalDetectorResidue rho U Y‖ ≤ 1 / 8) := by
  filter_upwards [eventually_fullScaleReady] with T hT
  intro q sigma rho hq hslo hshi hheight
  dsimp only
  let S := (q : ℝ) * T
  let U := fullScaleMollifier S
  let Y := fullScaleY S sigma
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hTpos : 0 < T := by linarith [hT.1]
  have hTS : T ≤ S := by dsimp [S]; nlinarith
  have hS := fullScaleReady_mono hT hTS
  have hSone : 1 ≤ S := by linarith [hS.1]
  have hSp : 0 < S := by linarith [hS.1]
  have hqS : (q : ℝ) ≤ S := by dsimp [S]; nlinarith [hT.1]
  have hheightS : |rho.im| ≤ S := hheight.trans hTS
  have hUb := fullScaleMollifier_bounds (by linarith [hS.1] : 12 ≤ S)
  have hYb := fullScaleY_bounds hSone hslo hshi
  have hYone : 1 ≤ Y := hSone.trans hYb.1
  have hB : 1 ≤ detectorVerticalCutoff S := by
    unfold detectorVerticalCutoff
    nlinarith [hS.2.1, sq_nonneg (Real.log S - 20)]
  have hUN : U ≤ detectorArithmeticCutoff Y S := by
    apply Nat.ceil_mono
    have hlog : 10 ≤ (Real.log S) ^ 2 := by nlinarith [hS.2.1, sq_nonneg (Real.log S - 20)]
    calc
      10 * S ≤ S * (Real.log S) ^ 2 := by nlinarith
      _ ≤ Y * (Real.log S) ^ 2 := mul_le_mul_of_nonneg_right hYb.1 (sq_nonneg _)
  have hn := nonprincipal_error_le_two_inv hSone hS.2.1 hS.2.2.1 hS.2.2.2.1
    hqS hUb.2 hheightS hYone hYb.2
  have hp := principal_error_le_two_inv hSone hS.2.1 hS.2.2.1 hS.2.2.2.2
    hUb.2 hheightS hYone hYb.2
  have hsmall : 2 / S ≤ 1 / 8 := (div_le_iff₀ hSp).2 (by linarith [hS.1])
  have hmain : 1 / 2 ≤ Real.exp (-(1 / Y)) := by
    have hYtwo : 2 ≤ Y := by linarith [hYb.1, hS.1]
    have hinv : 1 / Y ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hYtwo
    have he := Real.add_one_le_exp (-(1 / Y))
    linarith
  refine ⟨hUb.1, hYone, hUN, hB, ?_, ?_, ?_⟩
  · exact (by linarith [hn.trans hsmall] :
      detectorTruncationErrorEnvelopePolynomialHeight q U rho Y S + 1/8 + 1/8 ≤
        Real.exp (-(1/Y)))
  · exact (by linarith [hp.trans hsmall] :
      principalPoleSubtractedPaperScaleError U rho Y S + 1/8 + 1/8 + 1/8 ≤
        Real.exp (-(1/Y)))
  · intro hrho hblo hbhi hgamma
    have hr := principal_residue_le_inv hS.1 hS.2.1 hUb.2 hYone hYb.2
      hrho hblo hbhi hgamma
    exact hr.trans ((div_le_iff₀ hSp).2 (by linarith [hS.1]))

#print axioms eventually_fullScale_detector_budgets
end
end MAPMontgomeryFullScaleDetectorBudgets
