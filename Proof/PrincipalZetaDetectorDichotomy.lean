import PrincipalZetaContourTails
import PostA5RecenteredSourceSplit
import LowStripGammaKernel

/-!
# Residue-aware principal detector dichotomy

The conductor-one detector now has a complete Appendix A.4 identity.  This
file performs the same finite arithmetic/vertical truncation as the shared
post-A.5 pipeline, retaining the one crossed-pole residue as an explicit
error term.  The output uses the existing `arithmeticDetectorBlock` and
`normalizedCentralGammaIntegral` definitions, so all later coefficient and
Fourier provenance lemmas remain applicable.
-/

namespace MAPPrincipalZetaDetectorDichotomy

open Set MeasureTheory Complex Filter
open scoped Topology ArithmeticFunction LSeries.notation BigOperators
open MAPMollifierCoefficientIdentity MAPAppendixA4GammaEndpoint
open MAPAppendixA4FullContourLimit MAPAppendixA4GammaTails
open MAPAppendixA4DetectorDichotomy MAPPrincipalZetaDetectorPoleRemoval
open MAPPrincipalZetaContourTails
open CGLProofDAG MAPAppendixA4PostA5SetAdapter
open PostA5RecenteredSourceSplit

noncomputable section

set_option maxHeartbeats 800000

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)
local notation "principalF" => MAPPrincipalZetaFixedStrip.principalRegularized

/-- Exact residue-aware decomposition into the paper's finite arithmetic
block, central critical-line integral, and the two discarded tails. -/
theorem principal_quantitative_detector_decomposition
    {U N : ℕ} (hU : 1 ≤ U) (hUN : U ≤ N)
    {rho : ℂ} (hrho : principalF rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y : ℝ} (hY : 1 ≤ Y) (B : ℝ) :
    (Real.exp (-(1 / Y)) : ℂ) +
        arithmeticDetectorBlock chiOne U N rho Y +
        ∑' k : ℕ, arithmeticDetectorTerm chiOne U rho Y (k + (N + 1)) =
      principalDetectorResidue rho U Y +
        normalizedCentralGammaIntegral chiOne U rho Y B +
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ((∫ t : ℝ in Set.Iic (-B), gammaLeftIntegrand chiOne U rho Y t) +
            ∫ t : ℝ in Set.Ioi B, gammaLeftIntegrand chiOne U rho Y t)) := by
  let f : ℕ → ℂ := arithmeticDetectorTerm chiOne U rho Y
  let g : ℝ → ℂ := gammaLeftIntegrand chiOne U rho Y
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hsum : Summable f :=
    summable_arithmeticDetectorTerm chiOne U (by linarith) hYpos
  have hsplitSum := hsum.sum_add_tsum_nat_add (N + 1)
  have hUN' : U + 1 ≤ N + 1 := by omega
  have hfinite := Finset.sum_range_add_sum_Ico f hUN'
  have hmain :
      ∑ n ∈ Finset.range (U + 1), f n =
        (Real.exp (-(1 / Y)) : ℂ) := by
    simpa [f] using arithmeticDetectorTerm_sum_range_eq_main
      chiOne hU rho hYpos
  rw [hmain] at hfinite
  have hseries :
      (Real.exp (-(1 / Y)) : ℂ) +
          arithmeticDetectorBlock chiOne U N rho Y +
          ∑' k : ℕ, arithmeticDetectorTerm chiOne U rho Y (k + (N + 1)) =
        ∑' n : ℕ, arithmeticDetectorTerm chiOne U rho Y n := by
    dsimp [arithmeticDetectorBlock, f] at hfinite hsplitSum ⊢
    rw [← hsplitSum, ← hfinite]
  have hg : Integrable g := by
    have hraw := integrable_principalRawDetector_left
      hrho hbetaLow hbetaHigh U hY
    exact hraw.congr (Filter.Eventually.of_forall fun t =>
      principalRawDetector_left_eq_gammaLeft rho U Y t)
  have hfull := intervalIntegral.integral_Iic_add_Ioi
    (b := B) hg.integrableOn hg.integrableOn
  have hcenter := intervalIntegral.integral_Iic_sub_Iic
    (a := -B) (b := B) hg.integrableOn hg.integrableOn
  have hintegral :
      (∫ t : ℝ, gammaLeftIntegrand chiOne U rho Y t) =
        (∫ t : ℝ in (-B)..B, gammaLeftIntegrand chiOne U rho Y t) +
          ((∫ t : ℝ in Set.Iic (-B), gammaLeftIntegrand chiOne U rho Y t) +
            ∫ t : ℝ in Set.Ioi B, gammaLeftIntegrand chiOne U rho Y t) := by
    dsimp [g] at hfull hcenter
    rw [← hfull, ← hcenter]
    abel
  have hA4 := literal_principal_A4_full_identity hU hrho hbetaLow
    hbetaHigh hY
  have hrawIntegral :
      (∫ t : ℝ, MAPPrincipalZetaPoleContour.principalRawDetector rho U Y
        (((1 / 2 - rho.re : ℝ) : ℂ) + t * I)) =
      ∫ t : ℝ, gammaLeftIntegrand chiOne U rho Y t := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t =>
      principalRawDetector_left_eq_gammaLeft rho U Y t
  have hfullSeries := arithmetic_detector_tsum_eq_main_add_tail
    chiOne hU (by linarith : 1 / 2 < rho.re) hYpos
  rw [← hfullSeries] at hA4
  rw [← hseries, hrawIntegral, hintegral] at hA4
  dsimp [normalizedCentralGammaIntegral]
  linear_combination hA4

/-- Literal finite truncation budget, including the norm of the crossed-pole
residue. -/
def principalDetectorTruncationError
    (U N : ℕ) (rho : ℂ) (Y B : ℝ) : ℝ :=
  (U + 1) * (Real.exp (-(1 / Y))) ^ (N + 1) *
      (1 - Real.exp (-(1 / Y)))⁻¹ +
    (1 / (2 * Real.pi)) *
      (4 * (12 * 3200 * (U + 1) * (4 + |rho.im|) ^ 6 *
        (2 : ℝ) ^ 7 * (Nat.factorial 7 : ℝ) * Real.exp (1 / 2)) *
          Real.exp (-B / 2)) +
    ‖principalDetectorResidue rho U Y‖

/-- The residue-aware finite detector error. -/
theorem norm_principal_quantitative_detector_truncation_error_le
    {U N : ℕ} (hU : 1 ≤ U) (hUN : U ≤ N)
    {rho : ℂ} (hrho : principalF rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y B : ℝ} (hY : 1 ≤ Y) (hB : 1 ≤ B) :
    ‖(Real.exp (-(1 / Y)) : ℂ) +
        arithmeticDetectorBlock chiOne U N rho Y -
        normalizedCentralGammaIntegral chiOne U rho Y B‖ ≤
      principalDetectorTruncationError U N rho Y B := by
  let A : ℂ := ∑' k : ℕ,
    arithmeticDetectorTerm chiOne U rho Y (k + (N + 1))
  let V : ℂ :=
    (∫ t : ℝ in Set.Iic (-B), gammaLeftIntegrand chiOne U rho Y t) +
      ∫ t : ℝ in Set.Ioi B, gammaLeftIntegrand chiOne U rho Y t
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  let R : ℂ := principalDetectorResidue rho U Y
  have hdecomp := principal_quantitative_detector_decomposition hU hUN hrho
    hbetaLow hbetaHigh hY B
  have herr :
      (Real.exp (-(1 / Y)) : ℂ) +
          arithmeticDetectorBlock chiOne U N rho Y -
          normalizedCentralGammaIntegral chiOne U rho Y B =
        R + c * V - A := by
    dsimp [A, V, c, R]
    linear_combination hdecomp
  have hA := norm_arithmetic_shifted_tail_le chiOne U N
    (by linarith : 0 ≤ rho.re) (lt_of_lt_of_le zero_lt_one hY)
  have hV := norm_principalGammaLeft_two_tails_le_exp_polynomial_height
    hbetaLow hbetaHigh U hY hB
  have hc : ‖c‖ = 1 / (2 * Real.pi) := by
    dsimp [c]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    positivity
  rw [herr]
  calc
    ‖R + c * V - A‖ ≤ ‖R‖ + ‖c * V‖ + ‖A‖ := by
      exact (norm_sub_le _ _).trans (by
        simpa [add_assoc, add_comm, add_left_comm] using
          add_le_add_right (norm_add_le R (c * V)) ‖A‖)
    _ = ‖R‖ + ‖c‖ * ‖V‖ + ‖A‖ := by rw [norm_mul]
    _ ≤ ‖R‖ + (1 / (2 * Real.pi)) *
          (4 * (12 * 3200 * (U + 1) * (4 + |rho.im|) ^ 6 *
            (2 : ℝ) ^ 7 * (Nat.factorial 7 : ℝ) * Real.exp (1 / 2)) *
              Real.exp (-B / 2)) +
          ((U + 1) * (Real.exp (-(1 / Y))) ^ (N + 1) *
            (1 - Real.exp (-(1 / Y)))⁻¹) := by
      rw [hc]
      have hc0 : 0 ≤ 1 / (2 * Real.pi) := by positivity
      have hcV : (1 / (2 * Real.pi)) * ‖V‖ ≤
          (1 / (2 * Real.pi)) *
            (4 * (12 * 3200 * (U + 1) * (4 + |rho.im|) ^ 6 *
              (2 : ℝ) ^ 7 * (Nat.factorial 7 : ℝ) * Real.exp (1 / 2)) *
                Real.exp (-B / 2)) :=
        mul_le_mul_of_nonneg_left hV hc0
      have hRV : ‖R‖ + (1 / (2 * Real.pi)) * ‖V‖ ≤
          ‖R‖ + (1 / (2 * Real.pi)) *
            (4 * (12 * 3200 * (U + 1) * (4 + |rho.im|) ^ 6 *
              (2 : ℝ) ^ 7 * (Nat.factorial 7 : ℝ) * Real.exp (1 / 2)) *
                Real.exp (-B / 2)) := by
        linarith
      exact add_le_add hRV hA
    _ = principalDetectorTruncationError U N rho Y B := by
      dsimp [principalDetectorTruncationError, R]
      ring

/-- Paper-scale specialization, with exactly the shared cutoffs. -/
def principalPaperScaleTruncationError
    (U : ℕ) (rho : ℂ) (Y R : ℝ) : ℝ :=
  principalDetectorTruncationError U
    (detectorArithmeticCutoff Y R) rho Y (detectorVerticalCutoff R)

theorem norm_principal_paper_scale_detector_error_le
    {U : ℕ} (hU : 1 ≤ U) {rho : ℂ}
    (hrho : principalF rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y R : ℝ} (hY : 1 ≤ Y)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R) :
    ‖(Real.exp (-(1 / Y)) : ℂ) +
        arithmeticDetectorBlock chiOne U (detectorArithmeticCutoff Y R) rho Y -
        normalizedCentralGammaIntegral chiOne U rho Y
          (detectorVerticalCutoff R)‖ ≤
      principalPaperScaleTruncationError U rho Y R := by
  exact norm_principal_quantitative_detector_truncation_error_le
    hU hUN hrho hbetaLow hbetaHigh hY hB

/-- Principal post-A.5 detector dichotomy with the pole residue fully
accounted for in the certified error budget. -/
theorem principal_post_A5_quantitative_detector_dichotomy
    {U : ℕ} (hU : 1 ≤ U) {rho : ℂ}
    (hrho : principalF rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y R a b : ℝ} (hY : 1 ≤ Y)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R)
    (hbudget : principalPaperScaleTruncationError U rho Y R + a + b ≤
      Real.exp (-(1 / Y))) :
    a ≤ ‖arithmeticDetectorBlock chiOne U
        (detectorArithmeticCutoff Y R) rho Y‖ ∨
      b ≤ ‖normalizedCentralGammaIntegral chiOne U rho Y
        (detectorVerticalCutoff R)‖ := by
  apply detector_norm_dichotomy_of_error
    (norm_principal_paper_scale_detector_error_le hU hrho hbetaLow
      hbetaHigh hY hUN hB)
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos (-(1 / Y)))]
  exact hbudget

/-! ## Pole-subtracted detector on the complete open half strip -/

/-- Truncation error after the crossed residue is subtracted from the scalar
main term.  In contrast with `principalDetectorTruncationError`, this contains
only the arithmetic and vertical tails. -/
def principalPoleSubtractedTruncationError
    (U N : ℕ) (rho : ℂ) (Y B : ℝ) : ℝ :=
  (U + 1) * (Real.exp (-(1 / Y))) ^ (N + 1) *
      (1 - Real.exp (-(1 / Y)))⁻¹ +
    (1 / (2 * Real.pi)) *
      (4 * (12 * 3200 * (U + 1) * (4 + |rho.im|) ^ 6 *
        (2 : ℝ) ^ 7 * (Nat.factorial 7 : ℝ) * Real.exp (1 / 2)) *
          Real.exp (-B / 2))

/-- Exact pole-subtracted truncation inequality.  The finite Dirichlet block
is unchanged; the residue is part of the scalar main term rather than an
error. -/
theorem norm_principal_poleSubtracted_detector_truncation_error_le
    {U N : ℕ} (hU : 1 ≤ U) (hUN : U ≤ N)
    {rho : ℂ} (hrho : principalF rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y B : ℝ} (hY : 1 ≤ Y) (hB : 1 ≤ B) :
    ‖((Real.exp (-(1 / Y)) : ℂ) - principalDetectorResidue rho U Y) +
        arithmeticDetectorBlock chiOne U N rho Y -
        normalizedCentralGammaIntegral chiOne U rho Y B‖ ≤
      principalPoleSubtractedTruncationError U N rho Y B := by
  let A : ℂ := ∑' k : ℕ,
    arithmeticDetectorTerm chiOne U rho Y (k + (N + 1))
  let V : ℂ :=
    (∫ t : ℝ in Set.Iic (-B), gammaLeftIntegrand chiOne U rho Y t) +
      ∫ t : ℝ in Set.Ioi B, gammaLeftIntegrand chiOne U rho Y t
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hdecomp := principal_quantitative_detector_decomposition hU hUN hrho
    hbetaLow hbetaHigh hY B
  have herr :
      ((Real.exp (-(1 / Y)) : ℂ) - principalDetectorResidue rho U Y) +
          arithmeticDetectorBlock chiOne U N rho Y -
          normalizedCentralGammaIntegral chiOne U rho Y B = c * V - A := by
    dsimp [A, V, c]
    linear_combination hdecomp
  have hA := norm_arithmetic_shifted_tail_le chiOne U N
    (le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) hbetaLow.le)
    (lt_of_lt_of_le zero_lt_one hY)
  have hV := norm_principalGammaLeft_two_tails_le_exp_polynomial_height
    hbetaLow hbetaHigh U hY hB
  have hc : ‖c‖ = 1 / (2 * Real.pi) := by
    dsimp [c]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    positivity
  rw [herr]
  calc
    ‖c * V - A‖ ≤ ‖c * V‖ + ‖A‖ := norm_sub_le _ _
    _ = ‖c‖ * ‖V‖ + ‖A‖ := by rw [norm_mul]
    _ ≤ (1 / (2 * Real.pi)) *
          (4 * (12 * 3200 * (U + 1) * (4 + |rho.im|) ^ 6 *
            (2 : ℝ) ^ 7 * (Nat.factorial 7 : ℝ) * Real.exp (1 / 2)) *
              Real.exp (-B / 2)) +
          ((U + 1) * (Real.exp (-(1 / Y))) ^ (N + 1) *
            (1 - Real.exp (-(1 / Y)))⁻¹) := by
      rw [hc]
      exact add_le_add
        (mul_le_mul_of_nonneg_left hV (by positivity)) hA
    _ = principalPoleSubtractedTruncationError U N rho Y B := by
      dsimp [principalPoleSubtractedTruncationError]
      ring

/-- Pole-subtracted error at the paper cutoffs. -/
def principalPoleSubtractedPaperScaleError
    (U : ℕ) (rho : ℂ) (Y R : ℝ) : ℝ :=
  principalPoleSubtractedTruncationError U
    (detectorArithmeticCutoff Y R) rho Y (detectorVerticalCutoff R)

/-- The conductor-one detector dichotomy on the complete open half strip.
The budget is compared with the literal pole-subtracted main scalar. -/
theorem principal_post_A5_quantitative_detector_dichotomy_poleSubtracted
    {U : ℕ} (hU : 1 ≤ U) {rho : ℂ}
    (hrho : principalF rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y R a b : ℝ} (hY : 1 ≤ Y)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R)
    (hbudget : principalPoleSubtractedPaperScaleError U rho Y R + a + b ≤
      ‖(Real.exp (-(1 / Y)) : ℂ) - principalDetectorResidue rho U Y‖) :
    a ≤ ‖arithmeticDetectorBlock chiOne U
        (detectorArithmeticCutoff Y R) rho Y‖ ∨
      b ≤ ‖normalizedCentralGammaIntegral chiOne U rho Y
        (detectorVerticalCutoff R)‖ := by
  apply detector_norm_dichotomy_of_error
    (norm_principal_poleSubtracted_detector_truncation_error_le
      hU hUN hrho hbetaLow hbetaHigh hY hB)
  exact hbudget

/-- Reverse-triangle lower bound for the pole-subtracted scalar. -/
theorem exp_sub_principalDetectorResidue_norm_lower
    (rho : ℂ) (U : ℕ) (Y : ℝ) :
    Real.exp (-(1 / Y)) - ‖principalDetectorResidue rho U Y‖ ≤
      ‖(Real.exp (-(1 / Y)) : ℂ) - principalDetectorResidue rho U Y‖ := by
  have h := norm_sub_norm_le
    ((Real.exp (-(1 / Y)) : ℝ) : ℂ) (principalDetectorResidue rho U Y)
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos (-(1 / Y)))] at h
  exact h

/-- Budget form used after a separate high-ordinate residue estimate.  The
residue is still subtracted exactly in the detector identity; `c` is used only
to certify that the resulting scalar main term remains large. -/
theorem principal_post_A5_quantitative_detector_dichotomy_of_residue_bound
    {U : ℕ} (hU : 1 ≤ U) {rho : ℂ}
    (hrho : principalF rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y R a b c : ℝ} (hY : 1 ≤ Y)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R)
    (hresidue : ‖principalDetectorResidue rho U Y‖ ≤ c)
    (hbudget : principalPoleSubtractedPaperScaleError U rho Y R +
        c + a + b ≤ Real.exp (-(1 / Y))) :
    a ≤ ‖arithmeticDetectorBlock chiOne U
        (detectorArithmeticCutoff Y R) rho Y‖ ∨
      b ≤ ‖normalizedCentralGammaIntegral chiOne U rho Y
        (detectorVerticalCutoff R)‖ := by
  apply principal_post_A5_quantitative_detector_dichotomy_poleSubtracted
    hU hrho hbetaLow hbetaHigh hY hUN hB
  have hmain := exp_sub_principalDetectorResidue_norm_lower rho U Y
  linarith

/-- Continuity of the actual modulus-one critical-line product.  This is the
only place where the nonprincipal extractor used `chi != 1`; on conductor one
the critical line stays a fixed real distance from zeta's pole. -/
theorem continuous_principalCriticalLineProductNorm
    (U : ℕ) (rho : ℂ) :
    Continuous (criticalLineProductNorm chiOne U rho) := by
  have hfun : criticalLineProductNorm chiOne U rho =
      fun t : ℝ =>
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I) *
          mollifier chiOne U
            (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I)‖ := by
    funext t
    rw [criticalLineProductNorm_eq, DirichletCharacter.LFunction_modOne_eq]
  rw [hfun]
  apply Continuous.norm
  apply Continuous.mul
  · rw [continuous_iff_continuousAt]
    intro t
    let s : ℂ := (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I)
    have hs1 : s ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num [s] at hre
    exact (differentiableAt_riemannZeta hs1).continuousAt.comp_of_eq
      (by fun_prop) rfl
  · rw [continuous_iff_continuousAt]
    intro t
    exact (MAPAppendixA4Detector.analyticAt_mollifier chiOne _).continuousAt.comp_of_eq
      (by fun_prop) rfl

/-- Maximum extraction for the principal central integral. -/
theorem principal_exists_criticalLine_large_value_div_mass_of_central
    (U : ℕ) {rho : ℂ}
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y B b : ℝ} (hY : 0 < Y) (hB : 0 < B)
    (hcentral : b ≤ ‖normalizedCentralGammaIntegral chiOne U rho Y B‖) :
    ∃ t ∈ Set.Icc (-B) B,
      b / ((1 / (2 * Real.pi)) * truncatedGammaLeftKernelMass rho Y B) ≤
        criticalLineProductNorm chiOne U rho t := by
  let P : ℝ → ℝ := criticalLineProductNorm chiOne U rho
  let W : ℝ → ℝ := gammaLeftKernelNorm rho Y
  have hP : Continuous P := continuous_principalCriticalLineProductNorm U rho
  have hW : Continuous W :=
    continuous_gammaLeftKernelNorm hbetaLow hbetaHigh hY
  obtain ⟨t0, ht0, hmax⟩ := isCompact_uIcc.exists_isMaxOn
    Set.nonempty_uIcc hP.continuousOn
  have huIcc : Set.uIcc (-B) B = Set.Icc (-B) B := by
    rw [Set.uIcc_of_le]
    linarith
  rw [huIcc] at ht0 hmax
  have hkernel : IntervalIntegrable (fun t => W t * P t) volume (-B) B :=
    (hW.mul hP).intervalIntegrable _ _
  have hmajor : IntervalIntegrable (fun t => W t * P t0) volume (-B) B :=
    (hW.mul continuous_const).intervalIntegrable _ _
  have hraw :
      ‖∫ t : ℝ in (-B)..B, gammaLeftIntegrand chiOne U rho Y t‖ ≤
        ∫ t : ℝ in (-B)..B, W t * P t := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
    · exact Filter.Eventually.of_forall fun t _ => by
        simpa [W, P] using
          norm_gammaLeftIntegrand_eq_kernel_mul_criticalLineProductNorm
            chiOne U rho Y t |>.le
    · exact hkernel
  have hmono :
      (∫ t : ℝ in (-B)..B, W t * P t) ≤
        ∫ t : ℝ in (-B)..B, W t * P t0 := by
    apply intervalIntegral.integral_mono_on (by linarith) hkernel hmajor
    intro t ht
    exact mul_le_mul_of_nonneg_left (hmax ht) (norm_nonneg _)
  have hc : ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ =
      1 / (2 * Real.pi) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    positivity
  have hlarge : b ≤
      (1 / (2 * Real.pi)) * truncatedGammaLeftKernelMass rho Y B * P t0 := by
    calc
      b ≤ ‖normalizedCentralGammaIntegral chiOne U rho Y B‖ := hcentral
      _ = (1 / (2 * Real.pi)) *
          ‖∫ t : ℝ in (-B)..B, gammaLeftIntegrand chiOne U rho Y t‖ := by
        unfold normalizedCentralGammaIntegral
        rw [norm_mul, hc]
      _ ≤ (1 / (2 * Real.pi)) *
          (∫ t : ℝ in (-B)..B, W t * P t) :=
        mul_le_mul_of_nonneg_left hraw (by positivity)
      _ ≤ (1 / (2 * Real.pi)) *
          (∫ t : ℝ in (-B)..B, W t * P t0) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = (1 / (2 * Real.pi)) * truncatedGammaLeftKernelMass rho Y B *
          P t0 := by
        rw [intervalIntegral.integral_mul_const]
        dsimp [truncatedGammaLeftKernelMass, W, P]
        ring
  refine ⟨t0, ht0, ?_⟩
  apply (div_le_iff₀ ?_).2
  · simpa [P, mul_assoc, mul_comm, mul_left_comm] using hlarge
  · exact mul_pos (by positivity)
      (truncatedGammaLeftKernelMass_pos hbetaLow hbetaHigh hY hB)

/-- Source-normalized principal Type-I/Type-II alternative. -/
theorem principal_post_A5_detector_to_typeI_or_sourceTypeII
    {U : ℕ} (hU : 1 ≤ U) {rho : ℂ}
    (hrho : principalF rho = 0)
    (hbetaLow : 7 / 10 ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y R V : ℝ} (hY : 1 ≤ Y) (hV : 0 < V)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R)
    (hbudget : principalPaperScaleTruncationError U rho Y R + V + V ≤
      Real.exp (-(1 / Y))) :
    V ≤ ‖arithmeticDetectorBlock chiOne U
        (detectorArithmeticCutoff Y R) rho Y‖ ∨
      ∃ t ∈ Set.Icc (-(detectorVerticalCutoff R))
          (detectorVerticalCutoff R),
        V / (29 * Real.rpow Y (1 / 2 - rho.re) *
            (2 * Real.sqrt U)) ≤
          ‖DirichletCharacter.LFunction chiOne
            (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I)‖ := by
  rcases principal_post_A5_quantitative_detector_dichotomy hU hrho
    (by linarith) hbetaHigh hY hUN hB hbudget with hI | hII
  · exact Or.inl hI
  · right
    obtain ⟨t, ht, htlarge⟩ :=
      principal_exists_criticalLine_large_value_div_mass_of_central U
        (by linarith) hbetaHigh (lt_of_lt_of_le zero_lt_one hY)
        (lt_of_lt_of_le zero_lt_one hB) hII
    let s : ℂ := (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I)
    let D : ℝ := (1 / (2 * Real.pi)) *
      truncatedGammaLeftKernelMass rho Y (detectorVerticalCutoff R)
    let W : ℝ := 2 * Real.sqrt U
    let E : ℝ := 29 * Real.rpow Y (1 / 2 - rho.re) * W
    have hYpos : 0 < Y := zero_lt_one.trans_le hY
    have hBpos : 0 < detectorVerticalCutoff R := zero_lt_one.trans_le hB
    have hmasspos : 0 <
        truncatedGammaLeftKernelMass rho Y (detectorVerticalCutoff R) :=
      truncatedGammaLeftKernelMass_pos (by linarith) hbetaHigh hYpos hBpos
    have hDpos : 0 < D := by dsimp [D]; positivity
    have hUpos : (0 : ℝ) < U := by exact_mod_cast hU
    have hWpos : 0 < W := by dsimp [W]; positivity
    have hEpos : 0 < E := by dsimp [E]; positivity
    have hDle : D ≤ 29 * Real.rpow Y (1 / 2 - rho.re) := by
      have h := normalized_truncatedGammaLeftKernelMass_le_uniform
        hbetaLow hbetaHigh 0 hY (zero_le_one.trans hB)
      simpa [D] using h
    have hDE : D * W ≤ E := by
      dsimp [E]
      exact mul_le_mul_of_nonneg_right hDle hWpos.le
    have hsre : s.re = 1 / 2 := by dsimp [s]; simp
    have hM := PostA5TypeIIFourthMoment.norm_mollifier_criticalLine_le_two_sqrt
      chiOne U hsre
    have hproduct : V / D ≤
        ‖DirichletCharacter.LFunction chiOne s * mollifier chiOne U s‖ := by
      simpa [D, s, criticalLineProductNorm_eq] using htlarge
    have hLraw := PostA5TypeIIFourthMoment.norm_lower_of_product
      hWpos hproduct hM
    have hL : V / (D * W) ≤ ‖DirichletCharacter.LFunction chiOne s‖ := by
      simpa [div_div] using hLraw
    refine ⟨t, ht, ?_⟩
    have hquot : V / E ≤ V / (D * W) :=
      (div_le_div_iff_of_pos_left hV hEpos (mul_pos hDpos hWpos)).2 hDE
    exact hquot.trans (by simpa [E, W, s] using hL)

/-- Pole-subtracted principal Type-I/Type-II alternative on
`1/2 < beta <= 7/10`.  The arithmetic branch is the unchanged source block;
the Type-II normalization records the necessary low-strip Gamma loss. -/
theorem principal_post_A5_poleSubtracted_detector_to_typeI_or_lowStripTypeII
    {U : ℕ} (hU : 1 ≤ U) {rho : ℂ}
    (hrho : principalF rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 7 / 10)
    {Y R V : ℝ} (hY : 1 ≤ Y) (hV : 0 < V)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R)
    (hbudget : principalPoleSubtractedPaperScaleError U rho Y R + V + V ≤
      ‖(Real.exp (-(1 / Y)) : ℂ) - principalDetectorResidue rho U Y‖) :
    V ≤ ‖arithmeticDetectorBlock chiOne U
        (detectorArithmeticCutoff Y R) rho Y‖ ∨
      ∃ t ∈ Set.Icc (-(detectorVerticalCutoff R))
          (detectorVerticalCutoff R),
        V / ((MAPMontgomeryLowStripGamma.lowStripGammaConstant
              (rho.re - 1 / 2) / 2) *
            Real.rpow Y (1 / 2 - rho.re) * (2 * Real.sqrt U)) ≤
          ‖DirichletCharacter.LFunction chiOne
            (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I)‖ := by
  rcases principal_post_A5_quantitative_detector_dichotomy_poleSubtracted
    hU hrho hbetaLow (by linarith) hY hUN hB hbudget with hI | hII
  · exact Or.inl hI
  · right
    obtain ⟨t, ht, htlarge⟩ :=
      principal_exists_criticalLine_large_value_div_mass_of_central U
        hbetaLow (by linarith) (lt_of_lt_of_le zero_lt_one hY)
        (lt_of_lt_of_le zero_lt_one hB) hII
    let delta : ℝ := rho.re - 1 / 2
    let s : ℂ := (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I)
    let D : ℝ := (1 / (2 * Real.pi)) *
      truncatedGammaLeftKernelMass rho Y (detectorVerticalCutoff R)
    let W : ℝ := 2 * Real.sqrt U
    let E : ℝ :=
      (MAPMontgomeryLowStripGamma.lowStripGammaConstant delta / 2) *
        Real.rpow Y (1 / 2 - rho.re) * W
    have hdelta : 0 < delta := by dsimp [delta]; linarith
    have hYpos : 0 < Y := zero_lt_one.trans_le hY
    have hBpos : 0 < detectorVerticalCutoff R := zero_lt_one.trans_le hB
    have hmasspos : 0 <
        truncatedGammaLeftKernelMass rho Y (detectorVerticalCutoff R) :=
      truncatedGammaLeftKernelMass_pos hbetaLow (by linarith) hYpos hBpos
    have hDpos : 0 < D := by dsimp [D]; positivity
    have hUpos : (0 : ℝ) < U := by exact_mod_cast hU
    have hWpos : 0 < W := by dsimp [W]; positivity
    have hEpos : 0 < E := by
      dsimp [E]
      exact mul_pos
        (mul_pos (div_pos
          (MAPMontgomeryLowStripGamma.lowStripGammaConstant_pos hdelta)
          (by norm_num)) (Real.rpow_pos_of_pos hYpos _)) hWpos
    have hDle : D ≤
        (MAPMontgomeryLowStripGamma.lowStripGammaConstant delta / 2) *
          Real.rpow Y (1 / 2 - rho.re) := by
      have h :=
        MAPMontgomeryLowStripGamma.normalized_truncatedGammaLeftKernelMass_le_lowStrip
          hdelta (rho := rho) (by dsimp [delta]; linarith) hbetaHigh 0 hY
          (zero_le_one.trans hB)
      simpa [D] using h
    have hDE : D * W ≤ E := by
      dsimp [E]
      exact mul_le_mul_of_nonneg_right hDle hWpos.le
    have hsre : s.re = 1 / 2 := by dsimp [s]; simp
    have hM := PostA5TypeIIFourthMoment.norm_mollifier_criticalLine_le_two_sqrt
      chiOne U hsre
    have hproduct : V / D ≤
        ‖DirichletCharacter.LFunction chiOne s * mollifier chiOne U s‖ := by
      simpa [D, s, criticalLineProductNorm_eq] using htlarge
    have hLraw := PostA5TypeIIFourthMoment.norm_lower_of_product
      hWpos hproduct hM
    have hL : V / (D * W) ≤ ‖DirichletCharacter.LFunction chiOne s‖ := by
      simpa [div_div] using hLraw
    refine ⟨t, ht, ?_⟩
    have hquot : V / E ≤ V / (D * W) :=
      (div_le_div_iff_of_pos_left hV hEpos (mul_pos hDpos hWpos)).2 hDE
    exact hquot.trans (by simpa [E, W, delta, s] using hL)

/-- Finite principal zero-set split with the same common Type-I dyadic shell
and source-normalized Type-II set as the nonprincipal pipeline. -/
theorem principal_post_A5_budgeted_zeroSet_common_dyadic_or_sourceTypeII
    {kappa eta : ℝ} (hkappa : 0 < kappa) (heta : 0 < eta)
    {U : ℕ} (hU : 1 ≤ U)
    {Z : Finset ℂ} {Y R : ℝ} (hY : 1 ≤ Y) (hR : 0 < R)
    (hzero : ∀ rho ∈ Z, principalF rho = 0)
    (hbetaLow : ∀ rho ∈ Z, 7 / 10 ≤ rho.re)
    (hbetaHigh : ∀ rho ∈ Z, rho.re ≤ 1)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R)
    (hbudget : ∀ rho ∈ Z,
      principalPaperScaleTruncationError U rho Y R +
          Real.rpow R (-inputLoss kappa eta) +
          Real.rpow R (-inputLoss kappa eta) ≤
        Real.exp (-(1 / Y))) :
    ∃ j : Fin (detectorDyadicCount (detectorArithmeticCutoff Y R)),
      ∃ S : Finset ℂ,
        S ⊆ postA5TypeISet chiOne U Y R
          (Real.rpow R (-inputLoss kappa eta)) Z ∧
        (postA5TypeISet chiOne U Y R
          (Real.rpow R (-inputLoss kappa eta)) Z).card ≤
            detectorDyadicCount (detectorArithmeticCutoff Y R) * S.card ∧
        (∀ rho ∈ S,
          Real.rpow R (-inputLoss kappa eta) ≤
            detectorDyadicCount (detectorArithmeticCutoff Y R) *
              ‖arithmeticDetectorDyadicBlock chiOne U
                (detectorArithmeticCutoff Y R) rho Y j‖) ∧
        Z.card ≤
          (postA5TypeISet chiOne U Y R
            (Real.rpow R (-inputLoss kappa eta)) Z).card +
          (postA5SourceTypeIISet chiOne U Y R
            (Real.rpow R (-inputLoss kappa eta)) Z).card := by
  classical
  let V := Real.rpow R (-inputLoss kappa eta)
  let ZI := postA5TypeISet chiOne U Y R V Z
  let ZII := postA5SourceTypeIISet chiOne U Y R V Z
  have hsubset : Z ⊆ ZI ∪ ZII := by
    intro rho hrho
    have hVpos : 0 < V := by dsimp [V]; exact Real.rpow_pos_of_pos hR _
    rcases principal_post_A5_detector_to_typeI_or_sourceTypeII hU
      (hzero rho hrho) (hbetaLow rho hrho) (hbetaHigh rho hrho)
      hY hVpos hUN hB (by simpa [V] using hbudget rho hrho) with hI | hII
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hrho, hI⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hrho, hII⟩)
  have hcard : Z.card ≤ ZI.card + ZII.card :=
    (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)
  have hlarge : ∀ rho ∈ ZI,
      V ≤ ‖arithmeticDetectorBlock chiOne U
        (detectorArithmeticCutoff Y R) rho Y‖ := by
    intro rho hrho
    exact (Finset.mem_filter.mp hrho).2
  obtain ⟨j, S, hS, hcardI, hblock⟩ :=
    exists_common_arithmeticDetectorDyadicBlock chiOne hU hUN hlarge
  refine ⟨j, S, hS, hcardI, hblock, ?_⟩
  simpa [ZI, ZII, V] using hcard

end
end MAPPrincipalZetaDetectorDichotomy

#print axioms MAPPrincipalZetaDetectorDichotomy.principal_quantitative_detector_decomposition
#print axioms MAPPrincipalZetaDetectorDichotomy.norm_principal_quantitative_detector_truncation_error_le
#print axioms MAPPrincipalZetaDetectorDichotomy.principal_post_A5_quantitative_detector_dichotomy
#print axioms MAPPrincipalZetaDetectorDichotomy.norm_principal_poleSubtracted_detector_truncation_error_le
#print axioms MAPPrincipalZetaDetectorDichotomy.principal_post_A5_quantitative_detector_dichotomy_poleSubtracted
#print axioms MAPPrincipalZetaDetectorDichotomy.principal_post_A5_quantitative_detector_dichotomy_of_residue_bound
#print axioms MAPPrincipalZetaDetectorDichotomy.continuous_principalCriticalLineProductNorm
#print axioms MAPPrincipalZetaDetectorDichotomy.principal_post_A5_detector_to_typeI_or_sourceTypeII
#print axioms MAPPrincipalZetaDetectorDichotomy.principal_post_A5_poleSubtracted_detector_to_typeI_or_lowStripTypeII
#print axioms MAPPrincipalZetaDetectorDichotomy.principal_post_A5_budgeted_zeroSet_common_dyadic_or_sourceTypeII
