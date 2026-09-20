import AppendixA4GammaEndpoint
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Infinite contour limit for Appendix (A.4)

The theorem in this file is the exact deterministic passage from the certified
finite rectangle to equality of the two full vertical Bochner integrals.  It
isolates only integrability of the two vertical slices and decay of the two
horizontal sides; no density estimate or zero-count premise occurs.
-/

namespace MAPAppendixA4FullContourLimit

open Set MeasureTheory Complex Filter
open scoped Topology

noncomputable section

/-- A premise-free abstract contour-limit theorem.  It is tailored to the
orientation used by `finite_rectangle_balance`: both vertical slices are
parametrized upward by `t`, and both horizontal sides run from `a` to `c`. -/
theorem full_vertical_integrals_eq_of_horizontal_tendsto_zero
    (F : ℂ → ℂ) {a c : ℝ} (hac : a ≤ c)
    (hF : ∀ z : ℂ, a ≤ z.re → z.re ≤ c → AnalyticAt ℂ F z)
    (hleft : Integrable (fun t : ℝ => F (a + t * I)))
    (hright : Integrable (fun t : ℝ => F (c + t * I)))
    (hminus : Tendsto (fun B : ℝ =>
        ∫ x : ℝ in a..c, F (x - B * I)) atTop (𝓝 0))
    (hplus : Tendsto (fun B : ℝ =>
        ∫ x : ℝ in a..c, F (x + B * I)) atTop (𝓝 0)) :
    (∫ t : ℝ, F (c + t * I)) = ∫ t : ℝ, F (a + t * I) := by
  let R : ℝ → ℂ := fun B => ∫ t : ℝ in -B..B, F (c + t * I)
  let L : ℝ → ℂ := fun B => ∫ t : ℝ in -B..B, F (a + t * I)
  let Hminus : ℝ → ℂ := fun B => ∫ x : ℝ in a..c, F (x - B * I)
  let Hplus : ℝ → ℂ := fun B => ∫ x : ℝ in a..c, F (x + B * I)
  have hR : Tendsto R atTop (𝓝 (∫ t : ℝ, F (c + t * I))) := by
    exact MeasureTheory.intervalIntegral_tendsto_integral hright
      Filter.tendsto_neg_atTop_atBot tendsto_id
  have hL : Tendsto L atTop (𝓝 (∫ t : ℝ, F (a + t * I))) := by
    exact MeasureTheory.intervalIntegral_tendsto_integral hleft
      Filter.tendsto_neg_atTop_atBot tendsto_id
  have hbalance : ∀ᶠ B : ℝ in atTop,
      I * (R B - L B) = Hplus B - Hminus B := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
    have hrect := MAPAppendixA4Detector.finite_rectangle_balance
      F hac hB (fun z hz => by
        apply hF z
        · have hzleft := hz.1.1
          simpa [min_eq_left hac] using hzleft
        · have hzright := hz.1.2
          simpa [max_eq_right hac] using hzright)
    dsimp [R, L, Hplus, Hminus]
    linear_combination hrect
  have hlhs : Tendsto (fun B => I * (R B - L B)) atTop
      (𝓝 (I * ((∫ t : ℝ, F (c + t * I)) -
        ∫ t : ℝ, F (a + t * I)))) :=
    tendsto_const_nhds.mul (hR.sub hL)
  have hrhs : Tendsto (fun B => Hplus B - Hminus B) atTop (𝓝 0) := by
    simpa [Hplus, Hminus] using hplus.sub hminus
  have hlhs0 : Tendsto (fun B => I * (R B - L B)) atTop (𝓝 0) :=
    hrhs.congr' (hbalance.mono fun B hB => hB.symm)
  have hzero : I * ((∫ t : ℝ, F (c + t * I)) -
      ∫ t : ℝ, F (a + t * I)) = 0 :=
    tendsto_nhds_unique hlhs hlhs0
  have hdiff : (∫ t : ℝ, F (c + t * I)) -
      ∫ t : ℝ, F (a + t * I) = 0 := by
    exact (mul_eq_zero.mp hzero).resolve_left Complex.I_ne_zero
  exact sub_eq_zero.mp hdiff


variable {q : ℕ} [NeZero q]

open MAPAppendixA4GammaEndpoint

/-- The literal Gamma--L--mollifier integrand on `Re z=1/2` is integrable.
This is derived from the same coefficientwise Bochner majorant used for the
right-line identity; it is not an extra contour hypothesis. -/
theorem integrable_gammaRightIntegrand
    (chi : DirichletCharacter ℂ q) (U : ℕ) {rho : ℂ}
    (hbeta : 1 / 2 < rho.re) {Y : ℝ} (hY : 0 < Y) :
    Integrable (MAPAppendixA4GammaEndpoint.gammaRightIntegrand
      chi U rho Y) := by
  have hs : LSeriesSummable (detectorCoeff chi U)
      ((rho.re + 1 / 2 : ℝ) : ℂ) := by
    have hline := detectorCoeff_LSeriesSummable chi U hbeta 0
    exact (LSeriesSummable_iff_of_re_eq_re (f := detectorCoeff chi U)
      (s := rho + ((1 / 2 : ℝ) + (0 : ℝ) * I))
      (s' := ((rho.re + 1 / 2 : ℝ) : ℂ)) (by simp)).mp hline
  have hcoeff : Summable fun n : ℕ =>
      ‖LSeries.term (detectorCoeff chi U)
        ((rho.re + 1 / 2 : ℝ) : ℂ) n‖ := summable_norm_iff.mpr hs
  let C : ℝ := (∑' n : ℕ,
      ‖LSeries.term (detectorCoeff chi U)
        ((rho.re + 1 / 2 : ℝ) : ℂ) n‖) * Y ^ (1 / 2 : ℝ)
  have hGamma : Integrable (fun t : ℝ =>
      Complex.Gamma ((1 / 2 : ℝ) + t * I)) :=
    MAPGammaMellinInversion.verticalIntegrable_Gamma (by norm_num)
  have hdom : Integrable (fun t : ℝ =>
      C * ‖Complex.Gamma ((1 / 2 : ℝ) + t * I)‖) :=
    hGamma.norm.const_mul C
  apply hdom.mono'
  · have hmeas : AEStronglyMeasurable (fun t : ℝ =>
        ∑' n : ℕ, gammaRightTerm chi U rho Y n t) :=
      AEStronglyMeasurable.tsum (fun n =>
        (continuous_gammaRightTerm chi U rho hY n).aestronglyMeasurable)
    exact hmeas.congr (Filter.Eventually.of_forall fun t =>
      (tsum_gammaRightTerm_eq_gammaRightIntegrand chi U hbeta Y t))
  · exact Filter.Eventually.of_forall fun t => by
      have hpoint : Summable fun n : ℕ =>
          ‖gammaRightTerm chi U rho Y n t‖ := by
        have hscaled := hcoeff.mul_right
          (Y ^ (1 / 2 : ℝ) *
            ‖Complex.Gamma ((1 / 2 : ℝ) + t * I)‖)
        exact hscaled.congr (fun n => by
          rw [norm_gammaRightTerm_eq chi U rho hY])
      rw [← tsum_gammaRightTerm_eq_gammaRightIntegrand chi U hbeta Y t]
      refine (norm_tsum_le_tsum_norm hpoint).trans_eq ?_
      rw [show (fun n : ℕ => ‖gammaRightTerm chi U rho Y n t‖) =
          (fun n : ℕ =>
            ‖LSeries.term (detectorCoeff chi U)
              ((rho.re + 1 / 2 : ℝ) : ℂ) n‖ *
              (Y ^ (1 / 2 : ℝ) *
                ‖Complex.Gamma ((1 / 2 : ℝ) + t * I)‖)) by
        funext n
        rw [norm_gammaRightTerm_eq chi U rho hY]]
      rw [tsum_mul_right]
      dsimp [C]
      ring


/-- Literal raw shifted critical-line integrand on `Re z=1/2-beta`. -/
def gammaLeftIntegrand
    (chi : DirichletCharacter ℂ q) (U : ℕ)
    (rho : ℂ) (Y : ℝ) (t : ℝ) : ℂ :=
  let a : ℝ := 1 / 2 - rho.re
  MAPMellinDetectorLeaf.gammaMellinWeight Y (a + t * I) *
    DirichletCharacter.LFunction chi (rho + (a + t * I)) *
    MAPMollifierCoefficientIdentity.mollifier chi U (rho + (a + t * I))

/-- On the right vertical line, the canonical removable extension is the raw
Gamma integrand.  The point `z=0` is not on this line. -/
theorem regularized_eq_gammaRight
    (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hrho : DirichletCharacter.LFunction chi rho = 0)
    (U : ℕ) (Y : ℝ) (t : ℝ) :
    MAPAppendixA4Detector.regularizedDetectorIntegrand chi rho U Y
        ((1 / 2 : ℝ) + t * I) =
      gammaRightIntegrand chi U rho Y t := by
  have hz : ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  rw [MAPAppendixA4Detector.regularizedDetectorIntegrand_eq_raw chi hrho hz]
  unfold gammaRightIntegrand MAPMellinDetectorLeaf.gammaMellinWeight
  ring

/-- On the shifted left vertical line, the canonical extension is also raw.
Strict `beta>1/2` keeps this line away from `z=0`. -/
theorem regularized_eq_gammaLeft
    (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbeta : 1 / 2 < rho.re) (U : ℕ) (Y : ℝ) (t : ℝ) :
    MAPAppendixA4Detector.regularizedDetectorIntegrand chi rho U Y
        ((1 / 2 - rho.re : ℝ) + t * I) =
      gammaLeftIntegrand chi U rho Y t := by
  have hz : (((1 / 2 - rho.re : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  rw [MAPAppendixA4Detector.regularizedDetectorIntegrand_eq_raw chi hrho hz]
  unfold gammaLeftIntegrand
  dsimp only

/-- Exact remaining contour contract after the premise-free right-line weld.
It contains no theorem-valued proposition: the hypotheses are literal
integrability and two literal horizontal-side limits for the actual canonical
integrand.  Proving these three analytic facts closes the full displayed A.4. -/
theorem literal_A4_full_identity_of_left_integrable_horizontal_decay
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {U : ℕ} (hU : 1 ≤ U) {rho : ℂ}
    (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y : ℝ} (hY : 0 < Y)
    (hleft : Integrable (gammaLeftIntegrand chi U rho Y))
    (hminus : Tendsto (fun B : ℝ =>
      ∫ x : ℝ in (1 / 2 - rho.re)..(1 / 2),
        MAPAppendixA4Detector.regularizedDetectorIntegrand chi rho U Y
          (x - B * I)) atTop (𝓝 0))
    (hplus : Tendsto (fun B : ℝ =>
      ∫ x : ℝ in (1 / 2 - rho.re)..(1 / 2),
        MAPAppendixA4Detector.regularizedDetectorIntegrand chi rho U Y
          (x + B * I)) atTop (𝓝 0)) :
    (Real.exp (-(1 / Y)) : ℂ) +
        ∑' n : {n // n ∉ Finset.range (U + 1)},
          arithmeticDetectorTerm chi U rho Y n =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, gammaLeftIntegrand chi U rho Y t) := by
  let a : ℝ := 1 / 2 - rho.re
  let c : ℝ := 1 / 2
  let F : ℂ → ℂ :=
    MAPAppendixA4Detector.regularizedDetectorIntegrand chi rho U Y
  have hac : a ≤ c := by dsimp [a, c]; linarith
  have hleftF : Integrable (fun t : ℝ => F (a + t * I)) := by
    apply hleft.congr
    exact Filter.Eventually.of_forall fun t => by
      dsimp [F, a]
      exact (regularized_eq_gammaLeft chi hrho hbetaLow U Y t).symm
  have hrightRaw := integrable_gammaRightIntegrand chi U hbetaLow hY
  have hrightF : Integrable (fun t : ℝ => F (c + t * I)) := by
    apply hrightRaw.congr
    exact Filter.Eventually.of_forall fun t => by
      dsimp [F, c]
      exact (regularized_eq_gammaRight chi hrho U Y t).symm
  have hshift :
      (∫ t : ℝ, F (c + t * I)) = ∫ t : ℝ, F (a + t * I) := by
    apply full_vertical_integrals_eq_of_horizontal_tendsto_zero F hac
    · intro z hzlo hzhi
      apply MAPAppendixA4Detector.analyticAt_regularizedDetectorIntegrand chi hchi hY
      change -1 < z.re
      have ha : -1 < a := by dsimp [a]; linarith
      exact lt_of_lt_of_le ha hzlo
    · exact hleftF
    · exact hrightF
    · simpa [F, a, c] using hminus
    · simpa [F, a, c] using hplus
  have hrightEq :
      (∫ t : ℝ, F (c + t * I)) =
        ∫ t : ℝ, gammaRightIntegrand chi U rho Y t := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by
      dsimp [F, c]
      exact regularized_eq_gammaRight chi hrho U Y t
  have hleftEq :
      (∫ t : ℝ, F (a + t * I)) =
        ∫ t : ℝ, gammaLeftIntegrand chi U rho Y t := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by
      dsimp [F, a]
      exact regularized_eq_gammaLeft chi hrho hbetaLow U Y t
  rw [literal_A4_right_line_identity chi hU hbetaLow hY]
  rw [← hrightEq, hshift, hleftEq]

end
end MAPAppendixA4FullContourLimit

#print axioms MAPAppendixA4FullContourLimit.full_vertical_integrals_eq_of_horizontal_tendsto_zero
