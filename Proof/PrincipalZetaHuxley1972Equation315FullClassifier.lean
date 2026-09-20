import PrincipalZetaHuxley1972Equation315RightClassifier
import PrincipalZetaHuxley1972ClassifierWitnesses
import PrincipalZetaContourTails

/-!
# Huxley 1972, equations (3.12)--(3.15): the complete literal classifier

This file welds the independently certified right and left halves.  Failure
of the literal class-I blocks makes the shifted contour integral have real
part greater than `1/3`; failure of the literal class-II witnesses makes the
norm of that same integral less than `1/3`.

The class-II normalizer is the source-faithful repaired constant from
`PrincipalZetaHuxley1972ClassifierWitnesses`: the printed `(3.14)` uses a
central-line Gamma factor although `(3.5)` is on a beta-shifted line.  The
repair chooses a smaller fixed positive constant from the certified
compact-strip Gamma envelope and does not change the later class estimates.
-/

namespace MAPPrincipalZetaHuxley1972Equation315FullClassifier

open scoped ArithmeticFunction LSeries.notation BigOperators
open MAPMollifierCoefficientIdentity MAPAppendixA4GammaEndpoint
open MAPAppendixA4FullContourLimit
open MAPPrincipalZetaDetectorPoleRemoval MAPPrincipalZetaPoleContour
open MAPPrincipalZetaHuxley1972Equation315ClassifierArithmetic
open MAPPrincipalZetaHuxley1972Equation315RightClassifier
open MAPPrincipalZetaHuxley1972ClassifierWitnesses
open MAPPrincipalZetaContourTails

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)
local notation "principalF" => MAPPrincipalZetaFixedStrip.principalRegularized

/-- The literal `(3.12)` / `(3.13)` classifier, with both contour attachments
and the entire `(3.15)` contradiction discharged.  No integrability premise
remains: it is supplied by the already certified principal contour estimate.
-/
theorem huxleyClassI_or_classII
    {T Y ell alpha : ℝ} {U N : ℕ} {rho : ℂ}
    (hT : 480 ≤ T) (hY : 15 / 2 < Y)
    (hU : 1 ≤ U) (hUN : U ≤ N)
    (hUY : (U + 1 : ℝ) ≤ 2 * Y) (hYT : Y ≤ T ^ 2)
    (hrho : principalF rho = 0)
    (hbetaLow : 7 / 10 ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    (halpha : alpha ≤ rho.re)
    (hgamma : 100 * Real.log T ≤ |rho.im|)
    (hcut : 100 * Y * Real.log T ≤ (N + 1 : ℕ))
    (hell : 0 < ell)
    (hcard : (huxleyOccupiedDyadicBlocks U N Y).card ≤
      ⌊2 * ell⌋₊) :
    HuxleyClassI U N rho Y ell ∨
      HuxleyClassII rho U Y alpha shiftedEquation314Normalizer := by
  let left : ℂ :=
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t : ℝ, gammaLeftIntegrand chiOne U rho Y t)
  let right : ℂ :=
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t : ℝ, principalRawDetector rho U Y
        (((1 / 2 - rho.re : ℝ) : ℂ) + t * Complex.I))
  have hYone : 1 ≤ Y := by linarith
  have hrawIntegrable := integrable_principalRawDetector_left
    hrho (by linarith) hbetaHigh U hYone
  have hgammaIntegrable :
      MeasureTheory.Integrable (gammaLeftIntegrand chiOne U rho Y) :=
    hrawIntegrable.congr (Filter.Eventually.of_forall fun t =>
      principalRawDetector_left_eq_gammaLeft rho U Y t)
  have heq : left = right := by
    dsimp [left, right]
    congr 1
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun t =>
      (principalRawDetector_left_eq_gammaLeft rho U Y t).symm
  apply classI_or_classII_of_equation35_bounds heq
  · intro hnotClassI
    exact huxleyEquation315_right_real_gt_oneThird_of_not_classI
      hT hY hU hUN hUY hYT hrho hbetaLow hbetaHigh hgamma hcut
      hell hcard hnotClassI
  · intro hnotClassII
    exact huxleyEquation314_full_shifted_integral_lt_oneThird_of_not_classII
      hbetaLow hbetaHigh hYone halpha hgammaIntegrable hnotClassII

end
end MAPPrincipalZetaHuxley1972Equation315FullClassifier

#print axioms MAPPrincipalZetaHuxley1972Equation315FullClassifier.huxleyClassI_or_classII
