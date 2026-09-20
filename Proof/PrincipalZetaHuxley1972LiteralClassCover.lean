import PrincipalZetaHuxley1972Equation315FullClassifier
import PrincipalZetaHuxley1972Equation39Exceptions

/-!
# Huxley 1972: literal finite class cover

The contour classifier is pointwise in a zero.  This file performs the
finite-set step which the source describes as counting the exceptional,
class-I, and class-II zeros.  The two nonexceptional sets are filters by the
literal `(3.12)` and `(3.13)` predicates, with `alpha = sigma`.
-/

namespace MAPPrincipalZetaHuxley1972LiteralClassCover

open DirichletZeros
open MAPPrincipalZetaHuxley1972Equation39Exceptions
open MAPPrincipalZetaHuxley1972Equation315ClassifierArithmetic
open MAPPrincipalZetaHuxley1972Equation315RightClassifier
open MAPPrincipalZetaHuxley1972ClassifierWitnesses
open MAPPrincipalZetaHuxley1972Equation315FullClassifier

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)

/-- The literal class-I subset of the zeta zeros in Huxley's rectangle. -/
def huxleyClassISet
    (sigma T Y ell : ℝ) (U N : ℕ) : Finset ℂ := by
  classical
  exact (zeroSupport chiOne sigma T).filter fun rho =>
    HuxleyClassI U N rho Y ell

/-- The literal class-II subset, with the repaired fixed normalizer and
`alpha=sigma` as in the density argument. -/
def huxleyClassIISet
    (sigma T Y : ℝ) (U : ℕ) : Finset ℂ := by
  classical
  exact (zeroSupport chiOne sigma T).filter fun rho =>
    HuxleyClassII rho U Y sigma shiftedEquation314Normalizer

/-- Exact `(3.9)`--`(3.15)` finite cover.  Every hypothesis other than
membership in the zero rectangle is a displayed scale condition from the
source.  No analytic class estimate occurs here. -/
theorem zeroSupport_card_le_exceptional_add_literalClasses
    {T sigma Y ell : ℝ} {U N : ℕ}
    (hT : 480 ≤ T) (hsigmaLow : 279 / 280 ≤ sigma)
    (hY : 15 / 2 < Y)
    (hU : 1 ≤ U) (hUN : U ≤ N)
    (hUY : (U + 1 : ℝ) ≤ 2 * Y) (hYT : Y ≤ T ^ 2)
    (hcut : 100 * Y * Real.log T ≤ (N + 1 : ℕ))
    (hell : 0 < ell)
    (hcard : (huxleyOccupiedDyadicBlocks U N Y).card ≤
      ⌊2 * ell⌋₊) :
    (zeroSupport chiOne sigma T).card ≤
      (equation39ExceptionalSet sigma T).card +
        (huxleyClassISet sigma T Y ell U N).card +
          (huxleyClassIISet sigma T Y U).card := by
  classical
  have hcover : ∀ rho ∈ zeroSupport chiOne sigma T,
      |rho.im| < 100 * Real.log T ∨
        HuxleyClassI U N rho Y ell ∨
          HuxleyClassII rho U Y sigma shiftedEquation314Normalizer := by
    intro rho hrho
    by_cases hexc : |rho.im| < 100 * Real.log T
    · exact Or.inl hexc
    right
    have hrect : rho ∈ zeroRectangle sigma T :=
      (zeroDivisor chiOne sigma T).supportWithinDomain
        ((zeroSupport_mem_iff chiOne sigma T rho).mp hrho)
    have hrect' := Complex.mem_reProdIm.mp hrect
    have hbetaLow : 7 / 10 ≤ rho.re := by
      exact (by norm_num : (7 / 10 : ℝ) ≤ 279 / 280) |>.trans
        (hsigmaLow.trans hrect'.1.1)
    have hbetaHigh : rho.re ≤ 1 := hrect'.1.2
    have hgamma : 100 * Real.log T ≤ |rho.im| := le_of_not_gt hexc
    have hrhoZero : MAPPrincipalZetaFixedStrip.principalRegularized rho = 0 :=
      by
        have hzero :=
          DirichletZeros.regularizedLFunction_eq_zero_of_mem_zeroSupport
            chiOne sigma T hrho
        simpa [DirichletZeros.regularizedLFunction,
          MAPPrincipalZetaFixedStrip.principalRegularized] using hzero
    exact huxleyClassI_or_classII
      hT hY hU hUN hUY hYT hrhoZero hbetaLow hbetaHigh
      hrect'.1.1 hgamma hcut hell hcard
  simpa [equation39ExceptionalSet, huxleyClassISet,
    huxleyClassIISet] using
      (card_le_exceptional_add_classI_add_classII
        (zeroSupport chiOne sigma T)
        (fun rho => |rho.im| < 100 * Real.log T)
        (fun rho => HuxleyClassI U N rho Y ell)
        (fun rho => HuxleyClassII rho U Y sigma
          shiftedEquation314Normalizer) hcover)

end
end MAPPrincipalZetaHuxley1972LiteralClassCover

#print axioms MAPPrincipalZetaHuxley1972LiteralClassCover.zeroSupport_card_le_exceptional_add_literalClasses
