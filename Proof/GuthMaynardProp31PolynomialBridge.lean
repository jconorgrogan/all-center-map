import GuthMaynardSectionFourTrace
import GuthMaynardSmoothedProp31Consumer

open scoped BigOperators
open GuthMaynardSectionThreeCutoff
open GuthMaynardSectionFourTrace
open GuthMaynardSmoothedProp31Consumer
open GuthMaynardTwoPlateauSmoothingBridge
open CGLProofDAG

noncomputable section
namespace GuthMaynardProp31PolynomialBridge

/-- The real two-bump cutoff is exactly one across the full plateau interval.
The proof uses the bump branches themselves, rather than recovering a real
weight from the squared complex cutoff. -/
theorem sectionThreeCutoffReal_plateau :
    PlateauWeight sectionThreeCutoffReal := by
  intro x hxlow hxhigh
  by_cases hmid : x ≤ 8 / 5
  · have hleft : |x - 7 / 5| ≤ (1 / 5 : ℝ) := by
      rw [abs_le]
      constructor <;> linarith
    unfold sectionThreeCutoffReal
    rw [GuthMaynardJIteration.sourceBump_eq_one_of_abs_le
      (1 / 5) fifth_pos hleft]
    norm_num
  · have hright : |x - 8 / 5| ≤ (1 / 5 : ℝ) := by
      rw [abs_le]
      constructor <;> linarith
    unfold sectionThreeCutoffReal
    rw [GuthMaynardJIteration.sourceBump_eq_one_of_abs_le
      (1 / 5) fifth_pos hright]
    norm_num

/-- The Section 4 trace polynomial and the Prop. 3.1 smoothed polynomial are
definitionally the same finite sum, including the source phase. -/
theorem sourceDN_eq_smoothedPolynomial
    (b : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    sourceDN b N t =
      smoothedPolynomial sectionThreeCutoffReal b N t := by
  unfold sourceDN smoothedPolynomial sourcePhase
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- On supported plateau coefficients and in the legal range, the concrete
smoothed source polynomial is exactly the sharp Dirichlet polynomial. -/
theorem sourceDN_eq_dirichletPolynomial
    {b : ℕ → ℂ} {N : ℕ} (hN : 32 ≤ N)
    (hsupp : supportedOnPlateau N b) (t : ℝ) :
    sourceDN b N t = dirichletPolynomial b N t := by
  calc
    sourceDN b N t = smoothedPolynomial sectionThreeCutoffReal b N t :=
      sourceDN_eq_smoothedPolynomial b N t
    _ = dirichletPolynomial b N t :=
      smoothed_eq_sharp_of_supported sectionThreeCutoffReal_plateau hN hsupp t

end GuthMaynardProp31PolynomialBridge

#print axioms GuthMaynardProp31PolynomialBridge.sectionThreeCutoffReal_plateau
#print axioms GuthMaynardProp31PolynomialBridge.sourceDN_eq_smoothedPolynomial
#print axioms GuthMaynardProp31PolynomialBridge.sourceDN_eq_dirichletPolynomial
