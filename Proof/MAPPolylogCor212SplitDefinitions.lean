import BHPCanonicalAllCharacterLiteral

/-! # Interfaces for the split literal Corollary 2.12 route -/

namespace MAPPolylogCor212SplitDefinitions

open MAPMRTLemma211AllCharacterSource
open MAPBHPCanonicalAllCharacterLiteral
open MAPBHPCanonicalAllCharacterFromPrincipal

noncomputable section

/-- Exact MAP Type-d1/d2 source range.  The exponent parameter `K` is
quantified before all packet data in the final source proposition. -/
structure MAPTypeD12MomentRange
    (X H Q lambda U T K : ℝ) (q cutoff : ℕ) : Prop where
  X_large : 8 ≤ X
  H_ge_one : 1 ≤ H
  Q_ge_one : 1 ≤ Q
  lambda_pos : 0 < lambda
  U_eq : U = lambda * H
  T_ge_two : 2 ≤ T
  q_ge_one : 1 ≤ q
  cutoff_ge_two : 2 ≤ cutoff
  K_nonneg : 0 ≤ K
  K_le_loglog : K ≤ Real.log (Real.log X)
  q_polylog : (q : ℝ) ≤ Real.rpow (Real.log X) K
  q_le_T : (q : ℝ) ≤ T
  cutoff_le_T : (cutoff : ℝ) ≤ T
  cutoff_le_X : (cutoff : ℝ) ≤ X
  two_T_le_X : 2 * T ≤ X

/-- Global-constant selected-prefix source.  The `card/cutoff²` and principal
decay terms remain literal and are multiplied by the same global log factor. -/
def MAPPolylogSelectedPrefixFourthMomentLiteral : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ, 4 ≤ B ∧
    ∀ (X H Q lambda U T K : ℝ) (q cutoff : ℕ)
      (S : Finset (DirichletCharacter ℂ q × ℝ)),
      MAPTypeD12MomentRange X H Q lambda U T K q cutoff →
      (∀ z ∈ S, |z.2| ≤ T) →
      SameCharacterOneSeparated S →
      selectedPrefixFourthMass cutoff S ≤ C *
        (1 + Real.log X) ^ B *
        ((q : ℝ) * T +
          (S.card : ℝ) *
            ((q : ℝ) ^ 2 / T ^ 2 + (cutoff : ℝ) ^ 2 / T ^ 4 +
              1 / (cutoff : ℝ) ^ 2) +
          (cutoff : ℝ) ^ 2 * selectedPrincipalDecayMass S)

end
end MAPPolylogCor212SplitDefinitions
