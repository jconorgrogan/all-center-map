import MAPPolylogCor212SplitRamachandra
import MRTProposition61TypeD1FirstInequality

/-!
# Literal sampled Corollary 2.12 budget for Type-d1/d2

The selected-prefix source is discretized without changing its three error
sectors.  In particular the `card/cutoff^2` error and the principal annular
`cutoff^2 * card * 16/T^4` term remain explicit.
-/

namespace MAPPolylogCor212SplitSampled

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

open scoped BigOperators
open MAPMRTLemma211AllCharacterSource
open MAPMRTProposition61TypeD1FirstInequality
open MAPBHPCanonicalAllCharacterFromPrincipal
open MAPPolylogCor212SplitDefinitions
open MAPPolylogCor212SplitRamachandra
open RamachandraTheorem6ShiftedStripSource

noncomputable section

theorem principalDecayMass_eq_selected
    {q : ℕ} [NeZero q]
    (S : Finset (DirichletCharacter ℂ q × ℝ)) :
    bhpPrincipalDecayMass S = selectedPrincipalDecayMass S := by
  classical
  unfold bhpPrincipalDecayMass selectedPrincipalDecayMass
  apply Finset.sum_congr rfl
  intro z hz
  rw [isPrincipalCharacter_iff_eq_one]
  split_ifs <;> rfl

theorem selectedFourthMass_prefix_eq
    {q cutoff : ℕ} [NeZero q]
    (S : Finset (DirichletCharacter ℂ q × ℝ)) :
    bhpSelectedFourthMass
        (fun chi t => ‖criticalPrefixPolynomial q cutoff chi t‖) S =
      selectedPrefixFourthMass cutoff S := by
  rfl

/-- Exact low Type-d1/d2 termwise budget.  Constants quantify globally before
all MAP parameters, including the polylog exponent parameter `K`. -/
def MAPLowTypeD12SampledBudget : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ, 4 ≤ B ∧
    ∀ {X H Q lambda U T K : ℝ} {q cutoff : ℕ} [NeZero q]
      {S : Finset (DirichletCharacter ℂ q × ℝ)}
      {left right : DirichletCharacter ℂ q × ℝ → ℝ} {A : ℝ},
      MAPTypeD12MomentRange X H Q lambda U T K q cutoff →
      (∀ z ∈ S, 0 ≤ right z - left z ∧ right z - left z ≤ 1) →
      (∀ z ∈ S, ∀ t ∈ Set.Icc (left z) (right z),
        ‖criticalPrefixPolynomial q cutoff z.1 t‖ ^ 4 ≤
          ‖criticalPrefixPolynomial q cutoff z.1 z.2‖ ^ 4) →
      (∀ z ∈ S, T / 2 ≤ |z.2|) →
      (∀ z ∈ S, |z.2| ≤ T) →
      (S.card : ℝ) ≤ A * (q : ℝ) * T →
      SameCharacterOneSeparated S →
      bhpSampledPieceMass
          (fun chi t => ‖criticalPrefixPolynomial q cutoff chi t‖)
          S left right ≤ C * (1 + Real.log X) ^ B *
        ((q : ℝ) * T +
          (A * (q : ℝ) * T) *
            ((q : ℝ) ^ 2 / T ^ 2 + (cutoff : ℝ) ^ 2 / T ^ 4 +
              1 / (cutoff : ℝ) ^ 2) +
          (cutoff : ℝ) ^ 2 *
            ((A * (q : ℝ) * T) * (16 / T ^ 4)))

/-- Discretize a globally quantified selected-prefix source. -/
theorem sampledBudget_of_selected
    (hSelected : MAPPolylogSelectedPrefixFourthMomentLiteral) :
    MAPLowTypeD12SampledBudget := by
  classical
  obtain ⟨C, hC, B, hB, hsource⟩ := hSelected
  refine ⟨C, hC, B, hB, ?_⟩
  intro X H Q lambda U T K q cutoff _inst S left right A
    hrange hlength hmax hannulus hheight hcard hspacing
  let F : DirichletCharacter ℂ q → ℝ → ℝ :=
    fun chi t => ‖criticalPrefixPolynomial q cutoff chi t‖
  have hF : ∀ chi, Continuous (F chi) := by
    intro chi
    unfold F criticalPrefixPolynomial
    unfold MAPMRTLemma210OrthogonalityReduction.twistedFinitePolynomial
      MAPMRTLemma210OrthogonalityReduction.twistedPhase
    fun_prop
  have hTpos : 0 < T := by linarith [hrange.T_ge_two]
  have hdisc := bhpSampledPieceMass_le_selectedFourthMass hF hlength hmax
  have hsource' := hsource X H Q lambda U T K q cutoff S
    hrange hheight hspacing
  have htail0 := bhpPrincipalDecayMass_le_card_mul_sixteen_div
    (S := S) hTpos hannulus
  have htail : selectedPrincipalDecayMass S ≤
      (A * (q : ℝ) * T) * (16 / T ^ 4) := by
    rw [← principalDecayMass_eq_selected]
    exact htail0.trans
      (mul_le_mul_of_nonneg_right hcard (by positivity))
  have hshape0 : 0 ≤
      (q : ℝ) ^ 2 / T ^ 2 + (cutoff : ℝ) ^ 2 / T ^ 4 +
        1 / (cutoff : ℝ) ^ 2 := by positivity
  have hlog0 : 0 ≤ (1 + Real.log X) ^ B := by
    have hlog : 0 ≤ Real.log X :=
      Real.log_nonneg (by linarith [hrange.X_large])
    positivity
  calc
    bhpSampledPieceMass F S left right ≤
        bhpSelectedFourthMass F S := hdisc
    _ = selectedPrefixFourthMass cutoff S := selectedFourthMass_prefix_eq S
    _ ≤ C * (1 + Real.log X) ^ B *
        ((q : ℝ) * T +
          (S.card : ℝ) *
            ((q : ℝ) ^ 2 / T ^ 2 + (cutoff : ℝ) ^ 2 / T ^ 4 +
              1 / (cutoff : ℝ) ^ 2) +
          (cutoff : ℝ) ^ 2 * selectedPrincipalDecayMass S) := hsource'
    _ ≤ C * (1 + Real.log X) ^ B *
        ((q : ℝ) * T +
          (A * (q : ℝ) * T) *
            ((q : ℝ) ^ 2 / T ^ 2 + (cutoff : ℝ) ^ 2 / T ^ 4 +
              1 / (cutoff : ℝ) ^ 2) +
          (cutoff : ℝ) ^ 2 *
            ((A * (q : ℝ) * T) * (16 / T ^ 4))) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le hlog0)
      gcongr

/-- Direct principal-closed/Ramachandra-to-Type-d1/d2 budget. -/
theorem sampledBudget_of_ramachandra
    (hRamachandra : RamachandraTheorem6K2Source) :
    MAPLowTypeD12SampledBudget :=
  sampledBudget_of_selected
    (selectedPrefixFourthMoment_of_ramachandra hRamachandra)

end
end MAPPolylogCor212SplitSampled

#print axioms MAPPolylogCor212SplitSampled.sampledBudget_of_selected
#print axioms MAPPolylogCor212SplitSampled.sampledBudget_of_ramachandra
