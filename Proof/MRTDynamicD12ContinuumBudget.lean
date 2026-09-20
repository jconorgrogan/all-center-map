import MRTDynamicD12ContinuumWeld
import MRTDynamicD12MomentSource

namespace MRTDynamicD12ContinuumSampling
noncomputable section
open scoped BigOperators
open MAPMRTProposition61TypeD1FirstInequality MAPMRTLemma211AllCharacterSource
open MAPPolylogCor212SplitDefinitions
open MRTDynamicD12MomentSource

/-- Exact three-sector shape after inserting the constructed `A=1` cardinal budget. -/
def continuumBudgetShape (T : ℝ) (q cutoff : ℕ) : ℝ :=
  (q : ℝ) * T + (q : ℝ) * T *
    ((q : ℝ)^2 / T^2 + (cutoff : ℝ)^2 / T^4 + 1 / (cutoff : ℝ)^2) +
    (cutoff : ℝ)^2 * (((q : ℝ) * T) * (16 / T^4))

/-- Fully constructed continuum budget on any short interval in the annulus. -/
theorem dynamicD12ContinuumIntervalBudget_proved :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ, 4 ≤ B ∧
      ∀ {X T K a b : ℝ} {q cutoff : ℕ} [NeZero q],
        DynamicD12MomentRange X T K q cutoff →
        a ≤ b → b-a+1 ≤ T →
        (∀ t ∈ Set.Icc a b, T/2 ≤ |t| ∧ |t| ≤ T) →
        (∑ χ : DirichletCharacter ℂ q,
          ∫ t in a..b, ‖criticalPrefixPolynomial q cutoff χ t‖^4) ≤
          C * (1 + Real.log X)^B * continuumBudgetShape T q cutoff := by
  classical
  obtain ⟨C,hC,B,hB,hsource⟩ := dynamicD12SampledBudget_proved
  refine ⟨2*C, by positivity, B,hB, ?_⟩
  intro X T K a b q cutoff _ hrange hab hlen hann
  let F : DirichletCharacter ℂ q → ℝ → ℝ :=
    fun χ t => ‖criticalPrefixPolynomial q cutoff χ t‖
  have hF : ∀ χ, Continuous (F χ) := by
    intro χ
    unfold F criticalPrefixPolynomial
    unfold MAPMRTLemma210OrthogonalityReduction.twistedFinitePolynomial
      MAPMRTLemma210OrthogonalityReduction.twistedPhase
    fun_prop
  have hcolor (c : ℕ) :
      bhpSampledPieceMass F (fourthSamples (a := a) (b := b) F hF c)
        (fourthLeft (a := a) (b := b) F hF c) (fourthRight (a := a) (b := b) F hF c) ≤
      C * (1 + Real.log X)^B * continuumBudgetShape T q cutoff := by
    have hcard := coloredSamples_card_le_qT hab hlen
      (fun χ t => F χ t ^ 4) (fourthContinuous F hF) c
    have hs := hsource (A := 1) hrange
      (fun z hz => fourthSamples_length F hF c hz)
      (fun z hz t ht => fourthSamples_max F hF c hz ht)
      (fun z hz => (hann z.2 (coloredSamples_range _ _ c hz)).1)
      (fun z hz => (hann z.2 (coloredSamples_range _ _ c hz)).2)
      (by simpa only [one_mul] using hcard)
      (coloredSamples_spacing (a := a) (b := b)
        (fun χ t => F χ t ^ 4) (fourthContinuous F hF) c)
    simpa only [one_mul, continuumBudgetShape] using hs
  change (∑ χ, ∫ t in a..b, F χ t ^ 4) ≤ _
  rw [continuum_fourth_eq_sampled F hF hab]
  have h := add_le_add (hcolor 0) (hcolor 1)
  nlinarith

/-- Both literal half-annuli satisfy the same uniform continuum budget. -/
theorem dynamicD12ContinuumHalfAnnulusBudget_proved :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ, 4 ≤ B ∧
      ∀ {X T K : ℝ} {q cutoff : ℕ} [NeZero q],
        DynamicD12MomentRange X T K q cutoff →
        ((∑ χ : DirichletCharacter ℂ q,
          ∫ t in T/2..T, ‖criticalPrefixPolynomial q cutoff χ t‖^4) ≤
          C * (1 + Real.log X)^B * continuumBudgetShape T q cutoff) ∧
        ((∑ χ : DirichletCharacter ℂ q,
          ∫ t in -T..-T/2, ‖criticalPrefixPolynomial q cutoff χ t‖^4) ≤
          C * (1 + Real.log X)^B * continuumBudgetShape T q cutoff) := by
  obtain ⟨C,hC,B,hB,hsource⟩ := dynamicD12ContinuumIntervalBudget_proved
  refine ⟨C,hC,B,hB, ?_⟩
  intro X T K q cutoff _ hrange
  have hT := hrange.T_ge_two
  constructor
  · apply hsource hrange (by linarith) (by linarith)
    intro t ht
    rw [abs_of_nonneg (by linarith [ht.1] : 0 ≤ t)]
    exact ht
  · apply hsource hrange (by linarith) (by linarith)
    intro t ht
    rw [abs_of_nonpos (by linarith [ht.2] : t ≤ 0)]
    constructor <;> linarith [ht.1,ht.2]

end
end MRTDynamicD12ContinuumSampling

#print axioms MRTDynamicD12ContinuumSampling.dynamicD12ContinuumHalfAnnulusBudget_proved
