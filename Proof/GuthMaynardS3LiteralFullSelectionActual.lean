import GuthMaynardS3LiteralFullSelection
import GuthMaynardS3LiteralUnbalancedPermutationTail

namespace GuthMaynardS3LiteralFullSelectionActual

open scoped BigOperators
open GuthMaynardS3LiteralFullSelection
open GuthMaynardS3LiteralBalancedSectorGeometry
open GuthMaynardS3LiteralActualSixSectorBound
open GuthMaynardS3LiteralUnbalancedPermutationTail
open GuthMaynardS3LiteralTruncation
open GuthMaynardEquation55Infinite
open GuthMaynardEquation55Split
open GuthMaynardS3LiteralGlobalReduction
open GuthMaynardS3LiteralRadialDecay
open GuthMaynardS3LiteralLocalization

noncomputable section

/-- The actual finite-frequency selector.  The unbalanced part is discharged
internally by the literal permutation tail theorem; the only infinite-source
remainder is the explicit prefix-to-infinite Fourier error. -/
theorem norm_sourceS3_le_selected_ordered_block_actual
    {N Mcut q : ℕ} (hN : 0 < N) (hMcut : 1 ≤ Mcut)
    {T : ℝ} (hT : 0 ≤ T) (W : Finset ℝ)
    (hdiam : ∀ a ∈ W, ∀ b ∈ W, |a - b| ≤ T)
    {rho : ℝ} (hrho : 0 < rho)
    (hslack : rho / (N : ℝ) ≤ 1) (hj : 2 ≤ q) :
    ∃ i ∈ dyadicExponents Mcut, ∃ k ∈ dyadicExponents Mcut,
      ∃ d ∈ Finset.range 4,
        ‖sourceS3 N W‖ ≤
          6 * ((orderedBalancedKeys Mcut).card : ℝ) *
              (∑ p ∈ orderedBalancedBlock Mcut i k d, f N W p) +
          ((prefixFrequencyCube Mcut).card : ℝ) *
            ((9 / 4 : ℝ) * (N : ℝ) ^ 3 * radialDerivativeBudget q *
              (W.card : ℝ) ^ 3 / rho ^ q) +
          3 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 *
            prefixError T N Mcut q * prefixEnvelope T N Mcut q ^ 2 := by
  have hunbal : ∀ p ∈ prefixFrequencyCube Mcut,
      p ∉ GuthMaynardS3LiteralFullSelection.balancedCube Mcut →
        f N W p ≤ (9 / 4 : ℝ) * (N : ℝ) ^ 3 * radialDerivativeBudget q *
          (W.card : ℝ) ^ 3 / rho ^ q := by
    intro p hp hnot
    have hnot' : p ∉ GuthMaynardS3LiteralUnbalancedPermutationTail.balancedCube Mcut := by
      intro hpb
      apply hnot
      simpa only [GuthMaynardS3LiteralFullSelection.balancedCube,
        GuthMaynardS3LiteralUnbalancedPermutationTail.balancedCube] using hpb
    exact GuthMaynardS3LiteralUnbalancedPermutationTail.norm_sourceIm_unbalanced_of_not_balanced
      hN W hrho hslack hp hnot'
  obtain ⟨i, hi, k, hk, d, hd, hprefix⟩ :=
    GuthMaynardS3LiteralFullSelection.norm_sourceS3Prefix_le_selected_block
      hN W Mcut hrho q hunbal
  have htrunc := GuthMaynardS3LiteralTruncation.norm_sourceS3_le_finite_block_add_error
    hN hMcut hj hT W hdiam
  rw [← GuthMaynardS3LiteralTruncation.sourceS3Prefix_eq_finite_frequency_block] at htrunc
  refine ⟨i, hi, k, hk, d, hd, ?_⟩
  calc
    ‖sourceS3 N W‖ ≤ ‖sourceS3Prefix N Mcut W‖ +
        3 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 *
          prefixError T N Mcut q * prefixEnvelope T N Mcut q ^ 2 := htrunc
    _ ≤ 6 * ((orderedBalancedKeys Mcut).card : ℝ) *
          (∑ p ∈ orderedBalancedBlock Mcut i k d, f N W p) +
        ((prefixFrequencyCube Mcut).card : ℝ) *
          ((9 / 4 : ℝ) * (N : ℝ) ^ 3 * radialDerivativeBudget q *
            (W.card : ℝ) ^ 3 / rho ^ q) +
        3 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 *
          prefixError T N Mcut q * prefixEnvelope T N Mcut q ^ 2 := by
      linarith only [hprefix]

end
end GuthMaynardS3LiteralFullSelectionActual

#print axioms GuthMaynardS3LiteralFullSelectionActual.norm_sourceS3_le_selected_ordered_block_actual
