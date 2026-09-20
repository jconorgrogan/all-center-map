import GuthMaynardSectionFourNormalization
import GuthMaynardProposition46PoissonTrace

/-!
# Raw matrix form of Guth--Maynard Proposition 4.6

This weld transports the already certified absolutely convergent Poisson
frequency split back to the literal Section 4 matrix trace.
-/
namespace GuthMaynardProposition46RawTrace

open GuthMaynardSectionFourTrace
open GuthMaynardSectionFourNormalization
open GuthMaynardEquation55Infinite
open GuthMaynardEquation55Split
open GuthMaynardProposition46PoissonTrace

noncomputable section

/-- Exact Poisson identity for the Hilbert--Schmidt trace in Lemma 4.4. -/
theorem sourceTraceOne_eq_frequencyTsum
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) :
    sourceTraceOne W N =
      (W.card : ℂ) * ((N : ℂ) *
        ∑' m : ℤ, GuthMaynardS1Source.sourceHhat 0 ((m : ℝ) * (N : ℝ))) := by
  have hdiag (t : SourceRow W) :
      sourceGram W N t t = sourceNormalizedGram W N t t := by
    rw [sourceGram_eq_rowPhases_mul_normalized hN W,
      sourceRowPhase_mul_star]
    simp
  calc
    sourceTraceOne W N = ∑ t : SourceRow W, sourceGram W N t t := by
      rfl
    _ = ∑ t : SourceRow W, sourceNormalizedGram W N t t := by
      apply Finset.sum_congr rfl
      intro t ht
      exact hdiag t
    _ = ∑ t : SourceRow W, ∑ n : SourceColumn N,
        GuthMaynardSectionThreeCutoffDerivativeBudget.sectionThreeOscillatory 0
          (((n : ℕ) : ℝ) / (N : ℝ)) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [sourceNormalizedGram_apply_oscillatory hN]
      simp
    _ = (W.card : ℂ) *
        ∑ n : SourceColumn N,
          GuthMaynardSectionThreeCutoffDerivativeBudget.sectionThreeOscillatory 0
            (((n : ℕ) : ℝ) / (N : ℝ)) := by simp
    _ = (W.card : ℂ) *
        (∑' z : ℤ,
          GuthMaynardSectionThreeCutoffDerivativeBudget.sectionThreeOscillatory 0
            ((z : ℝ) / (N : ℝ))) := by
      rw [tsum_oscillatory_eq_columnSum 0 hN]
    _ = _ := by
      rw [GuthMaynardSectionFourPoisson.tsum_sectionThreeOscillatory_scaled_eq 0 hN]

/-- Exact raw cubic trace split into its zero frequency and the three source
sectors of (5.5). -/
theorem sourceTraceCube_eq_zero_add_S1_S2_S3
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) :
    sourceTraceCube W N =
      sourceIm N W 0 0 0 +
        (sourceS1 N W + sourceS2 N W + sourceS3 N W) := by
  rw [sourceTraceCube_eq_normalized hN W,
    sourceNormalizedMatrixTraceCube_eq_poissonTrace hN W,
    sourceNormalizedTraceCube_eq_zero_add_S1_S2_S3 hN W]

/-- Constant-explicit raw-trace version of Lemma 4.5.  It exposes the exact
S₁/S₂/S₃ quantities and only the certified separated zero-frequency error. -/
theorem norm_sourceTraceCube_sub_main_and_sectors_le
    {N : ℕ} {W : Finset ℝ} {R : ℝ} (hN : 0 < N) (hR : 0 < R)
    (hsep : ∀ t₁ ∈ W, ∀ t₂ ∈ W, t₁ ≠ t₂ → R ≤ |t₁ - t₂|)
    (j : ℕ) :
    ‖sourceTraceCube W N -
      ((N : ℂ) ^ 3 * (W.card : ℂ) *
          GuthMaynardS1Source.sourceHhat 0 0 ^ 3 +
        (sourceS1 N W + sourceS2 N W + sourceS3 N W))‖ ≤
      (N : ℝ) ^ 3 *
        ((W.card : ℝ) ^ 3 *
          ((GuthMaynardS1Tail.s1VerticalConstant j /
              (R / (2 * Real.pi)) ^ j) *
            GuthMaynardSectionThreeCutoffDerivativeBudget.lemma43DerivativeConstant 0 ^ 2) +
        (W.card : ℝ) ^ 3 *
          (GuthMaynardSectionThreeCutoffDerivativeBudget.lemma43DerivativeConstant 0 *
            (GuthMaynardS1Tail.s1VerticalConstant j /
              (R / (2 * Real.pi)) ^ j) *
            GuthMaynardSectionThreeCutoffDerivativeBudget.lemma43DerivativeConstant 0)) := by
  rw [sourceTraceCube_eq_zero_add_S1_S2_S3 hN W]
  rw [show sourceIm N W 0 0 0 +
      (sourceS1 N W + sourceS2 N W + sourceS3 N W) -
      ((N : ℂ) ^ 3 * (W.card : ℂ) *
          GuthMaynardS1Source.sourceHhat 0 0 ^ 3 +
        (sourceS1 N W + sourceS2 N W + sourceS3 N W)) =
      sourceIm N W 0 0 0 -
        (N : ℂ) ^ 3 * (W.card : ℂ) *
          GuthMaynardS1Source.sourceHhat 0 0 ^ 3 by ring]
  exact norm_sourceIm_zero_sub_diagonal_le hR hsep j

end
end GuthMaynardProposition46RawTrace

#print axioms GuthMaynardProposition46RawTrace.sourceTraceCube_eq_zero_add_S1_S2_S3
#print axioms GuthMaynardProposition46RawTrace.norm_sourceTraceCube_sub_main_and_sectors_le
#print axioms GuthMaynardProposition46RawTrace.sourceTraceOne_eq_frequencyTsum
