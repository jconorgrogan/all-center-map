import MRTCorollary25CertifiedMAPWeld

/-!
# Literal one-factor Type-d branch after certified cutoff removal

This file performs the first source-facing HB weld on an actual Dirichlet
convolution, rather than on an abstract branch array.
-/

namespace MAPMRTCorollary25TypeD1LiteralWeld

open scoped BigOperators
open MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTCorollary25CertifiedMAPWeld MixedMeanFrontend

noncomputable section

/-- Finite Dirichlet convolution on positive antidiagonal divisor pairs. -/
def literalDirichletConvolution (alpha beta : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ z ∈ n.divisorsAntidiagonal, alpha z.1 * beta z.2

/-- Literal support on the real dyadic block `[N,2N]`. -/
def SupportedDyadic (N : ℝ) (f : ℕ → ℂ) : Prop :=
  ∀ n : ℕ, ¬ (N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N) → f n = 0

/-- A convolution of two dyadic coefficients is supported on the literal
product block `[NM,4NM]`. -/
theorem literalDirichletConvolution_eq_zero_off_productBlock
    {N M : ℝ} (hN : 0 ≤ N) (hM : 0 ≤ M)
    {alpha beta : ℕ → ℂ}
    (halpha : SupportedDyadic N alpha)
    (hbeta : SupportedDyadic M beta)
    {n : ℕ}
    (hn : ¬ (N * M ≤ (n : ℝ) ∧ (n : ℝ) ≤ 4 * N * M)) :
    literalDirichletConvolution alpha beta n = 0 := by
  unfold literalDirichletConvolution
  apply Finset.sum_eq_zero
  intro z hz
  have hmulNat : z.1 * z.2 = n := (Nat.mem_divisorsAntidiagonal.mp hz).1
  have hmulReal : (z.1 : ℝ) * (z.2 : ℝ) = (n : ℝ) := by
    exact_mod_cast hmulNat
  by_cases ha : N ≤ (z.1 : ℝ) ∧ (z.1 : ℝ) ≤ 2 * N
  · by_cases hb : M ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ 2 * M
    · exfalso
      apply hn
      constructor
      · rw [← hmulReal]
        exact mul_le_mul ha.1 hb.1 hM (by positivity)
      · rw [← hmulReal]
        have hupper := mul_le_mul ha.2 hb.2 (by positivity : (0 : ℝ) ≤ z.2)
          (by positivity : (0 : ℝ) ≤ 2 * N)
        nlinarith
    · rw [hbeta z.2 hb, mul_zero]
  · rw [halpha z.1 ha, zero_mul]

/-- The product-block support implies the uniform Corollary 2.5 support with
the fixed honest dilation constant `C=4`. -/
theorem supportedNear_four_literalDirichletConvolution
    {N M : ℝ} (hN : 0 < N) (hM : 0 < M)
    {alpha beta : ℕ → ℂ}
    (halpha : SupportedDyadic N alpha)
    (hbeta : SupportedDyadic M beta) :
    SupportedNear (N * M) 4 (literalDirichletConvolution alpha beta) := by
  intro n hn
  apply literalDirichletConvolution_eq_zero_off_productBlock hN.le hM.le
    halpha hbeta
  intro hblock
  rcases hn with hlower | hupper
  · have hNM : 0 < N * M := mul_pos hN hM
    nlinarith
  · nlinarith

/-- Premise-free Corollary 2.5 on the first literal Type-`d1` convolution.
The pointwise convolution bound remains explicit because its divisor-bound
proof belongs to the HB coefficient bookkeeping, not cutoff removal. -/
theorem cutoffRemoval_literalTypeD1_certified
    {N M T X1 X2 B : ℝ} {alpha beta phase : ℕ → ℂ}
    (hN : 0 < N) (hM : 0 < M) (hNM : 1 ≤ N * M)
    (hT : 1 ≤ T) (hB : 0 ≤ B)
    (halpha : SupportedDyadic N alpha)
    (hbeta : SupportedDyadic M beta)
    (hphase : ∀ n, ‖phase n‖ ≤ 1)
    (hcoeff : ∀ n, ‖literalDirichletConvolution alpha beta n‖ ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ,
      ‖halfLineDirichletPolynomial (N * M) 4
          (intervalCutoff X1 X2
            (characterTwist phase
              (literalDirichletConvolution alpha beta))) t‖ ≤
        K * ((∫ u in (-T)..T,
            ‖halfLineDirichletPolynomial (N * M) 4
              (characterTwist phase
                (literalDirichletConvolution alpha beta)) (t + u)‖ /
                (1 + |u|)) +
          B * Real.sqrt (N * M) * Real.log (2 + T) / T) := by
  obtain ⟨K, hK, hcut⟩ := cutoffRemoval_characterTwist_certified
    (C := (4 : ℝ)) (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro t
  exact hcut (N * M) T X1 X2 t B phase
    (literalDirichletConvolution alpha beta) hNM hT hB
    (supportedNear_four_literalDirichletConvolution hN hM halpha hbeta)
    hphase hcoeff

end
end MAPMRTCorollary25TypeD1LiteralWeld

#print axioms MAPMRTCorollary25TypeD1LiteralWeld.literalDirichletConvolution_eq_zero_off_productBlock
#print axioms MAPMRTCorollary25TypeD1LiteralWeld.supportedNear_four_literalDirichletConvolution
#print axioms MAPMRTCorollary25TypeD1LiteralWeld.cutoffRemoval_literalTypeD1_certified
