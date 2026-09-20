import MRTCorollary25Minkowski
import MRTCorollary25TypeD1CoefficientBound

/-!
# Integrated Type-d1 cutoff-removal weld for MRT (95)
-/

namespace MAPMRTCorollary25TypeD1IntegratedWeld

open scoped BigOperators
open MAPMRTCorollary25 MAPMRTCorollary25Certified
open MAPMRTCorollary25Instantiation
open MAPMRTCorollary25TypeD1LiteralWeld
open MAPMRTCorollary25TypeD1CoefficientBound
open MAPMRTCorollary25Minkowski MixedMeanFrontend

noncomputable section

theorem continuous_norm_halfLineDirichletPolynomial
    (X C : ℝ) (f : ℕ → ℂ) :
    Continuous (fun t ↦ ‖halfLineDirichletPolynomial X C f t‖) := by
  unfold halfLineDirichletPolynomial mellinPhase
  fun_prop

/-- The literal norm fields before and after the sharp `(X1,X2)` cutoff. -/
def typeD1FullNorm {Chi : Type*}
    (N M : ℝ) (phase : Chi → ℕ → ℂ) (alpha beta : ℕ → ℂ)
    (chi : Chi) (t : ℝ) : ℝ :=
  ‖halfLineDirichletPolynomial (N * M) 4
    (characterTwist (phase chi) (literalDirichletConvolution alpha beta)) t‖

def typeD1ClippedNorm {Chi : Type*}
    (N M X1 X2 : ℝ) (phase : Chi → ℕ → ℂ)
    (alpha beta : ℕ → ℂ) (chi : Chi) (t : ℝ) : ℝ :=
  ‖halfLineDirichletPolynomial (N * M) 4
    (intervalCutoff X1 X2
      (characterTwist (phase chi) (literalDirichletConvolution alpha beta))) t‖

theorem continuous_typeD1FullNorm {Chi : Type*}
    (N M : ℝ) (phase : Chi → ℕ → ℂ) (alpha beta : ℕ → ℂ)
    (chi : Chi) : Continuous (typeD1FullNorm N M phase alpha beta chi) := by
  exact continuous_norm_halfLineDirichletPolynomial _ _ _

theorem continuous_typeD1ClippedNorm {Chi : Type*}
    (N M X1 X2 : ℝ) (phase : Chi → ℕ → ℂ)
    (alpha beta : ℕ → ℂ) (chi : Chi) :
    Continuous (typeD1ClippedNorm N M X1 X2 phase alpha beta chi) := by
  exact continuous_norm_halfLineDirichletPolynomial _ _ _

/-- One connected component of the literal Type-d1 contribution to (95),
after certified Corollary 2.5, finite-character summation, compact Fubini,
Minkowski/Cauchy, and translated outer-window enlargement.

The error is displayed without asymptotic absorption, so the later padded far
budget can substitute the source choices of `T`, `U`, and `B`. -/
theorem literalTypeD1_component95_cutoff_transfer
    {Chi : Type*} [Fintype Chi]
    {N M T X1 X2 B U a b : ℝ}
    {alpha beta : ℕ → ℂ} {phase : Chi → ℕ → ℂ}
    (hN : 0 < N) (hM : 0 < M) (hNM : 1 ≤ N * M)
    (hT : 1 ≤ T) (hB : 0 ≤ B) (hU : 0 ≤ U) (hab : a ≤ b)
    (halpha : SupportedDyadic N alpha)
    (hbeta : SupportedDyadic M beta)
    (hphase : ∀ chi n, ‖phase chi n‖ ≤ 1)
    (hcoeff : ∀ n, ‖literalDirichletConvolution alpha beta n‖ ≤ B) :
    ∃ K : ℝ, 0 < K ∧
      (∫ t in a..b,
        (characterMovingMass
          (typeD1ClippedNorm N M X1 X2 phase alpha beta) U t) ^ 2) ≤
        2 * K ^ 2 *
          ((∫ u in (-T)..T, perronWeight u) ^ 2 *
              (∫ s in (a - T)..(b + T),
                (characterMovingMass
                  (typeD1FullNorm N M phase alpha beta) U s) ^ 2) +
            (b - a) *
              (2 * U * (Fintype.card Chi : ℝ) *
                (B * Real.sqrt (N * M) * Real.log (2 + T) / T)) ^ 2) := by
  obtain ⟨K, hK, hcut⟩ := mrtCorollary25_certified (4 : ℝ) (by norm_num)
  refine ⟨K, hK, ?_⟩
  let clip : Chi → ℝ → ℝ :=
    typeD1ClippedNorm N M X1 X2 phase alpha beta
  let full : Chi → ℝ → ℝ :=
    typeD1FullNorm N M phase alpha beta
  let E₀ := B * Real.sqrt (N * M) * Real.log (2 + T) / T
  have hfullCont : ∀ chi, Continuous (full chi) := fun chi ↦
    continuous_typeD1FullNorm N M phase alpha beta chi
  have hclipCont : ∀ chi, Continuous (clip chi) := fun chi ↦
    continuous_typeD1ClippedNorm N M X1 X2 phase alpha beta chi
  have hfull0 : ∀ chi t, 0 ≤ full chi t := fun chi t ↦ norm_nonneg _
  have hclip0 : ∀ chi t, 0 ≤ clip chi t := fun chi t ↦ norm_nonneg _
  have hE₀ : 0 ≤ E₀ := by
    dsimp only [E₀]
    have hlog : 0 ≤ Real.log (2 + T) := Real.log_nonneg (by linarith)
    positivity
  have hsupp : SupportedNear (N * M) 4
      (literalDirichletConvolution alpha beta) :=
    supportedNear_four_literalDirichletConvolution hN hM halpha hbeta
  have hpoint : ∀ chi s,
      clip chi s ≤ K * (perronConvolution (full chi) T s + E₀) := by
    intro chi s
    have hc := hcut (N * M) T X1 X2 s B
      (characterTwist (phase chi) (literalDirichletConvolution alpha beta))
      hNM hT hB (supportedNear_characterTwist hsupp)
      (norm_characterTwist_le (hphase chi) hcoeff)
    have hconv : perronConvolution (full chi) T s =
        ∫ u in (-T)..T,
          ‖halfLineDirichletPolynomial (N * M) 4
            (characterTwist (phase chi)
              (literalDirichletConvolution alpha beta)) (s + u)‖ /
              (1 + |u|) := by
      unfold perronConvolution
      apply intervalIntegral.integral_congr
      intro u hu
      dsimp only [full, typeD1FullNorm]
      rw [perronWeight]
      ring
    rw [hconv]
    simpa only [clip, E₀, typeD1ClippedNorm] using hc
  simpa only [clip, full, E₀] using
    character_component_square_cutoff_transfer hclipCont hfullCont
      hclip0 hfull0 hab hU (lt_of_lt_of_le zero_lt_one hT)
      hK.le hE₀ hpoint

/-- The literal Type-d1 contribution to (95), with the coefficient hypothesis
discharged by MRT's equation-(24) divisor--logarithm estimate.  The only
remaining integral on the right is the untruncated Type-d1 mean square treated
later in Proposition 6.1. -/
theorem literalTypeD1_component95_divisorLog_cutoff_transfer
    {Chi : Type*} [Fintype Chi]
    {r s ell j : ℕ} (hrs : 1 ≤ r + s)
    {eta A D N M T X1 X2 U a b : ℝ}
    {alpha beta : ℕ → ℂ} {phase : Chi → ℕ → ℂ}
    (heta : 0 < eta) (hA : 0 < A) (hD : 0 < D)
    (hN : 0 < N) (hM : 0 < M) (hNM : 1 ≤ N * M)
    (hT : 1 ≤ T) (hU : 0 ≤ U) (hab : a ≤ b)
    (halphaSupport : SupportedDyadic N alpha)
    (hbetaSupport : SupportedDyadic M beta)
    (halpha : DivisorLogMajorized r ell A alpha)
    (hbeta : DivisorLogMajorized s j D beta)
    (hphase : ∀ chi n, ‖phase chi n‖ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 0 < K ∧
      (∫ t in a..b,
        (characterMovingMass
          (typeD1ClippedNorm N M X1 X2 phase alpha beta) U t) ^ 2) ≤
        2 * K ^ 2 *
          ((∫ u in (-T)..T, perronWeight u) ^ 2 *
              (∫ z in (a - T)..(b + T),
                (characterMovingMass
                  (typeD1FullNorm N M phase alpha beta) U z) ^ 2) +
            (b - a) *
              (2 * U * (Fintype.card Chi : ℝ) *
                ((C * Real.rpow (4 * N * M) eta) *
                  Real.sqrt (N * M) * Real.log (2 + T) / T)) ^ 2) := by
  obtain ⟨C, hC, hcoeff⟩ :=
    literalDirichletConvolution_norm_le_productScale
      hrs heta hA hD hN hM halphaSupport hbetaSupport halpha hbeta
  have hscale0 : 0 ≤ 4 * N * M := by positivity
  have hB : 0 ≤ C * Real.rpow (4 * N * M) eta :=
    mul_nonneg hC.le (Real.rpow_nonneg hscale0 eta)
  obtain ⟨K, hK, htransfer⟩ :=
    literalTypeD1_component95_cutoff_transfer
      (N := N) (M := M) (T := T) (X1 := X1) (X2 := X2)
      (B := C * Real.rpow (4 * N * M) eta)
      (U := U) (a := a) (b := b)
      hN hM hNM hT hB hU hab halphaSupport hbetaSupport hphase hcoeff
  exact ⟨C, hC, K, hK, htransfer⟩

end
end MAPMRTCorollary25TypeD1IntegratedWeld

#print axioms MAPMRTCorollary25TypeD1IntegratedWeld.continuous_norm_halfLineDirichletPolynomial
#print axioms MAPMRTCorollary25TypeD1IntegratedWeld.literalTypeD1_component95_cutoff_transfer
#print axioms MAPMRTCorollary25TypeD1IntegratedWeld.literalTypeD1_component95_divisorLog_cutoff_transfer
