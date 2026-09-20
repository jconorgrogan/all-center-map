import GuthMaynardEquation55Infinite
import GuthMaynardS1Tail

/-!
# Exact Poisson trace decomposition below Guth--Maynard Proposition 4.6

This file separates the zero frequency from the absolutely convergent cubic
Poisson trace and then inserts the genuine infinite equation (5.5).  Thus no
finite frequency box or limiting premise remains in the `S₁+S₂+S₃`
decomposition.
-/

namespace GuthMaynardProposition46PoissonTrace

open GuthMaynardEquation55Split
open GuthMaynardEquation55Infinite
open GuthMaynardSectionFourPoisson

noncomputable section

/-- The off-diagonal part of the zero Poisson frequency. -/
def zeroFrequencyOffDiagonal (W : Finset ℝ) : ℂ :=
  ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
    if t₁ = t₂ ∧ t₂ = t₃ then 0 else
      GuthMaynardS1Source.sourceHhat (t₁ - t₂) 0 *
        GuthMaynardS1Source.sourceHhat (t₂ - t₃) 0 *
          GuthMaynardS1Source.sourceHhat (t₃ - t₁) 0

def zeroFrequencyOffDiagonalMass (W : Finset ℝ) : ℝ :=
  ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
    if t₁ = t₂ ∧ t₂ = t₃ then 0 else
      ‖GuthMaynardS1Source.sourceHhat (t₁ - t₂) 0 *
        GuthMaynardS1Source.sourceHhat (t₂ - t₃) 0 *
          GuthMaynardS1Source.sourceHhat (t₃ - t₁) 0‖

theorem norm_zeroFrequencyOffDiagonal_le_mass (W : Finset ℝ) :
    ‖zeroFrequencyOffDiagonal W‖ ≤ zeroFrequencyOffDiagonalMass W := by
  unfold zeroFrequencyOffDiagonal zeroFrequencyOffDiagonalMass
  refine (norm_sum_le W _).trans ?_
  apply Finset.sum_le_sum
  intro t₁ ht₁
  refine (norm_sum_le W _).trans ?_
  apply Finset.sum_le_sum
  intro t₂ ht₂
  refine (norm_sum_le W _).trans ?_
  apply Finset.sum_le_sum
  intro t₃ ht₃
  split_ifs <;> simp

/-- Explicit rapid-decay estimate for the zero-frequency off-diagonal term
in Lemma 4.5. -/
theorem zeroFrequencyOffDiagonalMass_le
    {W : Finset ℝ} {R : ℝ} (hR : 0 < R)
    (hsep : ∀ t₁ ∈ W, ∀ t₂ ∈ W, t₁ ≠ t₂ → R ≤ |t₁ - t₂|)
    (j : ℕ) :
    zeroFrequencyOffDiagonalMass W ≤
      (W.card : ℝ) ^ 3 *
        ((GuthMaynardS1Tail.s1VerticalConstant j /
            (R / (2 * Real.pi)) ^ j) *
          GuthMaynardSectionThreeCutoffDerivativeBudget.lemma43DerivativeConstant 0 ^ 2) +
      (W.card : ℝ) ^ 3 *
        (GuthMaynardSectionThreeCutoffDerivativeBudget.lemma43DerivativeConstant 0 *
          (GuthMaynardS1Tail.s1VerticalConstant j /
            (R / (2 * Real.pi)) ^ j) *
          GuthMaynardSectionThreeCutoffDerivativeBudget.lemma43DerivativeConstant 0) := by
  have hfirst := GuthMaynardS1Tail.sourceS1ThirdFiniteFirstGapMass_le
    (N := 1) (W := W) (M := {0}) hR hsep j
  have hsecond := GuthMaynardS1Tail.sourceS1ThirdFiniteSecondGapMass_le
    (N := 1) (W := W) (M := {0}) hR hsep j
  have hsplit : zeroFrequencyOffDiagonalMass W =
      GuthMaynardS1Source.sourceS1ThirdFiniteFirstGapMass 1 W {0} +
        GuthMaynardS1Source.sourceS1ThirdFiniteSecondGapMass 1 W {0} := by
    unfold zeroFrequencyOffDiagonalMass
      GuthMaynardS1Source.sourceS1ThirdFiniteFirstGapMass
      GuthMaynardS1Source.sourceS1ThirdFiniteSecondGapMass
      GuthMaynardS1Source.sourceS1KernelThird
    simp only [Finset.sum_singleton, Int.cast_zero, zero_mul]
    simp_rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t₁ ht₁
    apply Finset.sum_congr rfl
    intro t₂ ht₂
    apply Finset.sum_congr rfl
    intro t₃ ht₃
    by_cases h₁₂ : t₁ = t₂
    · by_cases h₂₃ : t₂ = t₃ <;> simp [h₁₂, h₂₃]
    · simp [h₁₂]
  rw [hsplit]
  simpa using add_le_add hfirst hsecond

/-- Exact diagonal/off-diagonal split of `I₀`.  The first term is the source
main term `N^3 |W| \widehat h_0(0)^3`; all cancellation error is now the
explicit finite `zeroFrequencyOffDiagonal`. -/
theorem sourceIm_zero_eq_diagonal_add_offDiagonal
    (N : ℕ) (W : Finset ℝ) :
    sourceIm N W 0 0 0 =
      (N : ℂ) ^ 3 * (W.card : ℂ) *
          GuthMaynardS1Source.sourceHhat 0 0 ^ 3 +
        (N : ℂ) ^ 3 * zeroFrequencyOffDiagonal W := by
  let K : ℝ → ℝ → ℝ → ℂ := fun t₁ t₂ t₃ =>
    GuthMaynardS1Source.sourceHhat (t₁ - t₂) 0 *
      GuthMaynardS1Source.sourceHhat (t₂ - t₃) 0 *
        GuthMaynardS1Source.sourceHhat (t₃ - t₁) 0
  have hpoint (t₁ t₂ t₃ : ℝ) :
      K t₁ t₂ t₃ =
        (if t₁ = t₂ ∧ t₂ = t₃ then
          GuthMaynardS1Source.sourceHhat 0 0 ^ 3 else 0) +
        (if t₁ = t₂ ∧ t₂ = t₃ then 0 else K t₁ t₂ t₃) := by
    by_cases hdiag : t₁ = t₂ ∧ t₂ = t₃
    · rcases hdiag with ⟨rfl, rfl⟩
      simp [K]
      ring
    · simp [hdiag]
  have hsum :
      (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, K t₁ t₂ t₃) =
        (W.card : ℂ) * GuthMaynardS1Source.sourceHhat 0 0 ^ 3 +
          zeroFrequencyOffDiagonal W := by
    calc
      (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, K t₁ t₂ t₃) =
          ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
            ((if t₁ = t₂ ∧ t₂ = t₃ then
                GuthMaynardS1Source.sourceHhat 0 0 ^ 3 else 0) +
              (if t₁ = t₂ ∧ t₂ = t₃ then 0 else K t₁ t₂ t₃)) := by
            apply Finset.sum_congr rfl
            intro t₁ ht₁
            apply Finset.sum_congr rfl
            intro t₂ ht₂
            apply Finset.sum_congr rfl
            intro t₃ ht₃
            exact hpoint t₁ t₂ t₃
      _ = (W.card : ℂ) * GuthMaynardS1Source.sourceHhat 0 0 ^ 3 +
          zeroFrequencyOffDiagonal W := by
            simp_rw [Finset.sum_add_distrib]
            unfold zeroFrequencyOffDiagonal
            congr 1
            calc
              (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
                  if t₁ = t₂ ∧ t₂ = t₃ then
                    GuthMaynardS1Source.sourceHhat 0 0 ^ 3 else 0) =
                  ∑ _t₁ ∈ W, GuthMaynardS1Source.sourceHhat 0 0 ^ 3 := by
                    apply Finset.sum_congr rfl
                    intro t₁ ht₁
                    classical
                    rw [Finset.sum_eq_single t₁]
                    · simp [ht₁]
                    · intro t₂ ht₂ ht₂ne
                      simp [Ne.symm ht₂ne]
                    · simp [ht₁]
              _ = (W.card : ℂ) *
                  GuthMaynardS1Source.sourceHhat 0 0 ^ 3 := by simp
  unfold sourceIm
  simp only [Int.cast_zero, zero_mul]
  rw [show (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
      GuthMaynardS1Source.sourceHhat (t₁ - t₂) 0 *
        GuthMaynardS1Source.sourceHhat (t₂ - t₃) 0 *
          GuthMaynardS1Source.sourceHhat (t₃ - t₁) 0) =
      (W.card : ℂ) * GuthMaynardS1Source.sourceHhat 0 0 ^ 3 +
        zeroFrequencyOffDiagonal W by simpa [K] using hsum]
  ring

/-- Constant-explicit Lemma 4.5 zero-frequency error.  Arbitrarily large `j`
turns the displayed separated-gap denominator into the source's
`O_epsilon(T^-100)` after the usual polynomial cardinality ledger. -/
theorem norm_sourceIm_zero_sub_diagonal_le
    {N : ℕ} {W : Finset ℝ} {R : ℝ} (hR : 0 < R)
    (hsep : ∀ t₁ ∈ W, ∀ t₂ ∈ W, t₁ ≠ t₂ → R ≤ |t₁ - t₂|)
    (j : ℕ) :
    ‖sourceIm N W 0 0 0 -
        (N : ℂ) ^ 3 * (W.card : ℂ) *
          GuthMaynardS1Source.sourceHhat 0 0 ^ 3‖ ≤
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
  have hmass := zeroFrequencyOffDiagonalMass_le hR hsep j
  have hoff := norm_zeroFrequencyOffDiagonal_le_mass W
  rw [sourceIm_zero_eq_diagonal_add_offDiagonal]
  have hnorm : ‖(N : ℂ) ^ 3 * zeroFrequencyOffDiagonal W‖ =
      (N : ℝ) ^ 3 * ‖zeroFrequencyOffDiagonal W‖ := by simp
  rw [show (N : ℂ) ^ 3 * (W.card : ℂ) *
        GuthMaynardS1Source.sourceHhat 0 0 ^ 3 +
        (N : ℂ) ^ 3 * zeroFrequencyOffDiagonal W -
        (N : ℂ) ^ 3 * (W.card : ℂ) *
          GuthMaynardS1Source.sourceHhat 0 0 ^ 3 =
      (N : ℂ) ^ 3 * zeroFrequencyOffDiagonal W by ring,
    hnorm]
  exact mul_le_mul_of_nonneg_left (hoff.trans hmass) (by positivity)

/-- Exact zero/nonzero frequency decomposition of the cubic Poisson trace. -/
theorem sourceNormalizedTraceCube_eq_zero_add_nonzero
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) :
    sourceNormalizedTraceCube N W =
      sourceIm N W 0 0 0 + sourceNonzeroFrequency N W := by
  rw [sourceNormalizedTraceCube_eq_tsum_sourceIm hN W]
  let f : Frequency → ℂ := frequencyTerm N W
  have hf : Summable f := summable_frequencyTerm hN W
  have hsplit := hf.tsum_eq_add_tsum_ite (((0, 0), 0) : Frequency)
  change (∑' p : Frequency, f p) = _
  rw [hsplit]
  congr 1
  apply tsum_congr
  intro p
  simp only [f, frequencyTerm]
  by_cases hp : p = (((0, 0), 0) : Frequency)
  · subst p
    simp
  · have hnz : p.1.1 ≠ 0 ∨ p.1.2 ≠ 0 ∨ p.2 ≠ 0 := by
      contrapose! hp
      rcases p with ⟨⟨p₁, p₂⟩, p₃⟩
      simp_all
    simp [hp, hnz]

/-- Exact infinite `S₁+S₂+S₃` form of the cubic Poisson trace.  This is the
identity immediately consumed by Sections 5, 6, and 7--11. -/
theorem sourceNormalizedTraceCube_eq_zero_add_S1_S2_S3
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) :
    sourceNormalizedTraceCube N W =
      sourceIm N W 0 0 0 +
        (sourceS1 N W + sourceS2 N W + sourceS3 N W) := by
  rw [sourceNormalizedTraceCube_eq_zero_add_nonzero hN W,
    source_equation5_5 hN W]

end
end GuthMaynardProposition46PoissonTrace

#print axioms GuthMaynardProposition46PoissonTrace.sourceNormalizedTraceCube_eq_zero_add_nonzero
#print axioms GuthMaynardProposition46PoissonTrace.sourceNormalizedTraceCube_eq_zero_add_S1_S2_S3
#print axioms GuthMaynardProposition46PoissonTrace.sourceIm_zero_eq_diagonal_add_offDiagonal
#print axioms GuthMaynardProposition46PoissonTrace.zeroFrequencyOffDiagonalMass_le
#print axioms GuthMaynardProposition46PoissonTrace.norm_sourceIm_zero_sub_diagonal_le
