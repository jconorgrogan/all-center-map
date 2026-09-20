import GuthMaynardSectionFourTrace

/-!
# Exact finite-frequency form of Guth--Maynard (5.5)

The source partitions the nonzero frequency triples by the number of nonzero
coordinates.  We make that partition literal at every finite truncation.  No
convergence or rearrangement of an infinite series is used here.
-/

namespace GuthMaynardEquation55Split

open scoped BigOperators
open GuthMaynardS1Source

noncomputable section

def exactlyOneNonzero (m₁ m₂ m₃ : ℤ) : Prop :=
  (m₁ ≠ 0 ∧ m₂ = 0 ∧ m₃ = 0) ∨
  (m₁ = 0 ∧ m₂ ≠ 0 ∧ m₃ = 0) ∨
  (m₁ = 0 ∧ m₂ = 0 ∧ m₃ ≠ 0)

def exactlyTwoNonzero (m₁ m₂ m₃ : ℤ) : Prop :=
  (m₁ = 0 ∧ m₂ ≠ 0 ∧ m₃ ≠ 0) ∨
  (m₁ ≠ 0 ∧ m₂ = 0 ∧ m₃ ≠ 0) ∨
  (m₁ ≠ 0 ∧ m₂ ≠ 0 ∧ m₃ = 0)

def exactlyThreeNonzero (m₁ m₂ m₃ : ℤ) : Prop :=
  m₁ ≠ 0 ∧ m₂ ≠ 0 ∧ m₃ ≠ 0

instance (m₁ m₂ m₃ : ℤ) : Decidable (exactlyOneNonzero m₁ m₂ m₃) := by
  unfold exactlyOneNonzero
  infer_instance

instance (m₁ m₂ m₃ : ℤ) : Decidable (exactlyTwoNonzero m₁ m₂ m₃) := by
  unfold exactlyTwoNonzero
  infer_instance

instance (m₁ m₂ m₃ : ℤ) : Decidable (exactlyThreeNonzero m₁ m₂ m₃) := by
  unfold exactlyThreeNonzero
  infer_instance

theorem nonzeroTriple_iff_frequency_partition (m₁ m₂ m₃ : ℤ) :
    (m₁ ≠ 0 ∨ m₂ ≠ 0 ∨ m₃ ≠ 0) ↔
      exactlyOneNonzero m₁ m₂ m₃ ∨ exactlyTwoNonzero m₁ m₂ m₃ ∨
        exactlyThreeNonzero m₁ m₂ m₃ := by
  unfold exactlyOneNonzero exactlyTwoNonzero exactlyThreeNonzero
  by_cases h₁ : m₁ = 0 <;> by_cases h₂ : m₂ = 0 <;>
    by_cases h₃ : m₃ = 0 <;> simp [h₁, h₂, h₃]

/-- The literal `I_m` of Lemma 4.5. -/
def sourceIm (N : ℕ) (W : Finset ℝ) (m₁ m₂ m₃ : ℤ) : ℂ :=
  (N : ℂ) ^ 3 *
    ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
      sourceHhat (t₁ - t₂) ((m₁ : ℝ) * N) *
      sourceHhat (t₂ - t₃) ((m₂ : ℝ) * N) *
      sourceHhat (t₃ - t₁) ((m₃ : ℝ) * N)

def sourceS1Finite (N : ℕ) (W : Finset ℝ) (M : Finset ℤ) : ℂ :=
  ∑ m₁ ∈ M, ∑ m₂ ∈ M, ∑ m₃ ∈ M,
    if exactlyOneNonzero m₁ m₂ m₃ then sourceIm N W m₁ m₂ m₃ else 0

def sourceS2Finite (N : ℕ) (W : Finset ℝ) (M : Finset ℤ) : ℂ :=
  ∑ m₁ ∈ M, ∑ m₂ ∈ M, ∑ m₃ ∈ M,
    if exactlyTwoNonzero m₁ m₂ m₃ then sourceIm N W m₁ m₂ m₃ else 0

def sourceS3Finite (N : ℕ) (W : Finset ℝ) (M : Finset ℤ) : ℂ :=
  ∑ m₁ ∈ M, ∑ m₂ ∈ M, ∑ m₃ ∈ M,
    if exactlyThreeNonzero m₁ m₂ m₃ then sourceIm N W m₁ m₂ m₃ else 0

def sourceNonzeroFrequencyFinite
    (N : ℕ) (W : Finset ℝ) (M : Finset ℤ) : ℂ :=
  ∑ m₁ ∈ M, ∑ m₂ ∈ M, ∑ m₃ ∈ M,
    if m₁ ≠ 0 ∨ m₂ ≠ 0 ∨ m₃ ≠ 0 then sourceIm N W m₁ m₂ m₃ else 0

/-- Exact finite version of (5.5).  The infinite equality may only be obtained
after absolute summability has been proved; this theorem cannot conceal that
analytic obligation. -/
theorem source_equation5_5_finite
    (N : ℕ) (W : Finset ℝ) (M : Finset ℤ) :
    sourceNonzeroFrequencyFinite N W M =
      sourceS1Finite N W M + sourceS2Finite N W M +
        sourceS3Finite N W M := by
  unfold sourceNonzeroFrequencyFinite sourceS1Finite sourceS2Finite
    sourceS3Finite
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m₁ hm₁
  apply Finset.sum_congr rfl
  intro m₂ hm₂
  apply Finset.sum_congr rfl
  intro m₃ hm₃
  by_cases h₁ : exactlyOneNonzero m₁ m₂ m₃
  · have h₂ : ¬ exactlyTwoNonzero m₁ m₂ m₃ := by
      simp only [exactlyOneNonzero] at h₁
      simp only [exactlyTwoNonzero]
      rcases h₁ with h₁ | h₁ | h₁ <;> aesop
    have h₃ : ¬ exactlyThreeNonzero m₁ m₂ m₃ := by
      simp only [exactlyOneNonzero] at h₁
      simp only [exactlyThreeNonzero]
      rcases h₁ with h₁ | h₁ | h₁ <;> aesop
    simp [h₁, h₂, h₃, nonzeroTriple_iff_frequency_partition]
  · by_cases h₂ : exactlyTwoNonzero m₁ m₂ m₃
    · have h₃ : ¬ exactlyThreeNonzero m₁ m₂ m₃ := by
        simp only [exactlyTwoNonzero] at h₂
        simp only [exactlyThreeNonzero]
        rcases h₂ with h₂ | h₂ | h₂ <;> aesop
      simp [h₁, h₂, h₃, nonzeroTriple_iff_frequency_partition]
    · by_cases h₃ : exactlyThreeNonzero m₁ m₂ m₃ <;>
        simp [h₁, h₂, h₃, nonzeroTriple_iff_frequency_partition]

end
end GuthMaynardEquation55Split

#print axioms GuthMaynardEquation55Split.nonzeroTriple_iff_frequency_partition
#print axioms GuthMaynardEquation55Split.source_equation5_5_finite
