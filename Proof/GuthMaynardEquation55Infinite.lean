import GuthMaynardSectionFourPoisson

/-!
# Absolutely convergent Guth--Maynard equation (5.5)

`GuthMaynardEquation55Split` proves the frequency partition at finite
truncation.  Section 4 also supplies enough Schwartz decay to sum the literal
three-frequency kernel absolutely.  This file joins those facts and proves
the actual infinite identity used before the estimates of `S₁`, `S₂`, and
`S₃`.
-/

namespace GuthMaynardEquation55Infinite

open scoped BigOperators
open GuthMaynardEquation55Split GuthMaynardSectionFourPoisson

noncomputable section

abbrev Frequency := (ℤ × ℤ) × ℤ

private theorem summable_finset_sum
    {ι α : Type*} [NormedAddCommGroup α] [CompleteSpace α]
    (s : Finset ι) (f : ι → Frequency → α)
    (hf : ∀ i ∈ s, Summable (f i)) :
    Summable fun p => ∑ i ∈ s, f i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

def frequencyTerm (N : ℕ) (W : Finset ℝ) (p : Frequency) : ℂ :=
  sourceIm N W p.1.1 p.1.2 p.2

def sourceS1 (N : ℕ) (W : Finset ℝ) : ℂ :=
  ∑' p : Frequency,
    if exactlyOneNonzero p.1.1 p.1.2 p.2 then frequencyTerm N W p else 0

def sourceS2 (N : ℕ) (W : Finset ℝ) : ℂ :=
  ∑' p : Frequency,
    if exactlyTwoNonzero p.1.1 p.1.2 p.2 then frequencyTerm N W p else 0

def sourceS3 (N : ℕ) (W : Finset ℝ) : ℂ :=
  ∑' p : Frequency,
    if exactlyThreeNonzero p.1.1 p.1.2 p.2 then frequencyTerm N W p else 0

def sourceNonzeroFrequency (N : ℕ) (W : Finset ℝ) : ℂ :=
  ∑' p : Frequency,
    if p.1.1 ≠ 0 ∨ p.1.2 ≠ 0 ∨ p.2 ≠ 0 then frequencyTerm N W p else 0

/-- Absolute summability of the literal `I_m` family.  This is the convergence
fact needed to pass from the finite partition to equation (5.5). -/
theorem summable_frequencyTerm {N : ℕ} (hN : 0 < N) (W : Finset ℝ) :
    Summable (frequencyTerm N W) := by
  let K : ℝ → ℝ → ℝ → Frequency → ℂ :=
    fun t₁ t₂ t₃ p => (N : ℂ) ^ 3 *
      (GuthMaynardS1Source.sourceHhat (t₁ - t₂) ((p.1.1 : ℝ) * (N : ℝ)) *
        GuthMaynardS1Source.sourceHhat (t₂ - t₃) ((p.1.2 : ℝ) * (N : ℝ)) *
        GuthMaynardS1Source.sourceHhat (t₃ - t₁) ((p.2 : ℝ) * (N : ℝ)))
  have hK (t₁ t₂ t₃ : ℝ) : Summable (K t₁ t₂ t₃) := by
    exact summable_sourceFrequencyKernel t₁ t₂ t₃ hN
  have hK₃ (t₁ t₂ : ℝ) :
      Summable fun p => ∑ t₃ ∈ W, K t₁ t₂ t₃ p :=
    summable_finset_sum W (fun t₃ p => K t₁ t₂ t₃ p)
      fun t₃ _ => hK t₁ t₂ t₃
  have hK₂ (t₁ : ℝ) :
      Summable fun p => ∑ t₂ ∈ W, ∑ t₃ ∈ W, K t₁ t₂ t₃ p :=
    summable_finset_sum W
      (fun t₂ p => ∑ t₃ ∈ W, K t₁ t₂ t₃ p)
      fun t₂ _ => hK₃ t₁ t₂
  have hK₁ :
      Summable fun p => ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        K t₁ t₂ t₃ p :=
    summable_finset_sum W
      (fun t₁ p => ∑ t₂ ∈ W, ∑ t₃ ∈ W, K t₁ t₂ t₃ p)
      fun t₁ _ => hK₂ t₁
  exact hK₁.congr (by
    intro p
    unfold frequencyTerm sourceIm K
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t₁ ht₁
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t₂ ht₂
    rw [Finset.mul_sum])

/-- The infinite, absolutely convergent form of Guth--Maynard (5.5). -/
theorem source_equation5_5
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) :
    sourceNonzeroFrequency N W =
      sourceS1 N W + sourceS2 N W + sourceS3 N W := by
  have hf := summable_frequencyTerm hN W
  let F1 : Frequency → ℂ := fun p =>
    if exactlyOneNonzero p.1.1 p.1.2 p.2 then frequencyTerm N W p else 0
  let F2 : Frequency → ℂ := fun p =>
    if exactlyTwoNonzero p.1.1 p.1.2 p.2 then frequencyTerm N W p else 0
  let F3 : Frequency → ℂ := fun p =>
    if exactlyThreeNonzero p.1.1 p.1.2 p.2 then frequencyTerm N W p else 0
  let FN : Frequency → ℂ := fun p =>
    if p.1.1 ≠ 0 ∨ p.1.2 ≠ 0 ∨ p.2 ≠ 0 then frequencyTerm N W p else 0
  have h1 : Summable F1 := by
    refine (hf.indicator {p | exactlyOneNonzero p.1.1 p.1.2 p.2}).congr ?_
    intro p
    classical
    simp [F1, Set.indicator]
  have h2 : Summable F2 := by
    refine (hf.indicator {p | exactlyTwoNonzero p.1.1 p.1.2 p.2}).congr ?_
    intro p
    classical
    simp [F2, Set.indicator]
  have h3 : Summable F3 := by
    refine (hf.indicator {p | exactlyThreeNonzero p.1.1 p.1.2 p.2}).congr ?_
    intro p
    classical
    simp [F3, Set.indicator]
  have hpoint : FN = F1 + F2 + F3 := by
    funext p
    simp only [FN, F1, F2, F3, Pi.add_apply]
    by_cases hp1 : exactlyOneNonzero p.1.1 p.1.2 p.2
    · have hp2 : ¬ exactlyTwoNonzero p.1.1 p.1.2 p.2 := by
        simp only [exactlyOneNonzero] at hp1
        simp only [exactlyTwoNonzero]
        rcases hp1 with hp1 | hp1 | hp1 <;> aesop
      have hp3 : ¬ exactlyThreeNonzero p.1.1 p.1.2 p.2 := by
        simp only [exactlyOneNonzero] at hp1
        simp only [exactlyThreeNonzero]
        rcases hp1 with hp1 | hp1 | hp1 <;> aesop
      simp [hp1, hp2, hp3, nonzeroTriple_iff_frequency_partition]
    · by_cases hp2 : exactlyTwoNonzero p.1.1 p.1.2 p.2
      · have hp3 : ¬ exactlyThreeNonzero p.1.1 p.1.2 p.2 := by
          simp only [exactlyTwoNonzero] at hp2
          simp only [exactlyThreeNonzero]
          rcases hp2 with hp2 | hp2 | hp2 <;> aesop
        simp [hp1, hp2, hp3, nonzeroTriple_iff_frequency_partition]
      · by_cases hp3 : exactlyThreeNonzero p.1.1 p.1.2 p.2 <;>
          simp [hp1, hp2, hp3, nonzeroTriple_iff_frequency_partition]
  have hsum : (∑' p, FN p) = (∑' p, F1 p) + (∑' p, F2 p) + ∑' p, F3 p := by
    rw [hpoint]
    simp only [Pi.add_apply]
    rw [(h1.add h2).tsum_add h3, h1.tsum_add h2]
  simpa [sourceNonzeroFrequency, sourceS1, sourceS2, sourceS3,
    FN, F1, F2, F3] using hsum

end
end GuthMaynardEquation55Infinite

#print axioms GuthMaynardEquation55Infinite.summable_frequencyTerm
#print axioms GuthMaynardEquation55Infinite.source_equation5_5
