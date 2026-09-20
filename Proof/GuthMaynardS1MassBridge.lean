import GuthMaynardEquation55Infinite
import GuthMaynardS1Tail

/-!
# Exact infinite `S₁` to positive-mass bridge

This file proves the norm domination used implicitly at the first line of
Guth--Maynard Proposition 5.1.  The exact equation-(5.5) `S₁` tsum has three
coordinate orientations.  Each is reduced to the third-axis positive mass by
absolute convergence and a cyclic permutation of the finite ordinate cube.
-/

namespace GuthMaynardS1MassBridge

open scoped BigOperators
open GuthMaynardEquation55Split GuthMaynardEquation55Infinite
open GuthMaynardS1Source GuthMaynardS1Tail

noncomputable section

private theorem summable_finset_sum_real
    {ι α : Type*} (s : Finset ι) (f : ι → α → ℝ)
    (hf : ∀ i ∈ s, Summable (f i)) :
    Summable fun a => ∑ i ∈ s, f i a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).add
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- Cyclic invariance of a finite cube sum. -/
theorem finset_sum3_cycle
    {α R : Type*} [DecidableEq α] [AddCommMonoid R]
    (W : Finset α) (f : α → α → α → R) :
    (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, f a b c) =
      ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, f b c a := by
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_comm]

private theorem norm_sum3_le
    {α : Type*} [DecidableEq α] (W : Finset α)
    (f : α → α → α → ℂ) :
    ‖∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, f a b c‖ ≤
      ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, ‖f a b c‖ := by
  calc
    _ ≤ ∑ a ∈ W, ‖∑ b ∈ W, ∑ c ∈ W, f a b c‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ W, ∑ b ∈ W, ‖∑ c ∈ W, f a b c‖ := by
      apply Finset.sum_le_sum
      intro a ha
      exact norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact norm_sum_le _ _

private def thirdMassSequence (N : ℕ) (W : Finset ℝ) (m : ℤ) : ℝ :=
  if m ≠ 0 then
    ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
      ‖sourceS1KernelThird N t₁ t₂ t₃ m‖
  else 0

private theorem summable_thirdMassSequence
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) :
    Summable (thirdMassSequence N W) := by
  have hpoint (t₁ t₂ t₃ : ℝ) :
      Summable fun m : ℤ => if m ≠ 0 then
        ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ else 0 := by
    have hfar := summable_sourceS1KernelThird_far
      (t₁ := t₁) (t₂ := t₂) (t₃ := t₃) (T := |t₃ - t₁|)
      (B := (1 : ℝ)) hN (abs_nonneg _) (by norm_num) le_rfl
    convert hfar using 1
    funext m
    by_cases hm : m = 0
    · simp [hm]
    · simp [hm, one_le_abs_intCast hm]
  unfold thirdMassSequence
  have h₃ (t₁ t₂ : ℝ) : Summable fun m : ℤ =>
      ∑ t₃ ∈ W, if m ≠ 0 then
        ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ else 0 :=
    summable_finset_sum_real W (fun t₃ m => if m ≠ 0 then
      ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ else 0)
      (fun t₃ _ => hpoint t₁ t₂ t₃)
  have h₂ (t₁ : ℝ) : Summable fun m : ℤ =>
      ∑ t₂ ∈ W, ∑ t₃ ∈ W, if m ≠ 0 then
        ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ else 0 :=
    summable_finset_sum_real W
      (fun t₂ m => ∑ t₃ ∈ W, if m ≠ 0 then
        ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ else 0)
      (fun t₂ _ => h₃ t₁ t₂)
  have h₁ : Summable fun m : ℤ =>
      ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, if m ≠ 0 then
        ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ else 0 :=
    summable_finset_sum_real W
      (fun t₁ m => ∑ t₂ ∈ W, ∑ t₃ ∈ W, if m ≠ 0 then
        ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ else 0)
      (fun t₁ _ => h₂ t₁)
  exact h₁.congr (by
    intro m
    by_cases hm : m = 0 <;> simp [hm])

private theorem norm_sourceIm_third_le
    (N : ℕ) (W : Finset ℝ) (m : ℤ) :
    ‖sourceIm N W 0 0 m‖ ≤
      (N : ℝ) ^ 3 *
        (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
          ‖sourceS1KernelThird N t₁ t₂ t₃ m‖) := by
  unfold sourceIm sourceS1KernelThird
  rw [norm_mul]
  simp only [Complex.norm_natCast, norm_pow, Int.cast_zero, zero_mul]
  gcongr
  exact norm_sum3_le W _

private theorem norm_sourceIm_first_le
    (N : ℕ) (W : Finset ℝ) (m : ℤ) :
    ‖sourceIm N W m 0 0‖ ≤
      (N : ℝ) ^ 3 *
        (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
          ‖sourceS1KernelThird N t₁ t₂ t₃ m‖) := by
  unfold sourceIm
  rw [norm_mul]
  simp only [Complex.norm_natCast, norm_pow, Int.cast_zero, zero_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        ‖sourceHhat (t₁ - t₂) ((m : ℝ) * N) *
          sourceHhat (t₂ - t₃) 0 * sourceHhat (t₃ - t₁) 0‖ :=
      norm_sum3_le W _
    _ = _ := by
      rw [finset_sum3_cycle W (fun a b c =>
        ‖sourceHhat (a - b) ((m : ℝ) * N) *
          sourceHhat (b - c) 0 * sourceHhat (c - a) 0‖)]
      rw [finset_sum3_cycle W (fun a b c =>
        ‖sourceHhat (b - c) ((m : ℝ) * N) *
          sourceHhat (c - a) 0 * sourceHhat (a - b) 0‖)]
      simp only [sourceS1KernelThird, norm_mul]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      ring

private theorem norm_sourceIm_second_le
    (N : ℕ) (W : Finset ℝ) (m : ℤ) :
    ‖sourceIm N W 0 m 0‖ ≤
      (N : ℝ) ^ 3 *
        (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
          ‖sourceS1KernelThird N t₁ t₂ t₃ m‖) := by
  unfold sourceIm
  rw [norm_mul]
  simp only [Complex.norm_natCast, norm_pow, Int.cast_zero, zero_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        ‖sourceHhat (t₁ - t₂) 0 *
          sourceHhat (t₂ - t₃) ((m : ℝ) * N) * sourceHhat (t₃ - t₁) 0‖ :=
      norm_sum3_le W _
    _ = _ := by
      rw [finset_sum3_cycle W (fun a b c =>
        ‖sourceHhat (a - b) 0 *
          sourceHhat (b - c) ((m : ℝ) * N) * sourceHhat (c - a) 0‖)]
      simp only [sourceS1KernelThird, norm_mul]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      ring

/-- The three coordinate axes partition the exact one-nonzero sector. -/
theorem sourceS1_eq_axis_tsums {N : ℕ} (hN : 0 < N) (W : Finset ℝ) :
    sourceS1 N W =
      (∑' m : ℤ, if m ≠ 0 then sourceIm N W m 0 0 else 0) +
      (∑' m : ℤ, if m ≠ 0 then sourceIm N W 0 m 0 else 0) +
      (∑' m : ℤ, if m ≠ 0 then sourceIm N W 0 0 m else 0) := by
  classical
  let F₁ : Frequency → ℂ := fun p =>
    if p.1.1 ≠ 0 ∧ p.1.2 = 0 ∧ p.2 = 0 then frequencyTerm N W p else 0
  let F₂ : Frequency → ℂ := fun p =>
    if p.1.1 = 0 ∧ p.1.2 ≠ 0 ∧ p.2 = 0 then frequencyTerm N W p else 0
  let F₃ : Frequency → ℂ := fun p =>
    if p.1.1 = 0 ∧ p.1.2 = 0 ∧ p.2 ≠ 0 then frequencyTerm N W p else 0
  have hf := summable_frequencyTerm hN W
  have h₁ : Summable F₁ := by
    refine (hf.indicator {p | p.1.1 ≠ 0 ∧ p.1.2 = 0 ∧ p.2 = 0}).congr ?_
    intro p
    simp [F₁, Set.indicator]
  have h₂ : Summable F₂ := by
    refine (hf.indicator {p | p.1.1 = 0 ∧ p.1.2 ≠ 0 ∧ p.2 = 0}).congr ?_
    intro p
    simp [F₂, Set.indicator]
  have h₃ : Summable F₃ := by
    refine (hf.indicator {p | p.1.1 = 0 ∧ p.1.2 = 0 ∧ p.2 ≠ 0}).congr ?_
    intro p
    simp [F₃, Set.indicator]
  have heq : sourceS1 N W = ∑' p, (F₁ p + F₂ p + F₃ p) := by
    apply tsum_congr
    intro p
    by_cases h1 : p.1.1 = 0 <;> by_cases h2 : p.1.2 = 0 <;>
      by_cases h3 : p.2 = 0 <;>
      simp [F₁, F₂, F₃, exactlyOneNonzero, h1, h2, h3]
  rw [heq, (h₁.add h₂).tsum_add h₃, h₁.tsum_add h₂]
  have e₁ : (∑' m : ℤ, F₁ ((m, 0), 0)) = ∑' p, F₁ p := by
    apply Function.Injective.tsum_eq (by intro a b h; simpa using h)
    rintro ⟨⟨a, b⟩, c⟩ hp
    simp only [Function.mem_support, F₁] at hp
    by_cases h : a ≠ 0 ∧ b = 0 ∧ c = 0
    · exact ⟨a, by simp [h.2.1, h.2.2]⟩
    · simp [h] at hp
  have e₂ : (∑' m : ℤ, F₂ ((0, m), 0)) = ∑' p, F₂ p := by
    apply Function.Injective.tsum_eq (by intro a b h; simpa using h)
    rintro ⟨⟨a, b⟩, c⟩ hp
    simp only [Function.mem_support, F₂] at hp
    by_cases h : a = 0 ∧ b ≠ 0 ∧ c = 0
    · exact ⟨b, by simp [h.1, h.2.2]⟩
    · simp [h] at hp
  have e₃ : (∑' m : ℤ, F₃ ((0, 0), m)) = ∑' p, F₃ p := by
    apply Function.Injective.tsum_eq (by intro a b h; simpa using h)
    rintro ⟨⟨a, b⟩, c⟩ hp
    simp only [Function.mem_support, F₃] at hp
    by_cases h : a = 0 ∧ b = 0 ∧ c ≠ 0
    · exact ⟨c, by simp [h.1, h.2.1]⟩
    · simp [h] at hp
  rw [← e₁, ← e₂, ← e₃]
  simp [F₁, F₂, F₃, frequencyTerm]

private theorem tsum_thirdMassSequence {N : ℕ} (hN : 0 < N) (W : Finset ℝ) :
    (∑' m, thirdMassSequence N W m) = sourceS1ThirdTotalMass N W := by
  have hp (a b c : ℝ) : Summable fun m : ℤ =>
      if m ≠ 0 then ‖sourceS1KernelThird N a b c m‖ else 0 := by
    have hfar := summable_sourceS1KernelThird_far
      (t₁ := a) (t₂ := b) (t₃ := c) (T := |c - a|)
      (B := (1 : ℝ)) hN (abs_nonneg _) (by norm_num) le_rfl
    convert hfar using 1
    funext m
    by_cases hm : m = 0
    · simp [hm]
    · simp [hm, one_le_abs_intCast hm]
  let f := fun a b c (m : ℤ) =>
    if m ≠ 0 then ‖sourceS1KernelThird N a b c m‖ else 0
  have h₃ (a b : ℝ) : Summable fun m => ∑ c ∈ W, f a b c m :=
    summable_finset_sum_real W _ (fun c _ => hp a b c)
  have h₂ (a : ℝ) : Summable fun m => ∑ b ∈ W, ∑ c ∈ W, f a b c m :=
    summable_finset_sum_real W _ (fun b _ => h₃ a b)
  have heq : thirdMassSequence N W = fun m =>
      ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, f a b c m := by
    funext m
    by_cases hm : m = 0 <;> simp [thirdMassSequence, f, hm]
  rw [heq, Summable.tsum_finsetSum (fun a _ => h₂ a)]
  unfold sourceS1ThirdTotalMass
  apply Finset.sum_congr rfl
  intro a ha
  rw [Summable.tsum_finsetSum (fun b _ => h₃ a b)]
  apply Finset.sum_congr rfl
  intro b hb
  exact Summable.tsum_finsetSum (fun c _ => hp a b c)


/-- Exact bridge from the complex equation-(5.5) `S₁` to the positive mass
estimated in Proposition 5.1. -/
theorem norm_sourceS1_le_sourceS1TotalContribution
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) :
    ‖sourceS1 N W‖ ≤ sourceS1TotalContribution N W := by
  have hmass := (summable_thirdMassSequence hN W).mul_left ((N : ℝ) ^ 3)
  have haxis (f : ℤ → ℂ)
      (hf : ∀ m, ‖f m‖ ≤ (N : ℝ) ^ 3 * thirdMassSequence N W m) :
      ‖∑' m, f m‖ ≤ (N : ℝ) ^ 3 * sourceS1ThirdTotalMass N W := by
    have hs : Summable fun m => ‖f m‖ :=
      Summable.of_nonneg_of_le (fun m => norm_nonneg _) hf hmass
    calc
      _ ≤ ∑' m, ‖f m‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' m, (N : ℝ) ^ 3 * thirdMassSequence N W m :=
        hs.tsum_le_tsum hf hmass
      _ = _ := by rw [tsum_mul_left, tsum_thirdMassSequence hN W]
  have h₁ := haxis (fun m => if m ≠ 0 then sourceIm N W m 0 0 else 0) (by
    intro m
    by_cases hm : m = 0
    · simp [hm, thirdMassSequence]
    · simpa [hm, thirdMassSequence] using norm_sourceIm_first_le N W m)
  have h₂ := haxis (fun m => if m ≠ 0 then sourceIm N W 0 m 0 else 0) (by
    intro m
    by_cases hm : m = 0
    · simp [hm, thirdMassSequence]
    · simpa [hm, thirdMassSequence] using norm_sourceIm_second_le N W m)
  have h₃ := haxis (fun m => if m ≠ 0 then sourceIm N W 0 0 m else 0) (by
    intro m
    by_cases hm : m = 0
    · simp [hm, thirdMassSequence]
    · simpa [hm, thirdMassSequence] using norm_sourceIm_third_le N W m)
  rw [sourceS1_eq_axis_tsums hN W]
  calc
    _ ≤ _ := (norm_add_le _ _).trans
      (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add h₁ h₂) h₃
    _ = sourceS1TotalContribution N W := by unfold sourceS1TotalContribution; ring

end
end GuthMaynardS1MassBridge

#print axioms GuthMaynardS1MassBridge.norm_sourceS1_le_sourceS1TotalContribution
