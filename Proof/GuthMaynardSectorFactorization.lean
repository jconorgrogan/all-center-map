import GuthMaynardS1MassBridge

/-! # Literal factorization of the two- and three-frequency sectors
Absolute convergence permits the frequency sums to be performed before the
finite ordinate sums. The nonzero Fourier sum remains complex, preserving
its cancellation for the reflection estimates of Section 6.
-/

namespace GuthMaynardSectorFactorization

open scoped BigOperators
open GuthMaynardEquation55Split GuthMaynardEquation55Infinite
open GuthMaynardSectionFourPoisson GuthMaynardS1Source GuthMaynardS1MassBridge

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- The full nonzero Fourier sum, with both signs and no frequency cutoff. -/
def sourceNonzeroFourier (N : ℕ) (t : ℝ) : ℂ :=
  ∑' m : ℤ, if m ≠ 0 then sourceHhat t ((m : ℝ) * N) else 0

private def maskedHhat (N : ℕ) (P : ℤ → Prop) [DecidablePred P] (t : ℝ) (m : ℤ) : ℂ :=
  if P m then sourceHhat t ((m : ℝ) * N) else 0

private theorem summable_maskedHhat {N : ℕ} (hN : 0 < N)
    (P : ℤ → Prop) [DecidablePred P] (t : ℝ) : Summable (maskedHhat N P t) := by
  classical
  refine ((summable_norm_sourceHhat_scaled t hN).of_norm.indicator {m | P m}).congr ?_
  intro m
  simp [maskedHhat, Set.indicator]

private theorem summable_finset_sum {ι α : Type*} (s : Finset ι)
    (f : ι → α → ℂ) (hf : ∀ i ∈ s, Summable (f i)) :
    Summable fun a => ∑ i ∈ s, f i a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).add
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- A rectangular frequency mask factors into three one-dimensional tsums. -/
theorem tsum_masked_frequencyTerm
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) (P Q R : ℤ → Prop)
    [DecidablePred P] [DecidablePred Q] [DecidablePred R] :
    (∑' p : Frequency,
      if P p.1.1 ∧ Q p.1.2 ∧ R p.2 then frequencyTerm N W p else 0) =
      (N : ℂ) ^ 3 *
        ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W,
          (∑' m, maskedHhat N P (a - b) m) *
            (∑' m, maskedHhat N Q (b - c) m) *
            (∑' m, maskedHhat N R (c - a) m) := by
  classical
  let K := fun a b c (p : Frequency) =>
    (N : ℂ) ^ 3 * (maskedHhat N P (a - b) p.1.1 *
      maskedHhat N Q (b - c) p.1.2 * maskedHhat N R (c - a) p.2)
  have hK (a b c : ℝ) : Summable (K a b c) :=
    (((summable_maskedHhat hN P (a - b)).norm.mul_norm
      (summable_maskedHhat hN Q (b - c)).norm).mul_norm
      (summable_maskedHhat hN R (c - a)).norm).of_norm.mul_left _
  have h₃ (a b : ℝ) : Summable fun p => ∑ c ∈ W, K a b c p :=
    summable_finset_sum W _ (fun c _ => hK a b c)
  have h₂ (a : ℝ) : Summable fun p => ∑ b ∈ W, ∑ c ∈ W, K a b c p :=
    summable_finset_sum W _ (fun b _ => h₃ a b)
  have hpoint (p : Frequency) :
      (if P p.1.1 ∧ Q p.1.2 ∧ R p.2 then frequencyTerm N W p else 0) =
        ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, K a b c p := by
    by_cases hP : P p.1.1 <;> by_cases hQ : Q p.1.2 <;> by_cases hR : R p.2 <;>
      simp [hP, hQ, hR, K, maskedHhat, frequencyTerm, sourceIm,
        Finset.mul_sum]
  simp_rw [hpoint]
  rw [Summable.tsum_finsetSum (fun a _ => h₂ a), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Summable.tsum_finsetSum (fun b _ => h₃ a b), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Summable.tsum_finsetSum (fun c _ => hK a b c), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  unfold K
  rw [tsum_mul_left]
  congr 1
  have hP := (summable_maskedHhat hN P (a - b)).norm
  have hQ := (summable_maskedHhat hN Q (b - c)).norm
  have hR := (summable_maskedHhat hN R (c - a)).norm
  rw [tsum_mul_tsum_of_summable_norm hP hQ]
  exact (tsum_mul_tsum_of_summable_norm (hP.mul_norm hQ) hR).symm

/-- Exact complex three-cycle represented by the all-nonzero sector. -/
theorem sourceS3_eq_nonzeroFourier_cube
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) :
    sourceS3 N W = (N : ℂ) ^ 3 *
      ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W,
        sourceNonzeroFourier N (a - b) * sourceNonzeroFourier N (b - c) *
          sourceNonzeroFourier N (c - a) := by
  simpa [sourceS3, exactlyThreeNonzero, sourceNonzeroFourier, maskedHhat] using
    tsum_masked_frequencyTerm hN W (· ≠ 0) (· ≠ 0) (· ≠ 0)

/-- Exact three-plane factorization of the two-nonzero sector. -/
theorem sourceS2_eq_nonzeroFourier_planes
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) :
    sourceS2 N W = (N : ℂ) ^ 3 *
      (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W,
        sourceHhat (a - b) 0 * sourceNonzeroFourier N (b - c) *
          sourceNonzeroFourier N (c - a)) +
      (N : ℂ) ^ 3 *
      (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W,
        sourceNonzeroFourier N (a - b) * sourceHhat (b - c) 0 *
          sourceNonzeroFourier N (c - a)) +
      (N : ℂ) ^ 3 *
      (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W,
        sourceNonzeroFourier N (a - b) * sourceNonzeroFourier N (b - c) *
          sourceHhat (c - a) 0) := by
  classical
  let F₁ : Frequency → ℂ := fun p =>
    if p.1.1 = 0 ∧ p.1.2 ≠ 0 ∧ p.2 ≠ 0 then frequencyTerm N W p else 0
  let F₂ : Frequency → ℂ := fun p =>
    if p.1.1 ≠ 0 ∧ p.1.2 = 0 ∧ p.2 ≠ 0 then frequencyTerm N W p else 0
  let F₃ : Frequency → ℂ := fun p =>
    if p.1.1 ≠ 0 ∧ p.1.2 ≠ 0 ∧ p.2 = 0 then frequencyTerm N W p else 0
  have hf := summable_frequencyTerm hN W
  have h₁ : Summable F₁ := by
    refine (hf.indicator {p | p.1.1 = 0 ∧ p.1.2 ≠ 0 ∧ p.2 ≠ 0}).congr ?_
    intro p
    simp [F₁, Set.indicator]
  have h₂ : Summable F₂ := by
    refine (hf.indicator {p | p.1.1 ≠ 0 ∧ p.1.2 = 0 ∧ p.2 ≠ 0}).congr ?_
    intro p
    simp [F₂, Set.indicator]
  have h₃ : Summable F₃ := by
    refine (hf.indicator {p | p.1.1 ≠ 0 ∧ p.1.2 ≠ 0 ∧ p.2 = 0}).congr ?_
    intro p
    simp [F₃, Set.indicator]
  have heq : sourceS2 N W = ∑' p, (F₁ p + F₂ p + F₃ p) := by
    apply tsum_congr
    intro p
    by_cases h1 : p.1.1 = 0 <;> by_cases h2 : p.1.2 = 0 <;>
      by_cases h3 : p.2 = 0 <;>
      simp [F₁, F₂, F₃, exactlyTwoNonzero, h1, h2, h3]
  rw [heq, (h₁.add h₂).tsum_add h₃, h₁.tsum_add h₂]
  have e₁ := tsum_masked_frequencyTerm hN W (· = 0) (· ≠ 0) (· ≠ 0)
  have e₂ := tsum_masked_frequencyTerm hN W (· ≠ 0) (· = 0) (· ≠ 0)
  have e₃ := tsum_masked_frequencyTerm hN W (· ≠ 0) (· ≠ 0) (· = 0)
  simp only [maskedHhat, sourceNonzeroFourier, tsum_ite_eq,
    Int.cast_zero, zero_mul] at e₁ e₂ e₃ ⊢
  rw [show (∑' p, F₁ p) = _ from e₁,
    show (∑' p, F₂ p) = _ from e₂,
    show (∑' p, F₃ p) = _ from e₃]

/-- Cyclic relabeling makes the three coordinate planes equal. -/
theorem sourceS2_eq_three_nonzeroFourier_plane
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) :
    sourceS2 N W = 3 * (N : ℂ) ^ 3 *
      ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W,
        sourceHhat (a - b) 0 * sourceNonzeroFourier N (b - c) *
          sourceNonzeroFourier N (c - a) := by
  rw [sourceS2_eq_nonzeroFourier_planes hN W]
  let A := ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W,
    sourceHhat (a - b) 0 * sourceNonzeroFourier N (b - c) *
      sourceNonzeroFourier N (c - a)
  have h₂ : (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W,
      sourceNonzeroFourier N (a - b) * sourceHhat (b - c) 0 *
        sourceNonzeroFourier N (c - a)) = A := by
    rw [finset_sum3_cycle W (fun a b c =>
      sourceNonzeroFourier N (a - b) * sourceHhat (b - c) 0 *
        sourceNonzeroFourier N (c - a))]
    rw [finset_sum3_cycle W (fun a b c =>
      sourceNonzeroFourier N (b - c) * sourceHhat (c - a) 0 *
        sourceNonzeroFourier N (a - b))]
    unfold A
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    ring
  have h₃ : (∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W,
      sourceNonzeroFourier N (a - b) * sourceNonzeroFourier N (b - c) *
        sourceHhat (c - a) 0) = A := by
    rw [finset_sum3_cycle W (fun a b c =>
      sourceNonzeroFourier N (a - b) * sourceNonzeroFourier N (b - c) *
        sourceHhat (c - a) 0)]
    unfold A
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    ring
  rw [h₂, h₃]
  change (N : ℂ) ^ 3 * A + (N : ℂ) ^ 3 * A + (N : ℂ) ^ 3 * A = _
  ring

end
end GuthMaynardSectorFactorization

#print axioms GuthMaynardSectorFactorization.sourceS3_eq_nonzeroFourier_cube
#print axioms GuthMaynardSectorFactorization.sourceS2_eq_nonzeroFourier_planes

#print axioms GuthMaynardSectorFactorization.sourceS2_eq_three_nonzeroFourier_plane
