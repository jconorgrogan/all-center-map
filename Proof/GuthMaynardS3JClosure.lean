import GuthMaynardJIterationCanonicalSupremum
import GuthMaynardLemma92ProfileRegularity
import GuthMaynardSourceDyadicRanges

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

private theorem finite_affine_sum_le_of_subsets
    (A A' B B' C C' : Finset ℤ) (f : ℝ → ℝ) (u : ℝ)
    (hf0 : ∀ x, 0 ≤ f x)
    (hA : A ⊆ A') (hB : B ⊆ B') (hC : C ⊆ C') :
    sourceFiniteAffineSum A B C f u ≤ sourceFiniteAffineSum A' B' C' f u := by
  unfold sourceFiniteAffineSum
  calc
    (∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C,
        f (((a : ℝ) * u + (c : ℝ)) / (b : ℝ))) ≤
      ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C',
        f (((a : ℝ) * u + (c : ℝ)) / (b : ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact Finset.sum_le_sum_of_subset_of_nonneg hC
        (fun c hc hnc => hf0 _)
    _ ≤ ∑ a ∈ A, ∑ b ∈ B', ∑ c ∈ C',
        f (((a : ℝ) * u + (c : ℝ)) / (b : ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.sum_le_sum_of_subset_of_nonneg hB
        (fun b hb hnb => Finset.sum_nonneg (fun c hc => hf0 _))
    _ ≤ ∑ a ∈ A', ∑ b ∈ B', ∑ c ∈ C',
        f (((a : ℝ) * u + (c : ℝ)) / (b : ℝ)) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hA
        (fun a ha hna => Finset.sum_nonneg (fun b hb =>
          Finset.sum_nonneg (fun c hc => hf0 _)))

private theorem finite_affine_energy_le_of_subsets
    (A A' B B' C C' : Finset ℤ) (f : ℝ → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hfCont : Continuous f)
    (hf2 : Integrable (fun x : ℝ => f x ^ 2))
    (hA : A ⊆ A') (hB : B ⊆ B') (hC : C ⊆ C')
    (hnA : ∀ m ∈ A, m ≠ 0) (hnB : ∀ m ∈ B, m ≠ 0)
    (hnA' : ∀ m ∈ A', m ≠ 0) (hnB' : ∀ m ∈ B', m ≠ 0) :
    sourceFiniteAffineEnergy A B C f ≤
      sourceFiniteAffineEnergy A' B' C' f := by
  have hsmall0 : ∀ u, 0 ≤ sourceFiniteAffineSum A B C f u := by
    intro u
    unfold sourceFiniteAffineSum
    apply Finset.sum_nonneg
    intro a ha
    apply Finset.sum_nonneg
    intro b hb
    apply Finset.sum_nonneg
    intro c hc
    exact hf0 _
  have hpoint : ∀ u, sourceFiniteAffineSum A B C f u ^ 2 ≤
      sourceFiniteAffineSum A' B' C' f u ^ 2 := by
    intro u
    have hbig : 0 ≤ sourceFiniteAffineSum A' B' C' f u := by
      unfold sourceFiniteAffineSum
      apply Finset.sum_nonneg
      intro a ha
      apply Finset.sum_nonneg
      intro b hb
      apply Finset.sum_nonneg
      intro c hc
      exact hf0 _
    exact pow_le_pow_left₀ (hsmall0 u)
      (finite_affine_sum_le_of_subsets A A' B B' C C' f u hf0 hA hB hC) 2
  have hleft := integrable_sq_sourceFiniteAffineSum A B C f hfCont hf2 hnA hnB
  have hright := integrable_sq_sourceFiniteAffineSum A' B' C' f hfCont hf2 hnA' hnB'
  apply integral_mono hleft hright
  exact fun u => hpoint u

private theorem lemma92_jrange_subset_centered16
    {M : ℕ} (hM : 0 < M) {T F Tdelta : ℝ}
    (hT : 0 < T) (hF0 : 0 ≤ F) (hF2 : F ≤ 2) (hdelta : Tdelta ≤ T) :
    sourceLemma92JRange M T F (2 * Tdelta) ⊆ sourceCenteredRange (16 * M) := by
  intro j hj
  rw [sourceLemma92JRange] at hj
  unfold sourceIntegerWindow at hj
  rw [Finset.mem_Icc] at hj
  rw [mem_sourceCenteredRange_iff]
  let R : ℝ := (2 * (M : ℝ)) * (F + (2 * Tdelta) / T + F)
  have hR : R ≤ 12 * (M : ℝ) := by
    dsimp only [R]
    have hdiv : (2 * Tdelta) / T ≤ 2 := by
      apply (div_le_iff₀ hT).2
      nlinarith
    nlinarith
  have hNreal : R ≤ ((16 * M : ℕ) : ℝ) := by
    have hMnonneg : (0 : ℝ) ≤ (M : ℝ) := by positivity
    have h16 : ((16 * M : ℕ) : ℝ) = 16 * (M : ℝ) := by norm_num
    rw [h16]
    nlinarith [hR]
  have hjlow : (⌊-R⌋ : ℤ) ≤ j := by simpa [R] using hj.1
  have hjhigh : j ≤ (⌈R⌉ : ℤ) := by simpa [R] using hj.2
  have hfloor : ((-(16 * M : ℕ) : ℤ)) ≤ (⌊-R⌋ : ℤ) := by
    apply Int.le_floor.mpr
    have : (-(16 * M : ℕ) : ℝ) ≤ -R := by
      have h16 : ((16 * M : ℕ) : ℝ) = 16 * (M : ℝ) := by norm_num
      rw [h16]
      nlinarith [hR]
    exact_mod_cast this
  have hceil : (⌈R⌉ : ℤ) ≤ ((16 * M : ℕ) : ℤ) := by
    apply Int.ceil_le.mpr
    exact_mod_cast hNreal
  exact ⟨hfloor.trans hjlow, hjhigh.trans hceil⟩

theorem sourceAffineJ_le_full_centered_energy
    {M : ℕ} {T S F Fprime Tdelta : ℝ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S Fprime f)
    (hM : 0 < M) (hT : 0 < T) (hF0 : 0 ≤ F) (hF2 : F ≤ 2)
    (hdelta : Tdelta ≤ T) :
    sourceAffineJ
        (sourceAffineConfigs (sourcePositiveDyadicRange M)
          (sourceLemma92JRange M T F (2 * Tdelta))) f ≤
      sourceFiniteAffineEnergy (sourcePositiveDyadicRange M)
        (sourcePositiveDyadicRange M) (sourceCenteredRange (16 * M)) f := by
  apply sourceAffineJ_le_of_forall_config
  intro cfg hcfg
  rw [mem_sourceAffineConfigs_iff] at hcfg
  apply finite_affine_energy_le_of_subsets
    cfg.1 (sourcePositiveDyadicRange M)
    cfg.2.1 (sourcePositiveDyadicRange M)
    cfg.2.2 (sourceCenteredRange (16 * M)) f hf.nonneg hf.continuous hf.squareIntegrable
  · exact hcfg.1
  · exact hcfg.2.1
  · exact hcfg.2.2.trans (lemma92_jrange_subset_centered16 hM hT hF0 hF2 hdelta)
  · intro m hm
    exact sourcePositiveDyadicRange_ne_zero hM (hcfg.1 hm)
  · intro m hm
    exact sourcePositiveDyadicRange_ne_zero hM (hcfg.2.1 hm)
  · intro m hm
    exact sourcePositiveDyadicRange_ne_zero hM hm
  · intro m hm
    exact sourcePositiveDyadicRange_ne_zero hM hm

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.sourceAffineJ_le_full_centered_energy
