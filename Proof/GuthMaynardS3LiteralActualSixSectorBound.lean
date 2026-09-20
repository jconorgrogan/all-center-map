import GuthMaynardS3LiteralBalancedSectorGeometry
import GuthMaynardS3SymmetryGenerators

namespace GuthMaynardS3LiteralActualSixSectorBound

open scoped BigOperators
open GuthMaynardS3LiteralBalancedSectorGeometry
open GuthMaynardS3LiteralTruncation
open GuthMaynardEquation55Infinite
open GuthMaynardEquation55Split
open GuthMaynardS3SymmetryGenerators

noncomputable section

abbrev B (Mcut i k d : ℕ) : Finset Frequency :=
  orderedBalancedBlock Mcut i k d

abbrev f (N : ℕ) (W : Finset ℝ) (p : Frequency) : ℝ :=
  ‖frequencyTerm N W p‖

def freqNeg (p : Frequency) : Frequency := ((-p.1.1, -p.1.2), -p.2)

theorem freqNeg_involutive (p : Frequency) : freqNeg (freqNeg p) = p := by
  rcases p with ⟨⟨a, b⟩, c⟩
  simp [freqNeg]

theorem prefix_mem_freqNeg {Mcut : ℕ} {p : Frequency}
    (hp : p ∈ prefixFrequencyCube Mcut) :
    freqNeg p ∈ prefixFrequencyCube Mcut := by
  obtain ⟨h12, h3⟩ := Finset.mem_product.mp hp
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp h12
  have h1' : -p.1.1 ∈ GuthMaynardS3LiteralTruncation.nonzeroPrefix Mcut := by
    rcases Finset.mem_union.mp h1 with h | h
    · obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp h
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      exact ⟨n, hn, by simp [heq]⟩
    · obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp h
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_image.mpr
      exact ⟨n, hn, by simpa only [neg_neg] using congrArg Neg.neg heq⟩
  have h2' : -p.1.2 ∈ GuthMaynardS3LiteralTruncation.nonzeroPrefix Mcut := by
    rcases Finset.mem_union.mp h2 with h | h
    · obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp h
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      exact ⟨n, hn, by simp [heq]⟩
    · obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp h
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_image.mpr
      exact ⟨n, hn, by simpa only [neg_neg] using congrArg Neg.neg heq⟩
  have h3' : -p.2 ∈ GuthMaynardS3LiteralTruncation.nonzeroPrefix Mcut := by
    rcases Finset.mem_union.mp h3 with h | h
    · obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp h
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      exact ⟨n, hn, by simp [heq]⟩
    · obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp h
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_image.mpr
      exact ⟨n, hn, by simpa only [neg_neg] using congrArg Neg.neg heq⟩
  exact Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr ⟨h1', h2'⟩, h3'⟩

theorem orderedBalancedBlock_freqNeg_mem {Mcut i k d : ℕ} {p : Frequency}
    (hp : p ∈ B Mcut i k d) : freqNeg p ∈ B Mcut i k d := by
  obtain ⟨hbase, hpred⟩ := Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨prefix_mem_freqNeg hbase, ?_⟩
  simpa [freqNeg, abs_neg] using hpred

theorem orderedBalancedBlock_image_freqNeg (Mcut i k d : ℕ) :
    (B Mcut i k d).image freqNeg = B Mcut i k d := by
  apply Finset.ext
  intro p
  constructor
  · intro hp
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hp
    rw [← heq]
    exact orderedBalancedBlock_freqNeg_mem hq
  · intro hp
    apply Finset.mem_image.mpr
    exact ⟨freqNeg p, orderedBalancedBlock_freqNeg_mem hp,
      freqNeg_involutive p⟩

private theorem freq132_injective : Function.Injective freq132 := by
  intro p q h
  rcases p with ⟨⟨a, b⟩, c⟩
  rcases q with ⟨⟨d, e⟩, f⟩
  simp [freq132] at h ⊢
  exact ⟨⟨h.1.1, h.2⟩, h.1.2⟩

private theorem freq213_injective : Function.Injective freq213 := by
  intro p q h
  rcases p with ⟨⟨a, b⟩, c⟩
  rcases q with ⟨⟨d, e⟩, f⟩
  simp [freq213] at h ⊢
  exact ⟨⟨h.1.2, h.1.1⟩, h.2⟩

private theorem freq231_injective : Function.Injective freq231 := by
  intro p q h
  rcases p with ⟨⟨a, b⟩, c⟩
  rcases q with ⟨⟨d, e⟩, f⟩
  simp [freq231] at h ⊢
  exact ⟨⟨h.2, h.1.1⟩, h.1.2⟩

private theorem freq312_injective : Function.Injective freq312 := by
  intro p q h
  rcases p with ⟨⟨a, b⟩, c⟩
  rcases q with ⟨⟨d, e⟩, f⟩
  simp [freq312] at h ⊢
  exact ⟨⟨h.1.2, h.2⟩, h.1.1⟩

private theorem freq321_injective : Function.Injective freq321 := by
  intro p q h
  rcases p with ⟨⟨a, b⟩, c⟩
  rcases q with ⟨⟨d, e⟩, f⟩
  simp [freq321] at h ⊢
  exact ⟨⟨h.2, h.1.2⟩, h.1.1⟩

private theorem sum_image_neg_eq_sum (N : ℕ) (W : Finset ℝ)
    (Mcut i k d : ℕ) :
    (∑ p ∈ (B Mcut i k d).image freqNeg, f N W p) =
      ∑ p ∈ B Mcut i k d, f N W p := by
  rw [orderedBalancedBlock_image_freqNeg]

private theorem norm_freq132_neg (N : ℕ) (W : Finset ℝ) (p : Frequency) :
    f N W (freq132 p) = f N W (freqNeg p) := by
  rcases p with ⟨⟨a, b⟩, c⟩
  change ‖sourceIm N W a c b‖ = ‖sourceIm N W (-a) (-b) (-c)‖
  calc
    ‖sourceIm N W a c b‖ = ‖sourceIm N W (-c) (-a) (-b)‖ :=
      norm_sourceIm_odd_neg_132 N W a b c
    _ = ‖sourceIm N W (-a) (-b) (-c)‖ := by
      exact congrArg norm (sourceIm_cycle N W (-c) (-a) (-b)).symm

private theorem norm_freq213_neg (N : ℕ) (W : Finset ℝ) (p : Frequency) :
    f N W (freq213 p) = f N W (freqNeg p) := by
  rcases p with ⟨⟨a, b⟩, c⟩
  exact norm_sourceIm_swap_global_neg N W a b c

private theorem norm_freq231 (N : ℕ) (W : Finset ℝ) (p : Frequency) :
    f N W (freq231 p) = f N W p := by
  rcases p with ⟨⟨a, b⟩, c⟩
  exact congrArg norm (sourceIm_cycle N W a b c)

private theorem norm_freq312 (N : ℕ) (W : Finset ℝ) (p : Frequency) :
    f N W (freq312 p) = f N W p := by
  rcases p with ⟨⟨a, b⟩, c⟩
  exact congrArg norm (sourceIm_cycle N W c a b).symm

private theorem norm_freq321_neg (N : ℕ) (W : Finset ℝ) (p : Frequency) :
    f N W (freq321 p) = f N W (freqNeg p) := by
  rcases p with ⟨⟨a, b⟩, c⟩
  calc
    ‖sourceIm N W c b a‖ = ‖sourceIm N W (-b) (-c) (-a)‖ :=
      norm_sourceIm_odd_neg_321 N W a b c
    _ = ‖sourceIm N W (-a) (-b) (-c)‖ := by
      calc
        _ = ‖sourceIm N W (-c) (-a) (-b)‖ :=
          congrArg norm (sourceIm_cycle N W (-b) (-c) (-a)).symm
        _ = ‖sourceIm N W (-a) (-b) (-c)‖ :=
          congrArg norm (sourceIm_cycle N W (-c) (-a) (-b)).symm


private theorem sum_freqNeg_eq_sum (N : ℕ) (W : Finset ℝ)
    (Mcut i k d : ℕ) :
    (∑ p ∈ B Mcut i k d, f N W (freqNeg p)) =
      ∑ p ∈ B Mcut i k d, f N W p := by
  calc
    _ = ∑ p ∈ (B Mcut i k d).image freqNeg, f N W p := by
      rw [Finset.sum_image]
      · exact Set.injOn_of_injective (by
          intro p q h
          rw [← freqNeg_involutive p, ← freqNeg_involutive q, h])
    _ = _ := sum_image_neg_eq_sum N W Mcut i k d

private theorem sum_freq132_eq_sum (N : ℕ) (W : Finset ℝ)
    (Mcut i k d : ℕ) :
    (∑ p ∈ (B Mcut i k d).image freq132, f N W p) =
      ∑ p ∈ B Mcut i k d, f N W p := by
  rw [Finset.sum_image]
  · calc
      _ = ∑ p ∈ B Mcut i k d, f N W (freqNeg p) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact norm_freq132_neg N W p
      _ = _ := sum_freqNeg_eq_sum N W Mcut i k d
  · exact Set.injOn_of_injective (by
      intro p q h
      exact freq132_injective h)

private theorem sum_freq213_eq_sum (N : ℕ) (W : Finset ℝ)
    (Mcut i k d : ℕ) :
    (∑ p ∈ (B Mcut i k d).image freq213, f N W p) =
      ∑ p ∈ B Mcut i k d, f N W p := by
  rw [Finset.sum_image]
  · calc
      _ = ∑ p ∈ B Mcut i k d, f N W (freqNeg p) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact norm_freq213_neg N W p
      _ = _ := sum_freqNeg_eq_sum N W Mcut i k d
  · exact Set.injOn_of_injective (by
      intro p q h
      exact freq213_injective h)

private theorem sum_freq231_eq_sum (N : ℕ) (W : Finset ℝ)
    (Mcut i k d : ℕ) :
    (∑ p ∈ (B Mcut i k d).image freq231, f N W p) =
      ∑ p ∈ B Mcut i k d, f N W p := by
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro p hp
    exact norm_freq231 N W p
  · exact Set.injOn_of_injective (by
      intro p q h
      exact freq231_injective h)

private theorem sum_freq312_eq_sum (N : ℕ) (W : Finset ℝ)
    (Mcut i k d : ℕ) :
    (∑ p ∈ (B Mcut i k d).image freq312, f N W p) =
      ∑ p ∈ B Mcut i k d, f N W p := by
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro p hp
    exact norm_freq312 N W p
  · exact Set.injOn_of_injective (by
      intro p q h
      exact freq312_injective h)

private theorem sum_freq321_eq_sum (N : ℕ) (W : Finset ℝ)
    (Mcut i k d : ℕ) :
    (∑ p ∈ (B Mcut i k d).image freq321, f N W p) =
      ∑ p ∈ B Mcut i k d, f N W p := by
  rw [Finset.sum_image]
  · calc
      _ = ∑ p ∈ B Mcut i k d, f N W (freqNeg p) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact norm_freq321_neg N W p
      _ = _ := sum_freqNeg_eq_sum N W Mcut i k d
  · exact Set.injOn_of_injective (by
      intro p q h
      exact freq321_injective h)

theorem sum_norm_sixSectorUnion_actual
    (N : ℕ) (W : Finset ℝ) (Mcut i k d : ℕ) :
    (∑ p ∈ sixSectorUnion Mcut i k d, f N W p) ≤
      6 * (∑ p ∈ B Mcut i k d, f N W p) := by
  let C := B Mcut i k d
  let g := f N W
  have hg : ∀ p, 0 ≤ g p := fun p => norm_nonneg _
  have hunion {s t : Finset Frequency} :
      (∑ p ∈ s ∪ t, g p) ≤
        (∑ p ∈ s, g p) + (∑ p ∈ t, g p) := by
    rw [show s ∪ t = s ∪ (t \ s) by ext p; simp]
    rw [Finset.sum_union (Finset.disjoint_sdiff)]
    have hdiff : (∑ p ∈ t \ s, g p) ≤ ∑ p ∈ t, g p :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        (fun p _ _ => hg p)
    exact add_le_add_right hdiff _
  have h1 :
      (∑ p ∈ C.image freq132 ∪
          (C.image freq213 ∪ (C.image freq231 ∪
            (C.image freq312 ∪ C.image freq321))), g p) ≤
        (∑ p ∈ C.image freq132, g p) +
          ((∑ p ∈ C.image freq213, g p) +
            ((∑ p ∈ C.image freq231, g p) +
              ((∑ p ∈ C.image freq312, g p) + ∑ p ∈ C.image freq321, g p))) := by
    calc
      _ ≤ (∑ p ∈ C.image freq132, g p) +
          (∑ p ∈ C.image freq213 ∪
            (C.image freq231 ∪ (C.image freq312 ∪ C.image freq321)), g p) :=
        hunion
      _ ≤ _ := by
        have h23 :
            (∑ p ∈ C.image freq213 ∪
                (C.image freq231 ∪ (C.image freq312 ∪ C.image freq321)), g p) ≤
              (∑ p ∈ C.image freq213, g p) +
                ((∑ p ∈ C.image freq231, g p) +
                  ((∑ p ∈ C.image freq312, g p) + ∑ p ∈ C.image freq321, g p)) := by
          calc
            _ ≤ (∑ p ∈ C.image freq213, g p) +
                (∑ p ∈ C.image freq231 ∪ (C.image freq312 ∪ C.image freq321), g p) :=
              hunion
            _ ≤ _ := by
              have h34 :
                  (∑ p ∈ C.image freq231 ∪ (C.image freq312 ∪ C.image freq321), g p) ≤
                    (∑ p ∈ C.image freq231, g p) +
                      ((∑ p ∈ C.image freq312, g p) + ∑ p ∈ C.image freq321, g p) := by
                calc
                  _ ≤ (∑ p ∈ C.image freq231, g p) +
                      (∑ p ∈ C.image freq312 ∪ C.image freq321, g p) := hunion
                  _ ≤ _ := add_le_add_right (hunion (s := C.image freq312)
                    (t := C.image freq321)) _
              exact add_le_add_right h34 _
        exact add_le_add_right h23 _
  calc
    (∑ p ∈ sixSectorUnion Mcut i k d, g p) ≤
        (∑ p ∈ C, g p) +
          (∑ p ∈ C.image freq132 ∪
            (C.image freq213 ∪ (C.image freq231 ∪
              (C.image freq312 ∪ C.image freq321))), g p) := hunion
    _ ≤ (∑ p ∈ C, g p) +
          ((∑ p ∈ C.image freq132, g p) +
            ((∑ p ∈ C.image freq213, g p) +
              ((∑ p ∈ C.image freq231, g p) +
                ((∑ p ∈ C.image freq312, g p) + ∑ p ∈ C.image freq321, g p)))) :=
      add_le_add_right h1 _
    _ = 6 * (∑ p ∈ C, g p) := by
      rw [sum_freq132_eq_sum N W Mcut i k d,
        sum_freq213_eq_sum N W Mcut i k d,
        sum_freq231_eq_sum N W Mcut i k d,
        sum_freq312_eq_sum N W Mcut i k d,
        sum_freq321_eq_sum N W Mcut i k d]
      ring

end
end GuthMaynardS3LiteralActualSixSectorBound
