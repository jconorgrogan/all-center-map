import GuthMaynardS3LiteralBalancedSectorGeometry
import GuthMaynardS3SymmetryGenerators
import GuthMaynardS3LiteralFrequencyGeometry

namespace GuthMaynardS3LiteralUnbalancedPermutationTail

open scoped BigOperators
open GuthMaynardS3LiteralBalancedSectorGeometry
open GuthMaynardS3LiteralTruncation
open GuthMaynardEquation55Infinite
open GuthMaynardEquation55Split
open GuthMaynardS3SymmetryGenerators
open GuthMaynardS3LiteralFrequencyGeometry
open GuthMaynardS3LiteralLocalization
open GuthMaynardS3LiteralRadialDecay

noncomputable section

def balancedCube (Mcut : ℕ) : Finset Frequency :=
  (prefixFrequencyCube Mcut).filter fun p =>
    ∃ i ∈ dyadicExponents Mcut, ∃ k ∈ dyadicExponents Mcut,
      ∃ d ∈ Finset.range 4, p ∈ sixSectorUnion Mcut i k d

private theorem balanced_of_case {Mcut : ℕ} {p : Frequency}
    (hp : p ∈ prefixFrequencyCube Mcut)
    (hcase :
      (|(p.1.1 : ℝ)| ≤ |(p.1.2 : ℝ)| ∧ |(p.1.2 : ℝ)| ≤ |(p.2 : ℝ)| ∧
        |(p.2 : ℝ)| ≤ 5 * |(p.1.2 : ℝ)|) ∨
      (|(p.1.1 : ℝ)| ≤ |(p.2 : ℝ)| ∧ |(p.2 : ℝ)| ≤ |(p.1.2 : ℝ)| ∧
        |(p.1.2 : ℝ)| ≤ 5 * |(p.2 : ℝ)|) ∨
      (|(p.1.2 : ℝ)| ≤ |(p.1.1 : ℝ)| ∧ |(p.1.1 : ℝ)| ≤ |(p.2 : ℝ)| ∧
        |(p.2 : ℝ)| ≤ 5 * |(p.1.1 : ℝ)|) ∨
      (|(p.1.2 : ℝ)| ≤ |(p.2 : ℝ)| ∧ |(p.2 : ℝ)| ≤ |(p.1.1 : ℝ)| ∧
        |(p.1.1 : ℝ)| ≤ 5 * |(p.2 : ℝ)|) ∨
      (|(p.2 : ℝ)| ≤ |(p.1.1 : ℝ)| ∧ |(p.1.1 : ℝ)| ≤ |(p.1.2 : ℝ)| ∧
        |(p.1.2 : ℝ)| ≤ 5 * |(p.1.1 : ℝ)|) ∨
      (|(p.2 : ℝ)| ≤ |(p.1.2 : ℝ)| ∧ |(p.1.2 : ℝ)| ≤ |(p.1.1 : ℝ)| ∧
        |(p.1.1 : ℝ)| ≤ 5 * |(p.1.2 : ℝ)|)) :
    p ∈ balancedCube Mcut := by
  obtain ⟨i, hi, k, hk, d, hd, hs⟩ :=
    mem_sixSectorUnion_of_ordered_case hp hcase
  exact Finset.mem_filter.mpr ⟨hp, ⟨i, hi, k, hk, d, hd, hs⟩⟩

theorem norm_sourceIm_unbalanced_of_not_balanced
    {N Mcut q : ℕ} (hN : 0 < N) (W : Finset ℝ)
    {rho : ℝ} (hrho : 0 < rho) (hslack : rho / (N : ℝ) ≤ 1)
    {p : Frequency} (hp : p ∈ prefixFrequencyCube Mcut)
    (hnot : p ∉ balancedCube Mcut) :
    ‖sourceIm N W p.1.1 p.1.2 p.2‖ ≤
      (9 / 4 : ℝ) * (N : ℝ) ^ 3 * radialDerivativeBudget q *
        (W.card : ℝ) ^ 3 / rho ^ q := by
  rcases p with ⟨⟨a, b⟩, c⟩
  change ((a, b), c) ∈ prefixFrequencyCube Mcut at hp
  obtain ⟨h12, h3⟩ := Finset.mem_product.mp hp
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp h12
  have ha : a ≠ 0 := nonzeroPrefix_ne_zero h1
  have hb : b ≠ 0 := nonzeroPrefix_ne_zero h2
  have hc : c ≠ 0 := nonzeroPrefix_ne_zero h3
  have hapos : (1 : ℝ) ≤ |(a : ℝ)| := by exact_mod_cast Int.one_le_abs ha
  have hbpos : (1 : ℝ) ≤ |(b : ℝ)| := by exact_mod_cast Int.one_le_abs hb
  have hcpos : (1 : ℝ) ≤ |(c : ℝ)| := by exact_mod_cast Int.one_le_abs hc
  rcases le_total |(a : ℝ)| |(b : ℝ)| with hab | hba
  · rcases le_total |(b : ℝ)| |(c : ℝ)| with hbc | hcb
    · by_cases hfive : |(c : ℝ)| ≤ 5 * |(b : ℝ)|
      · exact False.elim (hnot (balanced_of_case (by
          exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨
            h1,
            h2⟩,
            h3⟩) (Or.inl ⟨hab, hbc, hfive⟩)))
      · have hgap : 4 * |(b : ℝ)| + rho / (N : ℝ) < |(c : ℝ)| := by
          nlinarith
        exact GuthMaynardS3LiteralFrequencyGeometry.norm_sourceIm_unbalanced_le_tail hN W a b c hrho q hab hgap
    · rcases le_total |(a : ℝ)| |(c : ℝ)| with hac | hca
      · by_cases hfive : |(b : ℝ)| ≤ 5 * |(c : ℝ)|
        · exfalso
          apply hnot
          apply balanced_of_case hp
          exact Or.inr (Or.inl ⟨hac, hcb, hfive⟩)
        · have hgap : 4 * |(c : ℝ)| + rho / (N : ℝ) < |(b : ℝ)| := by nlinarith
          have ht := GuthMaynardS3LiteralFrequencyGeometry.norm_sourceIm_unbalanced_le_tail hN W (-a) (-c) (-b) hrho q (by simpa using hac) (by simpa [abs_neg] using hgap)
          calc
            ‖sourceIm N W a b c‖ = ‖sourceIm N W c a b‖ :=
              congrArg norm (sourceIm_cycle N W c a b)
            _ = ‖sourceIm N W (-a) (-c) (-b)‖ := by
              simpa only [neg_neg] using (norm_sourceIm_odd_neg_132 N W (-a) (-b) (-c)).symm
            _ ≤ _ := ht
      · by_cases hfive : |(b : ℝ)| ≤ 5 * |(a : ℝ)|
        · exfalso
          apply hnot
          apply balanced_of_case hp
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hca, hab, hfive⟩))))
        · have hgap : 4 * |(a : ℝ)| + rho / (N : ℝ) < |(b : ℝ)| := by nlinarith
          have ht := GuthMaynardS3LiteralFrequencyGeometry.norm_sourceIm_unbalanced_le_tail hN W c a b hrho q hca (by simpa [abs_neg] using hgap)
          calc
            ‖sourceIm N W a b c‖ = ‖sourceIm N W c a b‖ :=
              congrArg norm (sourceIm_cycle N W c a b)
            _ ≤ _ := ht
  · rcases le_total |(a : ℝ)| |(c : ℝ)| with hac | hca
    · by_cases hfive : |(c : ℝ)| ≤ 5 * |(a : ℝ)|
      · exfalso
        apply hnot
        apply balanced_of_case hp
        exact Or.inr (Or.inr (Or.inl ⟨hba, hac, hfive⟩))
      · have hgap : 4 * |(a : ℝ)| + rho / (N : ℝ) < |(c : ℝ)| := by nlinarith
        have ht := GuthMaynardS3LiteralFrequencyGeometry.norm_sourceIm_unbalanced_le_tail hN W (-b) (-a) (-c) hrho q (by simpa using hba) (by simpa [abs_neg] using hgap)
        calc
            ‖sourceIm N W a b c‖ = ‖sourceIm N W (-b) (-a) (-c)‖ :=
          by simpa only [neg_neg] using
            (norm_sourceIm_swap_global_neg N W (-a) (-b) (-c)).symm
          _ ≤ _ := ht
    · rcases le_total |(b : ℝ)| |(c : ℝ)| with hbc | hcb
      · by_cases hfive : |(a : ℝ)| ≤ 5 * |(c : ℝ)|
        · exfalso
          apply hnot
          apply balanced_of_case hp
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hbc, hca, hfive⟩)))
        · have hgap : 4 * |(c : ℝ)| + rho / (N : ℝ) < |(a : ℝ)| := by nlinarith
          have ht := GuthMaynardS3LiteralFrequencyGeometry.norm_sourceIm_unbalanced_le_tail hN W b c a hrho q hbc hgap
          calc
            ‖sourceIm N W a b c‖ = ‖sourceIm N W b c a‖ :=
              (congrArg norm (sourceIm_cycle N W a b c)).symm
            _ ≤ _ := ht
      · by_cases hfive : |(a : ℝ)| ≤ 5 * |(b : ℝ)|
        · exfalso
          apply hnot
          apply balanced_of_case hp
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hcb, hba, hfive⟩))))
        · have hgap : 4 * |(b : ℝ)| + rho / (N : ℝ) < |(a : ℝ)| := by nlinarith
          have ht := GuthMaynardS3LiteralFrequencyGeometry.norm_sourceIm_unbalanced_le_tail hN W (-c) (-b) (-a) hrho q (by simpa using hcb) (by simpa [abs_neg] using hgap)
          calc
            ‖sourceIm N W a b c‖ = ‖sourceIm N W b c a‖ :=
              (congrArg norm (sourceIm_cycle N W a b c)).symm
            _ = ‖sourceIm N W (-c) (-b) (-a)‖ :=
              norm_sourceIm_odd_neg_321 N W a c b
            _ ≤ _ := ht

end
end GuthMaynardS3LiteralUnbalancedPermutationTail
