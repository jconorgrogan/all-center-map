import FordDirichletShells
import FordDirichletPointwise

open scoped BigOperators
open FordDirichletShells
open FordDirichletPointwise

namespace FordDirichletKernelSum
noncomputable section

def normalizedWeight (L : ℕ) (gamma : ℝ) (d : ℤ) : ℝ :=
  ‖dirichletSum L ((d : ℝ) * gamma)‖ / (L : ℝ)

lemma diffSet_card_le_two_mul {K : ℕ} (hK : 2 ≤ K) :
    ((diffSet K).card : ℝ) ≤ 2 * (K : ℝ) := by
  rw [diffSet, Int.card_Icc]
  have hnonneg : 0 ≤ (K : ℤ) - 1 + 1 - (-(K : ℤ) + 1) := by omega
  have hi : (((K : ℤ) - 1 + 1 - (-(K : ℤ) + 1)).toNat : ℤ) =
      (K : ℤ) - 1 + 1 - (-(K : ℤ) + 1) := Int.toNat_of_nonneg hnonneg
  have hir : (((K : ℤ) - 1 + 1 - (-(K : ℤ) + 1)).toNat : ℝ) =
      (((K : ℤ) - 1 + 1 - (-(K : ℤ) + 1)) : ℝ) := by exact_mod_cast hi
  rw [hir]
  push_cast
  norm_num
  nlinarith

lemma normalizedWeight_nonneg {L : ℕ} {gamma : ℝ} (d : ℤ) :
    0 ≤ normalizedWeight L gamma d := by
  unfold normalizedWeight
  positivity

lemma normalizedWeight_le_one {L : ℕ} (hL : 2 ≤ L) {gamma : ℝ} (d : ℤ) :
    normalizedWeight L gamma d ≤ 1 := by
  unfold normalizedWeight
  have hnorm := dirichletSum_norm_le L ((d : ℝ) * gamma)
  have hL0 : 0 < (L : ℝ) := by positivity
  apply (div_le_iff₀ hL0).2
  simpa using hnorm

lemma normalizedWeight_central_le {L : ℕ} {gamma : ℝ}
    (hL : 2 ≤ L) (d : ℤ) :
    roundDist gamma d < (1 : ℝ) / (2 * L) →
      normalizedWeight L gamma d ≤ 1 := by
  intro _
  exact normalizedWeight_le_one hL d

lemma normalizedWeight_decay_le {L : ℕ} {gamma : ℝ}
    (hL : 2 ≤ L) (hgamma : 0 < gamma) (d : ℤ)
    (hrd : 0 < roundDist gamma d) :
    normalizedWeight L gamma d ≤
      1 / ((2 : ℝ) * L * roundDist gamma d) := by
  have hL0 : 0 < (L : ℝ) := by positivity
  have hrd0 : roundDist gamma d ≠ 0 := ne_of_gt hrd
  have hdiff : (d : ℝ) * gamma - (round ((d : ℝ) * gamma) : ℝ) ≠ 0 := by
    intro hz
    apply hrd0
    simp [roundDist, hz]
  have hrec := dirichletSum_norm_le_reciprocal
    (L := L) (x := (d : ℝ) * gamma) hdiff
  unfold normalizedWeight
  calc
    ‖dirichletSum L ((d : ℝ) * gamma)‖ / (L : ℝ) ≤
        (1 / (2 * |(d : ℝ) * gamma - (round ((d : ℝ) * gamma) : ℝ)|)) /
          (L : ℝ) := by
            exact div_le_div_of_nonneg_right hrec (by positivity)
    _ = 1 / ((2 : ℝ) * L * roundDist gamma d) := by
      rw [show roundDist gamma d =
        |(d : ℝ) * gamma - (round ((d : ℝ) * gamma) : ℝ)| by rfl]
      field_simp [hrd0]

lemma normalized_sum_le_shell_bound
    {K L q : ℕ} {gamma : ℝ} (hK : 2 ≤ K) (hL : 2 ≤ L)
    (hq : L < 2 ^ q) (hgamma : 0 < gamma) :
    (∑ d ∈ diffSet K, normalizedWeight L gamma d) ≤
      6 + (4 * (q : ℝ) + 2) * (K : ℝ) / L +
        6 * (K : ℝ) * gamma + (4 * (q : ℝ) + 2) / ((L : ℝ) * gamma) := by
  apply weighted_shell_sum_le_of_decay hK hL hq hgamma
  · intro d hd hcentral
    exact normalizedWeight_central_le hL d hcentral
  · intro d hd hrd
    exact normalizedWeight_decay_le hL hgamma d hrd

lemma normalized_sum_le_card_cap
    {K L : ℕ} {gamma : ℝ} (hK : 2 ≤ K) (hL : 2 ≤ L) :
    (∑ d ∈ diffSet K, normalizedWeight L gamma d) ≤ 2 * (K : ℝ) := by
  have hterm : ∀ d ∈ diffSet K, normalizedWeight L gamma d ≤ 1 := by
    intro d hd
    exact normalizedWeight_le_one hL d
  calc
    (∑ d ∈ diffSet K, normalizedWeight L gamma d) ≤
        ∑ d ∈ diffSet K, (1 : ℝ) := Finset.sum_le_sum hterm
    _ = ((diffSet K).card : ℝ) := by simp
    _ ≤ 2 * (K : ℝ) := diffSet_card_le_two_mul hK

 theorem normalized_sum_le_min
    {K L q : ℕ} {gamma : ℝ} (hK : 2 ≤ K) (hL : 2 ≤ L)
    (hq : L < 2 ^ q) (hgamma : 0 < gamma) :
    (∑ d ∈ diffSet K, normalizedWeight L gamma d) ≤ min (2 * (K : ℝ))
      (6 + (4 * (q : ℝ) + 2) * (K : ℝ) / L +
        6 * (K : ℝ) * gamma + (4 * (q : ℝ) + 2) / ((L : ℝ) * gamma)) := by
  exact le_min (normalized_sum_le_card_cap hK hL)
    (normalized_sum_le_shell_bound hK hL hq hgamma)

 theorem unnormalized_sum_le_mul_min
    {K L q : ℕ} {gamma : ℝ} (hK : 2 ≤ K) (hL : 2 ≤ L)
    (hq : L < 2 ^ q) (hgamma : 0 < gamma) :
    (∑ d ∈ diffSet K, ‖dirichletSum L ((d : ℝ) * gamma)‖) ≤
      (L : ℝ) * min (2 * (K : ℝ))
        (6 + (4 * (q : ℝ) + 2) * (K : ℝ) / L +
          6 * (K : ℝ) * gamma + (4 * (q : ℝ) + 2) / ((L : ℝ) * gamma)) := by
  have hnorm := normalized_sum_le_min hK hL hq hgamma
  have hL0 : 0 ≤ (L : ℝ) := by positivity
  calc
    (∑ d ∈ diffSet K, ‖dirichletSum L ((d : ℝ) * gamma)‖) =
        (L : ℝ) * (∑ d ∈ diffSet K, normalizedWeight L gamma d) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d hd
          unfold normalizedWeight
          field_simp
    _ ≤ (L : ℝ) * min (2 * (K : ℝ))
        (6 + (4 * (q : ℝ) + 2) * (K : ℝ) / L +
          6 * (K : ℝ) * gamma + (4 * (q : ℝ) + 2) / ((L : ℝ) * gamma)) :=
      mul_le_mul_of_nonneg_left hnorm hL0

end
end FordDirichletKernelSum

#print axioms FordDirichletKernelSum.normalized_sum_le_min
#print axioms FordDirichletKernelSum.unnormalized_sum_le_mul_min
