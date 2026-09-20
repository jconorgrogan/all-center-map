import GuthMaynardS1Tail

/-!
# Guth--Maynard Proposition 5.1

This file retains the `N^{-j}` factor in the finite diagonal sector.  The
earlier coarse finite-sector endpoint intentionally replaced that factor by
one and therefore cannot, by itself, imply the published `T^{-10}` bound.
-/

namespace GuthMaynardS1Proposition51

open scoped BigOperators Real
open GuthMaynardS1Source GuthMaynardS1Tail
open GuthMaynardJIteration
open GuthMaynardSectionThreeCutoffDerivativeBudget

noncomputable section

/-- The full-diagonal finite sector with the decisive `N^{-j}` saving kept
outside the summand. -/
theorem sourceS1ThirdFiniteDiagonalMass_le_with_N_decay
    {N : ℕ} (hN : 0 < N) {W : Finset ℝ} {M : Finset ℤ}
    (hm0 : ∀ m ∈ M, m ≠ 0) (j : ℕ) :
    sourceS1ThirdFiniteDiagonalMass N W M ≤
      (W.card : ℝ) ^ 3 * (M.card : ℝ) *
        (lemma43DerivativeConstant 0 ^ 2 * lemma43DerivativeConstant j /
          (N : ℝ) ^ j) := by
  unfold sourceS1ThirdFiniteDiagonalMass
  calc
    (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, ∑ m ∈ M,
        if t₁ = t₂ ∧ t₂ = t₃ then
          ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ else 0) ≤
      ∑ _t₁ ∈ W, ∑ _t₂ ∈ W, ∑ _t₃ ∈ W, ∑ _m ∈ M,
        (lemma43DerivativeConstant 0 ^ 2 * lemma43DerivativeConstant j /
          (N : ℝ) ^ j) := by
      apply Finset.sum_le_sum
      intro t₁ ht₁
      apply Finset.sum_le_sum
      intro t₂ ht₂
      apply Finset.sum_le_sum
      intro t₃ ht₃
      apply Finset.sum_le_sum
      intro m hm
      split_ifs with hdiag
      · rcases hdiag with ⟨h₁₂, h₂₃⟩
        have hraw := norm_sourceS1KernelThird_diagonal_le
          (t := t₃) (hm0 m hm) hN j
        have hmOne := one_le_abs_intCast (hm0 m hm)
        have hmPow : (1 : ℝ) ≤ |(m : ℝ)| ^ j := by
          simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hmOne j
        have hNpos : 0 < (N : ℝ) ^ j := by positivity
        have habsN : |(N : ℝ)| = (N : ℝ) :=
          abs_of_nonneg (Nat.cast_nonneg N)
        have hmN : |(m : ℝ) * (N : ℝ)| ^ j =
            |(m : ℝ)| ^ j * (N : ℝ) ^ j := by
          rw [abs_mul, habsN, mul_pow]
        rw [hmN] at hraw
        have hden : (N : ℝ) ^ j ≤ |(m : ℝ)| ^ j * (N : ℝ) ^ j := by
          simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right hmPow hNpos.le)
        have hfrac : lemma43DerivativeConstant j /
              (|(m : ℝ)| ^ j * (N : ℝ) ^ j) ≤
            lemma43DerivativeConstant j / (N : ℝ) ^ j := by
          exact div_le_div_of_nonneg_left
            (lemma43DerivativeConstant_nonneg j) hNpos hden
        calc
          ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ =
              ‖sourceS1KernelThird N t₃ t₃ t₃ m‖ := by rw [h₁₂, h₂₃]
          _ ≤
              lemma43DerivativeConstant 0 ^ 2 *
                (lemma43DerivativeConstant j /
                  (|(m : ℝ)| ^ j * (N : ℝ) ^ j)) := hraw
          _ ≤ lemma43DerivativeConstant 0 ^ 2 *
                (lemma43DerivativeConstant j / (N : ℝ) ^ j) := by
            exact mul_le_mul_of_nonneg_left hfrac (sq_nonneg _)
          _ = lemma43DerivativeConstant 0 ^ 2 *
                lemma43DerivativeConstant j / (N : ℝ) ^ j := by ring
      · rw [div_eq_mul_inv]
        exact mul_nonneg
          (mul_nonneg (sq_nonneg _)
            (lemma43DerivativeConstant_nonneg j))
          (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg N) j))
    _ = (W.card : ℝ) ^ 3 * (M.card : ℝ) *
        (lemma43DerivativeConstant 0 ^ 2 * lemma43DerivativeConstant j /
          (N : ℝ) ^ j) := by
      simp
      ring

/-- Finite-sector partition with both rapid-decay mechanisms retained. -/
theorem sourceS1ThirdFiniteMass_le_partition_bound_sharp
    {N : ℕ} (hN : 0 < N) {W : Finset ℝ} {M : Finset ℤ} {R : ℝ}
    (hR : 0 < R)
    (hsep : ∀ t₁ ∈ W, ∀ t₂ ∈ W, t₁ ≠ t₂ → R ≤ |t₁ - t₂|)
    (hm0 : ∀ m ∈ M, m ≠ 0) (j : ℕ) :
    sourceS1ThirdFiniteMass N W M ≤
      (W.card : ℝ) ^ 3 * (M.card : ℝ) *
        ((s1VerticalConstant j / (R / (2 * Real.pi)) ^ j) *
            lemma43DerivativeConstant 0 ^ 2) +
      (W.card : ℝ) ^ 3 * (M.card : ℝ) *
        (lemma43DerivativeConstant 0 *
          (s1VerticalConstant j / (R / (2 * Real.pi)) ^ j) *
          lemma43DerivativeConstant 0) +
      (W.card : ℝ) ^ 3 * (M.card : ℝ) *
        (lemma43DerivativeConstant 0 ^ 2 * lemma43DerivativeConstant j /
          (N : ℝ) ^ j) := by
  rw [sourceS1ThirdFiniteMass_partition]
  exact add_le_add
    (add_le_add
      (sourceS1ThirdFiniteFirstGapMass_le hR hsep j)
      (sourceS1ThirdFiniteSecondGapMass_le hR hsep j))
    (sourceS1ThirdFiniteDiagonalMass_le_with_N_decay hN hm0 j)

/-- A convenient real-valued cardinality bound for the finite frequency
range.  The coarse constant five avoids carrying ceiling functions into the
source power ledger. -/
theorem card_s1FiniteMRange_cast_le_five_mul
    {B : ℝ} (hB : 1 ≤ B) :
    ((s1FiniteMRange B).card : ℝ) ≤ 5 * B := by
  have hcardNat := card_s1FiniteMRange_le B
  have hcard : ((s1FiniteMRange B).card : ℝ) ≤
      2 * (Nat.ceil B : ℝ) + 1 := by exact_mod_cast hcardNat
  have hceil : (Nat.ceil B : ℝ) < B + 1 :=
    Nat.ceil_lt_add_one (by linarith)
  linarith

/-- Sharp all-frequency endpoint before inserting the source powers. -/
theorem sourceS1TotalContribution_le_sharp
    {N : ℕ} (hN : 0 < N) {W : Finset ℝ} {T R B : ℝ}
    (hT : 0 ≤ T) (hR : 0 < R) (hB : 0 < B)
    (hsep : ∀ t₁ ∈ W, ∀ t₂ ∈ W, t₁ ≠ t₂ → R ≤ |t₁ - t₂|)
    (hdiameter : ∀ t ∈ W, ∀ u ∈ W, |t - u| ≤ T)
    (j q : ℕ) :
    sourceS1TotalContribution N W ≤
      3 * (N : ℝ) ^ 3 *
        (((W.card : ℝ) ^ 3 * ((s1FiniteMRange B).card : ℝ) *
              ((s1VerticalConstant j / (R / (2 * Real.pi)) ^ j) *
                lemma43DerivativeConstant 0 ^ 2) +
            (W.card : ℝ) ^ 3 * ((s1FiniteMRange B).card : ℝ) *
              (lemma43DerivativeConstant 0 *
                (s1VerticalConstant j / (R / (2 * Real.pi)) ^ j) *
                lemma43DerivativeConstant 0) +
            (W.card : ℝ) ^ 3 * ((s1FiniteMRange B).card : ℝ) *
              (lemma43DerivativeConstant 0 ^ 2 * lemma43DerivativeConstant j /
                (N : ℝ) ^ j)) +
          (W.card : ℝ) ^ 3 *
            ((lemma43DerivativeConstant 0 ^ 2 *
                (lemma43DerivativeConstant (q + 2) * (1 + T) ^ (q + 2))) *
              ((1 / (N : ℝ) ^ (q + 2)) *
                (2 ^ (q + 2) *
                  ((1 / B ^ q) * integerQuadraticMass))))) := by
  refine (sourceS1TotalContribution_le_split hN hT hB hdiameter).trans ?_
  unfold sourceS1SplitContribution sourceS1ThirdSplitMass
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add
    (sourceS1ThirdFiniteMass_le_partition_bound_sharp hN hR hsep
      (fun m hm => mem_s1FiniteMRange_ne_zero hm) j)
    (sourceS1ThirdFarMass_le hN hT hB hdiameter q)

/-- The frequency split used in the proof of Proposition 5.1. -/
def sourceS1FrequencyCutoff (T epsilon N : ℝ) : ℝ :=
  Real.rpow T (1 + epsilon) / N

theorem one_le_sourceS1FrequencyCutoff
    {T epsilon N : ℝ} (hT : 1 ≤ T) (hepsilon : 0 ≤ epsilon)
    (hN : 0 < N) (hNT : N ≤ T) :
    1 ≤ sourceS1FrequencyCutoff T epsilon N := by
  have hpow : T ≤ Real.rpow T (1 + epsilon) := by
    calc
      T = Real.rpow T (1 : ℝ) := (Real.rpow_one T).symm
      _ ≤ Real.rpow T (1 + epsilon) :=
        Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  rw [sourceS1FrequencyCutoff, le_div_iff₀ hN]
  simpa using hNT.trans hpow

theorem sourceS1FrequencyCutoff_le_timePower
    {T epsilon N : ℝ} (hT : 0 ≤ T) (hN : 1 ≤ N) :
    sourceS1FrequencyCutoff T epsilon N ≤ Real.rpow T (1 + epsilon) := by
  unfold sourceS1FrequencyCutoff
  exact div_le_self (Real.rpow_nonneg hT _) hN

theorem sourceFiniteOuterFactor_le
    {T epsilon N : ℝ} {W : Finset ℝ}
    (hT : 1 ≤ T) (hepsilon : 0 ≤ epsilon)
    (hN : 1 ≤ N) (hNT : N ≤ T)
    (hW : (W.card : ℝ) ≤ 2 * T) :
    N ^ 3 * (W.card : ℝ) ^ 3 *
        ((s1FiniteMRange (sourceS1FrequencyCutoff T epsilon N)).card : ℝ) ≤
      40 * Real.rpow T (7 + epsilon) := by
  have hB1 := one_le_sourceS1FrequencyCutoff hT hepsilon
    (lt_of_lt_of_le zero_lt_one hN) hNT
  have hcard := card_s1FiniteMRange_cast_le_five_mul hB1
  have hBupper := sourceS1FrequencyCutoff_le_timePower (epsilon := epsilon)
    (zero_le_one.trans hT) hN
  have hcard' :
      ((s1FiniteMRange (sourceS1FrequencyCutoff T epsilon N)).card : ℝ) ≤
        5 * Real.rpow T (1 + epsilon) :=
    hcard.trans (mul_le_mul_of_nonneg_left hBupper (by norm_num))
  have hN3 : N ^ 3 ≤ T ^ 3 :=
    pow_le_pow_left₀ (by linarith) hNT 3
  have hW0 : 0 ≤ (W.card : ℝ) := by positivity
  have hW3 : (W.card : ℝ) ^ 3 ≤ (2 * T) ^ 3 :=
    pow_le_pow_left₀ hW0 hW 3
  calc
    N ^ 3 * (W.card : ℝ) ^ 3 *
        ((s1FiniteMRange (sourceS1FrequencyCutoff T epsilon N)).card : ℝ) ≤
      T ^ 3 * (2 * T) ^ 3 * (5 * Real.rpow T (1 + epsilon)) := by
        gcongr
    _ = 40 * (Real.rpow T (3 : ℝ) * Real.rpow T (3 : ℝ) *
        Real.rpow T (1 + epsilon)) := by
      have hT3 : Real.rpow T (3 : ℝ) = T ^ 3 := Real.rpow_natCast T 3
      rw [hT3]
      ring
    _ = 40 * Real.rpow T (7 + epsilon) := by
      have hTpos : 0 < T := by linarith
      have h33 : Real.rpow T (3 : ℝ) * Real.rpow T (3 : ℝ) =
          Real.rpow T (6 : ℝ) := by
        simpa only [show (3 : ℝ) + 3 = 6 by norm_num] using
          (Real.rpow_add hTpos (3 : ℝ) (3 : ℝ)).symm
      have h61 : Real.rpow T (6 : ℝ) * Real.rpow T (1 + epsilon) =
          Real.rpow T (7 + epsilon) := by
        simpa only [show (6 : ℝ) + (1 + epsilon) = 7 + epsilon by ring] using
          (Real.rpow_add hTpos (6 : ℝ) (1 + epsilon)).symm
      rw [h33, h61]

/-- The exact natural-power identity behind the off-diagonal exponent
`epsilon*j`. -/
theorem sourceSeparation_pow
    {T epsilon : ℝ} (hT : 0 ≤ T) (j : ℕ) :
    Real.rpow T epsilon ^ j = Real.rpow T (epsilon * j) := by
  exact (Real.rpow_mul_natCast hT epsilon j).symm

theorem sourceVerticalDecay_eq_timePower
    {T epsilon : ℝ} (hT : 0 < T) (j : ℕ) :
    (s1VerticalConstant j /
          (Real.rpow T epsilon / (2 * Real.pi)) ^ j) *
        lemma43DerivativeConstant 0 ^ 2 =
      (s1VerticalConstant j * (2 * Real.pi) ^ j *
          lemma43DerivativeConstant 0 ^ 2) *
        Real.rpow T (-(epsilon * j)) := by
  have hR : 0 < Real.rpow T epsilon := Real.rpow_pos_of_pos hT _
  have hpi : 0 < 2 * Real.pi := by positivity
  have hpowR := sourceSeparation_pow (epsilon := epsilon) hT.le j
  have hinv : (Real.rpow T (epsilon * j))⁻¹ =
      Real.rpow T (-(epsilon * j)) := by
    exact (Real.rpow_neg hT.le (epsilon * j)).symm
  rw [div_pow, hpowR]
  rw [div_eq_mul_inv, inv_div, div_eq_mul_inv, hinv]
  ring

theorem sourceDiagonalDecay_le_timePower
    {T epsilon N : ℝ} (hT : 0 < T) (hN : 0 < N)
    (hsepN : Real.rpow T epsilon ≤ N) (j : ℕ) :
    lemma43DerivativeConstant 0 ^ 2 * lemma43DerivativeConstant j / N ^ j ≤
      (lemma43DerivativeConstant 0 ^ 2 * lemma43DerivativeConstant j) *
        Real.rpow T (-(epsilon * j)) := by
  have hR : 0 < Real.rpow T epsilon := Real.rpow_pos_of_pos hT _
  have hpow : Real.rpow T epsilon ^ j ≤ N ^ j :=
    pow_le_pow_left₀ hR.le hsepN j
  have hpowR := sourceSeparation_pow (epsilon := epsilon) hT.le j
  rw [hpowR] at hpow
  have hinv : (N ^ j)⁻¹ ≤ (Real.rpow T (epsilon * j))⁻¹ :=
    (inv_le_inv₀ (pow_pos hN j) (Real.rpow_pos_of_pos hT _)).2 hpow
  have hconst : 0 ≤
      lemma43DerivativeConstant 0 ^ 2 * lemma43DerivativeConstant j :=
    mul_nonneg (sq_nonneg _) (lemma43DerivativeConstant_nonneg j)
  rw [div_eq_mul_inv]
  calc
    (lemma43DerivativeConstant 0 ^ 2 * lemma43DerivativeConstant j) *
        (N ^ j)⁻¹ ≤
      (lemma43DerivativeConstant 0 ^ 2 * lemma43DerivativeConstant j) *
        (Real.rpow T (epsilon * j))⁻¹ :=
      mul_le_mul_of_nonneg_left hinv hconst
    _ = (lemma43DerivativeConstant 0 ^ 2 * lemma43DerivativeConstant j) *
        Real.rpow T (-(epsilon * j)) := by
      rw [show (Real.rpow T (epsilon * j))⁻¹ =
        Real.rpow T (-(epsilon * j)) by
          exact (Real.rpow_neg hT.le (epsilon * j)).symm]

theorem finite_source_power_le_neg_thirteen
    {T epsilon : ℝ} (hT : 1 ≤ T) (hepsilon : 0 < epsilon) :
    Real.rpow T (7 + epsilon - epsilon * s1DecayOrder epsilon) ≤
      Real.rpow T (-13 : ℝ) :=
  Real.rpow_le_rpow_of_exponent_le hT
    (s1FiniteExponent_le_neg_thirteen hepsilon)

theorem far_source_power_le_neg_twelve
    {T epsilon : ℝ} (hT : 1 ≤ T) (hepsilon : 0 < epsilon) :
    Real.rpow T
        (8 - epsilon * (s1DecayOrder epsilon - 2 : ℕ)) ≤
      Real.rpow T (-12 : ℝ) :=
  Real.rpow_le_rpow_of_exponent_le hT
    (s1FarExponent_le_neg_twelve hepsilon)

/-- The two spare powers in the source ledger turn the sum of the finite and
far sectors into the published `T^{-10}` scale, with constant two. -/
theorem source_power_sum_le_two_mul_neg_ten
    {T epsilon : ℝ} (hT : 1 ≤ T) (hepsilon : 0 < epsilon) :
    Real.rpow T (7 + epsilon - epsilon * s1DecayOrder epsilon) +
        Real.rpow T
          (8 - epsilon * (s1DecayOrder epsilon - 2 : ℕ)) ≤
      2 * Real.rpow T (-10 : ℝ) := by
  have h13 := finite_source_power_le_neg_thirteen hT hepsilon
  have h12 := far_source_power_le_neg_twelve hT hepsilon
  have h13to10 : Real.rpow T (-13 : ℝ) ≤ Real.rpow T (-10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  have h12to10 : Real.rpow T (-12 : ℝ) ≤ Real.rpow T (-10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  nlinarith

end
end GuthMaynardS1Proposition51

#print axioms GuthMaynardS1Proposition51.sourceS1ThirdFiniteDiagonalMass_le_with_N_decay
#print axioms GuthMaynardS1Proposition51.sourceS1ThirdFiniteMass_le_partition_bound_sharp
#print axioms GuthMaynardS1Proposition51.card_s1FiniteMRange_cast_le_five_mul
#print axioms GuthMaynardS1Proposition51.sourceS1TotalContribution_le_sharp
#print axioms GuthMaynardS1Proposition51.source_power_sum_le_two_mul_neg_ten
