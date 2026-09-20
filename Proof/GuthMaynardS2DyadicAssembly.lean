import GuthMaynardS2DyadicReflection

/-! # Exact finite dyadic assembly of S2
Short differences are separated from the dyadic reflection scales. Every
long difference is covered by a literal gap mask, and endpoint overlap only
increases a nonnegative sum.
-/

namespace GuthMaynardS2DyadicAssembly

open scoped BigOperators
open GuthMaynardSectorFactorization GuthMaynardS2LiteralReduction
open GuthMaynardS2DyadicReflection GuthMaynardS1Tail
open GuthMaynardSectionThreeCutoffDerivativeBudget
open GuthMaynardHeathBrownInterface

noncomputable section

def sourceShortGapPairMoment (N : ℕ) (W : Finset ℝ) (A : ℝ) : ℝ :=
  ∑ t ∈ W, ∑ u ∈ W,
    if |t - u| < A then ‖sourceNonzeroFourier N (t - u)‖ ^ 2 else 0

private theorem exists_dyadic_gap {A x : ℝ} (hAx : A ≤ x)
    (K : ℕ) (hx : x ≤ A * (2 : ℝ) ^ (K + 1)) :
    ∃ i ∈ Finset.range (K + 1), A * (2 : ℝ) ^ i ≤ x ∧
      x ≤ A * (2 : ℝ) ^ (i + 1) := by
  induction K with
  | zero => exact ⟨0, by simp, by simpa using hAx, hx⟩
  | succ K ih =>
      by_cases h : x ≤ A * (2 : ℝ) ^ (K + 1)
      · obtain ⟨i, hi, hlo, hhi⟩ := ih h
        exact ⟨i, Finset.mem_range.mpr (by
          have := Finset.mem_range.mp hi
          omega), hlo, hhi⟩
      · exact ⟨K + 1, Finset.mem_range.mpr (by omega), (lt_of_not_ge h).le, hx⟩

/-- The full Fourier pair moment is covered by the short-gap part and the
finite dyadic gap masks. No frequency or ordinate mask is discarded. -/
theorem sourceNonzeroFourierPairMoment_le_dyadic
    (N : ℕ) (W : Finset ℝ) (A : ℝ) (K : ℕ)
    (hcover : ∀ t ∈ W, ∀ u ∈ W, |t - u| ≤ A * (2 : ℝ) ^ (K + 1)) :
    sourceNonzeroFourierPairMoment N W ≤ sourceShortGapPairMoment N W A +
      ∑ i ∈ Finset.range (K + 1),
        sourceFourierGapPairMoment N W (A * (2 : ℝ) ^ i) (A * (2 : ℝ) ^ (i + 1)) := by
  classical
  let f := fun t u i =>
    if A * (2 : ℝ) ^ i ≤ |t - u| ∧ |t - u| ≤ A * (2 : ℝ) ^ (i + 1)
    then ‖sourceNonzeroFourier N (t - u)‖ ^ 2 else 0
  have hcomm : (∑ t ∈ W, ∑ u ∈ W, ∑ i ∈ Finset.range (K + 1), f t u i) =
      ∑ i ∈ Finset.range (K + 1), ∑ t ∈ W, ∑ u ∈ W, f t u i := by
    calc
      _ = ∑ t ∈ W, ∑ i ∈ Finset.range (K + 1), ∑ u ∈ W, f t u i :=
        Finset.sum_congr rfl (fun t _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  have hp : ∀ t ∈ W, ∀ u ∈ W,
      ‖sourceNonzeroFourier N (t - u)‖ ^ 2 ≤
        (if |t - u| < A then ‖sourceNonzeroFourier N (t - u)‖ ^ 2 else 0) +
          ∑ i ∈ Finset.range (K + 1), f t u i := by
    intro t ht u hu
    by_cases hs : |t - u| < A
    · rw [if_pos hs]
      apply le_add_of_nonneg_right
      exact Finset.sum_nonneg fun i _ => by unfold f; split_ifs <;> positivity
    · rw [if_neg hs, zero_add]
      obtain ⟨i, hi, hlo, hhi⟩ := exists_dyadic_gap (le_of_not_gt hs) K (hcover t ht u hu)
      have hsummand : ‖sourceNonzeroFourier N (t - u)‖ ^ 2 = f t u i := by
        simp [f, hlo, hhi]
      rw [hsummand]
      exact Finset.single_le_sum (fun j _ => by unfold f; split_ifs <;> positivity) hi
  unfold sourceNonzeroFourierPairMoment sourceShortGapPairMoment sourceFourierGapPairMoment
  calc
    _ ≤ ∑ t ∈ W, ∑ u ∈ W,
        ((if |t - u| < A then ‖sourceNonzeroFourier N (t - u)‖ ^ 2 else 0) +
          ∑ i ∈ Finset.range (K + 1), f t u i) :=
      Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun u hu => hp t ht u hu
    _ = _ := by simp only [Finset.sum_add_distrib]; rw [hcomm]

/-- Finite dyadic S2 bound from the proved reflection and powered pair theorem.
The remaining cutoffs are ordinary numeric choices, not analytic premises. -/
theorem norm_sourceS2_le_dyadic_powered {eta : ℝ} (heta : 0 < eta) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (N : ℕ) (W : Finset ℝ) (A D R : ℝ)
        (K j k ell : ℕ) (J : ℕ → ℕ),
        T₀ ≤ T → 0 < N → 0 < D → 0 < R → R < A →
        (∀ t ∈ W, ∀ u ∈ W, t ≠ u → D ≤ |t - u|) →
        (∀ t ∈ W, ∀ u ∈ W, |t - u| ≤ A * (2 : ℝ) ^ (K + 1)) →
        (∀ i ∈ Finset.range (K + 1), ((2 ^ J i : ℕ) : ℝ) ≤ T) →
        2 ≤ k → 2 ≤ ell → CGLProofDAG.OneSeparated W →
        ContainedInIntervalOfLength W T →
        ‖GuthMaynardEquation55Infinite.sourceS2 N W‖ ≤
          3 * (N : ℝ) ^ 3 *
            (lemma43DerivativeConstant 0 + (W.card : ℝ) *
              (s1VerticalConstant j / (D / (2 * Real.pi)) ^ j)) *
            (sourceShortGapPairMoment N W A +
              ∑ i ∈ Finset.range (K + 1),
                sourceGapPoweredBudget C eta T N W
                  (A * (2 : ℝ) ^ i) (A * (2 : ℝ) ^ (i + 1)) R (J i) k ell) := by
  obtain ⟨C, T₀, hC, hT₀, hlocal⟩ := sourceFourierGapPairMoment_powered_bound heta
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T N W A D R K j k ell J hT hN hD hR hRA hsep hcover hJ hk hell honesep hinterval
  apply (norm_sourceS2_le_pairMoment hN W hD hsep j).trans
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (by positivity)
      (add_nonneg (lemma43DerivativeConstant_nonneg 0)
        (mul_nonneg (by positivity)
          (div_nonneg (s1VerticalConstant_nonneg j) (by positivity)))))
  apply (sourceNonzeroFourierPairMoment_le_dyadic N W A K hcover).trans
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro i hi
  have hA : 0 < A := hR.trans hRA
  have hAi : A ≤ A * (2 : ℝ) ^ i :=
    le_mul_of_one_le_right hA.le (one_le_pow₀ (by norm_num))
  apply hlocal T N W (A * (2 : ℝ) ^ i) (A * (2 : ℝ) ^ (i + 1)) R (J i) k ell
    hT hN hR (hRA.trans_le hAi) _ (hJ i hi) hk hell honesep hinterval
  rw [pow_succ]
  nlinarith [show 0 ≤ A * (2 : ℝ) ^ i by positivity]

end
end GuthMaynardS2DyadicAssembly

#print axioms GuthMaynardS2DyadicAssembly.norm_sourceS2_le_dyadic_powered
