import GuthMaynardLemma295WeightedPairAssembly
import GuthMaynardTPowerCardinality

/-!
# Off-diagonal AFE assembly in Jutila Lemma 29.5

This file sums the pointwise reflected approximate functional equation over
all distinct ordinate pairs.  The central integrals use the certified
`N*pi^2` pair bound; the pointwise power-saving remainder is retained with
its exact `R^2` multiplicity for the later spacing-cardinality absorption.
-/

namespace GuthMaynardLemma295OffDiagonalAssembly

open scoped BigOperators
open MeasureTheory
open GuthMaynardJutilaReflection2941
open GuthMaynardLemma295WeightedPairAssembly

noncomputable section

/-- Literal off-diagonal smooth pair moment from the first display in the
proof of Lemma 29.10. -/
def offDiagonalHPlusPairMoment (N : ℝ) (G : Finset ℝ) : ℝ :=
  ∑ g₁ ∈ G, ∑ g₂ ∈ G,
    if g₁ = g₂ then 0 else ‖sourceHPlusSum N (g₁ - g₂)‖ ^ 2

theorem offDiagonalHPlusPairMoment_nonneg (N : ℝ) (G : Finset ℝ) :
    0 ≤ offDiagonalHPlusPairMoment N G := by
  unfold offDiagonalHPlusPairMoment
  positivity

/-- Finite summation of a pointwise AFE.  The theorem is independent of how
the pointwise inequality was proved. -/
theorem offDiagonalHPlusPairMoment_le_of_pointwise
    {N T A C : ℝ} (hN : 0 ≤ N) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (M R : ℝ) (G : Finset ℝ)
    (hpoint : ∀ g₁ ∈ G, ∀ g₂ ∈ G, g₁ ≠ g₂ →
      ‖sourceHPlusSum N (g₁ - g₂)‖ ≤
        C * lemma295CentralMajorant N M (g₁ - g₂) R +
          C * Real.rpow T (-A)) :
    offDiagonalHPlusPairMoment N G ≤
      2 * C ^ 2 * (N * Real.pi ^ 2 * jutilaReflectedPrefixMoment M G) +
        2 * C ^ 2 * (G.card : ℝ) ^ 2 * Real.rpow T (-2 * A) := by
  let central : ℝ → ℝ → ℝ := fun g₁ g₂ =>
    lemma295CentralMajorant N M (g₁ - g₂) R
  let err : ℝ := Real.rpow T (-A)
  have herr : 0 ≤ err := Real.rpow_nonneg hT _
  have hcentral : ∀ g₁ g₂, 0 ≤ central g₁ g₂ := by
    intro g₁ g₂
    dsimp [central, lemma295CentralMajorant]
    exact mul_nonneg (Real.sqrt_nonneg _) (integral_nonneg fun t => by positivity)
  have hpairs :
      offDiagonalHPlusPairMoment N G ≤
        ∑ g₁ ∈ G, ∑ g₂ ∈ G,
          (2 * C ^ 2 * central g₁ g₂ ^ 2 + 2 * C ^ 2 * err ^ 2) := by
    unfold offDiagonalHPlusPairMoment
    apply Finset.sum_le_sum
    intro g₁ hg₁
    apply Finset.sum_le_sum
    intro g₂ hg₂
    by_cases heq : g₁ = g₂
    · simp [heq]
      positivity
    · rw [if_neg heq]
      have hraw := hpoint g₁ hg₁ g₂ hg₂ heq
      have hx : 0 ≤ C * central g₁ g₂ :=
        mul_nonneg hC (hcentral g₁ g₂)
      have hy : 0 ≤ C * err := mul_nonneg hC herr
      have hsum : 0 ≤ C * central g₁ g₂ + C * err := add_nonneg hx hy
      have hsquare :
          ‖sourceHPlusSum N (g₁ - g₂)‖ ^ 2 ≤
            (C * central g₁ g₂ + C * err) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hraw 2
      calc
        ‖sourceHPlusSum N (g₁ - g₂)‖ ^ 2 ≤
            (C * central g₁ g₂ + C * err) ^ 2 := hsquare
        _ ≤ 2 * C ^ 2 * central g₁ g₂ ^ 2 +
            2 * C ^ 2 * err ^ 2 := by
          nlinarith [sq_nonneg (C * central g₁ g₂ - C * err)]
  have hrearrange :
      (∑ g₁ ∈ G, ∑ g₂ ∈ G,
          (2 * C ^ 2 * central g₁ g₂ ^ 2 + 2 * C ^ 2 * err ^ 2)) =
        2 * C ^ 2 * (∑ g₁ ∈ G, ∑ g₂ ∈ G, central g₁ g₂ ^ 2) +
          2 * C ^ 2 * (G.card : ℝ) ^ 2 * err ^ 2 := by
    simp_rw [Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro g₁ hg₁
      rw [Finset.mul_sum]
    · simp
      ring
  have hcentralSum := centralMajorant_pairMoment_le hN M R G
  have hcentralSum' :
      (∑ g₁ ∈ G, ∑ g₂ ∈ G, central g₁ g₂ ^ 2) ≤
        N * Real.pi ^ 2 * jutilaReflectedPrefixMoment M G := by
    simpa [central] using hcentralSum
  have hfirstNonneg : 0 ≤ 2 * C ^ 2 := by positivity
  calc
    offDiagonalHPlusPairMoment N G ≤
        ∑ g₁ ∈ G, ∑ g₂ ∈ G,
          (2 * C ^ 2 * central g₁ g₂ ^ 2 + 2 * C ^ 2 * err ^ 2) := hpairs
    _ = 2 * C ^ 2 * (∑ g₁ ∈ G, ∑ g₂ ∈ G, central g₁ g₂ ^ 2) +
          2 * C ^ 2 * (G.card : ℝ) ^ 2 * err ^ 2 := hrearrange
    _ ≤ 2 * C ^ 2 *
          (N * Real.pi ^ 2 * jutilaReflectedPrefixMoment M G) +
      2 * C ^ 2 * (G.card : ℝ) ^ 2 * err ^ 2 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hcentralSum' hfirstNonneg) le_rfl
    _ = 2 * C ^ 2 *
          (N * Real.pi ^ 2 * jutilaReflectedPrefixMoment M G) +
          2 * C ^ 2 * (G.card : ℝ) ^ 2 * Real.rpow T (-2 * A) := by
      congr 1
      dsimp [err]
      rw [show -2 * A = (-A) * (2 : ℕ) by ring,
        Real.rpow_mul_natCast hT]

/-- Exact specialization of the pointwise Lemma-29.5 AFE to all distinct
differences in a `T^delta`-separated subset of `(0,T]`.  The only hypothesis
is the published contour/functional-equation statement itself. -/
theorem offDiagonalHPlusPairMoment_le_of_lemma295AFE
    (hAFE : Lemma295ApproximateFunctionalEquationExactM)
    {delta epsilon A : ℝ}
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) (hA : 0 < A) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T N : ℝ) (G : Finset ℝ),
        T₀ ≤ T → 1 ≤ N →
        N ≤ sourceReflectionNumerator29_40 T epsilon →
        TPowerSeparated G T delta → InOpenClosedZeroT G T →
        offDiagonalHPlusPairMoment N G ≤
          2 * C ^ 2 *
            (N * Real.pi ^ 2 *
              jutilaReflectedPrefixMoment
                (reflectedLength29_40 T epsilon N) G) +
          2 * C ^ 2 * (G.card : ℝ) ^ 2 *
            Real.rpow T (-2 * A) := by
  obtain ⟨C, T₀, hC, hT₀, hpoint⟩ :=
    hAFE delta epsilon A hdelta hepsilon hA
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T N G hT hN hNupper hsep hheight
  have hTone : 1 ≤ T := by linarith
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTone
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  apply offDiagonalHPlusPairMoment_le_of_pointwise
    hNpos.le hTpos.le hC.le
    (reflectedLength29_40 T epsilon N) (Real.rpow T epsilon) G
  intro g₁ hg₁ g₂ hg₂ hne
  have hgapLow : Real.rpow T delta ≤ |g₁ - g₂| :=
    hsep g₁ hg₁ g₂ hg₂ hne
  have hgapHigh : |g₁ - g₂| ≤ T := by
    rw [abs_le]
    constructor <;> linarith [(hheight g₁ hg₁).1, (hheight g₁ hg₁).2,
      (hheight g₂ hg₂).1, (hheight g₂ hg₂).2]
  exact hpoint T T N (g₁ - g₂)
    hT hNpos hNupper hgapLow hgapHigh le_rfl

end

end GuthMaynardLemma295OffDiagonalAssembly

#print axioms GuthMaynardLemma295OffDiagonalAssembly.offDiagonalHPlusPairMoment_le_of_pointwise
#print axioms GuthMaynardLemma295OffDiagonalAssembly.offDiagonalHPlusPairMoment_le_of_lemma295AFE
