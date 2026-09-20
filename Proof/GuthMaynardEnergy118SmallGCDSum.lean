import GuthMaynardEnergy118ReducedSampleBound
import GuthMaynardEnergy118ReducedCardBudget

open scoped BigOperators
open MeasureTheory
noncomputable section
namespace GuthMaynardEnergy118SmallGCDSum
open CGLProofDAG GuthMaynardHeathBrownInterface
open GuthMaynardRatioKernelIdentity GuthMaynardS3LiteralLemma83Energy
open GuthMaynardEnergy118ReducedSampleBound GuthMaynardEnergy118LogInterior
open GuthMaynardEnergy118GCD GuthMaynardLemma118

/-- Sum the actual reduced-ratio estimates. The tail is charged to the total
original dyadic pair count N², not once per gcd class. -/
theorem exists_small_gcd_sum_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N D : ℕ) (W : Finset ℝ) (T A : ℝ) (k : ℕ),
        1 ≤ N → 0 < T → 0 < A → OneSeparated W →
        ContainedInIntervalOfLength W T → A/(3*T) ≤ logFrequencyMargin →
        (∑ j ∈ Finset.range D, ∑ p ∈ reducedPairs N (j+1),
          ‖ratioDirichletKernel W ((p.1 : ℝ)/(p.2 : ℝ))‖^3) ≤
          C*((D : ℝ)*T+2*A*(N : ℝ)^2)*Real.sqrt (W.card : ℝ)*
            Real.sqrt (sourceApproximateAdditiveEnergy W : ℝ) +
          (N : ℝ)^2*((W.card : ℝ)^3*(A^k)⁻¹*sourceFourierTailMoment k) := by
  obtain ⟨C,hC,hbound⟩ := exists_reduced_cubic_sample_constant
  refine ⟨C,hC,?_⟩
  intro N D W T A k hN hT hA hsep hcontained hcollar
  let I : ℝ := Real.sqrt (W.card : ℝ)*Real.sqrt (sourceApproximateAdditiveEnergy W : ℝ)
  have hI : 0 ≤ I := by dsimp [I]; positivity
  let Tail : ℝ := (W.card : ℝ)^3*(A^k)⁻¹*sourceFourierTailMoment k
  have htailMoment : 0 ≤ sourceFourierTailMoment k := by
    apply integral_nonneg
    intro xi
    exact mul_nonneg (pow_nonneg (abs_nonneg xi) k) (norm_nonneg _)
  have hTail : 0 ≤ Tail := by dsimp [Tail]; positivity
  let G : ℕ → ℝ := fun d => ∑ p ∈ reducedPairs N d,
    ‖ratioDirichletKernel W ((p.1 : ℝ)/(p.2 : ℝ))‖^3
  let F : ℕ → ℝ := fun d => G d - (reducedPairs N d).card*Tail
  have hper : ∀ j ∈ Finset.range D,
      F (j+1) ≤ C*(T+(Real.sqrt A*(N : ℝ))^2/((j+1 : ℕ) : ℝ)^2)*I := by
    intro j hj
    have hh := hbound N (j+1) W T A k hN (by omega) hT hA hsep hcontained hcollar
    have hshape : (Real.sqrt A*(N : ℝ))^2/((j+1 : ℕ) : ℝ)^2 =
        A*((N : ℝ)/((j+1 : ℕ) : ℝ))^2 := by
      rw [mul_pow,Real.sq_sqrt hA.le,div_pow]
      ring
    rw [hshape]
    apply sub_le_iff_le_add.mpr
    simpa only [G,Tail,I,mul_assoc] using hh
  have hcumsum := sum_gcd_scale_cost_le D F hC.le hI hper
  have hNsq : (Real.sqrt A*(N : ℝ))^2 = A*(N : ℝ)^2 := by
    rw [mul_pow,Real.sq_sqrt hA.le]
  rw [hNsq] at hcumsum
  have hcard : (∑ j ∈ Finset.range D, ((reducedPairs N (j+1)).card : ℝ)) ≤ (N : ℝ)^2 := by
    exact_mod_cast sum_reducedPairs_card_le_sq N D
  have hidentity : (∑ j ∈ Finset.range D, G (j+1)) =
      (∑ j ∈ Finset.range D, F (j+1))+
        (∑ j ∈ Finset.range D, ((reducedPairs N (j+1)).card : ℝ))*Tail := by
    simp only [F,Finset.sum_sub_distrib,Finset.sum_mul]
    ring
  calc
    _ = (∑ j ∈ Finset.range D, F (j+1))+
        (∑ j ∈ Finset.range D, ((reducedPairs N (j+1)).card : ℝ))*Tail := hidentity
    _ ≤ C*((D : ℝ)*T+2*(A*(N : ℝ)^2))*I+(N : ℝ)^2*Tail :=
      add_le_add hcumsum (mul_le_mul_of_nonneg_right hcard hTail)
    _ = _ := by dsimp [I,Tail]; ring

end GuthMaynardEnergy118SmallGCDSum
#print axioms GuthMaynardEnergy118SmallGCDSum.exists_small_gcd_sum_constant
