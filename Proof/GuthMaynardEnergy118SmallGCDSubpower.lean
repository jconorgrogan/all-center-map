import GuthMaynardEnergy118SmallGCDSum
import GuthMaynardEnergy118PowerTail

open scoped BigOperators
open MeasureTheory
noncomputable section
namespace GuthMaynardEnergy118SmallGCDSubpower
open CGLProofDAG GuthMaynardHeathBrownInterface
open GuthMaynardRatioKernelIdentity GuthMaynardS3LiteralLemma83Energy
open GuthMaynardEnergy118ReducedSampleBound GuthMaynardEnergy118LogInterior
open GuthMaynardEnergy118GCD GuthMaynardLemma118
open GuthMaynardEnergy118SmallGCDSum GuthMaynardEnergy118PowerTail

/-- The actual small-gcd cubic sum, with the Fourier tail absorbed and all
constants chosen before the time, dyadic scale, cutoff, and point set. -/
theorem exists_small_gcd_subpower_bound :
    ∀ eta : ℝ, 0 < eta → eta < 1 →
      ∃ C : ℝ, 0 < C ∧ ∃ T0 : ℝ, 1 ≤ T0 ∧
        ∀ (N D : ℕ) (W : Finset ℝ) (T : ℝ),
          1 ≤ N → T0 ≤ T → (D : ℝ)*T ≤ (N : ℝ)^2 →
          OneSeparated W → ContainedInIntervalOfLength W T →
          (∑ j ∈ Finset.range D, ∑ p ∈ reducedPairs N (j+1),
            ‖ratioDirichletKernel W ((p.1 : ℝ)/(p.2 : ℝ))‖^3) ≤
            C*Real.rpow T eta*(N : ℝ)^2*Real.sqrt (W.card : ℝ)*
              Real.sqrt (sourceApproximateAdditiveEnergy W : ℝ) := by
  intro eta heta hetahi
  obtain ⟨C,hC,hbound⟩ := exists_small_gcd_sum_constant
  obtain ⟨k,hk⟩ := exists_bounded_tail_absorption eta heta
  obtain ⟨T0,hT0,hcollar⟩ := eventually_power_collar hetahi
  let J : ℝ := sourceFourierTailMoment k
  have hJ : 0 ≤ J := by
    apply integral_nonneg
    intro xi
    exact mul_nonneg (pow_nonneg (abs_nonneg xi) k) (norm_nonneg _)
  refine ⟨3*C+4*J+1,by positivity,T0,hT0,?_⟩
  intro N D W T hN hT hDT hsep hcontained
  have hTone : 1 ≤ T := hT0.trans hT
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTone
  let A : ℝ := Real.rpow T eta
  have hAone : 1 ≤ A := Real.one_le_rpow hTone heta.le
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hAone
  let I : ℝ := Real.sqrt (W.card : ℝ)*
    Real.sqrt (sourceApproximateAdditiveEnergy W : ℝ)
  have hI : 0 ≤ I := by dsimp [I]; positivity
  have hmain : (D : ℝ)*T+2*A*(N : ℝ)^2 ≤ 3*A*(N : ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_right hAone (sq_nonneg (N : ℝ))
    nlinarith
  have htail : (W.card : ℝ)^3*(A^k)⁻¹*J ≤ 4*I*J := by
    have hh := mul_le_mul_of_nonneg_right (hk T W hTone hsep hcontained) hJ
    simpa only [A,I,mul_assoc] using hh
  have hbound' := hbound N D W T A k hN hTpos hApos hsep hcontained (hcollar T hT)
  calc
    _ ≤ C*((D : ℝ)*T+2*A*(N : ℝ)^2)*I+
          (N : ℝ)^2*((W.card : ℝ)^3*(A^k)⁻¹*J) := by
      simpa only [I,J,mul_assoc] using hbound'
    _ ≤ C*(3*A*(N : ℝ)^2)*I+(N : ℝ)^2*(4*I*J) :=
      add_le_add (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmain hC.le) hI)
        (mul_le_mul_of_nonneg_left htail (sq_nonneg _))
    _ ≤ C*(3*A*(N : ℝ)^2)*I+A*((N : ℝ)^2*(4*I*J)) := by
      apply add_le_add (le_refl _)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hAone
        (by positivity : 0 ≤ (N : ℝ)^2*(4*I*J))
    _ ≤ (3*C+4*J+1)*A*(N : ℝ)^2*I := by
      nlinarith [mul_nonneg (mul_nonneg hApos.le (sq_nonneg (N : ℝ))) hI]
    _ = _ := by dsimp [A,I]; ring

end GuthMaynardEnergy118SmallGCDSubpower
#print axioms GuthMaynardEnergy118SmallGCDSubpower.exists_small_gcd_subpower_bound
