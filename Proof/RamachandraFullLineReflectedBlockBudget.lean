import RamachandraShiftedReflectedBlockBudget
import RamachandraShiftedReflectedTailInfiniteAssembly
import RamachandraGammaWeightUniformMass

/-!
# Full-Mellin-line budget for a reflected dyadic block

The compact-`v` block theorem is not by itself enough for the literal source
contours.  This module integrates the fixed-`v` all-character mean square over
the whole Mellin line against any integrable nonnegative continuous weight.
The statement is kept in the Tonelli-friendly order (`v` outside, `t`
inside); no truncation or hidden limiting convention remains.
-/

namespace RamachandraFullLineReflectedBlockBudget

open scoped BigOperators Interval
open Complex MeasureTheory
open BHPAllCharacterDyadicBudget
open RamachandraPrimitiveShiftedMellinReduction
open RamachandraShiftedReflectedSeries
open RamachandraShiftedReflectedTailInfiniteAssembly
open MontgomeryVaughanFiniteReduction

noncomputable section

/-- Whole-line continuous-Mellin version of the exact all-character dyadic
cost, under a uniform coefficient-energy envelope. -/
theorem integral_allCharacter_intervalIntegral_weightedBlock_le
    (d N : ℕ) [NeZero d] (hN : 1 ≤ N)
    {T E : ℝ} (hT : 0 ≤ T) (hE : 0 ≤ E)
    (b : ℝ → ℕ → ℂ) (hb : ∀ n, Continuous (fun v => b v n))
    (henergy : ∀ v, coefficientEnergy (b v) N ≤ E)
    (weight : ℝ → ℝ) (hweight : Continuous weight)
    (hweightInt : Integrable weight) (hweight0 : ∀ v, 0 ≤ weight v) :
    (∫ v : ℝ, weight v *
      (∫ t in (-T)..T,
        ∑ psi : DirichletCharacter ℂ d,
          ‖ramachandraDyadicBlock d N (b v) true psi t‖ ^ 2)) ≤
      (∫ v : ℝ, weight v) *
        (((d : ℝ) * (2 * T) + 8 * Real.pi * (N : ℝ)) * E) := by
  let F : ℝ := (d : ℝ) * (2 * T) + 8 * Real.pi * (N : ℝ)
  let G : ℝ → ℝ := fun v =>
    ∫ t in (-T)..T,
      ∑ psi : DirichletCharacter ℂ d,
        ‖ramachandraDyadicBlock d N (b v) true psi t‖ ^ 2
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hGcont : Continuous G := by
    unfold G
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    apply continuous_finsetSum
    intro psi hpsi
    exact (continuous_uncurry_ramachandraDyadicBlock
      d N true b hb psi).comp continuous_swap |>.norm.pow 2
  have hG0 (v : ℝ) : 0 ≤ G v := by
    unfold G
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    positivity
  have hGle (v : ℝ) : G v ≤ F * E := by
    have hmean := integral_sum_norm_ramachandraDyadicBlock_sq_le
      d N hN (b v) true hT
    calc
      G v ≤ ramachandraDyadicCost d N T (b v) := by
        simpa [G] using hmean
      _ ≤ F * E := by
        unfold ramachandraDyadicCost
        exact mul_le_mul_of_nonneg_left (henergy v) hF
  have hright : Integrable (fun v => weight v * (F * E)) :=
    hweightInt.mul_const (F * E)
  have hleft : Integrable (fun v => weight v * G v) := by
    apply hright.mono'
    · exact (hweight.mul hGcont).aestronglyMeasurable
    · filter_upwards with v
      rw [Real.norm_of_nonneg (mul_nonneg (hweight0 v) (hG0 v))]
      exact mul_le_mul_of_nonneg_left (hGle v) (hweight0 v)
  calc
    (∫ v : ℝ, weight v * G v) ≤
        ∫ v : ℝ, weight v * (F * E) := by
      apply integral_mono hleft hright
      intro v
      exact mul_le_mul_of_nonneg_left (hGle v) (hweight0 v)
    _ = (∫ v : ℝ, weight v) * (F * E) := by
      rw [MeasureTheory.integral_mul_const]
    _ = (∫ v : ℝ, weight v) *
        (((d : ℝ) * (2 * T) + 8 * Real.pi * (N : ℝ)) * E) := rfl

/-- Infinite-tail shell specialization.  The literal `X<n` mask can only
lower the sharp quarter-line coefficient energy. -/
theorem integral_longTailShell_le
    (d N : ℕ) [NeZero d] (hN : 1 ≤ N)
    {X T sigma E : ℝ} (hT : 0 ≤ T) (hE : 0 ≤ E)
    (henergy : ∀ v,
      coefficientEnergy
        (shiftedReflectedBlockCoeff sigma (-(sigma + 1 / 4)) v) N ≤ E)
    (weight : ℝ → ℝ) (hweight : Continuous weight)
    (hweightInt : Integrable weight) (hweight0 : ∀ v, 0 ≤ weight v) :
    (∫ v : ℝ, weight v *
      (∫ t in (-T)..T,
        ∑ psi : DirichletCharacter ℂ d,
          ‖ramachandraDyadicBlock d N
            (reflectedTailInfiniteShellCoeff X sigma
              (-(sigma + 1 / 4)) v) true psi t‖ ^ 2)) ≤
      (∫ v : ℝ, weight v) *
        (((d : ℝ) * (2 * T) + 8 * Real.pi * (N : ℝ)) * E) := by
  apply integral_allCharacter_intervalIntegral_weightedBlock_le
    d N hN hT hE
      (fun v => reflectedTailInfiniteShellCoeff X sigma
        (-(sigma + 1 / 4)) v)
      (fun n => continuous_reflectedTailInfiniteShellCoeff
        X sigma (-(sigma + 1 / 4)) n)
      (fun v => (coefficientEnergy_reflectedTailInfiniteShellCoeff_le
        X sigma (-(sigma + 1 / 4)) v N).trans (henergy v))
      weight hweight hweightInt hweight0

end
end RamachandraFullLineReflectedBlockBudget

#print axioms RamachandraFullLineReflectedBlockBudget.integral_allCharacter_intervalIntegral_weightedBlock_le
#print axioms RamachandraFullLineReflectedBlockBudget.integral_longTailShell_le
