import RamachandraShiftedReflectedSeries
import RamachandraPrimitiveShiftedMellinReduction

/-!
# Continuous-Mellin budget for literal shifted reflected blocks

This module combines the exact reflected-term identity, the shifted
coefficient energy, Fubini, character orthogonality, and the logarithmic
Hilbert inequality.  The only remaining contour-specific input is a
nonnegative continuous scalar weight and its one-dimensional mass.
-/

namespace RamachandraShiftedReflectedBlockBudget

open scoped BigOperators Interval
open Complex MeasureTheory
open RamachandraShiftedReflectedSeries
open RamachandraShiftedCoefficientEnergy
open RamachandraPrimitiveShiftedMellinReduction
open BHPAllCharacterDyadicBudget
open MontgomeryVaughanFiniteReduction

noncomputable section

/-- One reflected dyadic block with continuous Mellin ordinate.  The estimate
is valid under the lower bound on the reflected real exponent; it therefore
covers both the long and near contour lines. -/
theorem allCharacter_doubleIntegral_shiftedReflectedDyadicBlock_le
    (d N : ℕ) [NeZero d] (hN : 1 ≤ N)
    {T V Y sigma u delta W : ℝ}
    (weight : ℝ → ℝ)
    (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hNY : (2 * N : ℕ) ≤ Y) (hdelta : 0 ≤ delta)
    (hlineLow : 1 / 2 - delta ≤ 1 - sigma - u)
    (hweight : Continuous weight)
    (hweight0 : ∀ v ∈ Set.Icc (-V) V, 0 ≤ weight v)
    (hweightMass : (∫ v in (-V)..V, weight v) ≤ W) :
    (∑ psi : DirichletCharacter ℂ d,
      ∫ t in (-T)..T,
        ∫ v in (-V)..V,
          weight v *
            ‖shiftedReflectedDyadicBlock psi N sigma u v t‖ ^ 2) ≤
      W * (((d : ℝ) * (2 * T) + 8 * Real.pi * (N : ℝ)) *
        Real.exp (2 * delta * Real.log Y) *
          (harmonic (2 * N) : ℝ) ^ 4) := by
  have hraw := allCharacter_doubleIntegral_weightedBlock_le
    d N hN true (shiftedReflectedBlockCoeff sigma u) weight
      (fun n => continuous_shiftedReflectedBlockCoeff sigma u n)
      hweight hT hV hweight0
  simp_rw [shiftedReflectedDyadicBlock_eq_ramachandraDyadicBlock]
  apply hraw.trans
  let F : ℝ := (d : ℝ) * (2 * T) + 8 * Real.pi * (N : ℝ)
  let E : ℝ := Real.exp (2 * delta * Real.log Y) *
    (harmonic (2 * N) : ℝ) ^ 4
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have henergy (v : ℝ) :
      coefficientEnergy (shiftedReflectedBlockCoeff sigma u v) N ≤ E := by
    dsimp [E]
    exact coefficientEnergy_shiftedReflectedBlockCoeff_le_of_lower
      N hNY hdelta hlineLow v
  have hpoint : ∀ v ∈ Set.Icc (-V) V,
      weight v * ramachandraDyadicCost d N T
          (shiftedReflectedBlockCoeff sigma u v) ≤
        weight v * (F * E) := by
    intro v hv
    unfold ramachandraDyadicCost
    dsimp [F]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (henergy v) hF) (hweight0 v hv)
  have hcostContinuous : Continuous (fun v =>
      ramachandraDyadicCost d N T
        (shiftedReflectedBlockCoeff sigma u v)) := by
    unfold ramachandraDyadicCost coefficientEnergy
    apply continuous_const.mul
    apply continuous_finsetSum
    intro n hn
    exact (continuous_shiftedReflectedBlockCoeff sigma u n).norm.pow 2
  calc
    (∫ v in (-V)..V,
      weight v * ramachandraDyadicCost d N T
        (shiftedReflectedBlockCoeff sigma u v)) ≤
        ∫ v in (-V)..V, weight v * (F * E) := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact (hweight.mul hcostContinuous).intervalIntegrable _ _
      · exact (hweight.mul continuous_const).intervalIntegrable _ _
      · exact hpoint
    _ = (F * E) * ∫ v in (-V)..V, weight v := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext v
      ring
    _ ≤ (F * E) * W :=
      mul_le_mul_of_nonneg_left hweightMass (mul_nonneg hF hE)
    _ = W * (((d : ℝ) * (2 * T) + 8 * Real.pi * (N : ℝ)) *
        Real.exp (2 * delta * Real.log Y) *
          (harmonic (2 * N) : ℝ) ^ 4) := by
      dsimp [F, E]
      ring

/-- Specialization to Ramachandra's long reflected line. -/
theorem allCharacter_doubleIntegral_longReflectedDyadicBlock_le
    (d N : ℕ) [NeZero d] (hN : 1 ≤ N)
    {T V Y sigma W : ℝ}
    (weight : ℝ → ℝ)
    (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hNY : (2 * N : ℕ) ≤ Y)
    (hweight : Continuous weight)
    (hweight0 : ∀ v ∈ Set.Icc (-V) V, 0 ≤ weight v)
    (hweightMass : (∫ v in (-V)..V, weight v) ≤ W) :
    (∑ psi : DirichletCharacter ℂ d,
      ∫ t in (-T)..T,
        ∫ v in (-V)..V,
          weight v *
            ‖shiftedReflectedDyadicBlock psi N sigma
              (-(sigma + 1 / 4)) v t‖ ^ 2) ≤
      W * (((d : ℝ) * (2 * T) + 8 * Real.pi * (N : ℝ)) *
        (harmonic (2 * N) : ℝ) ^ 4) := by
  have h := allCharacter_doubleIntegral_shiftedReflectedDyadicBlock_le
    d N hN weight hT hV hNY (show (0 : ℝ) ≤ 0 by norm_num)
      (show (1 / 2 : ℝ) - 0 ≤
        1 - sigma - (-(sigma + 1 / 4)) by linarith)
      hweight hweight0 hweightMass
  simpa using h

/-- Sharp continuous-Mellin block budget on the literal long line, retaining
the `N⁻³ᐟ²` dyadic saving hidden by the coarse source envelope. -/
theorem allCharacter_doubleIntegral_quarterLineReflectedDyadicBlock_le
    (d N : ℕ) [NeZero d] (hN : 1 ≤ N)
    {T V sigma W : ℝ}
    (weight : ℝ → ℝ)
    (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hweight : Continuous weight)
    (hweight0 : ∀ v ∈ Set.Icc (-V) V, 0 ≤ weight v)
    (hweightMass : (∫ v in (-V)..V, weight v) ≤ W) :
    (∑ psi : DirichletCharacter ℂ d,
      ∫ t in (-T)..T,
        ∫ v in (-V)..V,
          weight v *
            ‖shiftedReflectedDyadicBlock psi N sigma
              (-(sigma + 1 / 4)) v t‖ ^ 2) ≤
      W * (((d : ℝ) * (2 * T) + 8 * Real.pi * (N : ℝ)) *
        Real.rpow (N : ℝ) (-(3 / 2 : ℝ)) *
          (harmonic (2 * N) : ℝ) ^ 4) := by
  have hraw := allCharacter_doubleIntegral_weightedBlock_le
    d N hN true
      (shiftedReflectedBlockCoeff sigma (-(sigma + 1 / 4))) weight
      (fun n => continuous_shiftedReflectedBlockCoeff
        sigma (-(sigma + 1 / 4)) n)
      hweight hT hV hweight0
  simp_rw [shiftedReflectedDyadicBlock_eq_ramachandraDyadicBlock]
  apply hraw.trans
  let F : ℝ := (d : ℝ) * (2 * T) + 8 * Real.pi * (N : ℝ)
  let E : ℝ := Real.rpow (N : ℝ) (-(3 / 2 : ℝ)) *
    (harmonic (2 * N) : ℝ) ^ 4
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have henergy (v : ℝ) :
      coefficientEnergy
          (shiftedReflectedBlockCoeff sigma (-(sigma + 1 / 4)) v) N ≤ E := by
    exact coefficientEnergy_quarterLineReflectedBlockCoeff_le N hN sigma v
  have hpoint : ∀ v ∈ Set.Icc (-V) V,
      weight v * ramachandraDyadicCost d N T
          (shiftedReflectedBlockCoeff sigma (-(sigma + 1 / 4)) v) ≤
        weight v * (F * E) := by
    intro v hv
    unfold ramachandraDyadicCost
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (henergy v) hF) (hweight0 v hv)
  have hcostContinuous : Continuous (fun v =>
      ramachandraDyadicCost d N T
        (shiftedReflectedBlockCoeff sigma (-(sigma + 1 / 4)) v)) := by
    unfold ramachandraDyadicCost coefficientEnergy
    apply continuous_const.mul
    apply continuous_finsetSum
    intro n hn
    exact (continuous_shiftedReflectedBlockCoeff
      sigma (-(sigma + 1 / 4)) n).norm.pow 2
  calc
    (∫ v in (-V)..V,
      weight v * ramachandraDyadicCost d N T
        (shiftedReflectedBlockCoeff sigma (-(sigma + 1 / 4)) v)) ≤
        ∫ v in (-V)..V, weight v * (F * E) := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact (hweight.mul hcostContinuous).intervalIntegrable _ _
      · exact (hweight.mul continuous_const).intervalIntegrable _ _
      · exact hpoint
    _ = (F * E) * ∫ v in (-V)..V, weight v := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext v
      ring
    _ ≤ (F * E) * W :=
      mul_le_mul_of_nonneg_left hweightMass (mul_nonneg hF hE)
    _ = W * (((d : ℝ) * (2 * T) + 8 * Real.pi * (N : ℝ)) *
        Real.rpow (N : ℝ) (-(3 / 2 : ℝ)) *
          (harmonic (2 * N) : ℝ) ^ 4) := by
      dsimp [F, E]
      ring

/-- Sharp continuous-Mellin block budget on the workaround line
`Re(s+w)=-1/2`.  Unlike the coarse fixed-strip envelope, this retains the
literal `N⁻²` coefficient saving from the reflected exponent `3/2`. -/
theorem allCharacter_doubleIntegral_negHalfReflectedDyadicBlock_le
    (d N : ℕ) [NeZero d] (hN : 1 ≤ N)
    {T V sigma W : ℝ}
    (weight : ℝ → ℝ)
    (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hweight : Continuous weight)
    (hweight0 : ∀ v ∈ Set.Icc (-V) V, 0 ≤ weight v)
    (hweightMass : (∫ v in (-V)..V, weight v) ≤ W) :
    (∑ psi : DirichletCharacter ℂ d,
      ∫ t in (-T)..T,
        ∫ v in (-V)..V,
          weight v *
            ‖shiftedReflectedDyadicBlock psi N sigma
              (-(sigma + 1 / 2)) v t‖ ^ 2) ≤
      W * (((d : ℝ) * (2 * T) + 8 * Real.pi * (N : ℝ)) *
        ((N : ℝ)⁻¹ ^ 2) * (harmonic (2 * N) : ℝ) ^ 4) := by
  have hraw := allCharacter_doubleIntegral_weightedBlock_le
    d N hN true
      (shiftedReflectedBlockCoeff sigma (-(sigma + 1 / 2))) weight
      (fun n => continuous_shiftedReflectedBlockCoeff
        sigma (-(sigma + 1 / 2)) n)
      hweight hT hV hweight0
  simp_rw [shiftedReflectedDyadicBlock_eq_ramachandraDyadicBlock]
  apply hraw.trans
  let F : ℝ := (d : ℝ) * (2 * T) + 8 * Real.pi * (N : ℝ)
  let E : ℝ := ((N : ℝ)⁻¹ ^ 2) * (harmonic (2 * N) : ℝ) ^ 4
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have henergy (v : ℝ) :
      coefficientEnergy
          (shiftedReflectedBlockCoeff sigma (-(sigma + 1 / 2)) v) N ≤ E := by
    exact coefficientEnergy_negHalfReflectedBlockCoeff_le N hN sigma v
  have hpoint : ∀ v ∈ Set.Icc (-V) V,
      weight v * ramachandraDyadicCost d N T
          (shiftedReflectedBlockCoeff sigma (-(sigma + 1 / 2)) v) ≤
        weight v * (F * E) := by
    intro v hv
    unfold ramachandraDyadicCost
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (henergy v) hF) (hweight0 v hv)
  have hcostContinuous : Continuous (fun v =>
      ramachandraDyadicCost d N T
        (shiftedReflectedBlockCoeff sigma (-(sigma + 1 / 2)) v)) := by
    unfold ramachandraDyadicCost coefficientEnergy
    apply continuous_const.mul
    apply continuous_finsetSum
    intro n hn
    exact (continuous_shiftedReflectedBlockCoeff
      sigma (-(sigma + 1 / 2)) n).norm.pow 2
  calc
    (∫ v in (-V)..V,
      weight v * ramachandraDyadicCost d N T
        (shiftedReflectedBlockCoeff sigma (-(sigma + 1 / 2)) v)) ≤
        ∫ v in (-V)..V, weight v * (F * E) := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact (hweight.mul hcostContinuous).intervalIntegrable _ _
      · exact (hweight.mul continuous_const).intervalIntegrable _ _
      · exact hpoint
    _ = (F * E) * ∫ v in (-V)..V, weight v := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext v
      ring
    _ ≤ (F * E) * W :=
      mul_le_mul_of_nonneg_left hweightMass (mul_nonneg hF hE)
    _ = W * (((d : ℝ) * (2 * T) + 8 * Real.pi * (N : ℝ)) *
        ((N : ℝ)⁻¹ ^ 2) * (harmonic (2 * N) : ℝ) ^ 4) := by
      dsimp [F, E]
      ring

/-- Sharp continuous-Mellin block budget on the short workaround line
`Re(s+w)=0`, retaining the literal `N⁻¹` coefficient saving. -/
theorem allCharacter_doubleIntegral_zeroLineReflectedDyadicBlock_le
    (d N : ℕ) [NeZero d] (hN : 1 ≤ N)
    {T V sigma W : ℝ}
    (weight : ℝ → ℝ)
    (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hweight : Continuous weight)
    (hweight0 : ∀ v ∈ Set.Icc (-V) V, 0 ≤ weight v)
    (hweightMass : (∫ v in (-V)..V, weight v) ≤ W) :
    (∑ psi : DirichletCharacter ℂ d,
      ∫ t in (-T)..T,
        ∫ v in (-V)..V,
          weight v *
            ‖shiftedReflectedDyadicBlock psi N sigma (-sigma) v t‖ ^ 2) ≤
      W * (((d : ℝ) * (2 * T) + 8 * Real.pi * (N : ℝ)) *
        (N : ℝ)⁻¹ * (harmonic (2 * N) : ℝ) ^ 4) := by
  have hraw := allCharacter_doubleIntegral_weightedBlock_le
    d N hN true
      (shiftedReflectedBlockCoeff sigma (-sigma)) weight
      (fun n => continuous_shiftedReflectedBlockCoeff sigma (-sigma) n)
      hweight hT hV hweight0
  simp_rw [shiftedReflectedDyadicBlock_eq_ramachandraDyadicBlock]
  apply hraw.trans
  let F : ℝ := (d : ℝ) * (2 * T) + 8 * Real.pi * (N : ℝ)
  let E : ℝ := (N : ℝ)⁻¹ * (harmonic (2 * N) : ℝ) ^ 4
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have henergy (v : ℝ) :
      coefficientEnergy
          (shiftedReflectedBlockCoeff sigma (-sigma) v) N ≤ E := by
    exact coefficientEnergy_zeroLineReflectedBlockCoeff_le N hN sigma v
  have hpoint : ∀ v ∈ Set.Icc (-V) V,
      weight v * ramachandraDyadicCost d N T
          (shiftedReflectedBlockCoeff sigma (-sigma) v) ≤
        weight v * (F * E) := by
    intro v hv
    unfold ramachandraDyadicCost
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (henergy v) hF) (hweight0 v hv)
  have hcostContinuous : Continuous (fun v =>
      ramachandraDyadicCost d N T
        (shiftedReflectedBlockCoeff sigma (-sigma) v)) := by
    unfold ramachandraDyadicCost coefficientEnergy
    apply continuous_const.mul
    apply continuous_finsetSum
    intro n hn
    exact (continuous_shiftedReflectedBlockCoeff sigma (-sigma) n).norm.pow 2
  calc
    (∫ v in (-V)..V,
      weight v * ramachandraDyadicCost d N T
        (shiftedReflectedBlockCoeff sigma (-sigma) v)) ≤
        ∫ v in (-V)..V, weight v * (F * E) := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact (hweight.mul hcostContinuous).intervalIntegrable _ _
      · exact (hweight.mul continuous_const).intervalIntegrable _ _
      · exact hpoint
    _ = (F * E) * ∫ v in (-V)..V, weight v := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext v
      ring
    _ ≤ (F * E) * W :=
      mul_le_mul_of_nonneg_left hweightMass (mul_nonneg hF hE)
    _ = W * (((d : ℝ) * (2 * T) + 8 * Real.pi * (N : ℝ)) *
        (N : ℝ)⁻¹ * (harmonic (2 * N) : ℝ) ^ 4) := by
      dsimp [F, E]
      ring

end
end RamachandraShiftedReflectedBlockBudget

#print axioms RamachandraShiftedReflectedBlockBudget.allCharacter_doubleIntegral_shiftedReflectedDyadicBlock_le
#print axioms RamachandraShiftedReflectedBlockBudget.allCharacter_doubleIntegral_longReflectedDyadicBlock_le
#print axioms RamachandraShiftedReflectedBlockBudget.allCharacter_doubleIntegral_quarterLineReflectedDyadicBlock_le
#print axioms RamachandraShiftedReflectedBlockBudget.allCharacter_doubleIntegral_negHalfReflectedDyadicBlock_le
#print axioms RamachandraShiftedReflectedBlockBudget.allCharacter_doubleIntegral_zeroLineReflectedDyadicBlock_le
