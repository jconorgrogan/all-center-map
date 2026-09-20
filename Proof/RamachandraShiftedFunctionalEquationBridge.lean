import RamachandraShiftedGammaPoleContour
import RamachandraShiftedReflectedBlockBudget
import HuxleyPrimitiveFunctionalEquation

/-!
# Functional-equation bridge for Ramachandra's shifted contour

This module identifies the left vertical line produced by the certified
Gamma-pole displacement with Ramachandra's literal reflected series.  The
character, root number, conductor power, and parity-dependent Gamma quotient
are kept exact.
-/

namespace RamachandraShiftedFunctionalEquationBridge

open Complex MeasureTheory
open scoped BigOperators LSeries.notation
open BHPRamachandraMeanValueFromDyadicAFE
open RamachandraPrimitiveShiftedContourReduction
open RamachandraShiftedGammaPoleContour
open RamachandraShiftedRightLineIdentity
open MAPHuxleyPrimitiveFunctionalEquation

noncomputable section

set_option maxHeartbeats 800000

/-- The ordinary primitive functional equation in exactly the orientation
used by Ramachandra's reflected contour. -/
theorem LFunction_eq_ramachandraFunctionalFactor_mul_dual
    {d : ℕ} [NeZero d] {psi : DirichletCharacter ℂ d}
    (hprim : psi.IsPrimitive) (hpsi : psi ≠ 1)
    {z : ℂ} (hz : 0 < (1 - z).re) :
    DirichletCharacter.LFunction psi z =
      ramachandraFunctionalFactor psi z *
        DirichletCharacter.LFunction psi⁻¹ (1 - z) := by
  have hfe := LFunction_one_sub_eq_huxleyFactor
    (χ := psi) hprim hpsi (s := 1 - z) hz
  have hone : (1 : ℂ) - (1 - z) = z := by ring
  rw [hone] at hfe
  rw [hfe]
  unfold ramachandraFunctionalFactor
  ring_nf

/-- Squared functional equation, the exact factor entering Lemma 3. -/
theorem LFunction_sq_eq_ramachandraFunctionalFactor_sq_mul_dual_sq
    {d : ℕ} [NeZero d] {psi : DirichletCharacter ℂ d}
    (hprim : psi.IsPrimitive) (hpsi : psi ≠ 1)
    {z : ℂ} (hz : 0 < (1 - z).re) :
    DirichletCharacter.LFunction psi z ^ 2 =
      ramachandraFunctionalFactor psi z ^ 2 *
        DirichletCharacter.LFunction psi⁻¹ (1 - z) ^ 2 := by
  rw [LFunction_eq_ramachandraFunctionalFactor_mul_dual hprim hpsi hz]
  ring

/-- Absolute convergence of the full reflected divisor series. -/
theorem summable_ramachandraReflectedTerm
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    {z : ℂ} (hz : 1 < (1 - z).re) :
    Summable (fun n : ℕ => ramachandraReflectedTerm psi z n) := by
  unfold ramachandraReflectedTerm
  exact LSeriesSummable_ramachandraDivisorCoeff psi⁻¹ hz

/-- The two source cutoffs form an exact partition of the full reflected
Dirichlet series, including the endpoint convention at `n = X`. -/
theorem ramachandraReflectedTail_add_head_eq_LFunction_sq
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    {X : ℝ} {z : ℂ} (hz : 1 < (1 - z).re) :
    ramachandraReflectedTail psi X z +
        ramachandraReflectedHead psi X z =
      DirichletCharacter.LFunction psi⁻¹ (1 - z) ^ 2 := by
  have hsum := summable_ramachandraReflectedTerm psi hz
  have htail : Summable (fun n : ℕ =>
      if X < (n : ℝ) then ramachandraReflectedTerm psi z n else 0) := by
    simpa [Set.indicator] using
      hsum.indicator ({n : ℕ | X < (n : ℝ)} : Set ℕ)
  have hhead : Summable (fun n : ℕ =>
      if (n : ℝ) ≤ X then ramachandraReflectedTerm psi z n else 0) := by
    simpa [Set.indicator] using
      hsum.indicator ({n : ℕ | (n : ℝ) ≤ X} : Set ℕ)
  unfold ramachandraReflectedTail ramachandraReflectedHead
  rw [← htail.tsum_add hhead]
  calc
    (∑' n : ℕ, (
        (if X < (n : ℝ) then ramachandraReflectedTerm psi z n else 0) +
          (if (n : ℝ) ≤ X then ramachandraReflectedTerm psi z n else 0))) =
        ∑' n : ℕ, ramachandraReflectedTerm psi z n := by
      apply tsum_congr
      intro n
      by_cases hn : X < (n : ℝ)
      · simp [hn, not_le.mpr hn]
      · simp [hn, le_of_not_gt hn]
    _ = LSeries (ramachandraDivisorCoeff psi⁻¹) (1 - z) := rfl
    _ = DirichletCharacter.LFunction psi⁻¹ (1 - z) ^ 2 :=
      LSeries_ramachandraDivisorCoeff_eq_LFunction_sq psi⁻¹ hz

/-- Pointwise identification of the functional-equation image of the raw
left-line integrand with the sum of Ramachandra's literal head and tail
integrands. -/
theorem shiftedGammaRawIntegrand_eq_reflectedTail_add_head
    {d : ℕ} [NeZero d] {psi : DirichletCharacter ℂ d}
    (hprim : psi.IsPrimitive) (hpsi : psi ≠ 1)
    {s w : ℂ} {X : ℝ} (hz : 1 < (1 - (s + w)).re) :
    shiftedGammaRawIntegrand psi s X w =
      ramachandraFunctionalFactor psi (s + w) ^ 2 *
          ramachandraReflectedTail psi X (s + w) *
            Complex.Gamma w * (X : ℂ) ^ w +
        ramachandraFunctionalFactor psi (s + w) ^ 2 *
          ramachandraReflectedHead psi X (s + w) *
            Complex.Gamma w * (X : ℂ) ^ w := by
  unfold shiftedGammaRawIntegrand
  rw [LFunction_sq_eq_ramachandraFunctionalFactor_sq_mul_dual_sq
    hprim hpsi (lt_trans (by norm_num) hz)]
  rw [← ramachandraReflectedTail_add_head_eq_LFunction_sq psi hz]
  ring

/-- On Ramachandra's long line `u = -(sigma+1/4)`, the raw contour image is
pointwise exactly the sum of the literal long-tail and long-head integrands.
This is the equality before the head is displaced to the near line. -/
theorem shiftedGammaRawIntegrand_longLine_eq_shiftedContour_tail_add_head
    {d : ℕ} [NeZero d] {psi : DirichletCharacter ℂ d}
    (hprim : psi.IsPrimitive) (hpsi : psi ≠ 1)
    (X sigma t v : ℝ) :
    shiftedGammaRawIntegrand psi (ramachandraShiftedPoint sigma t) X
        (((-(sigma + 1 / 4) : ℝ) : ℂ) + v * I) =
      ramachandraShiftedContourIntegrand psi X sigma
          (-(sigma + 1 / 4)) t v true +
        ramachandraShiftedContourIntegrand psi X sigma
          (-(sigma + 1 / 4)) t v false := by
  let s : ℂ := ramachandraShiftedPoint sigma t
  let w : ℂ := (((-(sigma + 1 / 4) : ℝ) : ℂ) + v * I)
  have hz : 1 < (1 - (s + w)).re := by
    dsimp [s, w, ramachandraShiftedPoint]
    norm_num
  have h := shiftedGammaRawIntegrand_eq_reflectedTail_add_head
    hprim hpsi (X := X) hz
  simpa [s, w, ramachandraShiftedContourIntegrand] using h

end
end RamachandraShiftedFunctionalEquationBridge

#print axioms RamachandraShiftedFunctionalEquationBridge.LFunction_eq_ramachandraFunctionalFactor_mul_dual
#print axioms RamachandraShiftedFunctionalEquationBridge.ramachandraReflectedTail_add_head_eq_LFunction_sq
#print axioms RamachandraShiftedFunctionalEquationBridge.shiftedGammaRawIntegrand_eq_reflectedTail_add_head
#print axioms RamachandraShiftedFunctionalEquationBridge.shiftedGammaRawIntegrand_longLine_eq_shiftedContour_tail_add_head
