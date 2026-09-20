import GuthMaynardS3DenominatorDilation

open scoped BigOperators Real
open MeasureTheory
noncomputable section
namespace GuthMaynardS3DilatedRectangleConsumer
open GuthMaynardJIteration GuthMaynardS3BlockRectangle
open GuthMaynardS3DenominatorDilation GuthMaynardS3RectangleFourierEnergy

/-- Every first-coordinate bin created by the literal dilation fits the
uniform signed-energy theorem's `M1 ≤ 16*M2` hypothesis. -/
theorem dilated_bin_le_sixteen_middle {k j : ℕ}
    (hj : j ∈ Finset.range (k+7)) : 2^j ≤ 16*2^(k+2) := by
  have hj' : j ≤ k+6 := by have hh := Finset.mem_range.mp hj; omega
  calc
    2^j ≤ 2^(k+6) := Nat.pow_le_pow_right (by norm_num) hj'
    _ = 16*2^(k+2) := by simp [pow_add]; ring

/-- Explicit finite consumer: a uniform signed-bin energy bound yields the
original, undilated source rectangle bound with its exact bin multiplier. -/
theorem rectangle_energy_le_of_dilated_signed_bound
    {T S F V : ℝ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S F (fun v => f (4*v))) (A k : ℕ)
    (hbin : ∀ j ∈ Finset.range (k+7),
      sourceFiniteAffineEnergy (sourceSignedDyadicRange (2^j))
        (sourcePositiveDyadicRange (2^(k+2)))
        (sourceCenteredRange (16*2^(k+2))) (fun v => f (4*v)) ≤ V) :
    sourceFiniteAffineEnergy (blockCoordinateRange A k) (blockMiddleRange A k)
      (blockCoordinateRange A k) f ≤ 4*(k+7 : ℝ)^2*V := by
  have hscale := rectangle_energy_le_dilated hf A k
  have hcover := rectangle_energy_le_four_bins_centered_energy hf (4*A) (k+2)
  have hsum : (∑ j ∈ Finset.range (k+7),
      sourceFiniteAffineEnergy (sourceSignedDyadicRange (2^j))
        (sourcePositiveDyadicRange (2^(k+2)))
        (sourceCenteredRange (16*2^(k+2))) (fun v => f (4*v))) ≤
      (k+7 : ℝ)*V := by
    calc
      _ ≤ ∑ j ∈ Finset.range (k+7), V := Finset.sum_le_sum hbin
      _ = _ := by simp
  have hcover' : sourceFiniteAffineEnergy (blockCoordinateRange (4*A) (k+2))
      (blockMiddleRange (4*A) (k+2)) (blockCoordinateRange (4*A) (k+2))
      (fun v => f (4*v)) ≤ 4*(k+7 : ℝ)^2*V := by
    have hh := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 4*(k+7 : ℝ))
    have heq : k+2+5=k+7 := by omega
    simp only [heq] at hcover
    push_cast at hcover
    calc
      _ ≤ _ := hcover
      _ ≤ _ := by nlinarith [hh]
  exact hscale.trans hcover'

end GuthMaynardS3DilatedRectangleConsumer
#print axioms GuthMaynardS3DilatedRectangleConsumer.dilated_bin_le_sixteen_middle
#print axioms GuthMaynardS3DilatedRectangleConsumer.rectangle_energy_le_of_dilated_signed_bound
