import GuthMaynardS3FullUniform
import GuthMaynardWholeSupportPlancherelDomination

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory
noncomputable section
namespace GuthMaynardS3PositiveFourierBridge
open GuthMaynardJIteration

/-- The positive first-coordinate rectangle is dominated by the literal signed
rectangle used in the source Plancherel theorem. -/
theorem positive_energy_le_signed
    {T S F : ℝ} {f : ℝ → ℝ} (hf : SourceAdmissibleProfile T S F f)
    {M1 M2 M3 : ℕ} (hM1 : 0 < M1) (hM2 : 0 < M2) :
    sourceFiniteAffineEnergy (sourcePositiveDyadicRange M1)
      (sourcePositiveDyadicRange M2) (sourceCenteredRange M3) f ≤
    sourceFiniteAffineEnergy (sourceSignedDyadicRange M1)
      (sourcePositiveDyadicRange M2) (sourceCenteredRange M3) f := by
  have hp : sourcePositiveDyadicRange M1 ⊆ sourceSignedDyadicRange M1 := by
    exact Finset.subset_union_right
  have hi := integrable_sq_sourceFiniteAffineSum (sourcePositiveDyadicRange M1)
    (sourcePositiveDyadicRange M2) (sourceCenteredRange M3) f
    hf.continuous hf.squareIntegrable
    (fun m hm => sourcePositiveDyadicRange_ne_zero hM1 hm)
    (fun m hm => sourcePositiveDyadicRange_ne_zero hM2 hm)
  have hj := integrable_sq_sourceFiniteAffineSum (sourceSignedDyadicRange M1)
    (sourcePositiveDyadicRange M2) (sourceCenteredRange M3) f
    hf.continuous hf.squareIntegrable
    (fun m hm => sourceSignedDyadicRange_ne_zero hM1 hm)
    (fun m hm => sourcePositiveDyadicRange_ne_zero hM2 hm)
  apply integral_mono hi hj
  intro u
  apply pow_le_pow_left₀
  · unfold sourceFiniteAffineSum
    exact Finset.sum_nonneg (fun m _ => Finset.sum_nonneg (fun n _ =>
      Finset.sum_nonneg (fun j _ => hf.nonneg _)))
  · unfold sourceFiniteAffineSum
    exact Finset.sum_le_sum_of_subset_of_nonneg hp
      (fun m _ _ => Finset.sum_nonneg (fun n _ =>
        Finset.sum_nonneg (fun j _ => hf.nonneg _)))

theorem positive_energy_le_whole_fourier
    {T S F : ℝ} {f : ℝ → ℝ} (hf : SourceAdmissibleProfile T S F f)
    (hT : 0 ≤ T) {M1 M2 M3 : ℕ}
    (hM1 : 0 < M1) (hM2 : 0 < M2) (hM3 : 0 < M3) :
    sourceFiniteAffineEnergy (sourcePositiveDyadicRange M1)
      (sourcePositiveDyadicRange M2) (sourceCenteredRange M3) f ≤
    ∫ xi : ℝ, ‖FourierTransform.fourier
      (sourceGFinite (sourceSignedDyadicRange M1) (sourcePositiveDyadicRange M2)
        (sourceBumpEllRange 1 (M3 : ℝ) 1)
        (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
        (fun u : ℝ => (f u : ℂ)) (M3 : ℝ)) xi‖^2 := by
  have hh := (positive_energy_le_signed hf hM1 hM2 (M3 := M3)).trans
    (sourceCenteredAffineEnergy_le_wholeSupport_fourierIntegral_of_sourceProfile
      hf (eta := 1) (by norm_num) hT hM1 hM2 hM3)
  simpa only [sourceBumpEllRange, Nat.cast_one, mul_one, div_one] using hh

end GuthMaynardS3PositiveFourierBridge
#print axioms GuthMaynardS3PositiveFourierBridge.positive_energy_le_whole_fourier
