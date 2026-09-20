import GuthMaynardS3MiddleNormalize
import GuthMaynardS3RectangleDyadicCover
import GuthMaynardWholeSupportPlancherelDomination

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory
noncomputable section
namespace GuthMaynardS3RectangleFourierEnergy
open GuthMaynardJIteration GuthMaynardS3BlockRectangle
open GuthMaynardS3MiddleNormalize GuthMaynardS3RectangleDyadicCover
open GuthMaynardS3LiteralTruncation

private lemma source_sum_nonneg (f : ℝ → ℝ) (hf : ∀ u, 0 ≤ f u)
    (R S U : Finset ℤ) (u : ℝ) : 0 ≤ sourceFiniteAffineSum R S U f u := by
  apply Finset.sum_nonneg
  intro m1 hm1
  apply Finset.sum_nonneg
  intro m2 hm2
  apply Finset.sum_nonneg
  intro m3 hm3
  exact hf _

/-- Only the third range is enlarged, to the source bump's unit plateau. -/
theorem coordinate_subset_centered (Mcut k : ℕ) :
    blockCoordinateRange Mcut k ⊆ sourceCenteredRange (16*2^k) := by
  intro m hm
  have ha := abs_le.mp (Finset.mem_filter.mp hm).2
  rw [mem_sourceCenteredRange_iff]
  constructor
  · exact_mod_cast ha.1
  · exact_mod_cast ha.2

private lemma source_sum_mono_third
    (f : ℝ → ℝ) (hf : ∀ u, 0 ≤ f u) (R S U V : Finset ℤ)
    (hUV : U ⊆ V) (u : ℝ) :
    sourceFiniteAffineSum R S U f u ≤ sourceFiniteAffineSum R S V f u := by
  apply Finset.sum_le_sum
  intro m1 hm1
  apply Finset.sum_le_sum
  intro m2 hm2
  exact Finset.sum_le_sum_of_subset_of_nonneg hUV (fun m3 _ _ => hf _)

/-- The literal rectangle is covered by positive-middle, dyadic-first,
centered-third source sums. -/
theorem rectangle_sum_le_two_dyadic_centered
    (f : ℝ → ℝ) (hf : ∀ u, 0 ≤ f u) (Mcut k : ℕ) (u : ℝ) :
    sourceFiniteAffineSum (blockCoordinateRange Mcut k) (blockMiddleRange Mcut k)
      (blockCoordinateRange Mcut k) f u ≤
      2 * ∑ j ∈ Finset.range (k+5),
        sourceFiniteAffineSum (sourceSignedDyadicRange (2^j))
          (sourcePositiveDyadicRange (2^k)) (sourceCenteredRange (16*2^k)) f u := by
  have hmid := block_sourceFiniteAffineSum_middle_le_two_positive Mcut k f u hf
  have hdyad := rectangle_positive_sum_le_dyadic f hf Mcut k u
  have hcenter :
      (∑ j ∈ Finset.range (k+5),
        sourceFiniteAffineSum (sourceSignedDyadicRange (2^j))
          (sourcePositiveDyadicRange (2^k)) (blockCoordinateRange Mcut k) f u) ≤
      ∑ j ∈ Finset.range (k+5),
        sourceFiniteAffineSum (sourceSignedDyadicRange (2^j))
          (sourcePositiveDyadicRange (2^k)) (sourceCenteredRange (16*2^k)) f u := by
    apply Finset.sum_le_sum
    intro j hj
    exact source_sum_mono_third f hf _ _ _ _ (coordinate_subset_centered Mcut k) u
  exact hmid.trans (mul_le_mul_of_nonneg_left (hdyad.trans hcenter) (by norm_num))

/-- The only new finite Cauchy loss is the number of dyadic first-coordinate
bins, not the number of frequencies in any rectangle. -/
theorem rectangle_sq_le_four_bins_sum_sq
    (f : ℝ → ℝ) (hf : ∀ u, 0 ≤ f u) (Mcut k : ℕ) (u : ℝ) :
    sourceFiniteAffineSum (blockCoordinateRange Mcut k) (blockMiddleRange Mcut k)
      (blockCoordinateRange Mcut k) f u ^ 2 ≤
      4 * (k+5 : ℝ) * ∑ j ∈ Finset.range (k+5),
        sourceFiniteAffineSum (sourceSignedDyadicRange (2^j))
          (sourcePositiveDyadicRange (2^k)) (sourceCenteredRange (16*2^k)) f u ^ 2 := by
  let A : ℕ → ℝ := fun j => sourceFiniteAffineSum (sourceSignedDyadicRange (2^j))
    (sourcePositiveDyadicRange (2^k)) (sourceCenteredRange (16*2^k)) f u
  have h0 := source_sum_nonneg f hf (blockCoordinateRange Mcut k)
    (blockMiddleRange Mcut k) (blockCoordinateRange Mcut k) u
  have hs := pow_le_pow_left₀ h0 (rectangle_sum_le_two_dyadic_centered f hf Mcut k u) 2
  have hcs : (∑ j ∈ Finset.range (k+5), A j)^2 ≤
      (k+5 : ℝ) * ∑ j ∈ Finset.range (k+5), (A j)^2 := by
    simpa using (Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (k+5))
      (fun _ : ℕ => (1 : ℝ)) A)
  have hscale := mul_le_mul_of_nonneg_left hcs (by norm_num : (0 : ℝ) ≤ 4)
  change _ ≤ 4 * (k+5 : ℝ) * ∑ j ∈ Finset.range (k+5), (A j)^2
  change _ ≤ (2 * ∑ j ∈ Finset.range (k+5), A j)^2 at hs
  nlinarith [hs,hscale]

/-- Integrated literal rectangle bound by the centered source-energy family. -/
theorem rectangle_energy_le_four_bins_centered_energy
    {T S F : ℝ} {f : ℝ → ℝ} (hf : SourceAdmissibleProfile T S F f)
    (Mcut k : ℕ) :
    sourceFiniteAffineEnergy (blockCoordinateRange Mcut k) (blockMiddleRange Mcut k)
      (blockCoordinateRange Mcut k) f ≤
      4 * (k+5 : ℝ) * ∑ j ∈ Finset.range (k+5),
        sourceFiniteAffineEnergy (sourceSignedDyadicRange (2^j))
          (sourcePositiveDyadicRange (2^k)) (sourceCenteredRange (16*2^k)) f := by
  have hR : ∀ m ∈ blockCoordinateRange Mcut k, m ≠ 0 := by
    intro m hm
    exact nonzeroPrefix_ne_zero (Finset.mem_filter.mp hm).1
  have hS : ∀ m ∈ blockMiddleRange Mcut k, m ≠ 0 := by
    intro m hm
    exact nonzeroPrefix_ne_zero (Finset.mem_filter.mp hm).1
  have hleft := integrable_sq_sourceFiniteAffineSum (blockCoordinateRange Mcut k)
    (blockMiddleRange Mcut k) (blockCoordinateRange Mcut k) f
    hf.continuous hf.squareIntegrable hR hS
  have hterms : ∀ j ∈ Finset.range (k+5), Integrable (fun u : ℝ =>
      sourceFiniteAffineSum (sourceSignedDyadicRange (2^j))
        (sourcePositiveDyadicRange (2^k)) (sourceCenteredRange (16*2^k)) f u ^ 2) := by
    intro j hj
    exact integrable_sq_sourceFiniteAffineSum _ _ _ f hf.continuous hf.squareIntegrable
      (fun m hm => sourceSignedDyadicRange_ne_zero (by positivity) hm)
      (fun m hm => sourcePositiveDyadicRange_ne_zero (by positivity) hm)
  have hright := (integrable_finsetSum (Finset.range (k+5)) hterms).const_mul (4*(k+5 : ℝ))
  have hh := integral_mono hleft hright (rectangle_sq_le_four_bins_sum_sq f hf.nonneg Mcut k)
  rw [integral_const_mul, integral_finsetSum _ hterms] at hh
  exact hh

/-- Exact source Plancherel insertion for every dyadic bin. The complete
radius-two bump support is retained. -/
theorem rectangle_energy_le_four_bins_fourier_energy
    {T S F : ℝ} {f : ℝ → ℝ} (hf : SourceAdmissibleProfile T S F f)
    (hT : 0 ≤ T) (Mcut k : ℕ) :
    sourceFiniteAffineEnergy (blockCoordinateRange Mcut k) (blockMiddleRange Mcut k)
      (blockCoordinateRange Mcut k) f ≤
      4 * (k+5 : ℝ) * ∑ j ∈ Finset.range (k+5),
        ∫ xi : ℝ,
          ‖FourierTransform.fourier
            (sourceGFinite (sourceSignedDyadicRange (2^j))
              (sourcePositiveDyadicRange (2^k))
              (sourceIntegerWindow 0 (2 * ((16*2^k : ℕ) : ℝ)))
              (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
              (fun u : ℝ => (f u : ℂ)) ((16*2^k : ℕ) : ℝ)) xi‖^2 := by
  have hcenter := rectangle_energy_le_four_bins_centered_energy hf Mcut k
  have hsum := Finset.sum_le_sum (s:=Finset.range (k+5)) (fun j hj =>
    sourceCenteredAffineEnergy_le_wholeSupport_fourierIntegral_of_sourceProfile
      hf (eta:=1) (by norm_num) hT
      (M1:=2^j) (M2:=2^k) (M3:=16*2^k) (by positivity) (by positivity) (by positivity))
  exact hcenter.trans (mul_le_mul_of_nonneg_left hsum (by positivity))

end GuthMaynardS3RectangleFourierEnergy
#print axioms GuthMaynardS3RectangleFourierEnergy.rectangle_energy_le_four_bins_fourier_energy
