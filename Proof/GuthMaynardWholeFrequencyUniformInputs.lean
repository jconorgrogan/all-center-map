import GuthMaynardLemma92ThreeScaleFrequencyInputs
import GuthMaynardJIterationSourceFourierDecay

/-!
# Uniform source inputs for the corrected whole-frequency theorem

These are the two pointwise inputs shared by regions I and II: the normalized
phase bound and a Fourier-inner bound valid also at `xi=0`.  The latter uses
the elementary `L¹` Fourier bound instead of rapid decay, whose source theorem
requires nonzero frequency.
-/

open scoped BigOperators Real FourierTransform
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-- The low-frequency counterpart of the existing region-II normalized phase
bound. -/
theorem abs_div_le_of_mem_lowFrequencyRegion
    {a M1 : ℝ} (hM1 : 0 < M1) {xi : ℝ}
    (hxi : xi ∈ lowFrequencyRegion a) {m1 : ℤ}
    (hm1 : M1 ≤ |(m1 : ℝ)|) :
    |xi / (m1 : ℝ)| ≤ a / M1 := by
  have hm1pos : 0 < |(m1 : ℝ)| := lt_of_lt_of_le hM1 hm1
  rw [abs_div]
  exact div_le_div₀ (le_trans (abs_nonneg _) hxi) hxi hM1 hm1

/-- One common `T^6/M₁` phase budget serves both source regions I and II. -/
theorem sourceLowMedium_abs_div_le_highCutoff
    (m1Range : Finset ℤ) {M1 : ℝ} (hM1 : 0 < M1)
    {T a : ℝ} (ha : a ≤ sourceHighFrequencyCutoff T)
    (hm1lo : ∀ m1 ∈ m1Range, M1 ≤ |(m1 : ℝ)|) :
    (∀ xi ∈ lowFrequencyRegion a, ∀ m1 ∈ m1Range,
      |xi / (m1 : ℝ)| ≤ sourceHighFrequencyCutoff T / M1) ∧
    (∀ xi ∈ mediumFrequencyRegion a (sourceHighFrequencyCutoff T),
      ∀ m1 ∈ m1Range,
      |xi / (m1 : ℝ)| ≤ sourceHighFrequencyCutoff T / M1) := by
  constructor
  · intro xi hxi m1 hm1
    exact (abs_div_le_of_mem_lowFrequencyRegion hM1 hxi
      (hm1lo m1 hm1)).trans
        (div_le_div_of_nonneg_right ha hM1.le)
  · intro xi hxi m1 hm1
    exact abs_div_le_of_mem_mediumFrequencyRegion hM1 hxi (hm1lo m1 hm1)

/-- Elementary Fourier `L¹` estimate in the exact normalization used by the
source profile. -/
theorem norm_fourier_ofReal_le_integral_norm
    (f : ℝ → ℝ) (xi : ℝ) :
    ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) xi‖ ≤
      ∫ u : ℝ, ‖(f u : ℂ)‖ := by
  exact VectorFourier.norm_fourierIntegral_le_integral_norm
    𝐞 volume (innerₗ ℝ) (fun u : ℝ => (f u : ℂ)) xi

/-- Uniform corrected-inner estimate, including the origin.  This is the
appropriate region-I envelope; no illegal use of nonzero-frequency rapid
decay occurs. -/
theorem norm_sourceCorrectedM2FourierInner_le_integral_norm
    (m2Range : Finset ℤ) (f : ℝ → ℝ) (m1 : ℤ) (xi : ℝ)
    {N2 Rhi : ℝ} (hN2 : (m2Range.card : ℝ) ≤ N2)
    (hRhi : 0 ≤ Rhi)
    (hratioHi : ∀ m2 ∈ m2Range,
      |((m2 : ℝ) / (m1 : ℝ))| ≤ Rhi) :
    ‖sourceCorrectedM2FourierInner m2Range
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ))) m1 xi‖ ≤
      N2 * Rhi * (∫ u : ℝ, ‖(f u : ℂ)‖) := by
  have hL1 : 0 ≤ ∫ u : ℝ, ‖(f u : ℂ)‖ :=
    integral_nonneg fun _ => norm_nonneg _
  unfold sourceCorrectedM2FourierInner
  calc
    ‖∑ m2 ∈ m2Range,
        ((|((m2 : ℝ) / (m1 : ℝ))| : ℝ) : ℂ) *
          FourierTransform.fourier (fun u : ℝ => (f u : ℂ))
            (((m2 : ℝ) / (m1 : ℝ)) * xi)‖ ≤
      ∑ m2 ∈ m2Range,
        ‖((|((m2 : ℝ) / (m1 : ℝ))| : ℝ) : ℂ) *
          FourierTransform.fourier (fun u : ℝ => (f u : ℂ))
            (((m2 : ℝ) / (m1 : ℝ)) * xi)‖ := norm_sum_le _ _
    _ ≤ ∑ _m2 ∈ m2Range,
        Rhi * (∫ u : ℝ, ‖(f u : ℂ)‖) := by
      apply Finset.sum_le_sum
      intro m2 hm2
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (abs_nonneg _)]
      exact mul_le_mul (hratioHi m2 hm2)
        (norm_fourier_ofReal_le_integral_norm f _)
        (norm_nonneg _) hRhi
    _ = (m2Range.card : ℝ) *
        (Rhi * (∫ u : ℝ, ‖(f u : ℂ)‖)) := by simp
    _ ≤ N2 * Rhi * (∫ u : ℝ, ‖(f u : ℂ)‖) := by
      calc
        (m2Range.card : ℝ) *
            (Rhi * (∫ u : ℝ, ‖(f u : ℂ)‖)) ≤
          N2 * (Rhi * (∫ u : ℝ, ‖(f u : ℂ)‖)) :=
            mul_le_mul_of_nonneg_right hN2 (mul_nonneg hRhi hL1)
        _ = _ := by ring

/-- Both region-I and region-II pointwise-inner premises are therefore
inhabited by the same exact finite `L¹` envelope. -/
theorem sourceCorrectedM2FourierInner_lowMedium_le_integral_norm
    (m1Range m2Range : Finset ℤ) (f : ℝ → ℝ)
    {a b N2 Rhi : ℝ} (hN2 : (m2Range.card : ℝ) ≤ N2)
    (hRhi : 0 ≤ Rhi)
    (hratioHi : ∀ m1 ∈ m1Range, ∀ m2 ∈ m2Range,
      |((m2 : ℝ) / (m1 : ℝ))| ≤ Rhi) :
    (∀ xi ∈ lowFrequencyRegion a, ∀ m1 ∈ m1Range,
      ‖sourceCorrectedM2FourierInner m2Range
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ))) m1 xi‖ ≤
        N2 * Rhi * (∫ u : ℝ, ‖(f u : ℂ)‖)) ∧
    (∀ xi ∈ mediumFrequencyRegion a b, ∀ m1 ∈ m1Range,
      ‖sourceCorrectedM2FourierInner m2Range
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ))) m1 xi‖ ≤
        N2 * Rhi * (∫ u : ℝ, ‖(f u : ℂ)‖)) := by
  constructor <;> intro xi hxi m1 hm1 <;>
    exact norm_sourceCorrectedM2FourierInner_le_integral_norm
      m2Range f m1 xi hN2 hRhi (hratioHi m1 hm1)

#print axioms GuthMaynardJIteration.abs_div_le_of_mem_lowFrequencyRegion
#print axioms GuthMaynardJIteration.sourceLowMedium_abs_div_le_highCutoff
#print axioms GuthMaynardJIteration.norm_fourier_ofReal_le_integral_norm
#print axioms GuthMaynardJIteration.norm_sourceCorrectedM2FourierInner_le_integral_norm
#print axioms GuthMaynardJIteration.sourceCorrectedM2FourierInner_lowMedium_le_integral_norm

end GuthMaynardJIteration
