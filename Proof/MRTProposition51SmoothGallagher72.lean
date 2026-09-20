import MRTFaithfulSmoothCutoff
import MRTProposition51Duality72
import GuthMaynardJIterationFirstPoissonFourierShift
import L1L2PlancherelBridge

/-!
# Faithful smooth Gallagher reduction for MRT equation (72)

One smooth cutoff is used in the initial Plancherel field and later in the
logarithmic dual function.  This repairs the sharp/smooth mismatch in the old
staging route.
-/

namespace MAPMRTProposition51SmoothGallagher72

open MeasureTheory Set
open scoped BigOperators FourierTransform
open MAPMRTProposition51Source MAPMRTProposition51FirstAnalytic
open MAPMRTFaithfulSmoothCutoff MAPGallagherPlancherel
open MAPMRTProposition51HardBranch
open GuthMaynardJIteration MAPMRTCorollary53Source

noncomputable section

/-- Smooth spatial atom `φ((n-x)/H)`. -/
def smoothCoefficientAtom (H : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  (faithfulCutoff (((n : ℝ) - x) / H) : ℂ)

/-- The exact smooth field paired with `g` in MRT equation (72). -/
def smoothCoefficientField
    (X H beta : ℝ) (f : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
    realPhaseTwist beta f n * smoothCoefficientAtom H n x

theorem continuous_smoothCoefficientAtom
    {H : ℝ} (n : ℕ) : Continuous (smoothCoefficientAtom H n) := by
  unfold smoothCoefficientAtom
  exact Complex.continuous_ofReal.comp
    (faithfulCutoff_continuous.comp (by fun_prop))

theorem smoothCoefficientAtom_eq_zero_off
    {H x : ℝ} {n : ℕ} (hH : 0 < H)
    (hx : x ∉ Icc ((n : ℝ) - H / 8) ((n : ℝ) + H / 8)) :
    smoothCoefficientAtom H n x = 0 := by
  unfold smoothCoefficientAtom
  apply congrArg Complex.ofReal
  apply faithfulCutoff_zero
  rw [abs_div, abs_of_pos hH]
  apply (le_div_iff₀ hH).2
  simp only [mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · rw [abs_of_nonneg (by linarith)]
    linarith
  · rw [abs_of_nonpos (by linarith)]
    linarith

theorem integrable_smoothCoefficientAtom
    {H : ℝ} (n : ℕ) (hH : 0 < H) :
    Integrable (smoothCoefficientAtom H n) := by
  apply (continuous_smoothCoefficientAtom n).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact
      (Icc ((n : ℝ) - H / 8) ((n : ℝ) + H / 8)))
  intro x hx
  by_contra hout
  exact hx (smoothCoefficientAtom_eq_zero_off hH hout)

theorem integrable_smoothCoefficientField
    {X H beta : ℝ} (f : ℕ → ℂ) (hH : 0 < H) :
    Integrable (smoothCoefficientField X H beta f) := by
  unfold smoothCoefficientField
  apply integrable_finset_sum
  intro n hn
  exact (integrable_smoothCoefficientAtom n hH).const_mul
    (realPhaseTwist beta f n)

theorem continuous_smoothCoefficientField
    (X H beta : ℝ) (f : ℕ → ℂ) :
    Continuous (smoothCoefficientField X H beta f) := by
  unfold smoothCoefficientField
  apply continuous_finset_sum
  intro n hn
  exact continuous_const.mul (continuous_smoothCoefficientAtom n)

theorem norm_smoothCoefficientField_le
    (X H beta x : ℝ) (f : ℕ → ℂ) :
    ‖smoothCoefficientField X H beta f x‖ ≤ coefficientMass X f := by
  unfold smoothCoefficientField coefficientMass
  calc
    ‖∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        realPhaseTwist beta f n * smoothCoefficientAtom H n x‖ ≤
      ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        ‖realPhaseTwist beta f n * smoothCoefficientAtom H n x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, ‖f n‖ := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, norm_realPhaseTwist]
      unfold smoothCoefficientAtom
      rw [Complex.norm_real, Real.norm_eq_abs]
      nlinarith [abs_faithfulCutoff_le_one (((n : ℝ) - x) / H),
        norm_nonneg (f n)]

theorem memLp_two_smoothCoefficientField
    {X H beta : ℝ} (f : ℕ → ℂ) (hH : 0 < H) :
    MemLp (smoothCoefficientField X H beta f) 2 := by
  exact MAPNearCollarGallagher.memLp_two_of_integrable_of_norm_le
    (integrable_smoothCoefficientField f hH)
    (coefficientMass_nonneg X f)
    (norm_smoothCoefficientField_le X H beta · f)

/-- Exact Fourier transform of one smooth atom. -/
theorem fourier_smoothCoefficientAtom
    {H : ℝ} (hH : 0 < H) (n : ℕ) (xi : ℝ) :
    (𝓕 (smoothCoefficientAtom H n)) xi =
      sourcePhase (-((n : ℝ) * xi)) *
        ((H : ℂ) * cutoffFourierKernel faithfulCutoff (-H * xi)) := by
  have h := source_fourier_affine_shift
    (fun y : ℝ ↦ (faithfulCutoff y : ℂ))
    (m1 := (-1 : ℝ)) (m2 := H) (by norm_num) hH.ne'
    (n : ℝ) xi
  change (𝓕 (fun u : ℝ ↦
    (faithfulCutoff (((n : ℝ) - u) / H) : ℂ))) xi = _
  have hfun : (fun u : ℝ ↦
      (faithfulCutoff (((n : ℝ) - u) / H) : ℂ)) =
      fun u : ℝ ↦ (faithfulCutoff ((-1 * u + (n : ℝ)) / H) : ℂ) := by
    funext u
    congr 2
    ring
  rw [hfun, h]
  congr 1
  · congr 1
    ring
  · unfold cutoffFourierKernel
    rw [abs_div, abs_neg, abs_one, div_one, abs_of_pos hH]
    push_cast
    ring

private theorem realPhaseTwist_mul_sourcePhase
    (beta xi : ℝ) (f : ℕ → ℂ) (n : ℕ) :
    realPhaseTwist beta f n * sourcePhase (-((n : ℝ) * xi)) =
      f n * fourier (n : ℤ) (((beta - xi : ℝ) : UnitAddCircle)) := by
  unfold realPhaseTwist sourcePhase
  rw [fourier_coe_apply, fourier_coe_apply]
  rw [mul_assoc, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact smooth Fourier pair used in the repaired Gallagher reduction. -/
theorem fourier_smoothCoefficientField
    {X H beta : ℝ} (f : ℕ → ℂ) (hH : 0 < H) (xi : ℝ) :
    (𝓕 (smoothCoefficientField X H beta f)) xi =
      (H : ℂ) * cutoffFourierKernel faithfulCutoff (-H * xi) *
        exponentialSum X f (beta - xi) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold smoothCoefficientField
  simp_rw [Finset.smul_sum]
  rw [integral_finset_sum]
  · simp_rw [← Real.fourier_real_eq_integral_exp_smul,
      GuthMaynardJIteration.source_fourier_const_mul,
      fourier_smoothCoefficientAtom hH]
    unfold exponentialSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← mul_assoc, realPhaseTwist_mul_sourcePhase]
    ring
  · intro n hn
    have hi := (integrable_smoothCoefficientAtom n hH).const_mul
      (realPhaseTwist beta f n)
    have hc : Continuous (fun x : ℝ ↦
        Complex.exp (↑(-2 * Real.pi * x * xi) * Complex.I)) := by fun_prop
    have hb : ∀ x : ℝ,
        ‖Complex.exp (↑(-2 * Real.pi * x * xi) * Complex.I)‖ ≤ 1 := by
      intro x
      rw [show (↑(-2 * Real.pi * x * xi) : ℂ) * Complex.I =
          ((-2 * Real.pi * x * xi : ℝ) : ℂ) * Complex.I by rfl,
        Complex.norm_exp_ofReal_mul_I]
    simpa only [smul_eq_mul] using
      hi.bdd_mul hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)

/-- Frequency-side smooth product belongs to `L²`. -/
theorem memLp_two_smoothFrequencyProduct
    {X H beta : ℝ} (f : ℕ → ℂ) (hH : 0 < H) :
    MemLp (fun xi : ℝ ↦
      (H : ℂ) * cutoffFourierKernel faithfulCutoff (-H * xi) *
        exponentialSum X f (beta - xi)) 2 := by
  rw [memLp_two_iff_integrable_sq_norm]
  · have hscale : -H ≠ 0 := neg_ne_zero.mpr hH.ne'
    have hk : Integrable (fun xi : ℝ ↦
        ‖cutoffFourierKernel faithfulCutoff (-H * xi)‖ ^ 2) :=
      (integrable_comp_mul_left_iff
        (fun z : ℝ ↦ ‖cutoffFourierKernel faithfulCutoff z‖ ^ 2)
        hscale).2 integrable_sq_norm_faithfulCutoffFourierKernel
    have hmajor := hk.const_mul
      (H ^ 2 * coefficientMass X f ^ 2)
    apply hmajor.mono
    · exact (((continuous_const.mul
        ((𝓕 faithfulCutoffSchwartz).continuous.comp (by fun_prop))).mul
          ((continuous_exponentialSum_real X f).comp (by fun_prop))).norm.pow 2)
        |>.aestronglyMeasurable
    · filter_upwards with xi
      have hs := norm_exponentialSum_le_coefficientMass X f (beta - xi)
      have hs2 := pow_le_pow_left₀ (norm_nonneg _) hs 2
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hH, Real.norm_eq_abs]
      rw [abs_of_nonneg (sq_nonneg
        (H * ‖cutoffFourierKernel faithfulCutoff (-H * xi)‖ *
          ‖exponentialSum X f (beta - xi)‖))]
      simp only [abs_pow, abs_of_pos hH,
        abs_of_nonneg (coefficientMass_nonneg X f),
        abs_of_nonneg (norm_nonneg _)]
      calc
        (H * ‖cutoffFourierKernel faithfulCutoff (-H * xi)‖ *
            ‖exponentialSum X f (beta - xi)‖) ^ 2 =
            H ^ 2 * ‖cutoffFourierKernel faithfulCutoff (-H * xi)‖ ^ 2 *
              ‖exponentialSum X f (beta - xi)‖ ^ 2 := by ring
        _ ≤ H ^ 2 * ‖cutoffFourierKernel faithfulCutoff (-H * xi)‖ ^ 2 *
              coefficientMass X f ^ 2 := by
          gcongr
        _ = H ^ 2 * coefficientMass X f ^ 2 *
              ‖cutoffFourierKernel faithfulCutoff (-H * xi)‖ ^ 2 := by ring
  · exact ((continuous_const.mul
      ((𝓕 faithfulCutoffSchwartz).continuous.comp (by fun_prop))).mul
        ((continuous_exponentialSum_real X f).comp (by fun_prop)))
      |>.aestronglyMeasurable

/-- Plancherel for the faithful smooth field. -/
theorem smoothGallagher_plancherel_identity
    {X H beta : ℝ} (f : ℕ → ℂ) (hH : 0 < H) :
    (∫ xi : ℝ,
      ‖(H : ℂ) * cutoffFourierKernel faithfulCutoff (-H * xi) *
        exponentialSum X f (beta - xi)‖ ^ 2) =
      ∫ x : ℝ, ‖smoothCoefficientField X H beta f x‖ ^ 2 := by
  exact integral_norm_sq_fourier_pair
    (integrable_smoothCoefficientField f hH)
    (memLp_two_smoothCoefficientField f hH)
    (memLp_two_smoothFrequencyProduct f hH)
    (fun xi ↦ (fourier_smoothCoefficientField f hH xi).symm)

#print axioms fourier_smoothCoefficientField
#print axioms smoothGallagher_plancherel_identity

end
end MAPMRTProposition51SmoothGallagher72
