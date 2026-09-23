import GuthMaynardLemma62ReflectionSubstitution
import MRTNonstationaryPhaseInverse

namespace GuthMaynardS2ShortGapPhase
open Real Complex Set MeasureTheory
open MAPMRTNonstationaryPhaseInverse
open MAPMRTCorollary53Source MAPMRTVanDerCorputProof
noncomputable section

def phase (t xi u : ℝ) : ℝ := t / (2 * Real.pi) * Real.log u - xi * u
def first (t xi u : ℝ) : ℝ := t / (2 * Real.pi * u) - xi
def second (t u : ℝ) : ℝ := -t / (2 * Real.pi * u ^ 2)
def third (t u : ℝ) : ℝ := t / (Real.pi * u ^ 3)

lemma phase_deriv {t xi u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (phase t xi) (first t xi u) u := by
  unfold phase first
  convert (Real.hasDerivAt_log hu).const_mul (t / (2 * Real.pi)) |>.sub
    ((hasDerivAt_id u).const_mul xi) using 1 <;>
    (try funext y) <;> (try simp only [Pi.sub_apply, id_eq]) <;>
    field_simp [Real.pi_ne_zero, hu]

lemma first_deriv {t xi u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (first t xi) (second t u) u := by
  unfold first second
  convert (hasDerivAt_inv hu).const_mul (t / (2 * Real.pi)) |>.sub_const xi
    using 1 <;> field_simp [Real.pi_ne_zero, hu]

lemma second_deriv {t u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (second t) (third t u) u := by
  unfold second third
  convert ((hasDerivAt_const u (-t / (2 * Real.pi))).div
    ((hasDerivAt_id u).pow 2) (pow_ne_zero 2 hu)) using 1
  · ext x; simp only [Pi.div_apply, Pi.pow_apply, id_eq]; ring
  · simp only [Pi.pow_apply, id_eq]
    field_simp [Real.pi_ne_zero, hu]; ring

/-- Literal phase separation, retaining both frequency signs and the source 2π. -/
lemma first_lower {t xi u : ℝ} (ht : |t| ≤ |xi|)
    (hu : u ∈ Icc (1/2 : ℝ) 3) : |xi| / 2 ≤ |first t xi u| := by
  have hu0 : 0 < u := by linarith [hu.1]
  have hden : 2 ≤ 2 * Real.pi * u := by nlinarith [Real.pi_gt_three, mul_nonneg (sub_nonneg.mpr hu.1) Real.pi_pos.le]
  have hsmall : |t / (2 * Real.pi * u)| ≤ |xi| / 2 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi * u)]
    exact div_le_div₀ (abs_nonneg _) ht (by norm_num) hden
  have htri := abs_sub (t / (2 * Real.pi * u)) (t / (2 * Real.pi * u) - xi)
  simp only [sub_sub_cancel] at htri
  unfold first
  linarith

lemma second_upper {t xi u : ℝ} (ht : |t| ≤ |xi|)
    (hu : u ∈ Icc (1/2 : ℝ) 3) : |second t u| ≤ 4 * |xi| := by
  have hu0 : 0 < u := by linarith [hu.1]
  have hden : 1/4 ≤ 2 * Real.pi * u ^ 2 := by
    have : (1/4 : ℝ) ≤ u^2 := by nlinarith [hu.1]
    nlinarith [Real.pi_gt_three]
  unfold second
  rw [abs_div, abs_neg, abs_of_pos (by positivity : 0 < 2 * Real.pi * u ^ 2)]
  have h := div_le_div₀ (abs_nonneg xi) ht (by norm_num : (0:ℝ)<1/4) hden
  convert h using 1 <;> ring

lemma third_upper {t xi u : ℝ} (ht : |t| ≤ |xi|)
    (hu : u ∈ Icc (1/2 : ℝ) 3) : |third t u| ≤ 8 * |xi| := by
  have hu0 : 0 < u := by linarith [hu.1]
  have hc : (1/8 : ℝ) ≤ u^3 := by nlinarith [sq_nonneg (u-1/2), hu.1]
  have hden : 1/8 ≤ Real.pi * u ^ 3 := by nlinarith [Real.pi_gt_three]
  unfold third
  rw [abs_div, abs_of_pos (by positivity : 0 < Real.pi * u ^ 3)]
  have h := div_le_div₀ (abs_nonneg xi) ht (by norm_num : (0:ℝ)<1/8) hden
  convert h using 1 <;> ring

#print axioms first_lower
#print axioms second_deriv
end
end GuthMaynardS2ShortGapPhase

namespace GuthMaynardS2ShortGapPhase
open Real Complex Set MeasureTheory
open MAPMRTNonstationaryPhaseInverse
noncomputable section

lemma inverse_bounds {t xi u : ℝ} (hxi : xi ≠ 0) (ht : |t| ≤ |xi|)
    (hu : u ∈ Icc (1/2 : ℝ) 3) :
    ‖inversePhaseDerivative (first t xi) u‖ ≤ 2 / |xi| ∧
    ‖inversePhaseDerivativeDeriv (first t xi) (second t) u‖ ≤ 16 / |xi| ∧
    ‖inversePhaseDerivativeSecond (first t xi) (second t) (third t) u‖ ≤ 288 / |xi| := by
  have hx : 0 < |xi| := abs_pos.mpr hxi
  have h0 := norm_inversePhaseDerivative_le (by positivity : 0 < |xi|/2) (first_lower ht hu)
  have h1 := norm_inversePhaseDerivativeDeriv_le (by positivity : 0 < |xi|/2)
    (by positivity : 0 ≤ 4*|xi|) (first_lower ht hu) (second_upper ht hu)
  have h2 := norm_inversePhaseDerivativeSecond_le (by positivity : 0 < |xi|/2)
    (by positivity : 0 ≤ 4*|xi|) (by positivity : 0 ≤ 8*|xi|)
    (first_lower ht hu) (second_upper ht hu) (third_upper ht hu)
  refine ⟨?_, ?_, ?_⟩
  · convert h0 using 1 <;> field_simp
  · convert h1 using 1 <;> field_simp <;> ring
  · convert h2 using 1 <;> field_simp <;> ring
end
end GuthMaynardS2ShortGapPhase
