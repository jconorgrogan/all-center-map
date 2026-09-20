import MRTVanDerCorput
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace MAPMRTPacketEnergy

open MeasureTheory Set

noncomputable section

/-- Exact mass of the translated and dilated Cauchy kernel. -/
theorem integral_cauchy_affine
    {c beta R : ℝ} (hbeta : beta ≠ 0) (hR : 0 < R) :
    (∫ x : ℝ, (1 + ((c + beta * x) / R) ^ 2)⁻¹) =
      Real.pi * R / |beta| := by
  let k : ℝ → ℝ := fun y ↦ (1 + y ^ 2)⁻¹
  let d : ℝ := c / beta
  have hemb : MeasurableEmbedding (fun x : ℝ ↦ x + d) :=
    (continuous_id.add continuous_const).measurableEmbedding
      (by intro x y h; dsimp at h; linarith)
  have htranslate := (measurePreserving_add_right volume d).integral_comp hemb
    (fun x : ℝ ↦ k ((beta / R) * x))
  have harg : ∀ x : ℝ,
      (beta / R) * (x + d) = (c + beta * x) / R := by
    intro x
    unfold d
    field_simp [hbeta, hR.ne']
    ring
  have htranslated :
      (∫ x : ℝ, k ((c + beta * x) / R)) =
        ∫ x : ℝ, k ((beta / R) * x) := by
    rw [← htranslate]
    apply integral_congr_ae
    filter_upwards with x
    rw [harg]
  have hscale := Measure.integral_comp_mul_left k (beta / R)
  have hscaleNe : beta / R ≠ 0 := div_ne_zero hbeta hR.ne'
  rw [htranslated, hscale, integral_univ_inv_one_add_sq]
  simp only [smul_eq_mul]
  rw [abs_inv, abs_div, abs_of_pos hR]
  field_simp [hbeta, abs_ne_zero.mpr hbeta]

/-- A uniform central bound and a quadratic far bound combine into the smooth
Cauchy envelope used in the proof of (83). -/
theorem norm_le_cauchy_envelope
    {c beta R A B x : ℝ} {J : ℝ → ℂ}
    (hR : 0 < R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcentral : ‖J x‖ ≤ A)
    (hfar : R ≤ |c + beta * x| →
      ‖J x‖ ≤ B / |c + beta * x| ^ 2)
    (hrelation : B / R ^ 2 ≤ A) :
    ‖J x‖ ≤ 2 * A / (1 + ((c + beta * x) / R) ^ 2) := by
  let y := |c + beta * x|
  have hy : 0 ≤ y := abs_nonneg _
  have hden : 0 < 1 + ((c + beta * x) / R) ^ 2 := by positivity
  by_cases hnear : y ≤ R
  · apply (le_div_iff₀ hden).2
    have hratio : ((c + beta * x) / R) ^ 2 ≤ 1 := by
      rw [div_pow]
      apply (div_le_one (sq_pos_of_pos hR)).2
      have hsquare := pow_le_pow_left₀ hy hnear 2
      unfold y at hsquare
      simpa [sq_abs] using hsquare
    nlinarith
  · have hyR : R ≤ y := le_of_not_ge hnear
    have hyPos : 0 < y := lt_of_lt_of_le hR hyR
    have hfar' := hfar hyR
    have hBR : B ≤ A * R ^ 2 := by
      exact (div_le_iff₀ (sq_pos_of_pos hR)).mp hrelation
    have hJ : ‖J x‖ ≤ A * R ^ 2 / y ^ 2 := by
      exact hfar'.trans (div_le_div_of_nonneg_right hBR (sq_nonneg y))
    apply hJ.trans
    apply (div_le_div_iff₀ (sq_pos_of_pos hyPos) hden).2
    have hySq : R ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hR.le hyR 2
    have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
    have habsSq : |c + beta * x| ^ 2 = (c + beta * x) ^ 2 := sq_abs _
    rw [show y = |c + beta * x| by rfl, habsSq]
    field_simp [hR.ne']
    nlinarith

/-- Equation (83)'s one-dimensional envelope calculation.  The only packet
input is the central/far pointwise pair; all x-integration is discharged. -/
theorem packet_energy_le_of_central_far
    {c beta R A B : ℝ} {J : ℝ → ℂ}
    (hbeta : beta ≠ 0) (hR : 0 < R)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcentral : ∀ x, ‖J x‖ ≤ A)
    (hfar : ∀ x, R ≤ |c + beta * x| →
      ‖J x‖ ≤ B / |c + beta * x| ^ 2)
    (hrelation : B / R ^ 2 ≤ A)
    (hJInt : Integrable (fun x ↦ ‖J x‖ ^ 2)) :
    (∫ x : ℝ, ‖J x‖ ^ 2) ≤
      4 * Real.pi * A ^ 2 * R / |beta| := by
  let K : ℝ → ℝ := fun x ↦ (1 + ((c + beta * x) / R) ^ 2)⁻¹
  have hKInt : Integrable K := by
    have hbase : Integrable (fun y : ℝ ↦ (1 + y ^ 2)⁻¹) :=
      integrable_inv_one_add_sq
    have hscaleNe : beta / R ≠ 0 := div_ne_zero hbeta hR.ne'
    have hscaled : Integrable (fun x : ℝ ↦
        (1 + ((beta / R) * x) ^ 2)⁻¹) := by
      exact (integrable_comp_mul_left_iff _ hscaleNe).2 hbase
    let d : ℝ := c / beta
    have hemb : MeasurableEmbedding (fun x : ℝ ↦ x + d) :=
      (continuous_id.add continuous_const).measurableEmbedding
        (by intro x y h; dsimp at h; linarith)
    have hmp := measurePreserving_add_right volume d
    have hcomp := (hmp.integrable_comp hscaled.aestronglyMeasurable).2 hscaled
    apply hcomp.congr
    filter_upwards with x
    unfold K d
    simp only [Function.comp_apply]
    rw [show (beta / R) * (x + c / beta) =
        (c + beta * x) / R by
      field_simp [hbeta, hR.ne']
      ring]
  have hmajorantInt : Integrable (fun x ↦ 4 * A ^ 2 * K x) :=
    hKInt.const_mul (4 * A ^ 2)
  have hpoint : ∀ x, ‖J x‖ ^ 2 ≤ 4 * A ^ 2 * K x := by
    intro x
    have henv := norm_le_cauchy_envelope hR hA hB
      (hcentral x) (hfar x) hrelation
    have hden : 0 < 1 + ((c + beta * x) / R) ^ 2 := by positivity
    have hsq := pow_le_pow_left₀ (norm_nonneg _) henv 2
    calc
      ‖J x‖ ^ 2 ≤ (2 * A / (1 + ((c + beta * x) / R) ^ 2)) ^ 2 := hsq
      _ ≤ 4 * A ^ 2 * (1 + ((c + beta * x) / R) ^ 2)⁻¹ := by
        rw [div_pow, show (2 * A) ^ 2 = 4 * A ^ 2 by ring]
        have hk : (1 + ((c + beta * x) / R) ^ 2)⁻¹ ≤ 1 := by
          rw [inv_le_one₀ hden]
          nlinarith [sq_nonneg ((c + beta * x) / R)]
        have hk0 : 0 ≤ (1 + ((c + beta * x) / R) ^ 2)⁻¹ := by positivity
        have := mul_le_mul_of_nonneg_left
          (show (1 + ((c + beta * x) / R) ^ 2)⁻¹ ^ 2 ≤
            (1 + ((c + beta * x) / R) ^ 2)⁻¹ by nlinarith)
          (by nlinarith [sq_nonneg A] : 0 ≤ 4 * A ^ 2)
        simpa [K, inv_pow] using this
  calc
    (∫ x : ℝ, ‖J x‖ ^ 2) ≤ ∫ x : ℝ, 4 * A ^ 2 * K x := by
      exact integral_mono hJInt hmajorantInt hpoint
    _ = 4 * A ^ 2 * (Real.pi * R / |beta|) := by
      rw [integral_const_mul, integral_cauchy_affine hbeta hR]
    _ = 4 * Real.pi * A ^ 2 * R / |beta| := by ring

end
end MAPMRTPacketEnergy
