import GuthMaynardS3StartingProfile
import GuthMaynardS3LiteralLemma82
import GuthMaynardLemma118IntervalPacking

noncomputable section
namespace GuthMaynardS3ProfileScaleGrowth
open GuthMaynardS3LiteralLemma82 GuthMaynardHeathBrownInterface

theorem card_le_two_time_of_separation
    {T eta : ℝ} {W : Finset ℝ} (hT : 1 ≤ T) (heta : 0 ≤ eta)
    (hsep : TEtaSeparated W T eta) (hW : ContainedInIntervalOfLength W T) :
    (W.card : ℝ) ≤ 2 * T := by
  obtain ⟨a, ha⟩ := hW
  have hp : (1 : ℝ) ≤ Real.rpow T eta := Real.one_le_rpow hT heta
  have hpack := GuthMaynardLemma118.card_cast_le_one_add_div
    W a T 1 (by norm_num) (by linarith) ha
    (fun x hx y hy hxy => hp.trans (hsep x hx y hy hxy))
  norm_num at hpack
  linarith

/-- The height bound used by both the compact and uncut source profiles
follows from the actual separation hypothesis. -/
theorem profile_scale_le_time_four
    {T eta : ℝ} {W : Finset ℝ} (hT4 : 4 ≤ T) (heta : 0 ≤ eta)
    (hsep : TEtaSeparated W T eta) (hW : ContainedInIntervalOfLength W T) :
    4 * (W.card : ℝ)^2 ≤ T ^ (4 : ℝ) := by
  have hc := card_le_two_time_of_separation (by linarith : 1 ≤ T) heta hsep hW
  have hsq : (W.card : ℝ)^2 ≤ (2*T)^2 := by gcongr
  have hT2 : (16 : ℝ) ≤ T^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hT2 (sq_nonneg T)
  have hr : T ^ (4 : ℝ) = T ^ (4 : ℕ) := by norm_num [Real.rpow_natCast]
  rw [hr]
  nlinarith
end GuthMaynardS3ProfileScaleGrowth
#print axioms GuthMaynardS3ProfileScaleGrowth.profile_scale_le_time_four
