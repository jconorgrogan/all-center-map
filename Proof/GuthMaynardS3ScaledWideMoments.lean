import GuthMaynardS3ScaledWideProfile
import GuthMaynardS3LiteralLemma82
import GuthMaynardS3LiteralLemma83Transfer

open scoped BigOperators Real
open MeasureTheory
noncomputable section
namespace GuthMaynardS3ScaledWideMoments
open GuthMaynardJIteration GuthMaynardS3ScaledWideProfile GuthMaynardS3WideProfile
open GuthMaynardS3LiteralProfile GuthMaynardS3LiteralLemma82
open GuthMaynardS3LiteralLemma83Transfer GuthMaynardHeathBrownInterface

/-- Literal Lemmas 8.2 and 8.3 after exact compression. The time horizon in
separation need not equal the analytic horizon used for profile admissibility. -/
theorem scaledWideProfile_masses_le
    {B T eta R : ℝ} {W : Finset ℝ}
    (hB : 4 ≤ B) (hT : 1 ≤ T) (heta : 0 < eta)
    (hsep : TEtaSeparated W T eta) (hW : ContainedInIntervalOfLength W T)
    (hR : 4 ≤ R) (q : ℕ) :
    (∫u : ℝ, scaledWideProfile B W u) ≤ lemma82Constant eta * W.card ∧
    (∫u : ℝ, scaledWideProfile B W u^2) ≤
      48 * lemma83EnergyBound W R (R_pos_of_four_le hR) q := by
  have hBp : 0 < B := by linarith
  have hB1 : 1 ≤ B := by linarith
  have h1 := scaledWideProfile_L1_eq_quarter (T:=B) hB1 hB (le_refl B) W
  have h2 := scaledWideProfile_L2_sq_eq_quarter (T:=B) hB1 hB (le_refl B) W
  have hL1 := GuthMaynardS3LiteralLemma82.integral_smoothedRatio_sq_le hBp hT heta hsep hW
  have hL2 := integral_smoothedRatio_four_le_energy hBp W hR q
  have hwide : ∀ u, wideProfile B W u = smoothedRatio B W u^2 := by
    intro u
    exact (smoothedRatio_sq hBp W u).symm
  have hscaled : ∀u, 0 ≤ scaledWideProfile B W u := scaledWideProfile_nonneg hBp W
  simp_rw [abs_of_nonneg (hscaled _)] at h1
  simp_rw [abs_of_nonneg (wideProfile_nonneg hBp W _), hwide] at h1
  simp_rw [hwide, ← pow_mul] at h2
  norm_num at h2
  constructor
  · linarith
  · unfold lemma83ProfileJacobian at hL2
    linarith

end GuthMaynardS3ScaledWideMoments
#print axioms GuthMaynardS3ScaledWideMoments.scaledWideProfile_masses_le
