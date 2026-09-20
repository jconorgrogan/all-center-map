import GuthMaynardS3FinalSeamSourceBound
import GuthMaynardS3ProfileScaleGrowth

open scoped Real
noncomputable section
namespace GuthMaynardS3FixedSeamSubpower
open GuthMaynardS3FinalSeamSourceBound GuthMaynardS3ProfileScaleGrowth
open GuthMaynardS3LiteralLemma82 GuthMaynardHeathBrownInterface
open GuthMaynardEquation55Infinite GuthMaynardS3LiteralLemma83Energy

/-- The restricted source S3 estimate with an arbitrary requested subpower
loss. Separation, cardinality and the analytic-horizon threshold are resolved
internally. The sole eventual condition is a fixed lower bound on N. -/
theorem sourceS3_fixed_seam_subpower {epsilon : ℝ} (heps : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, 256 ≤ N0 ∧
      ∀ (N : ℕ) (T : ℝ) (W : Finset ℝ),
        N0 ≤ N → T = (N : ℝ)^(6/5 : ℝ) →
        TEtaSeparated W T epsilon → ContainedInIntervalOfLength W T →
        ‖sourceS3 N W‖ ≤ C*T^epsilon*
          (T^2*(W.card : ℝ)^(3/2 : ℝ)+T*(N : ℝ)*Real.sqrt (W.card : ℝ)*
            Real.sqrt (sourceApproximateAdditiveEnergy W : ℝ)) + C*T^(-100 : ℝ) := by
  let eta : ℝ := min (epsilon/12) (1/100)
  have heta : 0 < eta := lt_min (by positivity) (by norm_num)
  have heta1 : eta ≤ 1/100 := min_le_right _ _
  have hetaeps : eta ≤ epsilon/12 := min_le_left _ _
  have hbudget : 6*eta ≤ epsilon := by linarith
  have hsepexp : eta ≤ epsilon := by linarith
  obtain ⟨C,hC,T0,hT0,hsource⟩ := norm_sourceS3_le_final_seam heta heta1
  let N0 : ℕ := Nat.ceil T0 + 256
  refine ⟨C,hC,N0,by dsimp [N0]; omega,?_⟩
  intro N T W hN0 hTdef hsep hcontained
  have hN256 : 256 ≤ N := by dsimp [N0] at hN0; omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hT1 : 1 ≤ T := by
    rw [hTdef]
    exact Real.one_le_rpow hN1 (by norm_num)
  have hNT : (N : ℝ) ≤ T := by
    rw [hTdef]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (1 : ℝ) ≤ 6/5)
  have hT3 : T ≤ T^3 := by
    simpa using pow_le_pow_right₀ hT1 (by norm_num : (1 : ℕ) ≤ 3)
  have hTU : T ≤ 64*T^3 := by nlinarith only [hT3,hT1]
  have hT0N : T0 ≤ (N : ℝ) := by
    have hc : Nat.ceil T0 ≤ N := by dsimp [N0] at hN0; omega
    exact (Nat.le_ceil T0).trans (by exact_mod_cast hc)
  have hUT : T0 ≤ 64*T^3 := hT0N.trans (hNT.trans hTU)
  have hsepeta : TEtaSeparated W T eta := by
    intro x hx y hy hxy
    exact (Real.rpow_le_rpow_of_exponent_le hT1 hsepexp).trans (hsep x hx y hy hxy)
  have hcard := card_le_two_time_of_separation hT1 heta.le hsepeta hcontained
  have hs := hsource N T W hN256 hTdef hUT hcard hsepeta hcontained
  have hpow : T^(6*eta) ≤ T^epsilon := Real.rpow_le_rpow_of_exponent_le hT1 hbudget
  have hmain0 : 0 ≤ T^2*(W.card : ℝ)^(3/2 : ℝ)+
      T*(N : ℝ)*Real.sqrt (W.card : ℝ)*Real.sqrt (sourceApproximateAdditiveEnergy W : ℝ) := by
    have hTpos : 0 < T := by linarith
    positivity
  exact hs.trans (add_le_add
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC.le) hmain0) (le_refl _))

end GuthMaynardS3FixedSeamSubpower
#print axioms GuthMaynardS3FixedSeamSubpower.sourceS3_fixed_seam_subpower
