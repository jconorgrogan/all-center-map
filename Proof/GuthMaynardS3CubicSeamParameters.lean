import GuthMaynardS3LiteralFinalSeamParameterAdapter

open scoped Real BigOperators
noncomputable section
namespace GuthMaynardS3CubicSeamParameters
open GuthMaynardS3LiteralFinalSeamParameterAdapter
open GuthMaynardS3LiteralUniform106Radial GuthMaynardS3LiteralBalancedSectorGeometry

structure CubicSeamParameters (N : ℕ) (T eta : ℝ) (k : ℕ) (W : Finset ℝ) : Prop where
  time_one : 1 ≤ T
  length_le_time : (N : ℝ) ≤ T
  rho_le_time : s3Rho T eta ≤ T
  bin_le_time_sq : (2 : ℝ)^k ≤ T^2
  profile_lower : 4 ≤ (N : ℝ)*2^k/(4*s3Rho T eta)
  profile_upper : (N : ℝ)*2^k/(4*s3Rho T eta) ≤ 64*T^3
  max_frequency : ((16*2^(k+2) : ℕ) : ℝ) ≤ 64*T^3
  profile_height : 4*(W.card : ℝ)^2 ≤ (64*T^3)^4
  horizon_lower : 7 ≤ 64*T^3
  frequency_product : (N : ℝ)*2^k ≤ 4*s3Rho T eta*T

/-- The actual fixed-weight endpoint supplies every arithmetic condition for
running the analytic iteration at U=64T³. Source T is not redefined. -/
theorem final_seam_cubic_parameters
    {N : ℕ} (hN : 256 ≤ N) {T eta : ℝ}
    (hTdef : T = (N : ℝ)^(6/5 : ℝ)) (heta : 0 < eta) (heta1 : eta ≤ 1/100)
    {k : ℕ} (hk : k ∈ dyadicExponents (s3FrequencyCutoff T eta N))
    (W : Finset ℝ) (hW : (W.card : ℝ) ≤ 2*T) :
    CubicSeamParameters N T eta k W := by
  have hb := final_seam_eventual_bounds hN hTdef heta heta1
  have hp := final_seam_parameter_adapter hN hTdef heta heta1 hk W hW
  dsimp at hp
  have hT : 1 ≤ T := hb.1
  have hTp : 0 < T := by linarith
  have hNp : 0 < N := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hnT : (N : ℝ) ≤ T := by
    rw [hTdef]
    calc
      (N : ℝ) = (N : ℝ)^(1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (N : ℝ)^(6/5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hrT : s3Rho T eta ≤ T := by
    simpa only [s3Rho, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT (show eta ≤ 1 by linarith)
  have hK : (2 : ℝ)^k ≤ T^2 := by linarith [hp.2.2.1]
  have h23 : T^2 ≤ T^3 := pow_le_pow_right₀ hT (by norm_num : (2 : ℕ) ≤ 3)
  have hUU : 64*T^2 ≤ 64*T^3 := mul_le_mul_of_nonneg_left h23 (by norm_num)
  have hT3 : T ≤ T^3 := by
    simpa using pow_le_pow_right₀ hT (by norm_num : (1 : ℕ) ≤ 3)
  have hTU : T ≤ 64*T^3 := by nlinarith [pow_nonneg hTp.le 3]
  have hU2nonneg : 0 ≤ 64*T^2 := by positivity
  have hUpow := pow_le_pow_left₀ hU2nonneg hUU 4
  have hM : ((16*2^(k+2) : ℕ) : ℝ) = 64*(2 : ℝ)^k := by
    push_cast
    rw [pow_add]
    norm_num
    ring
  have hrp : 0 < s3Rho T eta := s3Rho_pos hTp heta
  have hprod := (div_le_iff₀ (by positivity : 0 < 4*s3Rho T eta)).mp hp.2.1
  refine ⟨hT, hnT, hrT, hK, hp.1, hp.2.1.trans hTU, ?_,
    hp.2.2.2.1.trans hUpow, hp.2.2.2.2.trans hUU, ?_⟩
  · rw [hM]
    exact hp.2.2.1.trans hUU
  · nlinarith

theorem cubic_horizon_power {T : ℝ} (hT : 0 ≤ T) (a : ℝ) :
    (64*T^3)^a = (64 : ℝ)^a*T^(3*a) := by
  rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast T 3,
    ← Real.rpow_mul hT]
  norm_num

end GuthMaynardS3CubicSeamParameters
#print axioms GuthMaynardS3CubicSeamParameters.final_seam_cubic_parameters
#print axioms GuthMaynardS3CubicSeamParameters.cubic_horizon_power
