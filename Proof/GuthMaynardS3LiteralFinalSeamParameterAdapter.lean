import GuthMaynardS3LiteralUniform106Radial
import GuthMaynardS3LiteralBalancedSectorGeometry

namespace GuthMaynardS3LiteralFinalSeamParameterAdapter

open scoped BigOperators
open GuthMaynardS3LiteralUniform106Radial
open GuthMaynardS3LiteralBalancedSectorGeometry
open GuthMaynardS3LiteralTruncation
open GuthMaynardS3LiteralRadialDecay

noncomputable section

set_option maxHeartbeats 800000

/-- Restricted final-seam arithmetic adapter.  This is not a universal S3
range theorem: it uses the fixed-weight seam `T = N^(6/5)` and the eventual
threshold `N ≥ 256`, so the low-`B₀` branch never occurs. -/
theorem final_seam_parameter_adapter_of_cutoff
    {N : ℕ} (hN : 0 < N)
    {T eta : ℝ} (hTdef : T = Real.rpow (N : ℝ) (6 / 5 : ℝ))
    (heta : 0 < eta) (heta1 : eta ≤ 1 / 100)
    (hcut : 2 * (N : ℝ) ≤ Real.rpow T (1 + eta))
    (hNlarge : 16 * s3Rho T eta ≤ (N : ℝ))
    {k : ℕ} (hk : k ∈ dyadicExponents
      (s3FrequencyCutoff T eta N)) :
    let rho := s3Rho T eta
    let Mcut := s3FrequencyCutoff T eta N
    let B0 := (N : ℝ) * (2 ^ k : ℝ) / (4 * rho)
    let U := 64 * T ^ 2
    4 ≤ B0 ∧ B0 ≤ T ∧ 64 * (2 ^ k : ℝ) ≤ U := by
  let rho : ℝ := s3Rho T eta
  let Mcut : ℕ := s3FrequencyCutoff T eta N
  let B0 : ℝ := (N : ℝ) * (2 ^ k : ℝ) / (4 * rho)
  let U : ℝ := 64 * T ^ 2
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show (1 : ℕ) ≤ N by omega)
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hT1 : 1 ≤ T := by
    rw [hTdef]
    exact Real.one_le_rpow hN1 (by norm_num)
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hT0 : 0 ≤ T := hTpos.le
  have hMcut : 1 ≤ Mcut := by
    dsimp [Mcut, s3FrequencyCutoff]
    exact le_max_left _ _
  have hk' : k ∈ dyadicExponents Mcut := by simpa [Mcut] using hk
  have hklog : k ≤ Nat.log 2 Mcut := by
    dsimp [dyadicExponents] at hk'
    have hmax : max Mcut 1 = Mcut := max_eq_left hMcut
    rw [hmax] at hk'
    have hlt := Finset.mem_range.mp hk'
    omega
  have hKnat : 2 ^ k ≤ Mcut := by
    have hpow := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hklog
    have hlog := Nat.pow_log_le_self 2 (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hMcut))
    exact hpow.trans hlog
  have hMle := s3Cutoff_le_rpow hN hT1 hcut
  have hKreal : (2 ^ k : ℝ) ≤
      Real.rpow T (1 + eta) / (N : ℝ) := by
    have hKcast : (2 ^ k : ℝ) ≤ (Mcut : ℝ) := by exact_mod_cast hKnat
    exact hKcast.trans hMle
  have hN16rho : 16 * rho ≤ (N : ℝ) := by simpa [rho] using hNlarge
  have hRhoPos : 0 < rho := by
    dsimp [rho]
    exact s3Rho_pos hTpos heta
  have hB0lo : (4 : ℝ) ≤ B0 := by
    dsimp [B0]
    have hKone : (1 : ℝ) ≤ (2 ^ k : ℝ) := by
      have hpowpos : 0 < 2 ^ k := by positivity
      exact_mod_cast (show (1 : ℕ) ≤ 2 ^ k by omega)
    have hnum : 16 * rho ≤ (N : ℝ) * (2 ^ k : ℝ) := by
      calc
        16 * rho ≤ (N : ℝ) := hN16rho
        _ ≤ (N : ℝ) * (2 ^ k : ℝ) := by nlinarith
    apply (le_div_iff₀ (mul_pos (by norm_num) hRhoPos)).mpr
    convert hnum using 1 <;> ring
  have hB0hi : B0 ≤ T := by
    dsimp [B0]
    have hnum : (N : ℝ) * (2 ^ k : ℝ) ≤ Real.rpow T (1 + eta) := by
      have := (le_div_iff₀ hNpos).mp hKreal
      simpa [mul_comm] using this
    have hden : 0 < 4 * rho := by
      dsimp [rho]
      exact mul_pos (by norm_num) (s3Rho_pos hTpos heta)
    have hdiv : (N : ℝ) * (2 ^ k : ℝ) / (4 * rho) ≤
        Real.rpow T (1 + eta) / (4 * rho) :=
      div_le_div_of_nonneg_right hnum hden.le
    have hrhoT : rho = Real.rpow T eta := rfl
    calc
      (N : ℝ) * (2 ^ k : ℝ) / (4 * rho) ≤
          Real.rpow T (1 + eta) / (4 * rho) := hdiv
      _ = T / 4 := by
        rw [hrhoT]
        calc
          Real.rpow T (1 + eta) / (4 * Real.rpow T eta) =
              (Real.rpow T (1 + eta) / Real.rpow T eta) / 4 := by ring
          _ = T / 4 := by
            rw [show Real.rpow T (1 + eta) / Real.rpow T eta = T by
              calc
                _ = Real.rpow T ((1 + eta) - eta) :=
                  (Real.rpow_sub hTpos _ _).symm
                _ = T := by
                  have hexp : (1 + eta) - eta = (1 : ℝ) := by ring
                  rw [hexp]
                  exact Real.rpow_one T]
      _ ≤ T := by nlinarith
  have hKupper : (2 ^ k : ℝ) ≤ T ^ 2 := by
    have hMupper : (Mcut : ℝ) ≤ T ^ 2 := by
      have hle := hMle
      dsimp [Mcut] at hle
      have hNone : 1 ≤ (N : ℝ) := hN1
      have hdiv : Real.rpow T (1 + eta) / (N : ℝ) ≤
          Real.rpow T (1 + eta) := by
        exact (div_le_iff₀ hNpos).mpr (by
          calc
            Real.rpow T (1 + eta) = Real.rpow T (1 + eta) * 1 := by ring
            _ ≤ Real.rpow T (1 + eta) * (N : ℝ) :=
              mul_le_mul_of_nonneg_left hN1 (Real.rpow_nonneg hT0 _))
      have hpoweta : Real.rpow T (1 + eta) ≤ T ^ 2 := by
        rw [show T ^ 2 = Real.rpow T (2 : ℝ) by
          exact (Real.rpow_natCast T 2).symm]
        exact Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
      exact hle.trans (hdiv.trans hpoweta)
    have hKcast : (2 ^ k : ℝ) ≤ (Mcut : ℝ) := by exact_mod_cast hKnat
    exact hKcast.trans hMupper
  have hU : 64 * (2 ^ k : ℝ) ≤ U := by
    dsimp [U]
    exact mul_le_mul_of_nonneg_left hKupper (by norm_num)
  simpa [rho, Mcut, B0, U] using (And.intro hB0lo (And.intro hB0hi hU))

/- The fixed seam supplies the two hypotheses used by the arithmetic helper.
The proof keeps the finite horizon and profile-growth obligations in the same
certificate, so downstream consumers do not have to reintroduce them as
opaque premises. -/
theorem final_seam_eventual_bounds
    {N : ℕ} (hN256 : 256 ≤ N)
    {T eta : ℝ} (hTdef : T = Real.rpow (N : ℝ) (6 / 5 : ℝ))
    (heta : 0 < eta) (heta1 : eta ≤ 1 / 100) :
    1 ≤ T ∧
      2 * (N : ℝ) ≤ Real.rpow T (1 + eta) ∧
      16 * s3Rho T eta ≤ (N : ℝ) := by
  have hNposNat : 0 < N := by omega
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hNposNat
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show (1 : ℕ) ≤ N by omega)
  have hN256r : (256 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN256
  have hT1 : 1 ≤ T := by
    rw [hTdef]
    exact Real.one_le_rpow hN1 (by norm_num)
  have hroot2 : (2 : ℝ) ≤ Real.rpow (N : ℝ) (1 / 5 : ℝ) := by
    have hiff := Real.le_rpow_inv_iff_of_pos
      (by norm_num : (0 : ℝ) ≤ 2) hNpos.le (by norm_num : (0 : ℝ) < 5)
    have haux : (2 : ℝ) ≤ Real.rpow (N : ℝ) (5 : ℝ)⁻¹ := by
      apply hiff.mpr
      norm_num
      nlinarith [hN256r]
    convert haux using 1 <;> norm_num
  have hNpow : (N : ℝ) * Real.rpow (N : ℝ) (1 / 5 : ℝ) =
      Real.rpow (N : ℝ) (6 / 5 : ℝ) := by
    calc
      (N : ℝ) * Real.rpow (N : ℝ) (1 / 5 : ℝ) =
          Real.rpow (N : ℝ) 1 * Real.rpow (N : ℝ) (1 / 5 : ℝ) := by
            congr 1
            exact (Real.rpow_one (N : ℝ)).symm
      _ = Real.rpow (N : ℝ) (1 + 1 / 5 : ℝ) :=
        (Real.rpow_add hNpos _ _).symm
      _ = Real.rpow (N : ℝ) (6 / 5 : ℝ) := by congr 1 <;> norm_num
  have hTge2N : 2 * (N : ℝ) ≤ T := by
    rw [hTdef]
    calc
      2 * (N : ℝ) ≤ (N : ℝ) * Real.rpow (N : ℝ) (1 / 5 : ℝ) := by
        nlinarith [hroot2, hNpos]
      _ = Real.rpow (N : ℝ) (6 / 5 : ℝ) := hNpow
  have hTpow : T ≤ Real.rpow T (1 + eta) := by
    calc
      T = Real.rpow T 1 := by symm; exact Real.rpow_one T
      _ ≤ Real.rpow T (1 + eta) :=
        Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hcut : 2 * (N : ℝ) ≤ Real.rpow T (1 + eta) := hTge2N.trans hTpow
  have hrhoexp : s3Rho T eta =
      Real.rpow (N : ℝ) ((6 / 5 : ℝ) * eta) := by
    dsimp [s3Rho]
    rw [hTdef]
    exact (Real.rpow_mul hNpos.le (6 / 5 : ℝ) eta).symm
  have hrhole : s3Rho T eta ≤ Real.rpow (N : ℝ) (1 / 2 : ℝ) := by
    rw [hrhoexp]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    nlinarith [heta1]
  have hroot16 : (16 : ℝ) ≤ Real.rpow (N : ℝ) (1 / 2 : ℝ) := by
    have hiff := Real.le_rpow_inv_iff_of_pos
      (by norm_num : (0 : ℝ) ≤ 16) hNpos.le (by norm_num : (0 : ℝ) < 2)
    have haux : (16 : ℝ) ≤ Real.rpow (N : ℝ) (2 : ℝ)⁻¹ := by
      apply hiff.mpr
      norm_num
      exact_mod_cast hN256
    convert haux using 1 <;> norm_num
  have hNsqrt : 16 * Real.rpow (N : ℝ) (1 / 2 : ℝ) ≤ (N : ℝ) := by
    have hsq : (Real.rpow (N : ℝ) (1 / 2 : ℝ)) ^ 2 = (N : ℝ) := by
      calc
        (Real.rpow (N : ℝ) (1 / 2 : ℝ)) ^ 2 =
            Real.rpow (N : ℝ) (1 / 2 : ℝ) *
              Real.rpow (N : ℝ) (1 / 2 : ℝ) := by ring
        _ = Real.rpow (N : ℝ) ((1 / 2 : ℝ) + 1 / 2) :=
          (Real.rpow_add hNpos _ _).symm
        _ = (N : ℝ) := by
          have hexp : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
          rw [hexp]
          exact Real.rpow_one _
    nlinarith [hroot16, Real.rpow_nonneg hNpos.le (1 / 2 : ℝ), hsq]
  have hNlarge : 16 * s3Rho T eta ≤ (N : ℝ) := by
    exact (mul_le_mul_of_nonneg_left hrhole (by norm_num)).trans hNsqrt
  exact ⟨hT1, hcut, hNlarge⟩

theorem final_seam_parameter_adapter
    {N : ℕ} (hN256 : 256 ≤ N)
    {T eta : ℝ} (hTdef : T = Real.rpow (N : ℝ) (6 / 5 : ℝ))
    (heta : 0 < eta) (heta1 : eta ≤ 1 / 100)
    {k : ℕ} (hk : k ∈ dyadicExponents
      (s3FrequencyCutoff T eta N))
    (W : Finset ℝ) (hWle : (W.card : ℝ) ≤ 2 * T) :
    let rho := s3Rho T eta
    let Mcut := s3FrequencyCutoff T eta N
    let B0 := (N : ℝ) * (2 ^ k : ℝ) / (4 * rho)
    let U := 64 * T ^ 2
    4 ≤ B0 ∧ B0 ≤ T ∧ 64 * (2 ^ k : ℝ) ≤ U ∧
      4 * (W.card : ℝ) ^ 2 ≤ U ^ 4 ∧ 7 ≤ U := by
  have hNposNat : 0 < N := by omega
  have hb := final_seam_eventual_bounds hN256 hTdef heta heta1
  have hp := final_seam_parameter_adapter_of_cutoff hNposNat hTdef heta heta1
    hb.2.1 hb.2.2 hk
  let U : ℝ := 64 * T ^ 2
  have hT1 : 1 ≤ T := hb.1
  have hU1 : 1 ≤ U := by
    dsimp [U]
    have hT0 : 0 ≤ T := hT1.trans' (by norm_num)
    nlinarith [sq_nonneg T]
  have hSsmall : 4 * (W.card : ℝ) ^ 2 ≤ U := by
    have hsq : (W.card : ℝ) ^ 2 ≤ (2 * T) ^ 2 := by
      exact (sq_le_sq₀ (by positivity) (by positivity)).mpr hWle
    dsimp [U]
    nlinarith [hsq, sq_nonneg T]
  have hUpow : U ≤ U ^ 4 := by
    simpa using (pow_le_pow_right₀ hU1 (show (1 : ℕ) ≤ 4 by norm_num))
  have hSgrowth : 4 * (W.card : ℝ) ^ 2 ≤ U ^ 4 := hSsmall.trans hUpow
  have hU7 : 7 ≤ U := by
    dsimp [U]
    nlinarith [sq_nonneg T]
  simpa [U] using
    (And.intro hp.1 (And.intro hp.2.1 (And.intro hp.2.2
      (And.intro hSgrowth hU7))))

#print axioms GuthMaynardS3LiteralFinalSeamParameterAdapter.final_seam_parameter_adapter_of_cutoff
#print axioms GuthMaynardS3LiteralFinalSeamParameterAdapter.final_seam_eventual_bounds
#print axioms GuthMaynardS3LiteralFinalSeamParameterAdapter.final_seam_parameter_adapter

end
end GuthMaynardS3LiteralFinalSeamParameterAdapter
