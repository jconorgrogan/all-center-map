import GuthMaynardS3LiteralTruncation
import GuthMaynardS3LiteralRadialDecay
import GuthMaynardS3LiteralErrorContract

/-!
# Literal radial cube tail at the uniform `T⁻¹⁰⁶` reserve

This is the first concrete tail producer in the S3 continuation.  The
definitions are local to avoid pretending that the uncompiled Proposition 72
candidate is already in the dependency graph.
-/

namespace GuthMaynardS3LiteralUniform106Radial

open scoped BigOperators
open GuthMaynardS3LiteralTruncation
open GuthMaynardS3LiteralRadialDecay
open GuthMaynardS3LiteralLocalization
open GuthMaynardEquation55Infinite
open GuthMaynardS3LiteralErrorContract
open GuthMaynardSectionThreeCutoffDerivativeBudget

noncomputable section

def s3FrequencyCutoff (T eta : ℝ) (N : ℕ) : ℕ :=
  max 1 (Nat.floor (Real.rpow T (1 + eta) / (N : ℝ)))

def s3Rho (T eta : ℝ) : ℝ := Real.rpow T eta

def s3Uniform106DecayOrder (eta : ℝ) : ℕ :=
  GuthMaynardS3LiteralErrorContract.s3Uniform106DecayOrder eta

def s3RadialTail (N : ℕ) (W : Finset ℝ) (T eta : ℝ) : ℝ :=
  (9 / 4 : ℝ) * (N : ℝ) ^ 3 *
    radialDerivativeBudget (s3Uniform106DecayOrder eta) *
    (W.card : ℝ) ^ 3 /
      (s3Rho T eta) ^ s3Uniform106DecayOrder eta

def s3RadialCubeError (N : ℕ) (W : Finset ℝ) (T eta : ℝ) : ℝ :=
  ((prefixFrequencyCube (s3FrequencyCutoff T eta N)).card : ℝ) *
    s3RadialTail N W T eta

theorem nonzeroPrefix_card (M : ℕ) :
    (nonzeroPrefix M).card = 2 * M := by
  have hd : Disjoint ((Finset.Icc 1 M).image (fun m : ℕ => (m : ℤ)))
      ((Finset.Icc 1 M).image (fun m : ℕ => -(m : ℤ))) := by
    apply Finset.disjoint_left.mpr
    intro m hp hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, hb, h⟩ := Finset.mem_image.mp hn
    have ha' := (Finset.mem_Icc.mp ha).1
    have hb' := (Finset.mem_Icc.mp hb).1
    have : (a : ℤ) = -(b : ℤ) := h.symm
    have : (a : ℤ) ≤ 0 := by omega
    have : 0 < (a : ℤ) := by exact_mod_cast ha'
    omega
  have hpos : ((Finset.Icc 1 M).image (fun m : ℕ => (m : ℤ))).card = M := by
    rw [Finset.card_image_of_injective _ (by
      intro a b h
      dsimp only at h
      exact_mod_cast h)]
    rw [Nat.card_Icc]
    omega
  have hneg : ((Finset.Icc 1 M).image (fun m : ℕ => -(m : ℤ))).card = M := by
    rw [Finset.card_image_of_injective _ (by
      intro a b h
      dsimp only at h
      have h' : -(a : ℤ) = -(b : ℤ) := h
      have h'' : (a : ℤ) = (b : ℤ) := neg_injective h'
      exact_mod_cast h'')]
    rw [Nat.card_Icc]
    omega
  unfold nonzeroPrefix
  rw [Finset.card_union_of_disjoint hd, hpos, hneg]
  ring

theorem prefixFrequencyCube_card (M : ℕ) :
    (prefixFrequencyCube M).card = 8 * M ^ 3 := by
  unfold prefixFrequencyCube
  simp [Finset.card_product, nonzeroPrefix_card]
  ring

theorem s3Rho_pos {T eta : ℝ} (hT : 0 < T) (heta : 0 < eta) :
    0 < s3Rho T eta := by
  unfold s3Rho
  exact Real.rpow_pos_of_pos hT eta

theorem s3Rho_pow {T eta : ℝ} (hT : 0 ≤ T) (j : ℕ) :
    s3Rho T eta ^ j = Real.rpow T (eta * j) := by
  unfold s3Rho
  exact (Real.rpow_mul_natCast hT eta j).symm

theorem s3Cutoff_le_rpow {N : ℕ} (hN : 0 < N) {T eta : ℝ}
    (hT : 1 ≤ T)
    (hcut : 2 * (N : ℝ) ≤ Real.rpow T (1 + eta)) :
    (s3FrequencyCutoff T eta N : ℝ) ≤
      Real.rpow T (1 + eta) / (N : ℝ) := by
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hx : (2 : ℝ) ≤ Real.rpow T (1 + eta) / (N : ℝ) :=
    (le_div_iff₀ hNpos).mpr (by simpa [two_mul] using hcut)
  have hx1 : 1 ≤ Real.rpow T (1 + eta) / (N : ℝ) := le_trans (by norm_num) hx
  have hfloor :
      (Nat.floor (Real.rpow T (1 + eta) / (N : ℝ)) : ℝ) ≤
        Real.rpow T (1 + eta) / (N : ℝ) := by
    apply Nat.floor_le
    exact div_nonneg (Real.rpow_nonneg (by linarith [hT]) _) (by positivity)
  unfold s3FrequencyCutoff
  rw [Nat.cast_max]
  norm_num only [Nat.cast_one]
  exact max_le hx1 hfloor

theorem radial_uniform106_exponent {eta : ℝ} (heta : 0 < eta) :
    3 + 3 * eta - eta * (s3Uniform106DecayOrder eta : ℝ) ≤ -106 := by
  exact GuthMaynardS3LiteralErrorContract.radial_uniform106_exponent heta

theorem s3RadialCubeError_le_uniform106 {N : ℕ} (hN : 0 < N)
    {T eta : ℝ} (hT : 1 ≤ T) (heta : 0 < eta)
    (hcut : 2 * (N : ℝ) ≤ Real.rpow T (1 + eta))
    (W : Finset ℝ) (hNle : (N : ℝ) ≤ T)
    (hWle : (W.card : ℝ) ≤ 2 * T) :
    s3RadialCubeError N W T eta ≤
      18 * radialDerivativeBudget (s3Uniform106DecayOrder eta) *
        (8 * Real.rpow T (-100 : ℝ)) := by
  let j := s3Uniform106DecayOrder eta
  let M := s3FrequencyCutoff T eta N
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hT0 : 0 ≤ T := hTpos.le
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hMle := s3Cutoff_le_rpow hN hT hcut
  have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg _
  have hM3 : (M : ℝ) ^ 3 ≤
      Real.rpow T (3 + 3 * eta) / (N : ℝ) ^ 3 := by
    have hp := pow_le_pow_left₀ hM0 hMle 3
    have hr : Real.rpow T (1 + eta) ^ 3 =
        Real.rpow T (3 + 3 * eta) := by
      calc
        Real.rpow T (1 + eta) ^ (3 : ℕ) =
            Real.rpow (Real.rpow T (1 + eta)) (3 : ℝ) :=
          (Real.rpow_natCast _ 3).symm
        _ = Real.rpow T ((1 + eta) * (3 : ℝ)) :=
          (Real.rpow_mul hT0 (1 + eta) (3 : ℝ)).symm
        _ = Real.rpow T (3 + 3 * eta) := by
          congr 1
          ring
    calc
      (M : ℝ) ^ 3 ≤
          (Real.rpow T (1 + eta) / (N : ℝ)) ^ 3 := hp
      _ = Real.rpow T (1 + eta) ^ 3 / (N : ℝ) ^ 3 := by rw [div_pow]
      _ = Real.rpow T (3 + 3 * eta) / (N : ℝ) ^ 3 := by rw [hr]
  have hN3 : 0 ≤ (N : ℝ) ^ 3 := by positivity
  have hW3 : 0 ≤ (W.card : ℝ) ^ 3 := by positivity
  have hcard : ((prefixFrequencyCube M).card : ℝ) = 8 * (M : ℝ) ^ 3 := by
    rw [prefixFrequencyCube_card]
    norm_num
  have hcore :
      (M : ℝ) ^ 3 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 /
          (s3Rho T eta) ^ j ≤
        (W.card : ℝ) ^ 3 * Real.rpow T
          (3 + 3 * eta - eta * (j : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_right hM3 hN3
    have hmul' := mul_le_mul_of_nonneg_right hmul hW3
    have hrho : 0 < (s3Rho T eta) ^ j :=
      pow_pos (s3Rho_pos hTpos heta) _
    have hdiv := div_le_div_of_nonneg_right hmul' hrho.le
    have hrpow : (s3Rho T eta) ^ j = Real.rpow T (eta * (j : ℝ)) := by
      simpa only [Nat.cast_ofNat] using s3Rho_pow hT0 j
    calc
      (M : ℝ) ^ 3 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 /
          (s3Rho T eta) ^ j ≤
          (Real.rpow T (3 + 3 * eta) / (N : ℝ) ^ 3) *
            (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 /
              (s3Rho T eta) ^ j := hdiv
      _ = (W.card : ℝ) ^ 3 *
          Real.rpow T (3 + 3 * eta) /
            (s3Rho T eta) ^ j := by field_simp [hNpos.ne']
      _ = (W.card : ℝ) ^ 3 *
          Real.rpow T (3 + 3 * eta - eta * (j : ℝ)) := by
        have hsub : Real.rpow T (3 + 3 * eta) /
            Real.rpow T (eta * (j : ℝ)) =
            Real.rpow T (3 + 3 * eta - eta * (j : ℝ)) := by
          exact (Real.rpow_sub hTpos _ _).symm
        rw [hrpow]
        calc
          (W.card : ℝ) ^ 3 * Real.rpow T (3 + 3 * eta) /
              Real.rpow T (eta * (j : ℝ)) =
              (W.card : ℝ) ^ 3 *
                (Real.rpow T (3 + 3 * eta) /
                  Real.rpow T (eta * (j : ℝ))) := by ring
          _ = _ := by rw [hsub]
  have hsource :
      (W.card : ℝ) ^ 3 ≤
        (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 := by
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hN)
    have hN3one : (1 : ℝ) ≤ (N : ℝ) ^ 3 := by
      simpa only [one_pow] using
        (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hN1 3)
    exact le_mul_of_one_le_left hW3 hN3one
  have hexp := radial_uniform106_exponent heta
  have htime : Real.rpow T (3 + 3 * eta - eta * (j : ℝ)) ≤
      Real.rpow T (-106 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT hexp
  have hcore' :
      (M : ℝ) ^ 3 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 /
          (s3Rho T eta) ^ j ≤
        (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 * Real.rpow T (-106 : ℝ) := by
    exact hcore.trans ((mul_le_mul_of_nonneg_right hsource
      (Real.rpow_nonneg hT0 _)).trans
      (mul_le_mul_of_nonneg_left htime (by positivity)))
  have hbudget : 0 ≤ radialDerivativeBudget j := radialDerivativeBudget_nonneg j
  have hconvert := source_prefactor_time_neg106_le_eight_time_neg100
    hT hNle W hWle hbudget
  have hradial :
      18 * radialDerivativeBudget j *
          ((M : ℝ) ^ 3 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 /
            (s3Rho T eta) ^ j) ≤
        18 * radialDerivativeBudget j * (8 * Real.rpow T (-100 : ℝ)) := by
    have hleft := mul_le_mul_of_nonneg_left hcore'
      (show 0 ≤ (18 : ℝ) * radialDerivativeBudget j by
        exact mul_nonneg (by norm_num) (radialDerivativeBudget_nonneg j))
    have hright := mul_le_mul_of_nonneg_left hconvert
      (show 0 ≤ (18 : ℝ) by norm_num)
    exact hleft.trans (by simpa only [mul_assoc, mul_left_comm, mul_comm] using hright)
  unfold s3RadialCubeError s3RadialTail
  rw [hcard]
  dsimp only [M, j]
  convert hradial using 1 <;> ring

end
end GuthMaynardS3LiteralUniform106Radial

#print axioms GuthMaynardS3LiteralUniform106Radial.s3RadialCubeError_le_uniform106
