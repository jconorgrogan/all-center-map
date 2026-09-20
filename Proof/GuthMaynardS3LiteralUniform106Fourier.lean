import GuthMaynardS3LiteralUniform106Radial

/-!
# Literal Fourier truncation tail at the uniform `T⁻¹⁰⁶` reserve

The retained source error is the exact cubic telescoping term
`3*N^3*|W|^3*prefixError*prefixEnvelope^2`.  The cutoff lower bound is kept
explicit because it supplies the factor `T^(1+eta)/N` needed for decay.
-/

namespace GuthMaynardS3LiteralUniform106Fourier

open scoped BigOperators
open GuthMaynardS3LiteralTruncation
open GuthMaynardS3LiteralUniform106Radial
open GuthMaynardSectionThreeCutoffDerivativeBudget

noncomputable section

def s3FourierError (N : ℕ) (W : Finset ℝ) (T eta : ℝ) : ℝ :=
  3 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 *
    prefixError T N (s3FrequencyCutoff T eta N)
      (s3Uniform106DecayOrder eta) *
    prefixEnvelope T N (s3FrequencyCutoff T eta N)
      (s3Uniform106DecayOrder eta) ^ 2

def s3PrefixErrorCoeff (eta : ℝ) : ℝ :=
  lemma43DerivativeConstant (s3Uniform106DecayOrder eta) *
    (4 : ℝ) ^ s3Uniform106DecayOrder eta /
      ((s3Uniform106DecayOrder eta : ℝ) - 1)

def s3SourceFactor (N : ℕ) (W : Finset ℝ) : ℝ :=
  (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3

theorem s3SourceFactor_nonneg (N : ℕ) (W : Finset ℝ) :
    0 ≤ s3SourceFactor N W := by
  unfold s3SourceFactor
  positivity

theorem s3PrefixErrorCoeff_nonneg (eta : ℝ) :
    0 ≤ s3PrefixErrorCoeff eta := by
  unfold s3PrefixErrorCoeff
  apply div_nonneg
  · exact mul_nonneg (lemma43DerivativeConstant_nonneg _) (by positivity)
  · have h : 4 ≤ s3Uniform106DecayOrder eta := by
      dsimp [s3Uniform106DecayOrder,
        GuthMaynardS3LiteralErrorContract.s3Uniform106DecayOrder]
      have hc : 0 ≤ Nat.ceil (110 / eta) := Nat.zero_le _
      omega
    have hR : (4 : ℝ) ≤ (s3Uniform106DecayOrder eta : ℝ) := by
      exact_mod_cast h
    linarith

theorem s3Cutoff_ge_half {N : ℕ} (hN : 0 < N) {T eta : ℝ}
    (hT : 1 ≤ T)
    (hcut : 2 * (N : ℝ) ≤ Real.rpow T (1 + eta)) :
    Real.rpow T (1 + eta) / (2 * (N : ℝ)) ≤
      s3FrequencyCutoff T eta N := by
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hx : (2 : ℝ) ≤ Real.rpow T (1 + eta) / (N : ℝ) :=
    (le_div_iff₀ hNpos).mpr (by simpa [two_mul] using hcut)
  let x : ℝ := Real.rpow T (1 + eta) / (N : ℝ)
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hfl : x - 1 ≤ (Nat.floor x : ℝ) := by
    have h := Nat.lt_floor_add_one x
    linarith
  have hhalf : x / 2 ≤ x - 1 := by linarith
  have hxdiv : Real.rpow T (1 + eta) / (2 * (N : ℝ)) = x / 2 := by
    dsimp [x]
    field_simp
  unfold s3FrequencyCutoff
  rw [hxdiv]
  have hmax : (Nat.floor x : ℝ) ≤ (max 1 (Nat.floor x) : ℝ) := by
    exact_mod_cast le_max_right 1 _
  have : x / 2 ≤ (max 1 (Nat.floor x) : ℝ) := hhalf.trans hfl |>.trans hmax
  simpa [x] using this

theorem s3Cutoff_pow_le {N : ℕ} (hN : 0 < N) {T eta : ℝ}
    (hT : 1 ≤ T)
    (hcut : 2 * (N : ℝ) ≤ Real.rpow T (1 + eta)) (k : ℕ) :
    (s3FrequencyCutoff T eta N : ℝ) ^ k ≤
      Real.rpow T ((1 + eta) * k) / (N : ℝ) ^ k := by
  have hle := s3Cutoff_le_rpow hN hT hcut
  have h0 : 0 ≤ (s3FrequencyCutoff T eta N : ℝ) := Nat.cast_nonneg _
  have hp := pow_le_pow_left₀ h0 hle k
  have hrpow : Real.rpow T (1 + eta) ^ k =
      Real.rpow T ((1 + eta) * k) := by
    have hT0 : 0 ≤ T := le_trans (by norm_num) hT
    calc
      Real.rpow T (1 + eta) ^ k =
          Real.rpow (Real.rpow T (1 + eta)) (k : ℝ) :=
        (Real.rpow_natCast _ k).symm
      _ = Real.rpow T ((1 + eta) * (k : ℝ)) :=
        (Real.rpow_mul hT0 (1 + eta) (k : ℝ)).symm
      _ = _ := by rfl
  calc
    (s3FrequencyCutoff T eta N : ℝ) ^ k ≤
        (Real.rpow T (1 + eta) / (N : ℝ)) ^ k := hp
    _ = Real.rpow T (1 + eta) ^ k / (N : ℝ) ^ k := by rw [div_pow]
    _ = Real.rpow T ((1 + eta) * k) / (N : ℝ) ^ k := by rw [hrpow]

theorem rpow_N_neg {N j : ℕ} :
    Real.rpow (N : ℝ) (-(j : ℝ)) = ((N : ℝ) ^ j)⁻¹ := by
    calc
      Real.rpow (N : ℝ) (-(j : ℝ)) =
        (Real.rpow (N : ℝ) (j : ℝ))⁻¹ :=
      Real.rpow_neg (Nat.cast_nonneg N) (j : ℝ)
    _ = ((N : ℝ) ^ j)⁻¹ := by
      exact congrArg Inv.inv (Real.rpow_natCast (N : ℝ) j)

theorem rpow_M_one_sub {M j : ℕ} (hj : 1 ≤ j) :
    Real.rpow (M : ℝ) (1 - (j : ℝ)) = ((M : ℝ) ^ (j - 1))⁻¹ := by
  have heq : (1 : ℝ) - j = -((j - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hj]
    ring
  rw [heq]
  calc
    Real.rpow (M : ℝ) (-((j - 1 : ℕ) : ℝ)) =
        (Real.rpow (M : ℝ) ((j - 1 : ℕ) : ℝ))⁻¹ :=
      Real.rpow_neg (Nat.cast_nonneg M) _
    _ = ((M : ℝ) ^ (j - 1))⁻¹ := by
      exact congrArg Inv.inv (Real.rpow_natCast (M : ℝ) (j - 1))

theorem specialized_time_ratio {T eta : ℝ} (hT : 0 < T) {j : ℕ}
    (hj : 1 ≤ j) :
    T ^ j / Real.rpow T ((1 + eta) * (j - 1 : ℕ)) =
      Real.rpow T (1 - eta * (j - 1 : ℕ)) := by
  have hnum : T ^ j = Real.rpow T (j : ℝ) :=
    (Real.rpow_natCast T j).symm
  have hexp : (j : ℝ) - (1 + eta) * (j - 1 : ℕ) =
      1 - eta * (j - 1 : ℕ) := by
    have hjR : (j : ℝ) = ((j - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (Nat.sub_add_cancel hj).symm
    rw [hjR]
    ring
  calc
    T ^ j / Real.rpow T ((1 + eta) * (j - 1 : ℕ)) =
        Real.rpow T (j : ℝ) /
          Real.rpow T ((1 + eta) * (j - 1 : ℕ)) := by rw [hnum]
    _ = Real.rpow T ((j : ℝ) - (1 + eta) * (j - 1 : ℕ)) :=
      (Real.rpow_sub hT _ _).symm
    _ = _ := by rw [hexp]

theorem prefixError_specialized_le_uniform106 {N : ℕ} (hN : 0 < N)
    {T eta : ℝ} (hT : 1 ≤ T)
    (hcut : 2 * (N : ℝ) ≤ Real.rpow T (1 + eta)) :
    prefixError T N (s3FrequencyCutoff T eta N)
        (s3Uniform106DecayOrder eta) ≤
      s3PrefixErrorCoeff eta *
        Real.rpow T (1 - eta *
          (s3Uniform106DecayOrder eta - 1 : ℕ)) / (N : ℝ) := by
  let j := s3Uniform106DecayOrder eta
  let M := s3FrequencyCutoff T eta N
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hT0 : 0 ≤ T := hTpos.le
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hj : 1 ≤ j := by
    dsimp [j, s3Uniform106DecayOrder,
      GuthMaynardS3LiteralErrorContract.s3Uniform106DecayOrder]
    have hc : 0 ≤ Nat.ceil (110 / eta) := Nat.zero_le _
    omega
  have hjpos : (0 : ℝ) < (j : ℝ) - 1 := by
    have : 4 ≤ j := by
      dsimp [j, s3Uniform106DecayOrder,
        GuthMaynardS3LiteralErrorContract.s3Uniform106DecayOrder]
      have hc : 0 ≤ Nat.ceil (110 / eta) := Nat.zero_le _
      omega
    have hR : (4 : ℝ) ≤ (j : ℝ) := by exact_mod_cast this
    linarith
  have hM1 : 1 ≤ M := by unfold M s3FrequencyCutoff; exact le_max_left _ _
  have hMpos : 0 < (M : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le zero_lt_one hM1)
  have hCj := lemma43DerivativeConstant_nonneg j
  have hlo := s3Cutoff_ge_half hN hT hcut
  have hbase0 : 0 ≤ Real.rpow T (1 + eta) / (2 * (N : ℝ)) := by
    exact div_nonneg (Real.rpow_nonneg hT0 _) (by positivity)
  have hMpow : (Real.rpow T (1 + eta) / (2 * (N : ℝ))) ^ (j - 1) ≤
      (M : ℝ) ^ (j - 1) :=
    pow_le_pow_left₀ hbase0 hlo (j - 1)
  have hMpowPos : 0 < (M : ℝ) ^ (j - 1) := pow_pos hMpos _
  have hloPos : 0 < (Real.rpow T (1 + eta) / (2 * (N : ℝ))) ^ (j - 1) :=
    pow_pos (div_pos (Real.rpow_pos_of_pos hTpos _) (by positivity)) _
  have hinvM : ((M : ℝ) ^ (j - 1))⁻¹ ≤
      (2 * (N : ℝ)) ^ (j - 1) /
        Real.rpow T ((1 + eta) * (j - 1 : ℕ)) := by
    have hrpow : Real.rpow T (1 + eta) ^ (j - 1) =
        Real.rpow T ((1 + eta) * (j - 1 : ℕ)) := by
      calc
        Real.rpow T (1 + eta) ^ (j - 1) =
            Real.rpow (Real.rpow T (1 + eta)) ((j - 1 : ℕ) : ℝ) :=
          (Real.rpow_natCast _ (j - 1)).symm
        _ = Real.rpow T ((1 + eta) * ((j - 1 : ℕ) : ℝ)) :=
          (Real.rpow_mul hT0 (1 + eta) ((j - 1 : ℕ) : ℝ)).symm
        _ = _ := by rfl
    have hinv0 : ((M : ℝ) ^ (j - 1))⁻¹ ≤
        ((Real.rpow T (1 + eta) / (2 * (N : ℝ))) ^ (j - 1))⁻¹ :=
      (inv_le_inv₀ hMpowPos hloPos).mpr hMpow
    calc
      ((M : ℝ) ^ (j - 1))⁻¹ ≤
          ((Real.rpow T (1 + eta) / (2 * (N : ℝ))) ^ (j - 1))⁻¹ := hinv0
      _ = ((2 * (N : ℝ)) / Real.rpow T (1 + eta)) ^ (j - 1) := by
        rw [← inv_pow, inv_div]
      _ = (2 * (N : ℝ)) ^ (j - 1) /
          Real.rpow T (1 + eta) ^ (j - 1) := by rw [div_pow]
      _ = (2 * (N : ℝ)) ^ (j - 1) /
          Real.rpow T ((1 + eta) * (j - 1 : ℕ)) := by rw [hrpow]
  have h1T : (1 + T) ^ j ≤ (2 * T) ^ j :=
    pow_le_pow_left₀ (by positivity) (by linarith) j
  have h2T : (2 * T) ^ j = (2 : ℝ) ^ j * T ^ j := mul_pow _ _ _
  have hNrpow := rpow_N_neg (N := N) (j := j)
  have hMrpow := rpow_M_one_sub (M := M) (j := j) hj
  have hratio := specialized_time_ratio (eta := eta) hTpos hj
  have htwo : (2 * (N : ℝ)) ^ (j - 1) =
      (2 : ℝ) ^ (j - 1) * (N : ℝ) ^ (j - 1) := mul_pow _ _ _
  have hpow4 : (2 : ℝ) * (2 : ℝ) ^ j * (2 : ℝ) ^ (j - 1) =
      (4 : ℝ) ^ j := by
    have hnat : 1 + j + (j - 1) = 2 * j := by omega
    calc
      (2 : ℝ) * (2 : ℝ) ^ j * (2 : ℝ) ^ (j - 1) =
          (2 : ℝ) ^ (1 + j + (j - 1)) := by
            calc
              (2 : ℝ) * (2 : ℝ) ^ j * (2 : ℝ) ^ (j - 1) =
                  (2 : ℝ) ^ 1 * (2 : ℝ) ^ j * (2 : ℝ) ^ (j - 1) := by norm_num
              _ = (2 : ℝ) ^ (1 + j) * (2 : ℝ) ^ (j - 1) := by
                rw [← pow_add]
              _ = (2 : ℝ) ^ (1 + j + (j - 1)) := by
                rw [← pow_add]
      _ = (2 : ℝ) ^ (2 * j) := by rw [hnat]
      _ = ((2 : ℝ) ^ 2) ^ j := by rw [pow_mul]
      _ = (4 : ℝ) ^ j := by norm_num
  have hP : 0 ≤ 2 * lemma43DerivativeConstant j / ((j : ℝ) - 1) :=
    div_nonneg (mul_nonneg (by norm_num) hCj) hjpos.le
  have hMneg : 0 ≤ Real.rpow (M : ℝ) (1 - (j : ℝ)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hE : prefixError T N M j =
      (2 * lemma43DerivativeConstant j / ((j : ℝ) - 1)) *
        ((1 + T) ^ j * Real.rpow (N : ℝ) (-(j : ℝ)) *
          Real.rpow (M : ℝ) (1 - (j : ℝ))) := by
    unfold prefixError
    field_simp [hjpos.ne']
  have hprod1 :
      (1 + T) ^ j * Real.rpow (N : ℝ) (-(j : ℝ)) *
          Real.rpow (M : ℝ) (1 - (j : ℝ)) ≤
        ((2 : ℝ) ^ j * T ^ j) * ((N : ℝ) ^ j)⁻¹ *
          ((2 * (N : ℝ)) ^ (j - 1) /
            Real.rpow T ((1 + eta) * (j - 1 : ℕ))) := by
    have hleft : (1 + T) ^ j * Real.rpow (N : ℝ) (-(j : ℝ)) ≤
        ((2 : ℝ) ^ j * T ^ j) * ((N : ℝ) ^ j)⁻¹ := by
      rw [hNrpow]
      exact mul_le_mul_of_nonneg_right (h1T.trans_eq h2T) (by positivity)
    have hright : Real.rpow (M : ℝ) (1 - (j : ℝ)) ≤
        (2 * (N : ℝ)) ^ (j - 1) /
          Real.rpow T ((1 + eta) * (j - 1 : ℕ)) := by
      rw [hMrpow]
      exact hinvM
    exact mul_le_mul hleft hright hMneg
      (mul_nonneg (by positivity) (by positivity))
  have hprod2 :
      ((2 : ℝ) ^ j * T ^ j) * ((N : ℝ) ^ j)⁻¹ *
          ((2 * (N : ℝ)) ^ (j - 1) /
            Real.rpow T ((1 + eta) * (j - 1 : ℕ))) =
        ((2 : ℝ) ^ j * (2 : ℝ) ^ (j - 1)) *
          (T ^ j / Real.rpow T ((1 + eta) * (j - 1 : ℕ))) /
            (N : ℝ) := by
    rw [htwo]
    have hNj : (N : ℝ) ^ (j - 1) * ((N : ℝ) ^ j)⁻¹ =
        (N : ℝ)⁻¹ := by
      have hj' : j = (j - 1) + 1 := (Nat.sub_add_cancel hj).symm
      rw [hj', pow_add, pow_one]
      calc
        _ = (N : ℝ)⁻¹ *
            ((N : ℝ) ^ (j - 1) * ((N : ℝ) ^ (j - 1))⁻¹) := by
          rw [show j - 1 + 1 - 1 = j - 1 by omega]
          field_simp [hNpos.ne']
        _ = (N : ℝ)⁻¹ := by
          rw [mul_inv_cancel₀ (pow_ne_zero _ hNpos.ne')]
          ring
    simp only [div_eq_mul_inv]
    calc
      (2 : ℝ) ^ j * T ^ j * ((N : ℝ) ^ j)⁻¹ *
          ((2 : ℝ) ^ (j - 1) * (N : ℝ) ^ (j - 1) *
            (Real.rpow T ((1 + eta) * (j - 1 : ℕ)))⁻¹) =
        ((2 : ℝ) ^ j * (2 : ℝ) ^ (j - 1)) *
          (T ^ j * (Real.rpow T ((1 + eta) * (j - 1 : ℕ)))⁻¹) *
          ((N : ℝ) ^ (j - 1) * ((N : ℝ) ^ j)⁻¹) := by ring
      _ = ((2 : ℝ) ^ j * (2 : ℝ) ^ (j - 1)) *
          (T ^ j * (Real.rpow T ((1 + eta) * (j - 1 : ℕ)))⁻¹) *
          (N : ℝ)⁻¹ := by rw [hNj]
  have hPmul :
      (2 * lemma43DerivativeConstant j / ((j : ℝ) - 1)) *
          ((2 : ℝ) ^ j * (2 : ℝ) ^ (j - 1)) =
        lemma43DerivativeConstant j * (4 : ℝ) ^ j /
          ((j : ℝ) - 1) := by
    calc
      (2 * lemma43DerivativeConstant j / ((j : ℝ) - 1)) *
          ((2 : ℝ) ^ j * (2 : ℝ) ^ (j - 1)) =
        (lemma43DerivativeConstant j / ((j : ℝ) - 1)) *
          ((2 : ℝ) * (2 : ℝ) ^ j * (2 : ℝ) ^ (j - 1)) := by ring
      _ = (lemma43DerivativeConstant j / ((j : ℝ) - 1)) * (4 : ℝ) ^ j := by
        rw [hpow4]
      _ = lemma43DerivativeConstant j * (4 : ℝ) ^ j /
          ((j : ℝ) - 1) := by ring
  calc
    prefixError T N M j =
        (2 * lemma43DerivativeConstant j / ((j : ℝ) - 1)) *
          ((1 + T) ^ j * Real.rpow (N : ℝ) (-(j : ℝ)) *
            Real.rpow (M : ℝ) (1 - (j : ℝ))) := hE
    _ ≤ (2 * lemma43DerivativeConstant j / ((j : ℝ) - 1)) *
          (((2 : ℝ) ^ j * T ^ j) * ((N : ℝ) ^ j)⁻¹ *
            ((2 * (N : ℝ)) ^ (j - 1) /
              Real.rpow T ((1 + eta) * (j - 1 : ℕ)))) :=
      mul_le_mul_of_nonneg_left hprod1 hP
    _ = (2 * lemma43DerivativeConstant j / ((j : ℝ) - 1)) *
          (((2 : ℝ) ^ j * (2 : ℝ) ^ (j - 1)) *
            (T ^ j / Real.rpow T ((1 + eta) * (j - 1 : ℕ))) /
              (N : ℝ)) := by rw [hprod2]
    _ = ((2 * lemma43DerivativeConstant j / ((j : ℝ) - 1)) *
          ((2 : ℝ) ^ j * (2 : ℝ) ^ (j - 1))) *
            (T ^ j / Real.rpow T ((1 + eta) * (j - 1 : ℕ))) /
              (N : ℝ) := by ring
    _ = (lemma43DerivativeConstant j * (4 : ℝ) ^ j /
          ((j : ℝ) - 1)) *
            (T ^ j / Real.rpow T ((1 + eta) * (j - 1 : ℕ))) /
              (N : ℝ) := by rw [hPmul]
    _ = s3PrefixErrorCoeff eta *
          Real.rpow T (1 - eta * (j - 1 : ℕ)) / (N : ℝ) := by
      rw [hratio]
      simp [s3PrefixErrorCoeff, j]

theorem prefixError_mul_cutoff_sq_le_uniform106 {N : ℕ} (hN : 0 < N)
    {T eta : ℝ} (hT : 1 ≤ T)
    (hcut : 2 * (N : ℝ) ≤ Real.rpow T (1 + eta)) :
    (s3FrequencyCutoff T eta N : ℝ) ^ 2 *
        prefixError T N (s3FrequencyCutoff T eta N)
          (s3Uniform106DecayOrder eta) ≤
      s3PrefixErrorCoeff eta *
        Real.rpow T (3 + 2 * eta - eta *
          (s3Uniform106DecayOrder eta - 1 : ℕ)) /
          (N : ℝ) ^ 3 := by
  let j := s3Uniform106DecayOrder eta
  let M := s3FrequencyCutoff T eta N
  have hE := prefixError_specialized_le_uniform106 hN hT hcut
  have hE0 : 0 ≤ prefixError T N M j := by
    exact prefixError_nonneg (le_trans (by norm_num) hT) N M j (by
      dsimp [j, s3Uniform106DecayOrder,
        GuthMaynardS3LiteralErrorContract.s3Uniform106DecayOrder]
      have hc : 0 ≤ Nat.ceil (110 / eta) := Nat.zero_le _
      omega)
  have hM2 := s3Cutoff_pow_le hN hT hcut 2
  have h2' : ((1 + eta) * (2 : ℕ) : ℝ) = 2 + 2 * eta := by
    ring
  rw [h2'] at hM2
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hT0 : 0 ≤ T := hTpos.le
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hprod := mul_le_mul hM2 hE hE0
    (div_nonneg (Real.rpow_nonneg hT0 _) (by positivity))
  have hadd : Real.rpow T (2 + 2 * eta) *
      Real.rpow T (1 - eta * (j - 1 : ℕ)) =
        Real.rpow T (3 + 2 * eta - eta * (j - 1 : ℕ)) := by
    calc
      Real.rpow T (2 + 2 * eta) *
          Real.rpow T (1 - eta * (j - 1 : ℕ)) =
        Real.rpow T ((2 + 2 * eta) +
          (1 - eta * (j - 1 : ℕ))) :=
        (Real.rpow_add hTpos _ _).symm
      _ = Real.rpow T (3 + 2 * eta - eta * (j - 1 : ℕ)) := by
        congr 1
        ring
  have hNpow : (N : ℝ) ^ 2 * (N : ℝ) = (N : ℝ) ^ 3 := by ring
  calc
    (s3FrequencyCutoff T eta N : ℝ) ^ 2 *
        prefixError T N (s3FrequencyCutoff T eta N)
          (s3Uniform106DecayOrder eta) ≤
      (Real.rpow T (2 + 2 * eta) / (N : ℝ) ^ 2) *
        (s3PrefixErrorCoeff eta *
          Real.rpow T (1 - eta * (j - 1 : ℕ)) / (N : ℝ)) := by
      exact hprod
    _ = s3PrefixErrorCoeff eta *
          (Real.rpow T (2 + 2 * eta) *
            Real.rpow T (1 - eta * (j - 1 : ℕ))) /
          ((N : ℝ) ^ 2 * (N : ℝ)) := by
      field_simp [hNpos.ne']
      
    _ = s3PrefixErrorCoeff eta *
          Real.rpow T (3 + 2 * eta - eta * (j - 1 : ℕ)) /
          (N : ℝ) ^ 3 := by rw [hadd, hNpow]
    _ = _ := by rfl

theorem prefixError_pow_three_le_uniform106 {N : ℕ} (hN : 0 < N)
    {T eta : ℝ} (hT : 1 ≤ T)
    (hcut : 2 * (N : ℝ) ≤ Real.rpow T (1 + eta)) :
    prefixError T N (s3FrequencyCutoff T eta N)
        (s3Uniform106DecayOrder eta) ^ 3 ≤
      s3PrefixErrorCoeff eta ^ 3 *
        Real.rpow T (3 - 3 * eta *
          (s3Uniform106DecayOrder eta - 1 : ℕ)) /
          (N : ℝ) ^ 3 := by
  let j := s3Uniform106DecayOrder eta
  have hE := prefixError_specialized_le_uniform106 hN hT hcut
  have hE0 : 0 ≤ prefixError T N (s3FrequencyCutoff T eta N) j := by
    exact prefixError_nonneg (le_trans (by norm_num) hT) N _ j (by
      dsimp [j, s3Uniform106DecayOrder,
        GuthMaynardS3LiteralErrorContract.s3Uniform106DecayOrder]
      have hc : 0 ≤ Nat.ceil (110 / eta) := Nat.zero_le _
      omega)
  have hpow := pow_le_pow_left₀ hE0 hE 3
  have hcube :
      (s3PrefixErrorCoeff eta *
          Real.rpow T (1 - eta * (j - 1 : ℕ)) / (N : ℝ)) ^ 3 =
        s3PrefixErrorCoeff eta ^ 3 *
          Real.rpow T (3 - 3 * eta * (j - 1 : ℕ)) /
            (N : ℝ) ^ 3 := by
    rw [div_pow, mul_pow]
    have hrpow : Real.rpow T (1 - eta * (j - 1 : ℕ)) ^ 3 =
        Real.rpow T ((1 - eta * (j - 1 : ℕ)) * 3) := by
      calc
        Real.rpow T (1 - eta * (j - 1 : ℕ)) ^ (3 : ℕ) =
            Real.rpow (Real.rpow T (1 - eta * (j - 1 : ℕ))) (3 : ℝ) :=
          (Real.rpow_natCast _ 3).symm
        _ = Real.rpow T ((1 - eta * (j - 1 : ℕ)) * (3 : ℝ)) :=
          (Real.rpow_mul (le_trans (by norm_num) hT)
            (1 - eta * (j - 1 : ℕ)) (3 : ℝ)).symm
    rw [hrpow]
    congr 2
    ring
  exact hpow.trans_eq hcube

theorem prefixEnvelope_sq_le_uniform106 {T : ℝ} (hT : 0 ≤ T)
    (N M j : ℕ) :
    prefixEnvelope T N M j ^ 2 ≤
      8 * (M : ℝ) ^ 2 * lemma43DerivativeConstant 0 ^ 2 +
        2 * prefixError T N M j ^ 2 := by
  unfold prefixEnvelope
  nlinarith [sq_nonneg (2 * (M : ℝ) * lemma43DerivativeConstant 0 -
    prefixError T N M j)]

theorem s3FourierError_le_uniform106 {N : ℕ} (hN : 0 < N)
    {T eta : ℝ} (hT : 1 ≤ T) (heta : 0 < eta)
    (hcut : 2 * (N : ℝ) ≤ Real.rpow T (1 + eta))
    (W : Finset ℝ) (hNle : (N : ℝ) ≤ T)
    (hWle : (W.card : ℝ) ≤ 2 * T) :
    s3FourierError N W T eta ≤
    (24 * lemma43DerivativeConstant 0 ^ 2 * s3PrefixErrorCoeff eta +
          6 * s3PrefixErrorCoeff eta ^ 3) *
        (8 * Real.rpow T (-100 : ℝ)) := by
  let j := s3Uniform106DecayOrder eta
  let M := s3FrequencyCutoff T eta N
  let E := prefixError T N M j
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hT0 : 0 ≤ T := hTpos.le
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hj2 : 2 ≤ j := by
    dsimp [j, s3Uniform106DecayOrder,
      GuthMaynardS3LiteralErrorContract.s3Uniform106DecayOrder]
    have hc : 0 ≤ Nat.ceil (110 / eta) := Nat.zero_le _
    omega
  have hE0 : 0 ≤ E := by
    exact prefixError_nonneg hT0 N M j hj2
  have hK : 0 ≤ s3PrefixErrorCoeff eta := s3PrefixErrorCoeff_nonneg eta
  have hW0 : 0 ≤ (W.card : ℝ) ^ 3 := by positivity
  have henv := prefixEnvelope_sq_le_uniform106 hT0 N M j
  have hME := prefixError_mul_cutoff_sq_le_uniform106 hN hT hcut
  have hE3 := prefixError_pow_three_le_uniform106 hN hT hcut
  have hfexp := GuthMaynardS3LiteralErrorContract.fourier_uniform106_exponent heta
  have hcexp := GuthMaynardS3LiteralErrorContract.cubic_uniform106_exponent heta
  have hprod :
      E * prefixEnvelope T N M j ^ 2 ≤
        8 * (M : ℝ) ^ 2 * lemma43DerivativeConstant 0 ^ 2 * E +
          2 * E ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_left henv hE0
    have hring : E * (8 * (M : ℝ) ^ 2 *
          lemma43DerivativeConstant 0 ^ 2 + 2 * E ^ 2) =
        8 * (M : ℝ) ^ 2 * lemma43DerivativeConstant 0 ^ 2 * E +
          2 * E ^ 3 := by ring
    exact hmul.trans_eq hring
  have hscale : 0 ≤ 3 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 := by positivity
  have hmain :
      3 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 *
          (E * prefixEnvelope T N M j ^ 2) ≤
        24 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 *
            lemma43DerivativeConstant 0 ^ 2 * ((M : ℝ) ^ 2 * E) +
          6 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 * E ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_left hprod hscale
    have hring : 3 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 *
          (8 * (M : ℝ) ^ 2 * lemma43DerivativeConstant 0 ^ 2 * E +
            2 * E ^ 3) =
        24 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 *
            lemma43DerivativeConstant 0 ^ 2 * ((M : ℝ) ^ 2 * E) +
          6 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 * E ^ 3 := by ring
    exact hmul.trans_eq hring
  have hrewF : s3FourierError N W T eta =
      3 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 *
        (E * prefixEnvelope T N M j ^ 2) := by
    unfold s3FourierError
    dsimp only [E, M, j]
    ring
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hN)
  have hN3one : (1 : ℝ) ≤ (N : ℝ) ^ 3 := by
    simpa only [one_pow] using
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hN1 3)
  have hsource : (W.card : ℝ) ^ 3 ≤
      (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 :=
    le_mul_of_one_le_left (by positivity) hN3one
  have hr106 : 0 ≤ Real.rpow T (-106 : ℝ) := Real.rpow_nonneg hT0 _
  have hterm1 :
      24 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 *
          lemma43DerivativeConstant 0 ^ 2 * ((M : ℝ) ^ 2 * E) ≤
        24 * lemma43DerivativeConstant 0 ^ 2 * s3PrefixErrorCoeff eta *
          s3SourceFactor N W * Real.rpow T (-106 : ℝ) := by
    have hN3E : (N : ℝ) ^ 3 * ((M : ℝ) ^ 2 * E) ≤
        s3PrefixErrorCoeff eta * Real.rpow T (-106 : ℝ) := by
      have hME' : (M : ℝ) ^ 2 * E ≤
          s3PrefixErrorCoeff eta * Real.rpow T
            (3 + 2 * eta - eta * (j - 1 : ℕ)) /
              (N : ℝ) ^ 3 := by
        simpa [M, j] using hME
      have hle := mul_le_mul_of_nonneg_left hME' (by positivity)
      have hfexp' : 3 + 2 * eta - eta * (j - 1 : ℕ) ≤ -106 := by
        simpa [j, s3Uniform106DecayOrder] using
          GuthMaynardS3LiteralErrorContract.fourier_uniform106_exponent heta
      have htime := Real.rpow_le_rpow_of_exponent_le hT hfexp'
      have hle' : (N : ℝ) ^ 3 * ((M : ℝ) ^ 2 * E) ≤
          s3PrefixErrorCoeff eta * Real.rpow T
            (3 + 2 * eta - eta * (j - 1 : ℕ)) := by
        field_simp [hNpos.ne'] at hle ⊢
        exact hle
      exact hle'.trans (mul_le_mul_of_nonneg_left htime hK)
    have hmid : (W.card : ℝ) ^ 3 *
          ((N : ℝ) ^ 3 * ((M : ℝ) ^ 2 * E)) ≤
        (W.card : ℝ) ^ 3 *
          (s3PrefixErrorCoeff eta * Real.rpow T (-106 : ℝ)) :=
      mul_le_mul_of_nonneg_left hN3E hW0
    have hchain : (W.card : ℝ) ^ 3 *
          (s3PrefixErrorCoeff eta * Real.rpow T (-106 : ℝ)) ≤
        s3PrefixErrorCoeff eta * s3SourceFactor N W *
          Real.rpow T (-106 : ℝ) := by
      calc
        _ = s3PrefixErrorCoeff eta *
            ((W.card : ℝ) ^ 3 * Real.rpow T (-106 : ℝ)) := by ring
        _ ≤ s3PrefixErrorCoeff eta *
            ((N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 *
              Real.rpow T (-106 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hsource hr106) hK
        _ = _ := by
          unfold s3SourceFactor
          ring
    have hconst : 0 ≤ 24 * lemma43DerivativeConstant 0 ^ 2 := by
      positivity
    calc
      24 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 *
          lemma43DerivativeConstant 0 ^ 2 * ((M : ℝ) ^ 2 * E) =
        (24 * lemma43DerivativeConstant 0 ^ 2) *
          ((W.card : ℝ) ^ 3 * ((N : ℝ) ^ 3 * ((M : ℝ) ^ 2 * E))) := by ring
      _ ≤ (24 * lemma43DerivativeConstant 0 ^ 2) *
          ((W.card : ℝ) ^ 3 *
            (s3PrefixErrorCoeff eta * Real.rpow T (-106 : ℝ))) :=
        mul_le_mul_of_nonneg_left hmid hconst
      _ ≤ (24 * lemma43DerivativeConstant 0 ^ 2) *
          (s3PrefixErrorCoeff eta * s3SourceFactor N W *
            Real.rpow T (-106 : ℝ)) :=
        mul_le_mul_of_nonneg_left hchain hconst
      _ = _ := by ring
  have hterm2 :
      6 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 * E ^ 3 ≤
        6 * s3PrefixErrorCoeff eta ^ 3 * s3SourceFactor N W *
          Real.rpow T (-106 : ℝ) := by
    have hK3 : 0 ≤ s3PrefixErrorCoeff eta ^ 3 := pow_nonneg hK 3
    have hN3E : (N : ℝ) ^ 3 * E ^ 3 ≤
        s3PrefixErrorCoeff eta ^ 3 * Real.rpow T (-106 : ℝ) := by
      have hE3' : E ^ 3 ≤ s3PrefixErrorCoeff eta ^ 3 * Real.rpow T
          (3 - 3 * eta * (j - 1 : ℕ)) /
            (N : ℝ) ^ 3 := by
        simpa [M, j] using hE3
      have hle := mul_le_mul_of_nonneg_left hE3' (by positivity)
      have hcexp' : 3 - 3 * eta * (j - 1 : ℕ) ≤ -106 := by
        simpa [j, s3Uniform106DecayOrder] using
          GuthMaynardS3LiteralErrorContract.cubic_uniform106_exponent heta
      have htime := Real.rpow_le_rpow_of_exponent_le hT hcexp'
      have hle' : (N : ℝ) ^ 3 * E ^ 3 ≤
          s3PrefixErrorCoeff eta ^ 3 * Real.rpow T
            (3 - 3 * eta * (j - 1 : ℕ)) := by
        field_simp [hNpos.ne'] at hle ⊢
        exact hle
      exact hle'.trans (mul_le_mul_of_nonneg_left htime hK3)
    have hmid : (W.card : ℝ) ^ 3 * ((N : ℝ) ^ 3 * E ^ 3) ≤
        (W.card : ℝ) ^ 3 *
          (s3PrefixErrorCoeff eta ^ 3 * Real.rpow T (-106 : ℝ)) :=
      mul_le_mul_of_nonneg_left hN3E hW0
    have hchain : (W.card : ℝ) ^ 3 *
          (s3PrefixErrorCoeff eta ^ 3 * Real.rpow T (-106 : ℝ)) ≤
        s3PrefixErrorCoeff eta ^ 3 * s3SourceFactor N W *
          Real.rpow T (-106 : ℝ) := by
      calc
        _ = s3PrefixErrorCoeff eta ^ 3 *
            ((W.card : ℝ) ^ 3 * Real.rpow T (-106 : ℝ)) := by ring
        _ ≤ s3PrefixErrorCoeff eta ^ 3 *
            ((N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 *
              Real.rpow T (-106 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hsource hr106) hK3
        _ = _ := by
          unfold s3SourceFactor
          ring
    have hconst : 0 ≤ (6 : ℝ) := by norm_num
    calc
      6 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 * E ^ 3 =
        6 * ((W.card : ℝ) ^ 3 * ((N : ℝ) ^ 3 * E ^ 3)) := by ring
      _ ≤ 6 * ((W.card : ℝ) ^ 3 *
          (s3PrefixErrorCoeff eta ^ 3 * Real.rpow T (-106 : ℝ))) :=
        mul_le_mul_of_nonneg_left hmid hconst
      _ ≤ 6 * (s3PrefixErrorCoeff eta ^ 3 * s3SourceFactor N W *
          Real.rpow T (-106 : ℝ)) :=
        mul_le_mul_of_nonneg_left hchain hconst
      _ = _ := by ring
  have hc1 : 0 ≤ 24 * lemma43DerivativeConstant 0 ^ 2 *
      s3PrefixErrorCoeff eta := by positivity
  have hc2 : 0 ≤ 6 * s3PrefixErrorCoeff eta ^ 3 := by positivity
  have hconv1 := GuthMaynardS3LiteralErrorContract.source_prefactor_time_neg106_le_eight_time_neg100
    hT hNle W hWle hc1
  have hconv2 := GuthMaynardS3LiteralErrorContract.source_prefactor_time_neg106_le_eight_time_neg100
    hT hNle W hWle hc2
  have hterm1' :
      24 * lemma43DerivativeConstant 0 ^ 2 * s3PrefixErrorCoeff eta *
          s3SourceFactor N W *
          Real.rpow T (-106 : ℝ) ≤
        24 * lemma43DerivativeConstant 0 ^ 2 * s3PrefixErrorCoeff eta *
          (8 * Real.rpow T (-100 : ℝ)) := by
    simpa [s3SourceFactor, mul_assoc, mul_comm, mul_left_comm] using hconv1
  have hterm2' :
      6 * s3PrefixErrorCoeff eta ^ 3 * s3SourceFactor N W *
          Real.rpow T (-106 : ℝ) ≤
        6 * s3PrefixErrorCoeff eta ^ 3 *
          (8 * Real.rpow T (-100 : ℝ)) := by
    simpa [s3SourceFactor, mul_assoc, mul_comm, mul_left_comm] using hconv2
  have hsum := add_le_add (hterm1.trans hterm1') (hterm2.trans hterm2')
  calc
    s3FourierError N W T eta ≤
        24 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 *
            lemma43DerivativeConstant 0 ^ 2 * ((M : ℝ) ^ 2 * E) +
          6 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 * E ^ 3 :=
      hrewF ▸ hmain
    _ ≤ 24 * lemma43DerivativeConstant 0 ^ 2 *
          s3PrefixErrorCoeff eta *
          (8 * Real.rpow T (-100 : ℝ)) +
        6 * s3PrefixErrorCoeff eta ^ 3 *
          (8 * Real.rpow T (-100 : ℝ)) := hsum
    _ = (24 * lemma43DerivativeConstant 0 ^ 2 * s3PrefixErrorCoeff eta +
          6 * s3PrefixErrorCoeff eta ^ 3) *
        (8 * Real.rpow T (-100 : ℝ)) := by ring

end
end GuthMaynardS3LiteralUniform106Fourier

#print axioms GuthMaynardS3LiteralUniform106Fourier.s3FourierError_le_uniform106
