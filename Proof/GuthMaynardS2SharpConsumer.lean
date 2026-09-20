import GuthMaynardS2SharpNormalization

/-! # Printed k=2 S2 consumer
The O(1) zero-frequency Schur factor, the scale-local remainder
`C_err(ell) 2^L / N`, the power ledger, and the short-gap mass are
combined into Guth--Maynard Proposition 6.1 at `k = 2`:
`‖S2‖ ≤ C T^η (N^2 |W|^2 + T N |W|^(3/2) + N^2 T^(1/4) |W|^(13/8))`.
-/

namespace GuthMaynardS2SharpConsumer

open scoped BigOperators
open CGLProofDAG
open GuthMaynardEquation55Infinite
open GuthMaynardS2LiteralReduction
open GuthMaynardS2DyadicReflection
open GuthMaynardS2DyadicAssembly
open GuthMaynardS2PowerLedger
open GuthMaynardS2ShortGapMass
open GuthMaynardS2ReflectionError
open GuthMaynardS2SharpNormalization
open GuthMaynardS2CutoffGeometry
open GuthMaynardS1PowerLedger
open GuthMaynardHeathBrownInterface

noncomputable section

/-- Subpower used to absorb dyadic logarithms into `T^η`. -/
def sourceS2Subpower (eta : ℝ) : ℝ := min (eta / 16) (1 / 12)

/-- Far-Fourier order making `T ≤ (2^L)^(ell-1)` once `2^L ≥ T^δ`. -/
def sourceS2FarOrder (eta : ℝ) : ℕ :=
  Nat.ceil (1 / sourceS2Subpower eta) + 1

def sourceS2IndexConstant (eta : ℝ) : ℝ :=
  1 + 1 / (sourceS2Subpower eta * Real.log 2)

theorem sourceS2Subpower_pos {eta : ℝ} (heta : 0 < eta) :
    0 < sourceS2Subpower eta :=
  lt_min (div_pos heta (by norm_num)) (by norm_num)

theorem sourceS2Subpower_nonneg {eta : ℝ} (heta : 0 < eta) :
    0 ≤ sourceS2Subpower eta :=
  (sourceS2Subpower_pos heta).le

theorem sourceS2Subpower_le_eta_div_sixteen (eta : ℝ) :
    sourceS2Subpower eta ≤ eta / 16 :=
  min_le_left _ _

theorem sourceS2Subpower_le_one_div_twelve (eta : ℝ) :
    sourceS2Subpower eta ≤ 1 / 12 :=
  min_le_right _ _

theorem sourceS2FarOrder_ge_two {eta : ℝ} (heta : 0 < eta) :
    2 ≤ sourceS2FarOrder eta := by
  have hδ := sourceS2Subpower_pos heta
  have h12 : sourceS2Subpower eta ≤ 1 / 12 :=
    sourceS2Subpower_le_one_div_twelve eta
  have hge : (12 : ℝ) ≤ 1 / sourceS2Subpower eta := by
    have h := one_div_le_one_div_of_le hδ h12
    have hrew : 1 / (1 / 12 : ℝ) = 12 := by norm_num
    rwa [hrew] at h
  have hceil : (12 : ℝ) ≤ Nat.ceil (1 / sourceS2Subpower eta) :=
    hge.trans (Nat.le_ceil _)
  have : 12 ≤ Nat.ceil (1 / sourceS2Subpower eta) := by exact_mod_cast hceil
  unfold sourceS2FarOrder
  omega

theorem sourceS2FarOrder_mul_subpower {eta : ℝ} (heta : 0 < eta) :
    (1 : ℝ) ≤ sourceS2Subpower eta * (sourceS2FarOrder eta - 1 : ℕ) := by
  have hδ := sourceS2Subpower_pos heta
  have hceil : (1 : ℝ) / sourceS2Subpower eta ≤
      (Nat.ceil (1 / sourceS2Subpower eta) : ℝ) := Nat.le_ceil _
  have hmul : (1 : ℝ) ≤ sourceS2Subpower eta *
      (Nat.ceil (1 / sourceS2Subpower eta) : ℝ) :=
    by
      simpa [mul_comm] using (div_le_iff₀ hδ).mp hceil
  have heq : sourceS2FarOrder eta - 1 =
      Nat.ceil (1 / sourceS2Subpower eta) := by
    unfold sourceS2FarOrder
    exact Nat.add_sub_cancel _ 1
  simpa [heq] using hmul

theorem sourceS2IndexConstant_pos {eta : ℝ} (heta : 0 < eta) :
    0 < sourceS2IndexConstant eta := by
  unfold sourceS2IndexConstant
  have hδ := sourceS2Subpower_pos heta
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  positivity

theorem sourceS2IndexConstant_nonneg {eta : ℝ} (heta : 0 < eta) :
    0 ≤ sourceS2IndexConstant eta :=
  (sourceS2IndexConstant_pos heta).le

theorem sourceS2IndexConstant_one_le {eta : ℝ} (heta : 0 < eta) :
    1 ≤ sourceS2IndexConstant eta := by
  unfold sourceS2IndexConstant
  have hδ := sourceS2Subpower_pos heta
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have : 0 ≤ 1 / (sourceS2Subpower eta * Real.log 2) := by positivity
  linarith

private theorem two_pow_natCast (n : ℕ) :
    ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by
  exact_mod_cast Nat.cast_pow (2 : ℕ) n

private theorem self_le_mul_of_one_le {a b : ℝ} (ha : 0 ≤ a)
    (hb : 1 ≤ b) : a ≤ a * b := by
  nlinarith

private theorem rpow_nat_mul {T delta : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    Real.rpow T delta ^ (n : ℕ) = Real.rpow T (delta * (n : ℝ)) := by
  exact (Real.rpow_mul_natCast hT delta n).symm

private theorem rpow_sq {T delta : ℝ} (hT : 0 ≤ T) :
    Real.rpow T delta ^ (2 : ℕ) = Real.rpow T (2 * delta) := by
  calc
    _ = Real.rpow T (delta * (2 : ℝ)) := rpow_nat_mul hT 2
    _ = _ := by ring

private theorem two_pow_L_sq_le {T delta : ℝ} {L : ℕ}
    (hT : 0 ≤ T) (hL : (2 : ℝ) ^ L ≤ 2 * Real.rpow T delta) :
    ((2 : ℝ) ^ L) ^ 2 ≤ 4 * Real.rpow T (2 * delta) := by
  have hsq := pow_le_pow_left₀ (by positivity) hL 2
  have hr : (2 * Real.rpow T delta) ^ 2 = 4 * Real.rpow T (2 * delta) := by
    rw [mul_pow, rpow_sq hT]
    ring
  exact hsq.trans_eq hr

private theorem rpow_two_delta_div_N_le {T N delta : ℝ}
    (hN : 0 < N) (hT : 0 ≤ T)
    (h2 : 2 * Real.rpow T delta ≤ N) :
    Real.rpow T (2 * delta) / N ≤ Real.rpow T delta / 2 := by
  have hδ : 0 ≤ Real.rpow T delta := Real.rpow_nonneg hT _
  have h2δ : Real.rpow T (2 * delta) =
      Real.rpow T delta * Real.rpow T delta := by
    rw [← rpow_sq hT, sq]
  have hfrac : Real.rpow T delta / N ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hN (by norm_num : (0 : ℝ) < 2)]
    linarith
  calc
    Real.rpow T (2 * delta) / N =
        (Real.rpow T delta * Real.rpow T delta) / N := by rw [h2δ]
    _ = Real.rpow T delta * (Real.rpow T delta / N) := by ring
    _ ≤ Real.rpow T delta * (1 / 2) :=
      mul_le_mul_of_nonneg_left hfrac hδ
    _ = Real.rpow T delta / 2 := by ring

private theorem half_N_le {N : ℝ} {i : ℕ} (hN : 0 ≤ N) :
    N / 2 ≤ (N * (2 : ℝ) ^ i) / 2 := by
  have : (1 : ℝ) ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
  have : N ≤ N * (2 : ℝ) ^ i := le_mul_of_one_le_right hN this
  linarith

private theorem two_pow_i_le_of_cover {N T : ℝ} {i K : ℕ}
    (hN : 0 ≤ N) (hKN : N * (2 : ℝ) ^ K ≤ T) (hi : i ≤ K) :
    N * (2 : ℝ) ^ i ≤ T := by
  have hpow : (2 : ℝ) ^ i ≤ (2 : ℝ) ^ K :=
    pow_le_pow_right₀ (by norm_num) hi
  exact (mul_le_mul_of_nonneg_left hpow hN).trans hKN

theorem sourceS2SharpShape_ge_first {T : ℝ} (hT : 0 ≤ T)
    (N : ℕ) (W : Finset ℝ) :
    (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 ≤ sourceS2SharpShape T N W := by
  unfold sourceS2SharpShape
  have h₂ : 0 ≤ T * (N : ℝ) * Real.rpow (W.card : ℝ) (3 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg hT (Nat.cast_nonneg _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have h₃ : 0 ≤ (N : ℝ) ^ 2 * Real.rpow T (1 / 4 : ℝ) *
      Real.rpow (W.card : ℝ) (13 / 8 : ℝ) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hT _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  linarith

theorem sourceS2SharpShape_ge_second {T : ℝ} (hT : 0 ≤ T)
    (N : ℕ) (W : Finset ℝ) :
    T * (N : ℝ) * Real.rpow (W.card : ℝ) (3 / 2 : ℝ) ≤
      sourceS2SharpShape T N W := by
  unfold sourceS2SharpShape
  have h₁ : 0 ≤ (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 := by positivity
  have h₃ : 0 ≤ (N : ℝ) ^ 2 * Real.rpow T (1 / 4 : ℝ) *
      Real.rpow (W.card : ℝ) (13 / 8 : ℝ) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hT _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  linarith

theorem sourceS2SharpShape_ge_third {T : ℝ} (hT : 0 ≤ T)
    (N : ℕ) (W : Finset ℝ) :
    (N : ℝ) ^ 2 * Real.rpow T (1 / 4 : ℝ) *
      Real.rpow (W.card : ℝ) (13 / 8 : ℝ) ≤
      sourceS2SharpShape T N W := by
  unfold sourceS2SharpShape
  have h₁ : 0 ≤ (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 := by positivity
  have h₂ : 0 ≤ T * (N : ℝ) * Real.rpow (W.card : ℝ) (3 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg hT (Nat.cast_nonneg _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  linarith

/-- `T ≤ (2^L)^(ell-1)` on the chosen far-Fourier order. -/
theorem sourceS2_far_geometry {eta T : ℝ} {L : ℕ}
    (heta : 0 < eta) (hT : 1 ≤ T)
    (hL : Real.rpow T (sourceS2Subpower eta) ≤ (2 : ℝ) ^ L) :
    T ≤ ((2 : ℝ) ^ L) ^ (sourceS2FarOrder eta - 1) := by
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hexp := sourceS2FarOrder_mul_subpower heta
  calc
    T = Real.rpow T 1 := (Real.rpow_one T).symm
    _ ≤ Real.rpow T
          (sourceS2Subpower eta * (sourceS2FarOrder eta - 1 : ℕ)) :=
      Real.rpow_le_rpow_of_exponent_le hT hexp
    _ = Real.rpow T (sourceS2Subpower eta) ^
          (sourceS2FarOrder eta - 1) :=
      (rpow_nat_mul hT0 (sourceS2FarOrder eta - 1)).symm
    _ ≤ ((2 : ℝ) ^ L) ^ (sourceS2FarOrder eta - 1) :=
      pow_le_pow_left₀ (Real.rpow_nonneg hT0 _) hL _

/-- Insert `C_err(ell) 2^L / N` into one dyadic gap budget. -/
theorem sourceGapPoweredBudget_error_inserted
    {N : ℕ} {T : ℝ} {i L ell : ℕ} {C eta : ℝ} (W : Finset ℝ)
    (hN : 1 ≤ N) (hT1 : 1 ≤ T) (hTN : T ≤ (N : ℝ) ^ 2)
    (hUi : (N : ℝ) * (2 : ℝ) ^ i ≤ T)
    (hJ : (2 : ℝ) ^ (i + L) ≤ T)
    (hBell : T ≤ ((2 : ℝ) ^ L) ^ (ell - 1))
    (hell : 2 ≤ ell) :
    sourceGapPoweredBudget C eta T N W
        ((N : ℝ) * (2 : ℝ) ^ i) (2 * (N : ℝ) * (2 : ℝ) ^ i)
        ((N : ℝ) / 2) (i + L) 6 ell ≤
      sourceCentralBudget C eta T W ((N : ℝ) * (2 : ℝ) ^ i)
        ((N : ℝ) / 2) (i + L) +
      2 * (W.card : ℝ) ^ 2 *
        (sourceReflectionErrorConstant ell * (2 : ℝ) ^ L / (N : ℝ)) ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN)
  have hU : 0 < (N : ℝ) * (2 : ℝ) ^ i :=
    mul_pos hNpos (pow_pos (by norm_num) _)
  have hV : 0 ≤ 2 * (N : ℝ) * (2 : ℝ) ^ i := by positivity
  have hR : 0 < (N : ℝ) / 2 := by positivity
  have hE := sourceReflectionError_le hN hT1 hTN hUi hJ hBell hell
  have hEnonneg :=
    sourceReflectionError_nonneg N hU hV hR (i + L) 6 ell (by norm_num) hell
  rw [sourceGapPoweredBudget_eq]
  apply add_le_add (le_refl _)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hEnonneg hE 2)
    (by positivity)

private theorem two_pow_add_sq (i L : ℕ) :
    ((2 : ℝ) ^ (i + L)) ^ 2 = (2 : ℝ) ^ i * (2 : ℝ) ^ (i + 2 * L) := by
  have hmul : ((2 : ℝ) ^ (i + L)) ^ 2 = (2 : ℝ) ^ ((i + L) * 2) :=
    (pow_mul _ _ _).symm
  have hexp : (i + L) * 2 = i + (i + 2 * L) := by ring
  rw [hmul, hexp, pow_add]

private theorem scale_div_U (N : ℝ) (i L : ℕ) (hN : N ≠ 0) :
    (2 : ℝ) ^ (i + L) / (N * (2 : ℝ) ^ i) = (2 : ℝ) ^ L / N := by
  have hi : (2 : ℝ) ^ i ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [pow_add, mul_comm N]
  exact mul_div_mul_left _ _ hi

private theorem scale_sq_div_U (N : ℝ) (i L : ℕ) (hN : N ≠ 0) :
    ((2 : ℝ) ^ (i + L)) ^ 2 / (N * (2 : ℝ) ^ i) =
      (2 : ℝ) ^ (i + 2 * L) / N := by
  have hi : (2 : ℝ) ^ i ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [two_pow_add_sq, mul_comm N]
  exact mul_div_mul_left _ _ hi

/-- Scale-local pair shape after dividing by the gap `U = N 2^i`. -/
theorem n_pow_three_pairShape_div_le {T : ℝ} {N : ℕ} {i L : ℕ}
    (W : Finset ℝ) (hN : 1 ≤ N) (hT : 0 ≤ T) :
    (N : ℝ) ^ 3 *
      (pairShape T ((2 : ℝ) ^ (i + L)) (W.card : ℝ) /
        ((N : ℝ) * (2 : ℝ) ^ i)) ≤
      (2 : ℝ) ^ L * ((N : ℝ) ^ 2 * (W.card : ℝ) ^ 2) +
        (N : ℝ) ^ 2 * (2 : ℝ) ^ (i + 2 * L) *
          Real.rpow (W.card : ℝ) (3 / 2 : ℝ) +
        (2 : ℝ) ^ L * ((N : ℝ) ^ 2 * Real.rpow T (1 / 4 : ℝ) *
          Real.rpow (W.card : ℝ) (13 / 8 : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN)
  have hU : 0 < (N : ℝ) * (2 : ℝ) ^ i :=
    mul_pos hNpos (pow_pos (by norm_num) _)
  have hw : 0 ≤ (W.card : ℝ) := Nat.cast_nonneg _
  have hM : 0 ≤ (2 : ℝ) ^ (i + L) := by positivity
  have hthree := pairShape_le_three hT hM hw
  have hdiv := div_le_div_of_nonneg_right hthree hU.le
  have hMU := scale_div_U (N : ℝ) i L hNpos.ne'
  have hM2U := scale_sq_div_U (N : ℝ) i L hNpos.ne'
  have hsum :
      ( (W.card : ℝ) ^ 2 * (2 : ℝ) ^ (i + L) +
          Real.rpow (W.card : ℝ) (3 / 2 : ℝ) * ((2 : ℝ) ^ (i + L)) ^ 2 +
          Real.rpow (W.card : ℝ) (13 / 8 : ℝ) * Real.rpow T (1 / 4 : ℝ) *
            (2 : ℝ) ^ (i + L) ) /
        ((N : ℝ) * (2 : ℝ) ^ i) =
        (W.card : ℝ) ^ 2 * ((2 : ℝ) ^ L / (N : ℝ)) +
          Real.rpow (W.card : ℝ) (3 / 2 : ℝ) *
            ((2 : ℝ) ^ (i + 2 * L) / (N : ℝ)) +
          Real.rpow (W.card : ℝ) (13 / 8 : ℝ) * Real.rpow T (1 / 4 : ℝ) *
            ((2 : ℝ) ^ L / (N : ℝ)) := by
    have hi0 : (2 : ℝ) ^ i ≠ 0 := by positivity
    have hden : (N : ℝ) * (2 : ℝ) ^ i ≠ 0 :=
      mul_ne_zero hNpos.ne' hi0
    field_simp [hden, hNpos.ne', hi0]
    ring
  have hbound :
      pairShape T ((2 : ℝ) ^ (i + L)) (W.card : ℝ) /
          ((N : ℝ) * (2 : ℝ) ^ i) ≤
        (W.card : ℝ) ^ 2 * ((2 : ℝ) ^ L / (N : ℝ)) +
          Real.rpow (W.card : ℝ) (3 / 2 : ℝ) *
            ((2 : ℝ) ^ (i + 2 * L) / (N : ℝ)) +
          Real.rpow (W.card : ℝ) (13 / 8 : ℝ) * Real.rpow T (1 / 4 : ℝ) *
            ((2 : ℝ) ^ L / (N : ℝ)) :=
    hdiv.trans_eq hsum
  have hmul' :
      (N : ℝ) ^ 3 * (pairShape T ((2 : ℝ) ^ (i + L)) (W.card : ℝ) /
          ((N : ℝ) * (2 : ℝ) ^ i)) ≤
        (N : ℝ) ^ 3 * ((W.card : ℝ) ^ 2 * ((2 : ℝ) ^ L / (N : ℝ)) +
          Real.rpow (W.card : ℝ) (3 / 2 : ℝ) *
            ((2 : ℝ) ^ (i + 2 * L) / (N : ℝ)) +
          Real.rpow (W.card : ℝ) (13 / 8 : ℝ) * Real.rpow T (1 / 4 : ℝ) *
            ((2 : ℝ) ^ L / (N : ℝ))) :=
    mul_le_mul_of_nonneg_left hbound (by positivity)
  have hrewrite :
      (N : ℝ) ^ 3 * ((W.card : ℝ) ^ 2 * ((2 : ℝ) ^ L / (N : ℝ)) +
          Real.rpow (W.card : ℝ) (3 / 2 : ℝ) *
            ((2 : ℝ) ^ (i + 2 * L) / (N : ℝ)) +
          Real.rpow (W.card : ℝ) (13 / 8 : ℝ) * Real.rpow T (1 / 4 : ℝ) *
            ((2 : ℝ) ^ L / (N : ℝ))) =
        (2 : ℝ) ^ L * ((N : ℝ) ^ 2 * (W.card : ℝ) ^ 2) +
          (N : ℝ) ^ 2 * (2 : ℝ) ^ (i + 2 * L) *
            Real.rpow (W.card : ℝ) (3 / 2 : ℝ) +
          (2 : ℝ) ^ L * ((N : ℝ) ^ 2 * Real.rpow T (1 / 4 : ℝ) *
            Real.rpow (W.card : ℝ) (13 / 8 : ℝ)) := by
    field_simp [hNpos.ne']
  exact hmul'.trans_eq hrewrite

/-- Short-gap contribution is absorbed by the first printed term. -/
theorem sourceS2_short_contrib_le {N : ℕ} {T : ℝ} (W : Finset ℝ)
    (hN : 1 ≤ N) (hT : 0 ≤ T) :
    3 * (N : ℝ) ^ 3 * sourceZeroLegConstant *
      sourceShortGapPairMoment N W (N : ℝ) ≤
      3 * sourceZeroLegConstant * shortGapMassConstant ^ 2 *
        sourceS2SharpShape T N W := by
  have hNposN : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hNposN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hshort := sourceShortGapPairMoment_le hNposN W
  have hC0 := sourceZeroLegConstant_nonneg
  have hCs := shortGapMassConstant_nonneg
  have hleft := mul_le_mul_of_nonneg_left hshort (by positivity :
    0 ≤ 3 * (N : ℝ) ^ 3 * sourceZeroLegConstant)
  have hsimp : 3 * (N : ℝ) ^ 3 * sourceZeroLegConstant *
      ((W.card : ℝ) ^ 2 * (shortGapMassConstant / (N : ℝ) ^ 2) ^ 2) =
      3 * sourceZeroLegConstant * shortGapMassConstant ^ 2 *
        ((W.card : ℝ) ^ 2 / (N : ℝ)) := by
    field_simp [hNpos.ne']
  have hinv : (W.card : ℝ) ^ 2 / (N : ℝ) ≤
      (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 := by
    have h1N : (1 : ℝ) / N ≤ 1 := (div_le_one hNpos).2 hN1
    have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := one_le_pow₀ hN1
    calc
      (W.card : ℝ) ^ 2 / N = (1 / N) * (W.card : ℝ) ^ 2 := by ring
      _ ≤ 1 * (W.card : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right h1N (sq_nonneg _)
      _ ≤ (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hN2 (sq_nonneg _)
  have hshape := sourceS2SharpShape_ge_first hT N W
  have hmid : 3 * sourceZeroLegConstant * shortGapMassConstant ^ 2 *
      ((W.card : ℝ) ^ 2 / (N : ℝ)) ≤
      3 * sourceZeroLegConstant * shortGapMassConstant ^ 2 *
        ((N : ℝ) ^ 2 * (W.card : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hinv (by positivity)
  have hfin : 3 * sourceZeroLegConstant * shortGapMassConstant ^ 2 *
      ((N : ℝ) ^ 2 * (W.card : ℝ) ^ 2) ≤
      3 * sourceZeroLegConstant * shortGapMassConstant ^ 2 *
        sourceS2SharpShape T N W :=
    mul_le_mul_of_nonneg_left hshape (by positivity)
  exact hleft.trans_eq hsimp |>.trans hmid |>.trans hfin

/-- One-scale reflection-error contribution after the Schur factor. -/
theorem sourceS2_error_contrib_le {N : ℕ} {T eta : ℝ} {L ell : ℕ}
    (W : Finset ℝ) (hN : 1 ≤ N) (hT : 1 ≤ T) (heta : 0 < eta)
    (hell : 2 ≤ ell)
    (h2 : 2 * Real.rpow T (sourceS2Subpower eta) ≤ (N : ℝ))
    (hL : (2 : ℝ) ^ L ≤ 2 * Real.rpow T (sourceS2Subpower eta)) :
    3 * (N : ℝ) ^ 3 * sourceZeroLegConstant *
      (2 * (W.card : ℝ) ^ 2 *
        (sourceReflectionErrorConstant ell * (2 : ℝ) ^ L / (N : ℝ)) ^ 2) ≤
      12 * sourceZeroLegConstant *
        sourceReflectionErrorConstant ell ^ 2 *
        Real.rpow T (sourceS2Subpower eta) * sourceS2SharpShape T N W := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN)
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hC0 := sourceZeroLegConstant_nonneg
  have hE := sourceReflectionErrorConstant_nonneg hell
  have hδ := sourceS2Subpower_nonneg heta
  have hw2 : 0 ≤ (W.card : ℝ) ^ 2 := sq_nonneg _
  have hexpand :
      3 * (N : ℝ) ^ 3 * sourceZeroLegConstant *
          (2 * (W.card : ℝ) ^ 2 *
            (sourceReflectionErrorConstant ell * (2 : ℝ) ^ L / (N : ℝ)) ^ 2) =
        6 * sourceZeroLegConstant * sourceReflectionErrorConstant ell ^ 2 *
          (W.card : ℝ) ^ 2 * (N : ℝ) * ((2 : ℝ) ^ L) ^ 2 := by
    field_simp [hNpos.ne']
    ring
  have hL2 := two_pow_L_sq_le hT0 hL
  have hstep :
      6 * sourceZeroLegConstant * sourceReflectionErrorConstant ell ^ 2 *
          (W.card : ℝ) ^ 2 * (N : ℝ) * ((2 : ℝ) ^ L) ^ 2 ≤
        6 * sourceZeroLegConstant * sourceReflectionErrorConstant ell ^ 2 *
          (W.card : ℝ) ^ 2 * (N : ℝ) * (4 * Real.rpow T (2 * sourceS2Subpower eta)) :=
    mul_le_mul_of_nonneg_left hL2 (by positivity)
  have hnum :
      6 * sourceZeroLegConstant * sourceReflectionErrorConstant ell ^ 2 *
          (W.card : ℝ) ^ 2 * (N : ℝ) * (4 * Real.rpow T (2 * sourceS2Subpower eta)) =
        24 * sourceZeroLegConstant * sourceReflectionErrorConstant ell ^ 2 *
          (Real.rpow T (2 * sourceS2Subpower eta) / (N : ℝ)) *
          ((N : ℝ) ^ 2 * (W.card : ℝ) ^ 2) := by
    field_simp [hNpos.ne']
    ring
  have hfrac := rpow_two_delta_div_N_le hNpos hT0 h2
  have hfrac' :
      24 * sourceZeroLegConstant * sourceReflectionErrorConstant ell ^ 2 *
          (Real.rpow T (2 * sourceS2Subpower eta) / (N : ℝ)) *
          ((N : ℝ) ^ 2 * (W.card : ℝ) ^ 2) ≤
        24 * sourceZeroLegConstant * sourceReflectionErrorConstant ell ^ 2 *
          (Real.rpow T (sourceS2Subpower eta) / 2) *
          ((N : ℝ) ^ 2 * (W.card : ℝ) ^ 2) :=
    by
      have hcoef : 0 ≤ 24 * sourceZeroLegConstant *
          sourceReflectionErrorConstant ell ^ 2 := by
        exact mul_nonneg (mul_nonneg (by norm_num) hC0) (sq_nonneg _)
      have hq : 0 ≤ (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 := by positivity
      simpa [mul_assoc] using
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfrac hcoef) hq)
  have hhalf :
      24 * sourceZeroLegConstant * sourceReflectionErrorConstant ell ^ 2 *
          (Real.rpow T (sourceS2Subpower eta) / 2) *
          ((N : ℝ) ^ 2 * (W.card : ℝ) ^ 2) =
        12 * sourceZeroLegConstant * sourceReflectionErrorConstant ell ^ 2 *
          Real.rpow T (sourceS2Subpower eta) *
          ((N : ℝ) ^ 2 * (W.card : ℝ) ^ 2) := by ring
  have hshape := sourceS2SharpShape_ge_first hT0 N W
  have hfin :
      12 * sourceZeroLegConstant * sourceReflectionErrorConstant ell ^ 2 *
          Real.rpow T (sourceS2Subpower eta) *
          ((N : ℝ) ^ 2 * (W.card : ℝ) ^ 2) ≤
        12 * sourceZeroLegConstant * sourceReflectionErrorConstant ell ^ 2 *
          Real.rpow T (sourceS2Subpower eta) * sourceS2SharpShape T N W := by
    have hcoef : 0 ≤ 12 * sourceZeroLegConstant *
        sourceReflectionErrorConstant ell ^ 2 *
        Real.rpow T (sourceS2Subpower eta) := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hC0) (sq_nonneg _))
        (Real.rpow_nonneg hT0 _)
    exact mul_le_mul_of_nonneg_left hshape hcoef
  exact hexpand ▸
    (hstep.trans_eq hnum |>.trans hfrac' |>.trans_eq hhalf |>.trans hfin)

private theorem three_term_scale_le_shape {T : ℝ} {N i L : ℕ}
    {eta : ℝ} (W : Finset ℝ) (hN : 1 ≤ N) (hT : 1 ≤ T) (heta : 0 < eta)
    (hUi : (N : ℝ) * (2 : ℝ) ^ i ≤ T)
    (hL : (2 : ℝ) ^ L ≤ 2 * Real.rpow T (sourceS2Subpower eta)) :
    (2 : ℝ) ^ L * ((N : ℝ) ^ 2 * (W.card : ℝ) ^ 2) +
      (N : ℝ) ^ 2 * (2 : ℝ) ^ (i + 2 * L) *
        Real.rpow (W.card : ℝ) (3 / 2 : ℝ) +
      (2 : ℝ) ^ L * ((N : ℝ) ^ 2 * Real.rpow T (1 / 4 : ℝ) *
        Real.rpow (W.card : ℝ) (13 / 8 : ℝ)) ≤
      8 * Real.rpow T (2 * sourceS2Subpower eta) *
        sourceS2SharpShape T N W := by
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN)
  have hδpos := sourceS2Subpower_pos heta
  have hδ0 := hδpos.le
  have hone : 1 ≤ Real.rpow T (sourceS2Subpower eta) :=
    Real.one_le_rpow hT hδ0
  have hδmono : Real.rpow T (sourceS2Subpower eta) ≤
      Real.rpow T (2 * sourceS2Subpower eta) :=
    Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have hL2 := two_pow_L_sq_le hT0 hL
  have hfirst := sourceS2SharpShape_ge_first hT0 N W
  have hsecond := sourceS2SharpShape_ge_second hT0 N W
  have hthird := sourceS2SharpShape_ge_third hT0 N W
  have hw32 : 0 ≤ Real.rpow (W.card : ℝ) (3 / 2 : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hterm1 :
      (2 : ℝ) ^ L * ((N : ℝ) ^ 2 * (W.card : ℝ) ^ 2) ≤
        2 * Real.rpow T (sourceS2Subpower eta) * sourceS2SharpShape T N W :=
    mul_le_mul hL hfirst (by positivity) (by positivity)
  have hterm1' :
      2 * Real.rpow T (sourceS2Subpower eta) * sourceS2SharpShape T N W ≤
        2 * Real.rpow T (2 * sourceS2Subpower eta) * sourceS2SharpShape T N W :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hδmono (by norm_num))
      (sourceS2SharpShape_nonneg hT0 N W)
  have hi2L : (2 : ℝ) ^ (i + 2 * L) = (2 : ℝ) ^ i * ((2 : ℝ) ^ L) ^ 2 := by
    have : i + 2 * L = i + L * 2 := by ring
    rw [this, pow_add, pow_mul]
  have hterm2core :
      (N : ℝ) ^ 2 * (2 : ℝ) ^ (i + 2 * L) *
          Real.rpow (W.card : ℝ) (3 / 2 : ℝ) =
        ((N : ℝ) * (2 : ℝ) ^ i) * ((2 : ℝ) ^ L) ^ 2 *
          ((N : ℝ) * Real.rpow (W.card : ℝ) (3 / 2 : ℝ)) := by
    rw [hi2L]
    ring
  have hterm2 :
      (N : ℝ) ^ 2 * (2 : ℝ) ^ (i + 2 * L) *
          Real.rpow (W.card : ℝ) (3 / 2 : ℝ) ≤
        T * (4 * Real.rpow T (2 * sourceS2Subpower eta)) *
          ((N : ℝ) * Real.rpow (W.card : ℝ) (3 / 2 : ℝ)) := by
    rw [hterm2core]
    apply mul_le_mul
    · exact mul_le_mul hUi hL2 (by positivity)
        (le_trans zero_le_one hT)
    · exact le_rfl
    · exact mul_nonneg (Nat.cast_nonneg _) hw32
    · exact mul_nonneg (le_trans zero_le_one hT)
        (mul_nonneg (by norm_num) (Real.rpow_nonneg (le_trans zero_le_one hT) _))
  have hterm2' :
      T * (4 * Real.rpow T (2 * sourceS2Subpower eta)) *
          ((N : ℝ) * Real.rpow (W.card : ℝ) (3 / 2 : ℝ)) =
        4 * Real.rpow T (2 * sourceS2Subpower eta) *
          (T * (N : ℝ) * Real.rpow (W.card : ℝ) (3 / 2 : ℝ)) := by ring
  have hterm2'' :
      4 * Real.rpow T (2 * sourceS2Subpower eta) *
          (T * (N : ℝ) * Real.rpow (W.card : ℝ) (3 / 2 : ℝ)) ≤
        4 * Real.rpow T (2 * sourceS2Subpower eta) *
          sourceS2SharpShape T N W :=
    mul_le_mul_of_nonneg_left hsecond
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hT0 _))
  have hterm3 :
      (2 : ℝ) ^ L * ((N : ℝ) ^ 2 * Real.rpow T (1 / 4 : ℝ) *
          Real.rpow (W.card : ℝ) (13 / 8 : ℝ)) ≤
        2 * Real.rpow T (sourceS2Subpower eta) * sourceS2SharpShape T N W :=
    mul_le_mul hL hthird
      (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hT0 _))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (by positivity)
  have hterm3' :
      2 * Real.rpow T (sourceS2Subpower eta) * sourceS2SharpShape T N W ≤
        2 * Real.rpow T (2 * sourceS2Subpower eta) * sourceS2SharpShape T N W :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hδmono (by norm_num))
      (sourceS2SharpShape_nonneg hT0 N W)
  have hsum :
      (2 : ℝ) ^ L * ((N : ℝ) ^ 2 * (W.card : ℝ) ^ 2) +
          (N : ℝ) ^ 2 * (2 : ℝ) ^ (i + 2 * L) *
            Real.rpow (W.card : ℝ) (3 / 2 : ℝ) +
          (2 : ℝ) ^ L * ((N : ℝ) ^ 2 * Real.rpow T (1 / 4 : ℝ) *
            Real.rpow (W.card : ℝ) (13 / 8 : ℝ)) ≤
        (2 + 4 + 2) * Real.rpow T (2 * sourceS2Subpower eta) *
          sourceS2SharpShape T N W := by
    have a1 := hterm1.trans hterm1'
    have a2 := hterm2.trans_eq hterm2' |>.trans hterm2''
    have a3 := hterm3.trans hterm3'
    nlinarith [Real.rpow_nonneg hT0 (2 * sourceS2Subpower eta),
      sourceS2SharpShape_nonneg hT0 N W]
  have : (2 + 4 + 2 : ℝ) = 8 := by norm_num
  simpa [this] using hsum

/-- One-scale central contribution after the Schur factor and power ledger. -/
theorem sourceS2_central_contrib_le {C eta T : ℝ} {N i L : ℕ}
    (W : Finset ℝ) (hC : 0 ≤ C) (heta : 0 < eta) (hT : 1 ≤ T) (hN : 1 ≤ N)
    (hJ : (2 : ℝ) ^ (i + L) ≤ T)
    (hUi : (N : ℝ) * (2 : ℝ) ^ i ≤ T)
    (hL : (2 : ℝ) ^ L ≤ 2 * Real.rpow T (sourceS2Subpower eta)) :
    3 * (N : ℝ) ^ 3 * sourceZeroLegConstant *
      sourceCentralBudget C (eta / 2) T W
        ((N : ℝ) * (2 : ℝ) ^ i) ((N : ℝ) / 2) (i + L) ≤
      153600 * sourceZeroLegConstant * sourceMellinMass ^ 2 * (1 + C) *
        sourceS2IndexConstant eta ^ 4 *
        Real.rpow T (eta / 2 + 6 * sourceS2Subpower eta) *
        sourceS2SharpShape T N W := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN)
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hU : 0 < (N : ℝ) * (2 : ℝ) ^ i :=
    mul_pos hNpos (pow_pos (by norm_num) _)
  have hRhalf := half_N_le (i := i) hNpos.le
  have heta0 : 0 ≤ eta / 2 := by linarith
  have hδ := sourceS2Subpower_pos heta
  have hcent := sourceCentralBudget_le hC heta0 hT hU hRhalf W (i + L)
  have hPcast :
      pairShape T ((2 ^ (i + L) : ℕ) : ℝ) (W.card : ℝ) =
        pairShape T ((2 : ℝ) ^ (i + L)) (W.card : ℝ) := by
    rw [two_pow_natCast]
  have hC0 := sourceZeroLegConstant_nonneg
  have hMel := sourceMellinMass_nonneg
  have hidx := sourceS2IndexConstant_nonneg heta
  have hidx1 := sourceS2IndexConstant_one_le heta
  have hJ1 : (i + L + 1 : ℝ) ≤
      sourceS2IndexConstant eta * Real.rpow T (sourceS2Subpower eta) := by
    simpa [sourceS2IndexConstant] using
      dyadic_index_le_subpower hT hδ (i + L) hJ
  have hJ4 : (i + L + 1 : ℝ) ^ 4 ≤
      (sourceS2IndexConstant eta * Real.rpow T (sourceS2Subpower eta)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hJ1 4
  have hJ4' :
      (sourceS2IndexConstant eta * Real.rpow T (sourceS2Subpower eta)) ^ 4 =
        sourceS2IndexConstant eta ^ 4 *
          Real.rpow T (4 * sourceS2Subpower eta) := by
    calc
      _ = sourceS2IndexConstant eta ^ 4 *
          Real.rpow T (sourceS2Subpower eta * ((4 : ℕ) : ℝ)) := by
            rw [mul_pow, rpow_nat_mul hT0 4]
      _ = _ := by
        congr 2
        norm_num
        ring
  have hleft := mul_le_mul_of_nonneg_left hcent
    (by positivity : 0 ≤ 3 * (N : ℝ) ^ 3 * sourceZeroLegConstant)
  have hrewrite :
      3 * (N : ℝ) ^ 3 * sourceZeroLegConstant *
          (6400 * sourceMellinMass ^ 2 * (1 + C) * (i + L + 1 : ℝ) ^ 4 *
            Real.rpow T (eta / 2) / ((N : ℝ) * (2 : ℝ) ^ i) *
            pairShape T ((2 ^ (i + L) : ℕ) : ℝ) (W.card : ℝ)) =
        19200 * sourceZeroLegConstant * sourceMellinMass ^ 2 * (1 + C) *
          (i + L + 1 : ℝ) ^ 4 * Real.rpow T (eta / 2) *
          ((N : ℝ) ^ 3 * (pairShape T ((2 : ℝ) ^ (i + L)) (W.card : ℝ) /
            ((N : ℝ) * (2 : ℝ) ^ i))) := by
    rw [hPcast]
    field_simp [hU.ne']
    ring
  have hshape := n_pow_three_pairShape_div_le (T := T) (N := N) (i := i)
    (L := L) W hN hT0
  have hgeom := three_term_scale_le_shape (T := T) (N := N) (i := i) (L := L)
    (eta := eta) W hN hT heta hUi hL
  have hcore :
      (N : ℝ) ^ 3 * (pairShape T ((2 : ℝ) ^ (i + L)) (W.card : ℝ) /
          ((N : ℝ) * (2 : ℝ) ^ i)) ≤
        8 * Real.rpow T (2 * sourceS2Subpower eta) *
          sourceS2SharpShape T N W :=
    hshape.trans hgeom
  -- Collapse the remaining T-powers: T^{η/2} T^{4δ} T^{2δ} = T^{η/2+6δ}.
  have hpow :
      Real.rpow T (eta / 2) * Real.rpow T (4 * sourceS2Subpower eta) *
          Real.rpow T (2 * sourceS2Subpower eta) =
        Real.rpow T (eta / 2 + 6 * sourceS2Subpower eta) := by
    have h1 := Real.rpow_add (lt_of_lt_of_le zero_lt_one hT)
      (eta / 2) (4 * sourceS2Subpower eta)
    have h2 := Real.rpow_add (lt_of_lt_of_le zero_lt_one hT)
      (eta / 2 + 4 * sourceS2Subpower eta) (2 * sourceS2Subpower eta)
    have hp1 : Real.rpow T (eta / 2) *
        Real.rpow T (4 * sourceS2Subpower eta) =
        Real.rpow T (eta / 2 + 4 * sourceS2Subpower eta) :=
      (Real.rpow_add (lt_of_lt_of_le zero_lt_one hT)
        (eta / 2) (4 * sourceS2Subpower eta)).symm
    have hp2 : Real.rpow T (eta / 2 + 4 * sourceS2Subpower eta) *
        Real.rpow T (2 * sourceS2Subpower eta) =
        Real.rpow T (eta / 2 + 4 * sourceS2Subpower eta +
          2 * sourceS2Subpower eta) :=
      (Real.rpow_add (lt_of_lt_of_le zero_lt_one hT)
        (eta / 2 + 4 * sourceS2Subpower eta)
        (2 * sourceS2Subpower eta)).symm
    calc
      _ = Real.rpow T (eta / 2 + 4 * sourceS2Subpower eta) *
          Real.rpow T (2 * sourceS2Subpower eta) :=
        congrArg (fun z => z * Real.rpow T (2 * sourceS2Subpower eta)) hp1
      _ = Real.rpow T (eta / 2 + 4 * sourceS2Subpower eta +
          2 * sourceS2Subpower eta) := hp2
      _ = _ := by congr 1 <;> ring
  have hconst :
      19200 * 8 = (153600 : ℝ) := by norm_num
  -- Finish by rewriting the explicit constant and the T-power product.
  have hfin :
      19200 * sourceZeroLegConstant * sourceMellinMass ^ 2 * (1 + C) *
          (sourceS2IndexConstant eta * Real.rpow T (sourceS2Subpower eta)) ^ 4 *
          Real.rpow T (eta / 2) *
          (8 * Real.rpow T (2 * sourceS2Subpower eta) *
            sourceS2SharpShape T N W) =
        153600 * sourceZeroLegConstant * sourceMellinMass ^ 2 * (1 + C) *
          sourceS2IndexConstant eta ^ 4 *
          Real.rpow T (eta / 2 + 6 * sourceS2Subpower eta) *
          sourceS2SharpShape T N W := by
    rw [hJ4', hconst.symm]
    calc
      _ = 19200 * 8 * sourceZeroLegConstant * sourceMellinMass ^ 2 * (1 + C) *
            sourceS2IndexConstant eta ^ 4 *
            (Real.rpow T (eta / 2) * Real.rpow T (4 * sourceS2Subpower eta) *
              Real.rpow T (2 * sourceS2Subpower eta)) *
            sourceS2SharpShape T N W := by ring
      _ = _ := by
        rw [hpow]
  -- Assemble the chain through the index fourth power.
  have hchain :
      3 * (N : ℝ) ^ 3 * sourceZeroLegConstant *
          sourceCentralBudget C (eta / 2) T W
            ((N : ℝ) * (2 : ℝ) ^ i) ((N : ℝ) / 2) (i + L) ≤
        19200 * sourceZeroLegConstant * sourceMellinMass ^ 2 * (1 + C) *
          (sourceS2IndexConstant eta * Real.rpow T (sourceS2Subpower eta)) ^ 4 *
          Real.rpow T (eta / 2) *
          (8 * Real.rpow T (2 * sourceS2Subpower eta) *
            sourceS2SharpShape T N W) := by
    have hcast : ((i + L : ℕ) : ℝ) + 1 =
        (i : ℝ) + (L : ℝ) + 1 := by
      norm_num [Nat.cast_add]
    rw [← hcast] at hrewrite
    apply (hleft.trans_eq hrewrite).trans
    have hpre : 0 ≤ 19200 * sourceZeroLegConstant * sourceMellinMass ^ 2 *
        (1 + C) * Real.rpow T (eta / 2) := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) hC0) (sq_nonneg _))
          (by linarith))
        (Real.rpow_nonneg hT0 _)
    have hpair0 : 0 ≤ pairShape T ((2 : ℝ) ^ (i + L)) (W.card : ℝ) :=
      pairShape_nonneg (by positivity) (by positivity)
    have hcore0 : 0 ≤ (N : ℝ) ^ 3 *
        (pairShape T ((2 : ℝ) ^ (i + L)) (W.card : ℝ) /
          ((N : ℝ) * (2 : ℝ) ^ i)) := by
      exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) 3)
        (div_nonneg hpair0 (le_of_lt hU))
    have hJ40 : 0 ≤
        (sourceS2IndexConstant eta * Real.rpow T (sourceS2Subpower eta)) ^ 4 :=
      pow_nonneg
        (mul_nonneg hidx (Real.rpow_nonneg hT0 _)) _
    have hmul := mul_le_mul hJ4 hcore hcore0 hJ40
    have hh := mul_le_mul_of_nonneg_left hmul hpre
    simpa [mul_assoc, mul_comm, mul_left_comm] using hh
  exact hchain.trans_eq hfin

private theorem eta_half_add_seven_subpower_le {eta : ℝ} (heta : 0 < eta) :
    eta / 2 + 7 * sourceS2Subpower eta ≤ eta := by
  have hδ := sourceS2Subpower_le_eta_div_sixteen eta
  have : 7 * sourceS2Subpower eta ≤ 7 * (eta / 16) :=
    mul_le_mul_of_nonneg_left hδ (by norm_num)
  have : 7 * (eta / 16) = 7 * eta / 16 := by ring
  have : eta / 2 + 7 * eta / 16 = 15 * eta / 16 := by ring
  linarith

private theorem two_subpower_le_eta {eta : ℝ} (heta : 0 < eta) :
    2 * sourceS2Subpower eta ≤ eta := by
  have hδ := sourceS2Subpower_le_eta_div_sixteen eta
  have : 2 * sourceS2Subpower eta ≤ 2 * (eta / 16) :=
    mul_le_mul_of_nonneg_left hδ (by norm_num)
  linarith

set_option maxHeartbeats 2000000
/-‒ Explicit-cutoff form of the printed k=2 bound. Logarithmic dyadic
counts and the scale-local remainder are already absorbed into `T^η`. -/
theorem norm_sourceS2_le_sharp_cutoffs {eta : ℝ} (heta : 0 < eta) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (N : ℕ) (W : Finset ℝ) (K L : ℕ),
        T₀ ≤ T → 1 ≤ N → T ≤ (N : ℝ) ^ 2 →
        (N : ℝ) * (2 : ℝ) ^ K ≤ T →
        T < (N : ℝ) * (2 : ℝ) ^ (K + 1) →
        Real.rpow T (sourceS2Subpower eta) ≤ (2 : ℝ) ^ L →
        (2 : ℝ) ^ L ≤ 2 * Real.rpow T (sourceS2Subpower eta) →
        2 * Real.rpow T (sourceS2Subpower eta) ≤ (N : ℝ) →
        (∀ i : ℕ, i ≤ K → (2 : ℝ) ^ (i + L) ≤ T) →
        OneSeparated W → ContainedInIntervalOfLength W T →
        ‖sourceS2 N W‖ ≤
          C * Real.rpow T eta * sourceS2SharpShape T N W := by
  obtain ⟨C_hb, T₀hb, hChb, hT₀hb, hgap⟩ :=
    sourceFourierGapPairMoment_powered_bound
      (by positivity : 0 < eta / 2)
  let ell := sourceS2FarOrder eta
  let idx := sourceS2IndexConstant eta
  let Cbase : ℝ :=
    1 + 200000 * sourceZeroLegConstant *
      (1 + shortGapMassConstant ^ 2) *
      (1 + sourceReflectionErrorConstant ell ^ 2) *
      (1 + sourceMellinMass ^ 2) * (1 + C_hb) * (1 + idx) ^ 5
  let Cfin : ℝ := 3 * Cbase
  let T₀ : ℝ := max T₀hb 16
  refine ⟨Cfin, T₀, ?pos, ?T0, ?_⟩
  · have hC0 := sourceZeroLegConstant_nonneg
    have hCs := shortGapMassConstant_nonneg
    have hell := sourceS2FarOrder_ge_two heta
    have hE := sourceReflectionErrorConstant_nonneg hell
    have hMel := sourceMellinMass_nonneg
    have hidx := sourceS2IndexConstant_nonneg heta
    have hbase : 0 < Cbase := by
      unfold Cbase
      positivity
    exact mul_pos (by norm_num) hbase
  · exact le_trans (by norm_num : (2 : ℝ) ≤ 16) (le_max_right _ _)
  intro T N W K L hT0le hN hTN hKN hKcover hLlo hLhi h2N hJall hsep hinterval
  have hT : 16 ≤ T := (le_max_right T₀hb 16).trans hT0le
  have hT1 : 1 ≤ T := le_trans (by norm_num) hT
  have hT0 : 0 ≤ T := le_trans zero_le_one hT1
  have hThb : T₀hb ≤ T := (le_max_left T₀hb 16).trans hT0le
  have hNposN : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hNposN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hell := sourceS2FarOrder_ge_two heta
  have hBell := sourceS2_far_geometry heta hT1 hLlo
  have hδ := sourceS2Subpower_pos heta
  have hδ0 := hδ.le
  have hC0 := sourceZeroLegConstant_nonneg
  have hCs := shortGapMassConstant_nonneg
  have hE := sourceReflectionErrorConstant_nonneg hell
  have hMel := sourceMellinMass_nonneg
  have hidx0 := sourceS2IndexConstant_nonneg heta
  have hidx1 := sourceS2IndexConstant_one_le heta
  have hpoweta : 1 ≤ Real.rpow T eta := Real.one_le_rpow hT1 heta.le
  have hshape0 := sourceS2SharpShape_nonneg hT0 N W
  have hSchur := norm_sourceS2_le_oneSeparated_pairMoment hNposN W hsep
  have hdiam : ∀ t ∈ W, ∀ u ∈ W, |t - u| ≤ T :=
    fun t ht u hu => contained_abs_le hinterval ht hu
  have hcover : ∀ t ∈ W, ∀ u ∈ W,
      |t - u| ≤ (N : ℝ) * (2 : ℝ) ^ (K + 1) :=
    fun t ht u hu => (hdiam t ht u hu).trans hKcover.le
  have hsplit := sourceNonzeroFourierPairMoment_le_dyadic N W (N : ℝ) K hcover
  have hshort := sourceShortGapPairMoment_le hNposN W
  have hRpos : 0 < (N : ℝ) / 2 := by positivity
  have hgap_i : ∀ i ∈ Finset.range (K + 1),
      sourceFourierGapPairMoment N W ((N : ℝ) * (2 : ℝ) ^ i)
          ((N : ℝ) * (2 : ℝ) ^ (i + 1)) ≤
        sourceGapPoweredBudget C_hb (eta / 2) T N W
          ((N : ℝ) * (2 : ℝ) ^ i) (2 * (N : ℝ) * (2 : ℝ) ^ i)
          ((N : ℝ) / 2) (i + L) 6 ell := by
    intro i hi
    have hiK : i ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hU : (N : ℝ) * (2 : ℝ) ^ i ≤
        (N : ℝ) * (2 : ℝ) ^ (i + 1) := by
      have : (2 : ℝ) ^ i ≤ (2 : ℝ) ^ (i + 1) :=
        pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)
      exact mul_le_mul_of_nonneg_left this hNpos.le
    have hRU : (N : ℝ) / 2 < (N : ℝ) * (2 : ℝ) ^ i := by
      have hone : (1 : ℝ) ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
      have hhalf : (N : ℝ) / 2 < N := by nlinarith
      have hmul : (N : ℝ) ≤ N * (2 : ℝ) ^ i :=
        le_mul_of_one_le_right hNpos.le hone
      exact hhalf.trans_le hmul
    have hJT : ((2 ^ (i + L) : ℕ) : ℝ) ≤ T := by
      rw [two_pow_natCast]
      exact hJall i hiK
    have hV : (N : ℝ) * (2 : ℝ) ^ (i + 1) = 2 * (N : ℝ) * (2 : ℝ) ^ i := by
      rw [pow_succ]
      ring
    simpa [hV] using
      hgap T N W ((N : ℝ) * (2 : ℝ) ^ i) ((N : ℝ) * (2 : ℝ) ^ (i + 1))
        ((N : ℝ) / 2) (i + L) 6 ell hThb hNposN hRpos hRU hU hJT
        (by norm_num) hell hsep hinterval
  have hinserted : ∀ i ∈ Finset.range (K + 1),
      sourceGapPoweredBudget C_hb (eta / 2) T N W
          ((N : ℝ) * (2 : ℝ) ^ i) (2 * (N : ℝ) * (2 : ℝ) ^ i)
          ((N : ℝ) / 2) (i + L) 6 ell ≤
        sourceCentralBudget C_hb (eta / 2) T W
          ((N : ℝ) * (2 : ℝ) ^ i) ((N : ℝ) / 2) (i + L) +
        2 * (W.card : ℝ) ^ 2 *
          (sourceReflectionErrorConstant ell * (2 : ℝ) ^ L / (N : ℝ)) ^ 2 := by
    intro i hi
    have hiK : i ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    exact sourceGapPoweredBudget_error_inserted W hN hT1 hTN
      (two_pow_i_le_of_cover (le_trans zero_le_one hN1) hKN hiK)
        (hJall i hiK) hBell hell
  -- Pair moment through the dyadic ledger.
  have hpair :
      sourceNonzeroFourierPairMoment N W ≤
        sourceShortGapPairMoment N W (N : ℝ) +
          ∑ i ∈ Finset.range (K + 1),
            (sourceCentralBudget C_hb (eta / 2) T W
                ((N : ℝ) * (2 : ℝ) ^ i) ((N : ℝ) / 2) (i + L) +
              2 * (W.card : ℝ) ^ 2 *
                (sourceReflectionErrorConstant ell * (2 : ℝ) ^ L /
                  (N : ℝ)) ^ 2) := by
    apply hsplit.trans
    exact add_le_add_right (Finset.sum_le_sum fun i hi =>
      (hgap_i i hi).trans (hinserted i hi))
      (sourceShortGapPairMoment N W (N : ℝ))
  have hS2 := hSchur.trans (mul_le_mul_of_nonneg_left hpair (by positivity))
  -- Short contribution.
  have hshortC := sourceS2_short_contrib_le (T := T) W hN hT0
  -- Error contribution, uniform in the scale.
  have herrC := sourceS2_error_contrib_le (T := T) (eta := eta) (L := L)
    (ell := ell) W hN hT1 heta hell h2N hLhi
  have hK1 : (K + 1 : ℝ) ≤ idx * Real.rpow T (sourceS2Subpower eta) := by
    have h2K : (2 : ℝ) ^ K ≤ T := by
      have : (2 : ℝ) ^ K ≤ (N : ℝ) * (2 : ℝ) ^ K :=
        le_mul_of_one_le_left (by positivity) hN1
      exact this.trans hKN
    simpa [idx, sourceS2IndexConstant] using
      dyadic_index_le_subpower hT1 hδ K h2K
  have herrSum :
      3 * (N : ℝ) ^ 3 * sourceZeroLegConstant *
          ∑ i ∈ Finset.range (K + 1),
            (2 * (W.card : ℝ) ^ 2 *
              (sourceReflectionErrorConstant ell * (2 : ℝ) ^ L /
                (N : ℝ)) ^ 2) ≤
        12 * sourceZeroLegConstant *
          sourceReflectionErrorConstant ell ^ 2 * idx *
          Real.rpow T (2 * sourceS2Subpower eta) *
          sourceS2SharpShape T N W := by
    have hterm : ∀ i ∈ Finset.range (K + 1),
        3 * (N : ℝ) ^ 3 * sourceZeroLegConstant *
            (2 * (W.card : ℝ) ^ 2 *
              (sourceReflectionErrorConstant ell * (2 : ℝ) ^ L /
                (N : ℝ)) ^ 2) ≤
          12 * sourceZeroLegConstant *
            sourceReflectionErrorConstant ell ^ 2 *
            Real.rpow T (sourceS2Subpower eta) *
            sourceS2SharpShape T N W :=
      fun _ _ => herrC
    have hsum := Finset.sum_le_sum hterm
    have hcard : (∑ _i ∈ Finset.range (K + 1),
        12 * sourceZeroLegConstant *
          sourceReflectionErrorConstant ell ^ 2 *
          Real.rpow T (sourceS2Subpower eta) *
          sourceS2SharpShape T N W) =
        (K + 1 : ℝ) * (12 * sourceZeroLegConstant *
          sourceReflectionErrorConstant ell ^ 2 *
          Real.rpow T (sourceS2Subpower eta) *
          sourceS2SharpShape T N W) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    have hrew : 3 * (N : ℝ) ^ 3 * sourceZeroLegConstant *
        ∑ i ∈ Finset.range (K + 1),
          (2 * (W.card : ℝ) ^ 2 *
            (sourceReflectionErrorConstant ell * (2 : ℝ) ^ L /
              (N : ℝ)) ^ 2) =
        ∑ i ∈ Finset.range (K + 1),
          3 * (N : ℝ) ^ 3 * sourceZeroLegConstant *
            (2 * (W.card : ℝ) ^ 2 *
              (sourceReflectionErrorConstant ell * (2 : ℝ) ^ L /
                (N : ℝ)) ^ 2) := by
      simp only [Finset.mul_sum]
    have hpow :
        (K + 1 : ℝ) * Real.rpow T (sourceS2Subpower eta) ≤
          idx * Real.rpow T (2 * sourceS2Subpower eta) := by
      have hmul :
          (K + 1 : ℝ) * Real.rpow T (sourceS2Subpower eta) ≤
            (idx * Real.rpow T (sourceS2Subpower eta)) *
              Real.rpow T (sourceS2Subpower eta) :=
        mul_le_mul_of_nonneg_right hK1
          (Real.rpow_nonneg hT0 (sourceS2Subpower eta))
      have hr : idx * Real.rpow T (sourceS2Subpower eta) *
          Real.rpow T (sourceS2Subpower eta) =
          idx * Real.rpow T (2 * sourceS2Subpower eta) := by
        have hp := (Real.rpow_add (lt_of_lt_of_le zero_lt_one hT1)
          (sourceS2Subpower eta) (sourceS2Subpower eta)).symm
        calc
          _ = idx * (Real.rpow T (sourceS2Subpower eta) *
              Real.rpow T (sourceS2Subpower eta)) := by ring
          _ = idx * Real.rpow T
              (sourceS2Subpower eta + sourceS2Subpower eta) :=
            congrArg (fun z => idx * z) hp
          _ = _ := by congr 1 <;> ring
      exact hmul.trans_eq hr
    calc
      _ = _ := hrew
      _ ≤ _ := hsum
      _ = (K + 1 : ℝ) * (12 * sourceZeroLegConstant *
            sourceReflectionErrorConstant ell ^ 2 *
            Real.rpow T (sourceS2Subpower eta) *
            sourceS2SharpShape T N W) := hcard
      _ = 12 * sourceZeroLegConstant *
            sourceReflectionErrorConstant ell ^ 2 *
            ((K + 1 : ℝ) * Real.rpow T (sourceS2Subpower eta)) *
            sourceS2SharpShape T N W := by ring
      _ ≤ 12 * sourceZeroLegConstant *
            sourceReflectionErrorConstant ell ^ 2 *
            (idx * Real.rpow T (2 * sourceS2Subpower eta)) *
            sourceS2SharpShape T N W :=
        by
          have hcoef : 0 ≤ 12 * sourceZeroLegConstant *
              sourceReflectionErrorConstant ell ^ 2 := by
            exact mul_nonneg (mul_nonneg (by norm_num) hC0) (sq_nonneg _)
          have hshape0 : 0 ≤ sourceS2SharpShape T N W :=
            sourceS2SharpShape_nonneg hT0 N W
          have hh := mul_le_mul_of_nonneg_left hpow hcoef
          have hh' := mul_le_mul_of_nonneg_right hh hshape0
          simpa [mul_assoc] using hh'
      _ = _ := by ring
  -- Central contribution.
  have hcentC : ∀ i ∈ Finset.range (K + 1),
      3 * (N : ℝ) ^ 3 * sourceZeroLegConstant *
        sourceCentralBudget C_hb (eta / 2) T W
          ((N : ℝ) * (2 : ℝ) ^ i) ((N : ℝ) / 2) (i + L) ≤
        153600 * sourceZeroLegConstant * sourceMellinMass ^ 2 * (1 + C_hb) *
          idx ^ 4 * Real.rpow T (eta / 2 + 6 * sourceS2Subpower eta) *
          sourceS2SharpShape T N W := by
    intro i hi
    have hiK : i ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    simpa [idx] using
      sourceS2_central_contrib_le (C := C_hb) (eta := eta) (T := T)
        (N := N) (i := i) (L := L) W hChb.le heta hT1 hN (hJall i hiK)
        (two_pow_i_le_of_cover (le_trans zero_le_one hN1) hKN hiK) hLhi
  have hcentSum :
      3 * (N : ℝ) ^ 3 * sourceZeroLegConstant *
          ∑ i ∈ Finset.range (K + 1),
            sourceCentralBudget C_hb (eta / 2) T W
              ((N : ℝ) * (2 : ℝ) ^ i) ((N : ℝ) / 2) (i + L) ≤
        153600 * sourceZeroLegConstant * sourceMellinMass ^ 2 * (1 + C_hb) *
          idx ^ 5 * Real.rpow T (eta / 2 + 7 * sourceS2Subpower eta) *
          sourceS2SharpShape T N W := by
    have hrew : 3 * (N : ℝ) ^ 3 * sourceZeroLegConstant *
        ∑ i ∈ Finset.range (K + 1),
          sourceCentralBudget C_hb (eta / 2) T W
            ((N : ℝ) * (2 : ℝ) ^ i) ((N : ℝ) / 2) (i + L) =
        ∑ i ∈ Finset.range (K + 1),
          3 * (N : ℝ) ^ 3 * sourceZeroLegConstant *
            sourceCentralBudget C_hb (eta / 2) T W
              ((N : ℝ) * (2 : ℝ) ^ i) ((N : ℝ) / 2) (i + L) := by
      simp [Finset.mul_sum]
    have hsum := Finset.sum_le_sum hcentC
    have hcard : (∑ _i ∈ Finset.range (K + 1),
        153600 * sourceZeroLegConstant * sourceMellinMass ^ 2 * (1 + C_hb) *
          idx ^ 4 * Real.rpow T (eta / 2 + 6 * sourceS2Subpower eta) *
          sourceS2SharpShape T N W) =
        (K + 1 : ℝ) * (153600 * sourceZeroLegConstant *
          sourceMellinMass ^ 2 * (1 + C_hb) * idx ^ 4 *
          Real.rpow T (eta / 2 + 6 * sourceS2Subpower eta) *
          sourceS2SharpShape T N W) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    have hpow :
        (K + 1 : ℝ) * Real.rpow T (eta / 2 + 6 * sourceS2Subpower eta) ≤
          idx * Real.rpow T (eta / 2 + 7 * sourceS2Subpower eta) := by
      have hmul := mul_le_mul_of_nonneg_right hK1
        (Real.rpow_nonneg hT0 (eta / 2 + 6 * sourceS2Subpower eta))
      have hadd := Real.rpow_add (lt_of_lt_of_le zero_lt_one hT1)
        (sourceS2Subpower eta) (eta / 2 + 6 * sourceS2Subpower eta)
      have hexp : sourceS2Subpower eta + (eta / 2 + 6 * sourceS2Subpower eta) =
          eta / 2 + 7 * sourceS2Subpower eta := by ring
      have hprod : Real.rpow T (sourceS2Subpower eta) *
          Real.rpow T (eta / 2 + 6 * sourceS2Subpower eta) =
          Real.rpow T (eta / 2 + 7 * sourceS2Subpower eta) := by
        have hp := (Real.rpow_add (lt_of_lt_of_le zero_lt_one hT1)
          (sourceS2Subpower eta)
          (eta / 2 + 6 * sourceS2Subpower eta)).symm
        calc
          _ = Real.rpow T (sourceS2Subpower eta +
              (eta / 2 + 6 * sourceS2Subpower eta)) := hp
          _ = _ := by congr 1 <;> ring
      calc
        _ ≤ idx * Real.rpow T (sourceS2Subpower eta) *
            Real.rpow T (eta / 2 + 6 * sourceS2Subpower eta) := hmul
        _ = _ := by
          calc
            idx * Real.rpow T (sourceS2Subpower eta) *
                Real.rpow T (eta / 2 + 6 * sourceS2Subpower eta) =
              idx * (Real.rpow T (sourceS2Subpower eta) *
                Real.rpow T (eta / 2 + 6 * sourceS2Subpower eta)) := by ring
            _ = _ := by rw [hprod]
    calc
      _ = _ := hrew
      _ ≤ _ := hsum
      _ = _ := hcard
      _ = 153600 * sourceZeroLegConstant * sourceMellinMass ^ 2 * (1 + C_hb) *
            idx ^ 4 * ((K + 1 : ℝ) *
              Real.rpow T (eta / 2 + 6 * sourceS2Subpower eta)) *
            sourceS2SharpShape T N W := by ring
      _ ≤ 153600 * sourceZeroLegConstant * sourceMellinMass ^ 2 * (1 + C_hb) *
            idx ^ 4 * (idx * Real.rpow T (eta / 2 + 7 * sourceS2Subpower eta)) *
            sourceS2SharpShape T N W :=
        by
          have hcoef : 0 ≤ 153600 * sourceZeroLegConstant *
              sourceMellinMass ^ 2 * (1 + C_hb) * idx ^ 4 := by
            exact mul_nonneg
              (mul_nonneg
                (mul_nonneg
                  (mul_nonneg (by norm_num) hC0) (sq_nonneg _))
                (by linarith))
              (pow_nonneg hidx0 4)
          have hshape0 : 0 ≤ sourceS2SharpShape T N W :=
            sourceS2SharpShape_nonneg hT0 N W
          have hh := mul_le_mul_of_nonneg_left hpow hcoef
          have hh' := mul_le_mul_of_nonneg_right hh hshape0
          simpa [mul_assoc] using hh'
      _ = _ := by ring
  -- Absorb leftover subpowers into `T^η`.
  have hpow7 :
      Real.rpow T (eta / 2 + 7 * sourceS2Subpower eta) ≤ Real.rpow T eta :=
    Real.rpow_le_rpow_of_exponent_le hT1 (eta_half_add_seven_subpower_le heta)
  have hpow2 :
      Real.rpow T (2 * sourceS2Subpower eta) ≤ Real.rpow T eta :=
    Real.rpow_le_rpow_of_exponent_le hT1 (two_subpower_le_eta heta)
  have hshortAbs :
      3 * sourceZeroLegConstant * shortGapMassConstant ^ 2 *
          sourceS2SharpShape T N W ≤
        Cbase * Real.rpow T eta * sourceS2SharpShape T N W := by
    have hcoef : 3 * sourceZeroLegConstant * shortGapMassConstant ^ 2 ≤
        Cbase * Real.rpow T eta := by
      have h1 : 3 * sourceZeroLegConstant * shortGapMassConstant ^ 2 ≤
          200000 * sourceZeroLegConstant * (1 + shortGapMassConstant ^ 2) *
            (1 + sourceReflectionErrorConstant ell ^ 2) *
            (1 + sourceMellinMass ^ 2) * (1 + C_hb) * (1 + idx) ^ 5 := by
        have hS0 : 0 ≤ shortGapMassConstant ^ 2 := sq_nonneg _
        have hS1 : 1 ≤ 1 + shortGapMassConstant ^ 2 := by linarith
        have hE1 : 1 ≤ 1 + sourceReflectionErrorConstant ell ^ 2 := by
          linarith [sq_nonneg (sourceReflectionErrorConstant ell)]
        have hM1 : 1 ≤ 1 + sourceMellinMass ^ 2 := by
          linarith [sq_nonneg sourceMellinMass]
        have hC1 : 1 ≤ 1 + C_hb := by linarith only [hChb.le]
        have hidxBase : 0 ≤ 1 + idx := by linarith
        have hidx1 : 1 ≤ (1 + idx) ^ 5 := one_le_pow₀ (by linarith)
        have hprod : shortGapMassConstant ^ 2 ≤
            (1 + shortGapMassConstant ^ 2) *
              (1 + sourceReflectionErrorConstant ell ^ 2) *
              (1 + sourceMellinMass ^ 2) * (1 + C_hb) * (1 + idx) ^ 5 := by
          calc
            shortGapMassConstant ^ 2 ≤
            1 + shortGapMassConstant ^ 2 := by linarith
            _ ≤ (1 + shortGapMassConstant ^ 2) *
                (1 + sourceReflectionErrorConstant ell ^ 2) :=
              self_le_mul_of_one_le (by positivity) hE1
            _ ≤ ((1 + shortGapMassConstant ^ 2) *
                (1 + sourceReflectionErrorConstant ell ^ 2)) *
                (1 + sourceMellinMass ^ 2) :=
              self_le_mul_of_one_le (by positivity) hM1
            _ ≤ (((1 + shortGapMassConstant ^ 2) *
                (1 + sourceReflectionErrorConstant ell ^ 2)) *
                (1 + sourceMellinMass ^ 2)) * (1 + C_hb) := by
              exact self_le_mul_of_one_le (by positivity) hC1
            _ ≤ (((1 + shortGapMassConstant ^ 2) *
                (1 + sourceReflectionErrorConstant ell ^ 2)) *
                (1 + sourceMellinMass ^ 2)) * (1 + C_hb) *
                (1 + idx) ^ 5 :=
              self_le_mul_of_one_le (by positivity) hidx1
        have hcoef : 0 ≤ 200000 * sourceZeroLegConstant :=
          mul_nonneg (by norm_num) hC0
        have hmul := mul_le_mul_of_nonneg_left hprod hcoef
        have hnum : 3 * sourceZeroLegConstant * shortGapMassConstant ^ 2 ≤
            200000 * sourceZeroLegConstant * shortGapMassConstant ^ 2 := by
          have := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by norm_num : (3 : ℝ) ≤ 200000) hC0)
            hS0
          simpa [mul_assoc, mul_left_comm, mul_comm] using this
        exact hnum.trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using hmul)
      have : 200000 * sourceZeroLegConstant *
          (1 + shortGapMassConstant ^ 2) *
          (1 + sourceReflectionErrorConstant ell ^ 2) *
          (1 + sourceMellinMass ^ 2) * (1 + C_hb) * (1 + idx) ^ 5 ≤
          Cbase := by
        unfold Cbase
        linarith
      have := h1.trans this
      exact this.trans (le_mul_of_one_le_right (by
        unfold Cbase
        positivity) hpoweta)
    exact mul_le_mul_of_nonneg_right hcoef hshape0
  have herrAbs :
      12 * sourceZeroLegConstant * sourceReflectionErrorConstant ell ^ 2 *
          idx * Real.rpow T (2 * sourceS2Subpower eta) *
          sourceS2SharpShape T N W ≤
        Cbase * Real.rpow T eta * sourceS2SharpShape T N W := by
    have hcoef : 12 * sourceZeroLegConstant *
        sourceReflectionErrorConstant ell ^ 2 * idx *
          Real.rpow T (2 * sourceS2Subpower eta) ≤
        Cbase * Real.rpow T eta := by
      have h1 : 12 * sourceZeroLegConstant *
          sourceReflectionErrorConstant ell ^ 2 * idx ≤
          200000 * sourceZeroLegConstant * (1 + shortGapMassConstant ^ 2) *
            (1 + sourceReflectionErrorConstant ell ^ 2) *
            (1 + sourceMellinMass ^ 2) * (1 + C_hb) * (1 + idx) ^ 5 := by
        have hE0 : 0 ≤ sourceReflectionErrorConstant ell ^ 2 := sq_nonneg _
        have hE1 : sourceReflectionErrorConstant ell ^ 2 ≤
            1 + sourceReflectionErrorConstant ell ^ 2 := by linarith
        have hS1 : 1 ≤ 1 + shortGapMassConstant ^ 2 := by
          linarith [sq_nonneg shortGapMassConstant]
        have hM1 : 1 ≤ 1 + sourceMellinMass ^ 2 := by
          linarith [sq_nonneg sourceMellinMass]
        have hC1 : 1 ≤ 1 + C_hb := by linarith only [hChb.le]
        have hidxBase : 0 ≤ 1 + idx := by linarith
        have hidx1' : idx ≤ 1 + idx := by linarith only [hidx0]
        have hidx4 : idx ≤ (1 + idx) ^ 5 := by
          have hidx0' : 0 ≤ idx := by exact hidx0
          have hidxPow : idx ≤ idx ^ 5 := by
            have hidxOne : 1 ≤ idx := by exact hidx1
            simpa using (pow_le_pow_right₀ hidxOne
              (by norm_num : 1 ≤ 5))
          exact hidxPow.trans (pow_le_pow_left₀ hidx0' hidx1' 5)
        have hprod : sourceReflectionErrorConstant ell ^ 2 * idx ≤
            (1 + shortGapMassConstant ^ 2) *
              (1 + sourceReflectionErrorConstant ell ^ 2) *
              (1 + sourceMellinMass ^ 2) * (1 + C_hb) * (1 + idx) ^ 5 := by
          have hEP : sourceReflectionErrorConstant ell ^ 2 * idx ≤
              (1 + sourceReflectionErrorConstant ell ^ 2) * (1 + idx) ^ 5 := by
            exact mul_le_mul hE1 hidx4 hidx0 (by linarith)
          calc
            _ ≤ (1 + sourceReflectionErrorConstant ell ^ 2) * (1 + idx) ^ 5 := hEP
            _ ≤ ((1 + sourceReflectionErrorConstant ell ^ 2) * (1 + idx) ^ 5) *
                (1 + shortGapMassConstant ^ 2) :=
              self_le_mul_of_one_le (by positivity) hS1
            _ ≤ (((1 + sourceReflectionErrorConstant ell ^ 2) * (1 + idx) ^ 5) *
                (1 + shortGapMassConstant ^ 2)) *
                (1 + sourceMellinMass ^ 2) :=
              self_le_mul_of_one_le (by positivity) hM1
            _ ≤ ((((1 + sourceReflectionErrorConstant ell ^ 2) * (1 + idx) ^ 5) *
                (1 + shortGapMassConstant ^ 2)) *
                (1 + sourceMellinMass ^ 2)) * (1 + C_hb) :=
              self_le_mul_of_one_le (by positivity) hC1
            _ ≤ (1 + shortGapMassConstant ^ 2) *
                (1 + sourceReflectionErrorConstant ell ^ 2) *
                (1 + sourceMellinMass ^ 2) * (1 + C_hb) * (1 + idx) ^ 5 := by
              have hlast :
                  ((((1 + sourceReflectionErrorConstant ell ^ 2) *
                    (1 + idx) ^ 5) * (1 + shortGapMassConstant ^ 2)) *
                    (1 + sourceMellinMass ^ 2)) * (1 + C_hb) ≤
                  (((((1 + sourceReflectionErrorConstant ell ^ 2) *
                    (1 + idx) ^ 5) * (1 + shortGapMassConstant ^ 2)) *
                    (1 + sourceMellinMass ^ 2)) * (1 + C_hb)) *
                    (1 + idx) ^ 5 :=
                self_le_mul_of_one_le (by positivity)
                  (show 1 ≤ (1 + idx) ^ 5 from one_le_pow₀ (by linarith))
              -- The preceding insertion leaves the positive factors in a
              -- different commutative order; normalize only that identity.
              simpa [mul_assoc, mul_comm, mul_left_comm] using hlast
        have hcoef : 0 ≤ 200000 * sourceZeroLegConstant :=
          mul_nonneg (by norm_num) hC0
        have hmul := mul_le_mul_of_nonneg_left hprod hcoef
        have hnum : 12 * sourceZeroLegConstant *
            sourceReflectionErrorConstant ell ^ 2 * idx ≤
            200000 * sourceZeroLegConstant *
              sourceReflectionErrorConstant ell ^ 2 * idx := by
          have := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by norm_num : (12 : ℝ) ≤ 200000) hC0)
            (mul_nonneg hE0 hidx0)
          simpa [mul_assoc, mul_left_comm, mul_comm] using this
        exact hnum.trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using hmul)
      have hC : 200000 * sourceZeroLegConstant *
          (1 + shortGapMassConstant ^ 2) *
          (1 + sourceReflectionErrorConstant ell ^ 2) *
          (1 + sourceMellinMass ^ 2) * (1 + C_hb) * (1 + idx) ^ 5 ≤ Cbase := by
        unfold Cbase
        linarith only [show (0 : ℝ) ≤ 1 by norm_num]
      have hleft := (h1.trans hC)
      have hCbase : 0 ≤ Cbase := by
        unfold Cbase
        exact add_nonneg (by norm_num) (by positivity)
      have hh := mul_le_mul hleft hpow2 (Real.rpow_nonneg hT0 _) hCbase
      simpa [mul_assoc] using hh
    exact mul_le_mul_of_nonneg_right hcoef hshape0
  have hcentAbs :
      153600 * sourceZeroLegConstant * sourceMellinMass ^ 2 * (1 + C_hb) *
          idx ^ 5 * Real.rpow T (eta / 2 + 7 * sourceS2Subpower eta) *
          sourceS2SharpShape T N W ≤
        Cbase * Real.rpow T eta * sourceS2SharpShape T N W := by
    have hcoef : 153600 * sourceZeroLegConstant * sourceMellinMass ^ 2 *
        (1 + C_hb) * idx ^ 5 *
          Real.rpow T (eta / 2 + 7 * sourceS2Subpower eta) ≤
        Cbase * Real.rpow T eta := by
      have h1 : 153600 * sourceZeroLegConstant * sourceMellinMass ^ 2 *
          (1 + C_hb) * idx ^ 5 ≤
          200000 * sourceZeroLegConstant * (1 + shortGapMassConstant ^ 2) *
            (1 + sourceReflectionErrorConstant ell ^ 2) *
            (1 + sourceMellinMass ^ 2) * (1 + C_hb) * (1 + idx) ^ 5 := by
        have hidx1' : idx ≤ 1 + idx := by linarith only [hidx0]
        have hid : idx ^ 5 ≤ (1 + idx) ^ 5 := by
          have hidx0' : 0 ≤ idx := by exact hidx0
          exact pow_le_pow_left₀ hidx0' hidx1' 5
        have hm : sourceMellinMass ^ 2 ≤ 1 + sourceMellinMass ^ 2 := by
          linarith [sq_nonneg sourceMellinMass]
        have hS1 : 1 ≤ 1 + shortGapMassConstant ^ 2 := by
          linarith [sq_nonneg shortGapMassConstant]
        have hE1 : 1 ≤ 1 + sourceReflectionErrorConstant ell ^ 2 := by
          linarith [sq_nonneg (sourceReflectionErrorConstant ell)]
        have hC1 : 1 ≤ 1 + C_hb := by linarith only [hChb.le]
        have hCnon : 0 ≤ 1 + C_hb := by
          linarith only [hChb.le]
        have hprod : sourceMellinMass ^ 2 * ((1 + C_hb) * idx ^ 5) ≤
            (1 + shortGapMassConstant ^ 2) *
              (1 + sourceReflectionErrorConstant ell ^ 2) *
              (1 + sourceMellinMass ^ 2) * (1 + C_hb) * (1 + idx) ^ 5 := by
          have hMP0 : sourceMellinMass ^ 2 * ((1 + C_hb) * idx ^ 5) ≤
              (1 + sourceMellinMass ^ 2) * ((1 + C_hb) * idx ^ 5) :=
            mul_le_mul_of_nonneg_right hm
              (mul_nonneg hCnon (pow_nonneg hidx0 5))
          have hMP : sourceMellinMass ^ 2 * ((1 + C_hb) * idx ^ 5) ≤
              (1 + sourceMellinMass ^ 2) * (1 + C_hb) * (1 + idx) ^ 5 := by
            calc
              _ ≤ (1 + sourceMellinMass ^ 2) * ((1 + C_hb) * idx ^ 5) := hMP0
              _ = ((1 + sourceMellinMass ^ 2) * (1 + C_hb)) * idx ^ 5 := by ring
              _ ≤ ((1 + sourceMellinMass ^ 2) * (1 + C_hb)) * (1 + idx) ^ 5 :=
                mul_le_mul_of_nonneg_left hid
                  (mul_nonneg (by positivity) hCnon)
          calc
            _ ≤ (1 + sourceMellinMass ^ 2) * (1 + C_hb) * (1 + idx) ^ 5 := hMP
            _ ≤ ((1 + sourceMellinMass ^ 2) * (1 + C_hb) * (1 + idx) ^ 5) *
                (1 + shortGapMassConstant ^ 2) :=
              self_le_mul_of_one_le (by positivity) hS1
            _ ≤ (((1 + sourceMellinMass ^ 2) * (1 + C_hb) * (1 + idx) ^ 5) *
                (1 + shortGapMassConstant ^ 2)) *
                (1 + sourceReflectionErrorConstant ell ^ 2) :=
              self_le_mul_of_one_le (by positivity) hE1
            _ = (1 + shortGapMassConstant ^ 2) *
                (1 + sourceReflectionErrorConstant ell ^ 2) *
                (1 + sourceMellinMass ^ 2) * (1 + C_hb) * (1 + idx) ^ 5 := by
              ring
        have hnum : 153600 * sourceZeroLegConstant * sourceMellinMass ^ 2 *
            (1 + C_hb) * idx ^ 5 ≤
            200000 * sourceZeroLegConstant *
              (sourceMellinMass ^ 2 * ((1 + C_hb) * idx ^ 5)) := by
          have hcoef : (0 : ℝ) ≤ sourceZeroLegConstant := hC0
          have hmid : 153600 * sourceZeroLegConstant ≤
              200000 * sourceZeroLegConstant :=
            mul_le_mul_of_nonneg_right (by norm_num) hcoef
          have hrest : 0 ≤ sourceMellinMass ^ 2 *
              ((1 + C_hb) * idx ^ 5) := by
            exact mul_nonneg (sq_nonneg _) (mul_nonneg
              (by linarith only [hChb.le]) (pow_nonneg hidx0 5))
          have hh := mul_le_mul_of_nonneg_right hmid hrest
          calc
            153600 * sourceZeroLegConstant * sourceMellinMass ^ 2 *
                (1 + C_hb) * idx ^ 5 =
                (153600 * sourceZeroLegConstant) *
                  (sourceMellinMass ^ 2 * ((1 + C_hb) * idx ^ 5)) := by ring
            _ ≤ (200000 * sourceZeroLegConstant) *
                  (sourceMellinMass ^ 2 * ((1 + C_hb) * idx ^ 5)) := hh
            _ = 200000 * sourceZeroLegConstant *
                  (sourceMellinMass ^ 2 * ((1 + C_hb) * idx ^ 5)) := by ring
        have hcoef0 : 0 ≤ 200000 * sourceZeroLegConstant :=
          mul_nonneg (by norm_num) hC0
        calc
          153600 * sourceZeroLegConstant * sourceMellinMass ^ 2 *
              (1 + C_hb) * idx ^ 5 ≤
            200000 * sourceZeroLegConstant *
              (sourceMellinMass ^ 2 * ((1 + C_hb) * idx ^ 5)) := hnum
          _ ≤ (200000 * sourceZeroLegConstant) *
              ((1 + shortGapMassConstant ^ 2) *
                (1 + sourceReflectionErrorConstant ell ^ 2) *
                (1 + sourceMellinMass ^ 2) * (1 + C_hb) *
                (1 + idx) ^ 5) :=
            mul_le_mul_of_nonneg_left hprod hcoef0
          _ = 200000 * sourceZeroLegConstant *
              (1 + shortGapMassConstant ^ 2) *
              (1 + sourceReflectionErrorConstant ell ^ 2) *
              (1 + sourceMellinMass ^ 2) * (1 + C_hb) *
              (1 + idx) ^ 5 := by ac_rfl
      have hC : 200000 * sourceZeroLegConstant *
          (1 + shortGapMassConstant ^ 2) *
          (1 + sourceReflectionErrorConstant ell ^ 2) *
          (1 + sourceMellinMass ^ 2) * (1 + C_hb) * (1 + idx) ^ 5 ≤ Cbase := by
        unfold Cbase
        linarith only [show (0 : ℝ) ≤ 1 by norm_num]
      have hCbase : 0 ≤ Cbase := by
        have hS : 0 ≤ 1 + shortGapMassConstant ^ 2 :=
          add_nonneg (by norm_num) (sq_nonneg _)
        have hE : 0 ≤ 1 + sourceReflectionErrorConstant ell ^ 2 :=
          add_nonneg (by norm_num) (sq_nonneg _)
        have hM : 0 ≤ 1 + sourceMellinMass ^ 2 :=
          add_nonneg (by norm_num) (sq_nonneg _)
        have hC' : 0 ≤ 1 + C_hb := by
          linarith only [hChb.le]
        have hI : 0 ≤ (1 + idx) ^ 5 :=
          pow_nonneg (by linarith only [hidx0]) _
        have hbig : 0 ≤ 200000 * sourceZeroLegConstant *
            (1 + shortGapMassConstant ^ 2) *
            (1 + sourceReflectionErrorConstant ell ^ 2) *
            (1 + sourceMellinMass ^ 2) * (1 + C_hb) * (1 + idx) ^ 5 :=
          mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
            (mul_nonneg (mul_nonneg (by norm_num) hC0) hS) hE) hM) hC') hI
        exact le_trans hbig hC
      have hh := mul_le_mul (h1.trans hC) hpow7
        (Real.rpow_nonneg hT0 _) hCbase
      simpa [mul_assoc] using hh
    exact mul_le_mul_of_nonneg_right hcoef hshape0
  have hdecomp :
      3 * (N : ℝ) ^ 3 * sourceZeroLegConstant *
          (sourceShortGapPairMoment N W (N : ℝ) +
            ∑ i ∈ Finset.range (K + 1),
              (sourceCentralBudget C_hb (eta / 2) T W
                  ((N : ℝ) * (2 : ℝ) ^ i) ((N : ℝ) / 2) (i + L) +
                2 * (W.card : ℝ) ^ 2 *
                  (sourceReflectionErrorConstant ell * (2 : ℝ) ^ L /
                    (N : ℝ)) ^ 2)) =
        3 * (N : ℝ) ^ 3 * sourceZeroLegConstant *
            sourceShortGapPairMoment N W (N : ℝ) +
          3 * (N : ℝ) ^ 3 * sourceZeroLegConstant *
            ∑ i ∈ Finset.range (K + 1),
              sourceCentralBudget C_hb (eta / 2) T W
                ((N : ℝ) * (2 : ℝ) ^ i) ((N : ℝ) / 2) (i + L) +
          3 * (N : ℝ) ^ 3 * sourceZeroLegConstant *
            ∑ i ∈ Finset.range (K + 1),
              (2 * (W.card : ℝ) ^ 2 *
                (sourceReflectionErrorConstant ell * (2 : ℝ) ^ L /
                  (N : ℝ)) ^ 2) := by
    simp [Finset.sum_add_distrib, mul_add, add_assoc]
  have hsum3 := add_le_add (add_le_add hshortC hcentSum) herrSum
  have hsumAbs :
      3 * sourceZeroLegConstant * shortGapMassConstant ^ 2 *
          sourceS2SharpShape T N W +
        153600 * sourceZeroLegConstant * sourceMellinMass ^ 2 * (1 + C_hb) *
          idx ^ 5 * Real.rpow T (eta / 2 + 7 * sourceS2Subpower eta) *
          sourceS2SharpShape T N W +
        12 * sourceZeroLegConstant * sourceReflectionErrorConstant ell ^ 2 *
          idx * Real.rpow T (2 * sourceS2Subpower eta) *
          sourceS2SharpShape T N W ≤
        Cfin * Real.rpow T eta * sourceS2SharpShape T N W := by
    have hadd := add_le_add (add_le_add hshortAbs hcentAbs) herrAbs
    have hCbase :
        Cbase * Real.rpow T eta * sourceS2SharpShape T N W +
          Cbase * Real.rpow T eta * sourceS2SharpShape T N W +
          Cbase * Real.rpow T eta * sourceS2SharpShape T N W =
          Cfin * Real.rpow T eta * sourceS2SharpShape T N W := by
      unfold Cfin
      ring
    exact hadd.trans_eq hCbase
  exact (hS2.trans_eq hdecomp).trans (hsum3.trans hsumAbs)

theorem sourceT_le_Nsq {N T : ℝ} (hN : 1 ≤ N)
    (hT : T = Real.rpow N (6 / 5 : ℝ)) :
    T ≤ N ^ 2 := by
  rw [hT]
  exact (Real.rpow_le_rpow_of_exponent_le hN
    (by norm_num : (6 / 5 : ℝ) ≤ 2)).trans_eq (Real.rpow_natCast N 2)

/-- Printed Proposition 6.1 at `k = 2`, in the Guth--Maynard geometry
`T = N^(6/5)`. Cutoffs are ordinary numeric choices. -/
theorem norm_sourceS2_le_sharp {eta : ℝ} (heta : 0 < eta) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (N : ℕ) (W : Finset ℝ),
        T₀ ≤ T → 1 ≤ N →
        T = Real.rpow (N : ℝ) (6 / 5 : ℝ) →
        OneSeparated W → ContainedInIntervalOfLength W T →
        ‖sourceS2 N W‖ ≤
          C * Real.rpow T eta * sourceS2SharpShape T N W := by
  obtain ⟨C, T₀, hC, hT₀, hcut⟩ := norm_sourceS2_le_sharp_cutoffs heta
  let T₁ : ℝ := max T₀ 16
  refine ⟨C, T₁, hC, le_trans (by norm_num : (2 : ℝ) ≤ 16) (le_max_right _ _), ?_⟩
  intro T N W hT1 hN hTdef hsep hinterval
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hT16 : 16 ≤ T := (le_max_right T₀ 16).trans hT1
  have hT0le : T₀ ≤ T := (le_max_left T₀ 16).trans hT1
  have hδ0 := sourceS2Subpower_pos heta
  have hδ12 := sourceS2Subpower_le_one_div_twelve eta
  obtain ⟨K, L, hKlo, hKhi, hLlo, hLhi, hJall⟩ :=
    exists_sourceS2_dyadic_cutoffs hNreal hTdef hT16 hδ0 hδ12
  have h2N := two_time_subpower_le_sourceN hNreal hTdef hT16 hδ12
  have hTN := sourceT_le_Nsq hNreal hTdef
  exact hcut T N W K L hT0le hN hTN hKlo hKhi hLlo hLhi h2N hJall
    hsep hinterval

end
end GuthMaynardS2SharpConsumer

#print axioms GuthMaynardS2SharpConsumer.norm_sourceS2_le_sharp
#print axioms GuthMaynardS2SharpConsumer.norm_sourceS2_le_sharp_cutoffs
#print axioms GuthMaynardS2SharpConsumer.sourceGapPoweredBudget_error_inserted
#print axioms GuthMaynardS2SharpConsumer.sourceS2_error_contrib_le
#print axioms GuthMaynardS2SharpConsumer.sourceS2_central_contrib_le
