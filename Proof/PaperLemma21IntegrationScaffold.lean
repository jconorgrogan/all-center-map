import FourSectorCompletionRemaining
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Algebraic integration scaffold for manuscript Lemma 2.1

This module is deliberately an integration scaffold, not a certification of
the nonzero determinant estimate.  Its only analytic premise is the raw,
literal bound on `nonzeroTauSurvivorMass` at the scale which the forthcoming
Shiu aggregation must supply.  All later harmonic, logarithmic, prefactor,
and four-term assembly steps are proved here.
-/

noncomputable section

namespace MAPMixedMeanCompletion

open DeterminantCountWeld MixedMeanFrontend MixedMeanMajorantWeld
open MAPMixedMeanFloor MAPMixedMeanZeroClose MAPMixedMean MixedMellinCert

/-- On the manuscript range `M,N ≥ 2`, the common logarithm is at least one. -/
theorem one_le_paperCommonLog
    (M N : ℕ) (hM : 2 ≤ M) (hN : 2 ≤ N) :
    (1 : ℝ) ≤ Real.log (2 * (M : ℝ) * (N : ℝ)) := by
  have hMN8 : (8 : ℝ) ≤ 2 * (M : ℝ) * (N : ℝ) := by
    exact_mod_cast
      (Nat.mul_le_mul (Nat.mul_le_mul (show 2 ≤ 2 by omega) hM) hN)
  have hexp : Real.exp 1 ≤ 2 * (M : ℝ) * (N : ℝ) :=
    Real.exp_one_lt_three.le.trans (by linarith)
  calc
    (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (2 * (M : ℝ) * (N : ℝ)) :=
      Real.log_le_log (Real.exp_pos 1) hexp

/-- Any harmonic number whose index lies below `2MN` is at most twice the
single common logarithm used in the paper. -/
theorem harmonic_cast_le_two_paperCommonLog
    (M N X : ℕ) (hM : 2 ≤ M) (hN : 2 ≤ N)
    (hX : X ≤ 2 * M * N) :
    ((harmonic X : ℚ) : ℝ) ≤
      2 * Real.log (2 * (M : ℝ) * (N : ℝ)) := by
  let L := Real.log (2 * (M : ℝ) * (N : ℝ))
  have hL : (1 : ℝ) ≤ L := one_le_paperCommonLog M N hM hN
  by_cases hX0 : X = 0
  · subst X
    simp only [harmonic, Finset.range_zero, Finset.sum_empty, Rat.cast_zero]
    exact mul_nonneg (by norm_num) (zero_le_one.trans hL)
  · have hXpos : (0 : ℝ) < X := by exact_mod_cast (Nat.pos_of_ne_zero hX0)
    have hXreal : (X : ℝ) ≤ 2 * (M : ℝ) * (N : ℝ) := by
      exact_mod_cast hX
    have hlog : Real.log (X : ℝ) ≤ L :=
      Real.log_le_log hXpos hXreal
    have hharm := harmonic_le_one_add_log X
    exact hharm.trans (by dsimp [L] at hL hlog ⊢; linarith)

/-- The short floor collar also lies below the common harmonic cutoff `2MN`
when `N ≥ 2` and `U ≥ 1`. -/
theorem shortFloorCollar_le_commonProduct
    (M N : ℕ) {U : ℝ} (hN : 2 ≤ N) (hU : 1 ≤ U) :
    shortFloorCollar M U ≤ 2 * M * N := by
  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hK := shortFloorCollar_cast_le M hUpos
  have hdiv : Real.pi * (M : ℝ) / U ≤ Real.pi * (M : ℝ) :=
    div_le_self (by positivity) hU
  have hpi : Real.pi * (M : ℝ) ≤ 4 * (M : ℝ) :=
    mul_le_mul_of_nonneg_right Real.pi_lt_four.le (by positivity)
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hfour : 4 * (M : ℝ) ≤ 2 * (M : ℝ) * (N : ℝ) := by
    nlinarith [show (0 : ℝ) ≤ M by positivity]
  exact_mod_cast hK.trans (hdiv.trans (hpi.trans hfour))

private theorem harmonic_nonneg_real (X : ℕ) :
    (0 : ℝ) ≤ ((harmonic X : ℚ) : ℝ) := by
  exact_mod_cast
    (show (0 : ℚ) ≤ harmonic X by
      have hz := harmonic_mono (x := 0) (y := X) (Nat.zero_le X)
      simpa using hz)

private theorem paperCommonLog_pow_mono
    (M N p q : ℕ) (hM : 2 ≤ M) (hN : 2 ≤ N) (hpq : p ≤ q) :
    Real.log (2 * (M : ℝ) * (N : ℝ)) ^ p ≤
      Real.log (2 * (M : ℝ) * (N : ℝ)) ^ q := by
  exact pow_le_pow_right₀ (one_le_paperCommonLog M N hM hN) hpq

/-- The equal-short harmonic tail is absorbed by the single logarithmic power
appearing in Lemma 2.1. -/
theorem equalShort_prefactor_le_commonLogTerm
    (a k M N : ℕ) {T U : ℝ}
    (hk : 1 ≤ k) (hM : 2 ≤ M) (hN : 2 ≤ N)
    (hT : 1 ≤ T) (hU : 1 ≤ U) :
    256 * T * U *
        (Real.log (2 * (M : ℝ) * (N : ℝ)) ^ (4 * a) /
          ((M : ℝ) * (N : ℝ))) *
      weightedMass (tauTupleWeight k)
        (equalShortFrequencySector M N
          (Real.pi / (2 * U)) (Real.pi / (2 * T))) ≤
      (4096 * (2 : ℝ) ^ (k * k - 1)) *
        Real.log (2 * (M : ℝ) * (N : ℝ)) ^
          (4 * a + 2 * max 2 (k * k) + 2) *
        (U * T + U * (N : ℝ) + (M : ℝ) * (N : ℝ) + T) := by
  let L := Real.log (2 * (M : ℝ) * (N : ℝ))
  let e := k * k - 1
  let E := 4 * a + 2 * max 2 (k * k) + 2
  have hbase := equalShort_paper_prefactor_bound a k M N hk
    (by omega) (by omega) (lt_of_lt_of_le zero_lt_one hT)
    (lt_of_lt_of_le zero_lt_one hU)
  have hHN : ((harmonic (2 * N) : ℚ) : ℝ) ≤ 2 * L := by
    apply harmonic_cast_le_two_paperCommonLog M N (2 * N) hM hN
    nlinarith
  have hHNpow :
      ((harmonic (2 * N) : ℚ) : ℝ) ^ e ≤ (2 * L) ^ e :=
    pow_le_pow_left₀ (harmonic_nonneg_real (2 * N)) hHN e
  have hL : (1 : ℝ) ≤ L := one_le_paperCommonLog M N hM hN
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hexp : 4 * a + e ≤ E := by
    dsimp [e, E]
    omega
  have hpow : L ^ (4 * a) * (2 * L) ^ e ≤
      (2 : ℝ) ^ e * L ^ E := by
    rw [mul_pow]
    calc
      L ^ (4 * a) * (2 ^ e * L ^ e) =
          2 ^ e * L ^ (4 * a + e) := by rw [pow_add]; ring
      _ ≤ 2 ^ e * L ^ E := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hL hexp) (by positivity)
  let S := U * T + U * (N : ℝ) + (M : ℝ) * (N : ℝ) + T
  have hUT0 : 0 ≤ U * T := mul_nonneg (by linarith) (by linarith)
  have hUN0 : 0 ≤ U * (N : ℝ) := by positivity
  have hMN0 : 0 ≤ (M : ℝ) * (N : ℝ) := by positivity
  have hT0 : 0 ≤ T := by linarith
  have hsum : U * T + 2 * Real.pi * U * (N : ℝ) ≤ 8 * S := by
    have hpi : 2 * Real.pi ≤ (8 : ℝ) := by nlinarith [Real.pi_lt_four.le]
    have hpUN : 2 * Real.pi * (U * (N : ℝ)) ≤ 8 * (U * (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hpi hUN0
    dsimp [S]
    calc
      U * T + 2 * Real.pi * U * (N : ℝ) =
          U * T + (2 * Real.pi) * (U * (N : ℝ)) := by ring
      _ ≤ U * T + 8 * (U * (N : ℝ)) := by nlinarith
      _ ≤ 8 * (U * T + U * (N : ℝ) +
          (M : ℝ) * (N : ℝ) + T) := by nlinarith
  calc
    256 * T * U *
        (Real.log (2 * (M : ℝ) * (N : ℝ)) ^ (4 * a) /
          ((M : ℝ) * (N : ℝ))) *
      weightedMass (tauTupleWeight k)
        (equalShortFrequencySector M N
          (Real.pi / (2 * U)) (Real.pi / (2 * T))) ≤
      512 * (U * T + 2 * Real.pi * U * N) * L ^ (4 * a) *
        ((harmonic (2 * N) : ℚ) : ℝ) ^ e := by
          simpa [L, e] using hbase
    _ ≤ 512 * (U * T + 2 * Real.pi * U * N) * L ^ (4 * a) *
        (2 * L) ^ e := by
      exact mul_le_mul_of_nonneg_left hHNpow
        (mul_nonneg
          (mul_nonneg (by norm_num)
            (add_nonneg hUT0 (by positivity)))
          (pow_nonneg hL0 _))
    _ = 512 * (U * T + 2 * Real.pi * U * N) *
        (L ^ (4 * a) * (2 * L) ^ e) := by ring
    _ ≤ 512 * (8 * S) * (L ^ (4 * a) * (2 * L) ^ e) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum (by norm_num))
        (mul_nonneg (pow_nonneg hL0 _) (pow_nonneg (by positivity) _))
    _ ≤ 512 * (8 * S) * ((2 : ℝ) ^ e * L ^ E) := by
      exact mul_le_mul_of_nonneg_left hpow
        (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) (by
          dsimp [S]
          positivity)))
    _ = (4096 * (2 : ℝ) ^ (k * k - 1)) *
        Real.log (2 * (M : ℝ) * (N : ℝ)) ^
          (4 * a + 2 * max 2 (k * k) + 2) *
        (U * T + U * (N : ℝ) + (M : ℝ) * (N : ℝ) + T) := by
      dsimp [S, L, e, E]
      ring

/-- The zero-determinant harmonic tail is absorbed by the same common
logarithmic power. -/
theorem zeroSector_prefactor_le_commonLogTerm
    (a k M N : ℕ) {T U : ℝ}
    (hk : 1 ≤ k) (hM : 2 ≤ M) (hN : 2 ≤ N)
    (hT : 1 ≤ T) (hU : 1 ≤ U) :
    256 * T * U *
        (Real.log (2 * (M : ℝ) * (N : ℝ)) ^ (4 * a) /
          ((M : ℝ) * (N : ℝ))) *
      weightedMass (tauTupleWeight k)
        (zeroFrequencySector M N
          (Real.pi / (2 * U)) (Real.pi / (2 * T))) ≤
      (16384 * (2 : ℝ) ^ (k * k - 1) *
        (2 : ℝ) ^ (k * k - 1)) *
        Real.log (2 * (M : ℝ) * (N : ℝ)) ^
          (4 * a + 2 * max 2 (k * k) + 2) *
        (U * T + U * (N : ℝ) + (M : ℝ) * (N : ℝ) + T) := by
  let L := Real.log (2 * (M : ℝ) * (N : ℝ))
  let e := k * k - 1
  let E := 4 * a + 2 * max 2 (k * k) + 2
  let K := shortFloorCollar M U
  have hbase := zeroSector_paper_prefactor_bound a k M N hk
    (by omega) (by omega) (lt_of_lt_of_le zero_lt_one hT)
    (lt_of_lt_of_le zero_lt_one hU)
  have hKcommon : K ≤ 2 * M * N := by
    exact shortFloorCollar_le_commonProduct M N hN hU
  have hHK : ((harmonic K : ℚ) : ℝ) ≤ 2 * L :=
    harmonic_cast_le_two_paperCommonLog M N K hM hN hKcommon
  have hHN : ((harmonic (2 * N) : ℚ) : ℝ) ≤ 2 * L := by
    apply harmonic_cast_le_two_paperCommonLog M N (2 * N) hM hN
    nlinarith
  have hHM : ((harmonic (2 * M) : ℚ) : ℝ) ≤ 2 * L := by
    apply harmonic_cast_le_two_paperCommonLog M N (2 * M) hM hN
    nlinarith
  have hHNpow : ((harmonic (2 * N) : ℚ) : ℝ) ^ e ≤ (2 * L) ^ e :=
    pow_le_pow_left₀ (harmonic_nonneg_real (2 * N)) hHN e
  have hHMpow : ((harmonic (2 * M) : ℚ) : ℝ) ^ e ≤ (2 * L) ^ e :=
    pow_le_pow_left₀ (harmonic_nonneg_real (2 * M)) hHM e
  have hL : (1 : ℝ) ≤ L := one_le_paperCommonLog M N hM hN
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hexp : ((4 * a + 1) + e) + e ≤ E := by
    dsimp [e, E]
    omega
  have hpow :
      L ^ (4 * a) * (2 * L) * (2 * L) ^ e * (2 * L) ^ e ≤
        (2 * (2 : ℝ) ^ e * (2 : ℝ) ^ e) * L ^ E := by
    rw [mul_pow]
    calc
      L ^ (4 * a) * (2 * L) * (2 ^ e * L ^ e) * (2 ^ e * L ^ e) =
          (2 * 2 ^ e * 2 ^ e) * L ^ (((4 * a + 1) + e) + e) := by
            repeat' rw [pow_add]
            ring
      _ ≤ (2 * 2 ^ e * 2 ^ e) * L ^ E := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hL hexp) (by positivity)
  let S := U * T + U * (N : ℝ) + (M : ℝ) * (N : ℝ) + T
  have hT0 : 0 ≤ T := by linarith
  have hTsum : T ≤ S := by
    dsimp [S]
    nlinarith [mul_nonneg (by linarith : 0 ≤ U) (by linarith : 0 ≤ T),
      mul_nonneg (by linarith : 0 ≤ U) (show (0 : ℝ) ≤ N by positivity),
      mul_nonneg (show (0 : ℝ) ≤ M by positivity) (show (0 : ℝ) ≤ N by positivity)]
  calc
    256 * T * U *
        (Real.log (2 * (M : ℝ) * (N : ℝ)) ^ (4 * a) /
          ((M : ℝ) * (N : ℝ))) *
      weightedMass (tauTupleWeight k)
        (zeroFrequencySector M N
          (Real.pi / (2 * U)) (Real.pi / (2 * T))) ≤
      2048 * Real.pi * T * L ^ (4 * a) *
        ((harmonic K : ℚ) : ℝ) *
        ((harmonic (2 * N) : ℚ) : ℝ) ^ e *
        ((harmonic (2 * M) : ℚ) : ℝ) ^ e := by
          simpa [L, e, K] using hbase
    _ ≤ 2048 * Real.pi * T *
        (L ^ (4 * a) * (2 * L) * (2 * L) ^ e * (2 * L) ^ e) := by
      have htail :
          L ^ (4 * a) * ((harmonic K : ℚ) : ℝ) *
              ((harmonic (2 * N) : ℚ) : ℝ) ^ e *
              ((harmonic (2 * M) : ℚ) : ℝ) ^ e ≤
            L ^ (4 * a) * (2 * L) * (2 * L) ^ e * (2 * L) ^ e := by
        gcongr
        · exact pow_nonneg (harmonic_nonneg_real (2 * M)) e
        · exact pow_nonneg (harmonic_nonneg_real (2 * N)) e
      calc
        2048 * Real.pi * T * L ^ (4 * a) *
              ((harmonic K : ℚ) : ℝ) *
              ((harmonic (2 * N) : ℚ) : ℝ) ^ e *
              ((harmonic (2 * M) : ℚ) : ℝ) ^ e =
            (2048 * Real.pi * T) *
              (L ^ (4 * a) * ((harmonic K : ℚ) : ℝ) *
                ((harmonic (2 * N) : ℚ) : ℝ) ^ e *
                ((harmonic (2 * M) : ℚ) : ℝ) ^ e) := by ring
        _ ≤ (2048 * Real.pi * T) *
            (L ^ (4 * a) * (2 * L) * (2 * L) ^ e * (2 * L) ^ e) :=
          mul_le_mul_of_nonneg_left htail (by positivity)
        _ = 2048 * Real.pi * T *
            (L ^ (4 * a) * (2 * L) * (2 * L) ^ e * (2 * L) ^ e) := by ring
    _ ≤ 2048 * Real.pi * T *
        ((2 * (2 : ℝ) ^ e * (2 : ℝ) ^ e) * L ^ E) := by
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ 2048 * 4 * S *
        ((2 * (2 : ℝ) ^ e * (2 : ℝ) ^ e) * L ^ E) := by
      apply mul_le_mul_of_nonneg_right
      · have hpT : Real.pi * T ≤ 4 * S :=
          mul_le_mul Real.pi_lt_four.le hTsum hT0 (by norm_num)
        nlinarith
      · positivity
    _ = (16384 * (2 : ℝ) ^ (k * k - 1) *
        (2 : ℝ) ^ (k * k - 1)) *
        Real.log (2 * (M : ℝ) * (N : ℝ)) ^
          (4 * a + 2 * max 2 (k * k) + 2) *
        (U * T + U * (N : ℝ) + (M : ℝ) * (N : ℝ) + T) := by
      dsimp [S, L, e, E]
      ring

/-- The exact algebraic cancellation which turns the raw nonzero survivor
estimate into the `MN` term of Lemma 2.1. -/
theorem nonzero_prefactor_le_commonLogTerm
    (Cnonzero : ℝ) (a k M N : ℕ) {T U : ℝ}
    (hM : 2 ≤ M) (hN : 2 ≤ N) (hT : 1 ≤ T) (hU : 1 ≤ U)
    (hmass : nonzeroTauSurvivorMass k M N T U ≤
      Cnonzero *
        (((M : ℝ) * (N : ℝ)) ^ 2 / (T * U)) *
        Real.log (2 * (M : ℝ) * (N : ℝ)) ^
          (2 * max 2 (k * k) + 2)) :
    256 * T * U *
        (Real.log (2 * (M : ℝ) * (N : ℝ)) ^ (4 * a) /
          ((M : ℝ) * (N : ℝ))) *
      nonzeroTauSurvivorMass k M N T U ≤
      (256 * Cnonzero) *
        Real.log (2 * (M : ℝ) * (N : ℝ)) ^
          (4 * a + 2 * max 2 (k * k) + 2) *
        ((M : ℝ) * (N : ℝ)) := by
  let L := Real.log (2 * (M : ℝ) * (N : ℝ))
  have hL0 : 0 ≤ L := zero_le_one.trans (one_le_paperCommonLog M N hM hN)
  have hpref : 0 ≤ 256 * T * U *
      (L ^ (4 * a) / ((M : ℝ) * (N : ℝ))) := by positivity
  calc
    256 * T * U * (L ^ (4 * a) / ((M : ℝ) * (N : ℝ))) *
        nonzeroTauSurvivorMass k M N T U ≤
      256 * T * U * (L ^ (4 * a) / ((M : ℝ) * (N : ℝ))) *
        (Cnonzero * (((M : ℝ) * (N : ℝ)) ^ 2 / (T * U)) *
          L ^ (2 * max 2 (k * k) + 2)) :=
      mul_le_mul_of_nonneg_left hmass hpref
    _ = (256 * Cnonzero) *
        L ^ (4 * a + 2 * max 2 (k * k) + 2) *
        ((M : ℝ) * (N : ℝ)) := by
      have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
      have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      have hTr : T ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hT)
      have hUr : U ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hU)
      rw [pow_add]
      field_simp [hMr, hNr, hTr, hUr]
      ring

/-- Algebraic completion of the exact quantified conclusion of Lemma 2.1
from the narrow raw estimate on the literal nonzero survivor mass. -/
theorem paperMixedMeanLemma21_conclusion_of_nonzeroTauSurvivorMass_bound
    (c : ℝ) (a k : ℕ) (_hc : 0 < c) (hk : 1 ≤ k)
    (hNonzero : ∃ Cnonzero : ℝ, 0 < Cnonzero ∧
      ∀ (M N : ℕ) (T U : ℝ),
        2 ≤ M → 2 ≤ N →
        c * (M : ℝ) ^ 2 ≤ (N : ℝ) →
        1 ≤ T → 1 ≤ U →
        nonzeroTauSurvivorMass k M N T U ≤
          Cnonzero *
            (((M : ℝ) * (N : ℝ)) ^ 2 / (T * U)) *
            Real.log (2 * (M : ℝ) * (N : ℝ)) ^
              (2 * max 2 (k * k) + 2)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M N : ℕ) (βraw graw : ℕ → ℂ) (t₀ T U : ℝ),
        2 ≤ M → 2 ≤ N →
        c * (M : ℝ) ^ 2 ≤ (N : ℝ) →
        1 ≤ T → 1 ≤ U →
        MAPNormalizedWrapper.PaperCoefficientBounds
          M N a k βraw graw →
        (paperLiteralMixedMean M N βraw graw t₀ T U).re ≤
          C * Real.log (2 * (M : ℝ) * (N : ℝ)) ^
              (4 * a + 2 * max 2 (k * k) + 2) *
            (U * T + U * (N : ℝ) + (M : ℝ) * (N : ℝ) + T) := by
  obtain ⟨Cnonzero, hCnonzero, hNonzero⟩ := hNonzero
  let e := k * k - 1
  let Cequal : ℝ := 4096 * (2 : ℝ) ^ e
  let Czero : ℝ := 16384 * (2 : ℝ) ^ e * (2 : ℝ) ^ e
  let C : ℝ := Cequal + 256 * Cnonzero + Czero
  refine ⟨C, by dsimp [C, Cequal, Czero]; positivity, ?_⟩
  intro M N βraw graw t₀ T U hM hN hNM hT hU hcoeff
  let L := Real.log (2 * (M : ℝ) * (N : ℝ))
  let E := 4 * a + 2 * max 2 (k * k) + 2
  let S := U * T + U * (N : ℝ) + (M : ℝ) * (N : ℝ) + T
  let P := 256 * T * U * (L ^ (4 * a) / ((M : ℝ) * (N : ℝ)))
  have hfront := paperLiteralMixedMean_re_le_tauSurvivorMass
    (M := M) (N := N) (a := a) (k := k)
    (βraw := βraw) (graw := graw) t₀ hM hN
    (lt_of_lt_of_le zero_lt_one hT) (lt_of_lt_of_le zero_lt_one hU) hcoeff
  have heq := equalShort_prefactor_le_commonLogTerm
    a k M N hk hM hN hT hU
  have hzero := zeroSector_prefactor_le_commonLogTerm
    a k M N hk hM hN hT hU
  have hnzRaw := hNonzero M N T U hM hN hNM hT hU
  have hnz := nonzero_prefactor_le_commonLogTerm
    Cnonzero a k M N hM hN hT hU hnzRaw
  have hMNsum : (M : ℝ) * (N : ℝ) ≤ S := by
    dsimp [S]
    nlinarith [mul_nonneg (by linarith : 0 ≤ U) (by linarith : 0 ≤ T),
      mul_nonneg (by linarith : 0 ≤ U) (show (0 : ℝ) ≤ N by positivity),
      show (0 : ℝ) ≤ T by linarith]
  have hL0 : 0 ≤ L := zero_le_one.trans (one_le_paperCommonLog M N hM hN)
  have hLE0 : 0 ≤ L ^ E := pow_nonneg hL0 E
  have hnzS :
      (256 * Cnonzero) * L ^ E * ((M : ℝ) * (N : ℝ)) ≤
        (256 * Cnonzero) * L ^ E * S := by
    exact mul_le_mul_of_nonneg_left hMNsum
      (mul_nonneg (mul_nonneg (by norm_num) hCnonzero.le) hLE0)
  rw [paperTauSurvivorMass_eq_sector_sum] at hfront
  have hassembled :
      P *
        (weightedMass (tauTupleWeight k)
            (equalShortFrequencySector M N
              (Real.pi / (2 * U)) (Real.pi / (2 * T))) +
          weightedMass (tauTupleWeight k)
            (positiveFrequencySector M N
              (Real.pi / (2 * U)) (Real.pi / (2 * T))) +
          weightedMass (tauTupleWeight k)
            (negativeFrequencySector M N
              (Real.pi / (2 * U)) (Real.pi / (2 * T))) +
          weightedMass (tauTupleWeight k)
            (zeroFrequencySector M N
              (Real.pi / (2 * U)) (Real.pi / (2 * T)))) ≤
        C * L ^ E * S := by
    have hsplit :
        P *
          (weightedMass (tauTupleWeight k)
              (equalShortFrequencySector M N
                (Real.pi / (2 * U)) (Real.pi / (2 * T))) +
            weightedMass (tauTupleWeight k)
              (positiveFrequencySector M N
                (Real.pi / (2 * U)) (Real.pi / (2 * T))) +
            weightedMass (tauTupleWeight k)
              (negativeFrequencySector M N
                (Real.pi / (2 * U)) (Real.pi / (2 * T))) +
            weightedMass (tauTupleWeight k)
              (zeroFrequencySector M N
                (Real.pi / (2 * U)) (Real.pi / (2 * T)))) =
          P * weightedMass (tauTupleWeight k)
              (equalShortFrequencySector M N
                (Real.pi / (2 * U)) (Real.pi / (2 * T))) +
          P * nonzeroTauSurvivorMass k M N T U +
          P * weightedMass (tauTupleWeight k)
              (zeroFrequencySector M N
                (Real.pi / (2 * U)) (Real.pi / (2 * T))) := by
      unfold nonzeroTauSurvivorMass
      ring
    rw [hsplit]
    calc
      P * weightedMass (tauTupleWeight k)
            (equalShortFrequencySector M N
              (Real.pi / (2 * U)) (Real.pi / (2 * T))) +
          P * nonzeroTauSurvivorMass k M N T U +
          P * weightedMass (tauTupleWeight k)
            (zeroFrequencySector M N
              (Real.pi / (2 * U)) (Real.pi / (2 * T))) ≤
        Cequal * L ^ E * S +
          (256 * Cnonzero) * L ^ E * ((M : ℝ) * (N : ℝ)) +
          Czero * L ^ E * S := by
            dsimp [P, L, E, Cequal, Czero]
            exact add_le_add (add_le_add heq hnz) hzero
      _ ≤ Cequal * L ^ E * S +
          (256 * Cnonzero) * L ^ E * S +
          Czero * L ^ E * S := add_le_add_left (add_le_add_right hnzS _) _
      _ = C * L ^ E * S := by
        dsimp [C]
        ring
  exact hfront.trans (by simpa [P, L, E, S] using hassembled)

/-- Direct integration theorem: a forthcoming proof of the literal nonzero
aggregation estimate can be supplied here to discharge the sole analytic
premise and obtain the exact `PaperMixedMeanLemma21` surface. -/
theorem paperMixedMeanLemma21_of_nonzeroTauSurvivorMass_bound
    (c : ℝ) (a k : ℕ)
    (hNonzero : 0 < c → 1 ≤ k →
      ∃ Cnonzero : ℝ, 0 < Cnonzero ∧
        ∀ (M N : ℕ) (T U : ℝ),
          2 ≤ M → 2 ≤ N →
          c * (M : ℝ) ^ 2 ≤ (N : ℝ) →
          1 ≤ T → 1 ≤ U →
          nonzeroTauSurvivorMass k M N T U ≤
            Cnonzero *
              (((M : ℝ) * (N : ℝ)) ^ 2 / (T * U)) *
              Real.log (2 * (M : ℝ) * (N : ℝ)) ^
                (2 * max 2 (k * k) + 2)) :
    PaperMixedMeanLemma21 c a k := by
  intro hc hk
  exact paperMixedMeanLemma21_conclusion_of_nonzeroTauSurvivorMass_bound
    c a k hc hk (hNonzero hc hk)

end MAPMixedMeanCompletion
