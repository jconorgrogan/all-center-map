import FordSourceWPrefactor
import FordWeakCompleteMoment
import FordWeakBilinear
import FordScaleCancellation

open scoped BigOperators
noncomputable section

namespace FordBinaryPrefactorCost

open FordWeakCompleteMoment FordWeakBilinear FordSourceWProduct
open FordSourceWPrefactor FordScaleCancellation FordSourceWCoefficient

/-- The coefficient left after the source product insertion and the floor loss. -/
def binaryPrefactorCost (k : ℕ) : ℝ :=
  weakCoefficient k ^ 2 * (order k : ℝ) ^ k * (3 : ℝ) ^ k *
    prefactor (order k) k * (2 : ℝ) ^ deficit k

lemma nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        n + 1 ≤ 2 ^ n + 1 := Nat.succ_le_succ ih
        _ ≤ 2 ^ n + 2 ^ n := by
          have hp : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
          omega
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- The actual binary prefactor is bounded by one explicit natural power of two. -/
theorem binary_prefactor_cost_le {k : ℕ} (hk : 2000 ≤ k) :
    binaryPrefactorCost k ≤ (2 : ℝ) ^ ((2 ^ 26) * k ^ 6) := by
  let R := FordWeakBilinear.order k
  have hk1 : 1 ≤ k := by omega
  have hR : 1 ≤ R := by
    dsimp [R, FordWeakBilinear.order]
    nlinarith
  have hRpow : (R : ℝ) ^ k ≤ (2 : ℝ) ^ (R * k) := by
    have hn := nat_le_two_pow R
    have hp : R ^ k ≤ (2 ^ R) ^ k := Nat.pow_le_pow_left hn k
    have hp' : (R : ℝ) ^ k ≤ ((2 : ℝ) ^ R) ^ k := by exact_mod_cast hp
    simpa [← pow_mul] using hp'
  have h3pow : (3 : ℝ) ^ k ≤ (2 : ℝ) ^ (3 * k) := by
    have hp : (3 : ℕ) ^ k ≤ (2 ^ 3) ^ k :=
      Nat.pow_le_pow_left (by norm_num) k
    have hp' : (3 : ℝ) ^ k ≤ ((2 : ℝ) ^ 3) ^ k := by exact_mod_cast hp
    simpa [← pow_mul] using hp'
  have h32pow : (32 * (R : ℝ) * (k + 1)) ^ k ≤
      (2 : ℝ) ^ (32 * R * (k + 1) * k) := by
    have hn : 32 * R * (k + 1) ≤ 2 ^ (32 * R * (k + 1)) :=
      nat_le_two_pow _
    have hp := Nat.pow_le_pow_left hn k
    have hp' : (32 * (R : ℝ) * (k + 1)) ^ k ≤
        ((2 : ℝ) ^ (32 * R * (k + 1))) ^ k := by
      exact_mod_cast hp
    simpa [← pow_mul, Nat.cast_mul, Nat.cast_add] using hp'
  have h4pow : (4 : ℝ) ^ (k * k) = (2 : ℝ) ^ (2 * k * k) := by
    calc
      (4 : ℝ) ^ (k * k) = ((2 : ℝ) ^ 2) ^ (k * k) := by norm_num
      _ = (2 : ℝ) ^ (2 * (k * k)) := by rw [← pow_mul]
      _ = (2 : ℝ) ^ (2 * k * k) := by congr 1; ring
  have hdef : deficit k ≤ (k : ℝ) * k := by
    unfold deficit
    norm_num [FordWEnvelopeScalar.eps]
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hmul : 0 ≤ ((k : ℝ) - 1) * (k : ℝ) :=
      mul_nonneg (sub_nonneg.mpr hkR) (by positivity)
    nlinarith
  have hdefpowR : (2 : ℝ) ^ deficit k ≤ (2 : ℝ) ^ ((k : ℝ) * k) := by
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hdef
  have hdefpow : (2 : ℝ) ^ deficit k ≤ (2 : ℝ) ^ (k * k) := by
    calc
      _ ≤ (2 : ℝ) ^ ((k : ℝ) * k) := hdefpowR
      _ = (2 : ℝ) ^ (k * k) := by
        rw [← Real.rpow_natCast]
        congr 1
        norm_num [Nat.cast_mul]
  have hpref0 : 0 ≤ prefactor R k := by
    unfold prefactor FordSourceWEnvelope.coeff
    positivity
  have hpref : prefactor R k ≤
      (2 : ℝ) ^ (32 * R * (k + 1) * k + 2 * k * k) := by
    have hp := FordSourceWPrefactor.prefactor_le (R := R) (k := k) hR
    rw [h4pow] at hp
    calc
      _ ≤ (32 * (R : ℝ) * (k + 1)) ^ k * (2 : ℝ) ^ (2 * k * k) := hp
      _ ≤ (2 : ℝ) ^ (32 * R * (k + 1) * k) *
          (2 : ℝ) ^ (2 * k * k) :=
        mul_le_mul_of_nonneg_right h32pow (by positivity)
      _ = _ := by rw [← pow_add]
  have hweak : weakCoefficient k ^ 2 =
      (2 : ℝ) ^ (2 * (2 ^ 24) * k ^ 6) := by
    unfold weakCoefficient
    rw [← pow_mul]
    norm_num
    ring
  have hsumR :
      (2 * (2 ^ 24) : ℝ) * (k : ℝ) ^ 6 + (R : ℝ) * k + 3 * k +
          (32 * (R : ℝ) * (k + 1) * k + 2 * k * k) + k * k ≤
        (2 ^ 26 : ℝ) * k ^ 6 := by
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hp23 : (k : ℝ) ^ 3 ≤ k ^ 6 := pow_le_pow_right₀ hkR (by norm_num)
    have hp24 : (k : ℝ) ^ 4 ≤ k ^ 6 := pow_le_pow_right₀ hkR (by norm_num)
    have hp2 : (k : ℝ) ^ 2 ≤ k ^ 6 := pow_le_pow_right₀ hkR (by norm_num)
    dsimp [R, FordWeakBilinear.order]
    norm_num
    nlinarith
  have hsum :
      2 * (2 ^ 24) * k ^ 6 + R * k + 3 * k +
          (32 * R * (k + 1) * k + 2 * k * k) + k * k ≤
        (2 ^ 26) * k ^ 6 := by
    exact_mod_cast hsumR
  unfold binaryPrefactorCost
  dsimp [R] at hRpow h3pow h32pow hpref
  rw [hweak]
  calc
    _ ≤ (2 : ℝ) ^ (2 * (2 ^ 24) * k ^ 6) *
        (2 : ℝ) ^ (R * k) * (2 : ℝ) ^ (3 * k) *
        (2 : ℝ) ^ (32 * R * (k + 1) * k + 2 * k * k) *
        (2 : ℝ) ^ (k * k) := by
      gcongr
    _ = (2 : ℝ) ^
        (2 * (2 ^ 24) * k ^ 6 + R * k + 3 * k +
          (32 * R * (k + 1) * k + 2 * k * k) + k * k) := by
      rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
    _ ≤ (2 : ℝ) ^ ((2 ^ 26) * k ^ 6) := by
      exact pow_le_pow_right₀ (by norm_num) hsum

end FordBinaryPrefactorCost

#print axioms FordBinaryPrefactorCost.binary_prefactor_cost_le
