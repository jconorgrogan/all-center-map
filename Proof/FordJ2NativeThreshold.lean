import Mathlib
import FordNaturalScaleBounds

noncomputable section
namespace FordJ2NativeThreshold

private lemma nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        n + 1 ≤ 2 ^ n + 1 := Nat.succ_le_succ ih
        _ ≤ 2 ^ n + 2 ^ n := by
          have h : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
          omega
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

private lemma four_s_bound
    {k s : ℕ} (hk : 2000 ≤ k) (hs : s ≤ 1003 * k ^ 2) :
    4 * s ≤ 2 ^ (12 + 2 * k) := by
  have hk2 : k ^ 2 ≤ 2 ^ (2 * k) := by
    have h := pow_le_pow_left₀ (show 0 ≤ k by positivity)
      (show k ≤ 2 ^ k by exact nat_le_two_pow k) 2
    simpa [pow_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  have h4012 : 4012 ≤ 2 ^ 12 := by norm_num
  have hprod : 4 * s ≤ 4012 * k ^ 2 := by
    nlinarith [hs]
  calc
    4 * s ≤ 4012 * k ^ 2 := hprod
    _ ≤ 2 ^ 12 * 2 ^ (2 * k) := by
      exact Nat.mul_le_mul h4012 hk2
    _ = 2 ^ (12 + 2 * k) := by rw [← pow_add]

private lemma coeff_nat_bound
    {k s : ℕ} (hk : 2000 ≤ k) (hs : s ≤ 1003 * k ^ 2) :
    (4 * s) ^ 2 * 2 ^ (k ^ 3) ≤ 2 ^ (10 * k ^ 4) := by
  have h4s := four_s_bound hk hs
  have hsq := pow_le_pow_left₀ (show 0 ≤ 4 * s by positivity) h4s 2
  have hpow : (4 * s) ^ 2 ≤ 2 ^ (24 + 4 * k) := by
    calc
      (4 * s) ^ 2 ≤ (2 ^ (12 + 2 * k)) ^ 2 := hsq
      _ = 2 ^ (24 + 4 * k) := by rw [← pow_mul]; congr 1 <;> omega
  have hmul := Nat.mul_le_mul_right (2 ^ (k ^ 3)) hpow
  have hk4 : k ≤ k ^ 4 := Nat.le_pow (by omega)
  have hk3 : k ^ 3 ≤ k ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hfive : 5 * k ≤ 5 * k ^ 4 := Nat.mul_le_mul_left 5 hk4
  have hexp : 24 + 4 * k + k ^ 3 ≤ 10 * k ^ 4 := by omega
  calc
    (4 * s) ^ 2 * 2 ^ (k ^ 3) ≤ 2 ^ (24 + 4 * k) * 2 ^ (k ^ 3) := hmul
    _ = 2 ^ (24 + 4 * k + k ^ 3) := by rw [← pow_add]
    _ ≤ 2 ^ (10 * k ^ 4) := by exact pow_le_pow_right₀ (by norm_num) hexp

theorem terminal_coefficient_rpow
    {P k s : ℕ}
    (hk : 2000 ≤ k) (hP : 2 ^ (100 * k ^ 4) ≤ P)
    (hs : s ≤ 1003 * k ^ 2) :
    ((4 * s) ^ 2 * 2 ^ (k ^ 3) : ℝ) ≤ (P : ℝ) ^ ((1 : ℝ) / 10) := by
  have hcoeff :
      ((4 * s) ^ 2 * 2 ^ (k ^ 3) : ℝ) ≤ (2 : ℝ) ^ (10 * k ^ 4) := by
    exact_mod_cast coeff_nat_bound hk hs
  have hPreal : (2 : ℝ) ^ (100 * k ^ 4) ≤ (P : ℝ) := by
    exact_mod_cast hP
  have hroot :
      ((2 : ℝ) ^ (100 * k ^ 4)) ^ ((1 : ℝ) / 10) =
        (2 : ℝ) ^ (10 * k ^ 4) := by
    have hinner :
        (2 : ℝ) ^ (100 * k ^ 4) =
          (2 : ℝ) ^ ((100 * k ^ 4 : ℕ) : ℝ) := by
      symm
      exact Real.rpow_natCast (2 : ℝ) (100 * k ^ 4)
    calc
      ((2 : ℝ) ^ (100 * k ^ 4)) ^ ((1 : ℝ) / 10) =
          ((2 : ℝ) ^ ((100 * k ^ 4 : ℕ) : ℝ)) ^ ((1 : ℝ) / 10) := by rw [hinner]
      _ = (2 : ℝ) ^ (((100 * k ^ 4 : ℕ) : ℝ) * ((1 : ℝ) / 10)) := by
        rw [← Real.rpow_mul (by positivity)]
      _ = (2 : ℝ) ^ ((10 * k ^ 4 : ℕ) : ℝ) := by
        congr 1
        norm_num [Nat.cast_mul, Nat.cast_pow]
        ring
      _ = (2 : ℝ) ^ (10 * k ^ 4) := by rw [Real.rpow_natCast]
  have hmon := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 2 ^ (100 * k ^ 4))
    hPreal (by positivity : (0 : ℝ) ≤ (1 : ℝ) / 10)
  rw [hroot] at hmon
  exact hcoeff.trans hmon

end FordJ2NativeThreshold

#print axioms FordJ2NativeThreshold.terminal_coefficient_rpow

namespace FordJ2NativeThreshold

 theorem source_floor_native
    {P k : ℕ} (hk : 2000 ≤ k)
    (hP : 2 ^ (100 * k ^ 4) ≤ P) {a : ℝ}
    (ha : (1 : ℝ) / (k + 1 : ℝ) ≤ a) :
    k ≤ Nat.floor ((P : ℝ) ^ a) ∧
      P ≤ (Nat.floor ((P : ℝ) ^ a) + 1) ^ (k + 1) := by
  have hPnat : 1 ≤ P := by
    have hbase : 1 ≤ 2 ^ (100 * k ^ 4) := Nat.one_le_pow _ _ (by norm_num)
    exact hbase.trans hP
  have hP1 : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hPnat
  have hkR : (k : ℝ) ≤ (2 : ℝ) ^ k := by
    exact_mod_cast nat_le_two_pow k
  have hk1pos : 0 < (k + 1 : ℝ) := by positivity
  have hexp : (k : ℝ) ≤ ((100 * k ^ 4 : ℕ) : ℝ) * (1 / (k + 1 : ℝ)) := by
    rw [show ((100 * k ^ 4 : ℕ) : ℝ) * (1 / (k + 1 : ℝ)) =
        ((100 * k ^ 4 : ℕ) : ℝ) / (k + 1 : ℝ) by ring]
    apply (le_div_iff₀ hk1pos).2
    have hk2pow : k ^ 2 ≤ k ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have hkprod : k * (k + 1) ≤ 100 * k ^ 4 := by
      calc
        k * (k + 1) ≤ k * (2 * k) := Nat.mul_le_mul_left k (by omega)
        _ = 2 * k ^ 2 := by ring
        _ ≤ 2 * k ^ 4 := Nat.mul_le_mul_left 2 hk2pow
        _ ≤ 100 * k ^ 4 := by omega
    norm_num [Nat.cast_mul, Nat.cast_pow]
    exact_mod_cast hkprod
  have hroot_eq :
      ((2 : ℝ) ^ (100 * k ^ 4)) ^ (1 / (k + 1 : ℝ)) =
        (2 : ℝ) ^ (((100 * k ^ 4 : ℕ) : ℝ) * (1 / (k + 1 : ℝ))) := by
    have hinner :
        (2 : ℝ) ^ (100 * k ^ 4) =
          (2 : ℝ) ^ ((100 * k ^ 4 : ℕ) : ℝ) := by
      symm
      exact Real.rpow_natCast (2 : ℝ) (100 * k ^ 4)
    rw [hinner, ← Real.rpow_mul (by positivity)]
  have hroot_ge :
      (2 : ℝ) ^ k ≤ ((2 : ℝ) ^ (100 * k ^ 4)) ^ (1 / (k + 1 : ℝ)) := by
    have h2k : (2 : ℝ) ^ k = (2 : ℝ) ^ (k : ℝ) := by
      symm
      exact Real.rpow_natCast (2 : ℝ) k
    rw [h2k, hroot_eq]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hPbase : (2 : ℝ) ^ (100 * k ^ 4) ≤ (P : ℝ) := by
    exact_mod_cast hP
  have hbase_mon :
      ((2 : ℝ) ^ (100 * k ^ 4)) ^ (1 / (k + 1 : ℝ)) ≤
        (P : ℝ) ^ (1 / (k + 1 : ℝ)) :=
    Real.rpow_le_rpow (by positivity) hPbase (by positivity)
  have hka : (k : ℝ) ≤ (P : ℝ) ^ a := by
    have hpow_a : (P : ℝ) ^ (1 / (k + 1 : ℝ)) ≤ (P : ℝ) ^ a :=
      Real.rpow_le_rpow_of_exponent_le hP1 ha
    exact hkR.trans (hroot_ge.trans (hbase_mon.trans hpow_a))
  have hknat : k ≤ Nat.floor ((P : ℝ) ^ a) :=
    FordNaturalScaleBounds.nat_le_floor_rpow hka
  have hsource := FordNaturalScaleBounds.floor_source_power_lower
    (P := P) (k := k) hPnat (by omega) ha
  exact ⟨hknat, hsource⟩

end FordJ2NativeThreshold

#print axioms FordJ2NativeThreshold.source_floor_native

namespace FordJ2NativeThreshold

theorem floor_native_step
    {P k s : ℕ} (hk : 2000 ≤ k) (hs0 : 1 ≤ s)
    (hP : 2 ^ (100 * k ^ 4) ≤ P)
    (hs : s ≤ 1003 * k ^ 2)
    {a b : ℝ} (hsep : a + (1 / 10 : ℝ) ≤ b) :
    (4 * s) ^ 2 * 2 ^ (k ^ 3) * Nat.floor ((P : ℝ) ^ a) ≤
      Nat.floor ((P : ℝ) ^ b) := by
  have hPnat : 1 ≤ P := by
    have hbase : 1 ≤ 2 ^ (100 * k ^ 4) := Nat.one_le_pow _ _ (by norm_num)
    exact hbase.trans hP
  have hC : 1 ≤ (4 * s) ^ 2 * 2 ^ (k ^ 3) := by
    have h4s : 1 ≤ 4 * s := by
      have : 1 ≤ 4 := by norm_num
      omega
    have hpow : 1 ≤ (4 * s) ^ 2 := Nat.one_le_pow _ _ h4s
    have htwo : 1 ≤ 2 ^ (k ^ 3) := Nat.one_le_pow _ _ (by norm_num)
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ (4 * s) ^ 2 * 2 ^ (k ^ 3) :=
        Nat.mul_le_mul hpow htwo
  apply FordNaturalScaleBounds.floor_product_le
    (P := P) (C := (4 * s) ^ 2 * 2 ^ (k ^ 3))
    hPnat hC (by norm_num) hsep
  simpa [Nat.cast_mul, Nat.cast_pow] using terminal_coefficient_rpow hk hP hs


theorem threshold_large
    {P k : ℕ} (hk : 2000 ≤ k)
    (hP : 2 ^ (100 * k ^ 4) ≤ P) :
    16 * k ^ 4 < P := by
  have hn : 1 ≤ k ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hnk : k ^ 4 ≤ 2 ^ (k ^ 4) := nat_le_two_pow _
  have hmul : 16 * k ^ 4 ≤ 16 * 2 ^ (k ^ 4) :=
    Nat.mul_le_mul_left 16 hnk
  have hpow : 16 * 2 ^ (k ^ 4) = 2 ^ (4 + k ^ 4) := by
    calc
      16 * 2 ^ (k ^ 4) = 2 ^ 4 * 2 ^ (k ^ 4) := by norm_num
      _ = 2 ^ (4 + k ^ 4) := by rw [← pow_add]
  have hexp : 4 + k ^ 4 < 100 * k ^ 4 := by omega
  have hstrict : 2 ^ (4 + k ^ 4) < 2 ^ (100 * k ^ 4) :=
    Nat.pow_lt_pow_right (by norm_num) hexp
  exact (hmul.trans_lt (hpow ▸ hstrict)).trans_le hP

end FordJ2NativeThreshold

#print axioms FordJ2NativeThreshold.floor_native_step
