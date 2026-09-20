import Mathlib

noncomputable section
namespace FordTerminalPrimeScale

/-- A prime above the exact real floor of the `r`-th root has its `r`-th
power strictly above the source scale. -/
theorem terminal_prime_scale
    {P r p : ℕ}
    (hP : 1 ≤ P) (hr : 1 ≤ r)
    (hp : Nat.floor ((P : ℝ) ^ ((1 : ℝ) / (r : ℝ))) < p) :
    P < p ^ r := by
  have hPpos : 0 < (P : ℝ) := by
    exact_mod_cast (show 0 < P by omega)
  have hPnonneg : 0 ≤ (P : ℝ) := hPpos.le
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hroot0 : 0 ≤ (P : ℝ) ^ ((1 : ℝ) / (r : ℝ)) :=
    Real.rpow_nonneg hPnonneg _
  have hrootp : (P : ℝ) ^ ((1 : ℝ) / (r : ℝ)) < (p : ℝ) :=
    (Nat.floor_lt hroot0).mp hp
  have hpowlt :
      ((P : ℝ) ^ ((1 : ℝ) / (r : ℝ))) ^ r < (p : ℝ) ^ r := by
    exact pow_lt_pow_left₀ hrootp hroot0 (by omega)
  have hone : ((1 : ℝ) / (r : ℝ)) * (r : ℝ) = 1 := by
    field_simp
  have hrootpow :
      ((P : ℝ) ^ ((1 : ℝ) / (r : ℝ))) ^ r = (P : ℝ) := by
    calc
      ((P : ℝ) ^ ((1 : ℝ) / (r : ℝ))) ^ r =
          ((P : ℝ) ^ ((1 : ℝ) / (r : ℝ))) ^ (r : ℝ) := by
            rw [Real.rpow_natCast]
      _ = (P : ℝ) ^ (((1 : ℝ) / (r : ℝ)) * (r : ℝ)) := by
            rw [Real.rpow_mul hPnonneg]
      _ = (P : ℝ) ^ (1 : ℝ) := by rw [hone]
      _ = (P : ℝ) := by simp
  have hPp : (P : ℝ) < (p : ℝ) ^ r := by
    rw [← hrootpow]
    exact hpowlt
  exact_mod_cast hPp

/-- Exact natural shortening after flooring both endpoint scales. -/
theorem floor_quotient_shortening
    {P Q p : ℕ} {a b : ℝ}
    (hP : 1 ≤ P) (hab : a ≤ b)
    (hp : Nat.floor ((P : ℝ) ^ a) < p)
    (hQ : Q ≤ Nat.floor ((P : ℝ) ^ b)) :
    Q / p ≤ Nat.floor ((P : ℝ) ^ (b - a)) := by
  have hPpos : 0 < (P : ℝ) := by
    exact_mod_cast (show 0 < P by omega)
  have hPnonneg : 0 ≤ (P : ℝ) := hPpos.le
  have hPa0 : 0 ≤ (P : ℝ) ^ a := Real.rpow_nonneg hPnonneg _
  have hPb0 : 0 ≤ (P : ℝ) ^ b := Real.rpow_nonneg hPnonneg _
  have hPapos : 0 < (P : ℝ) ^ a := Real.rpow_pos_of_pos hPpos _
  have hpa : (P : ℝ) ^ a < (p : ℝ) :=
    (Nat.floor_lt hPa0).mp hp
  have hpapos : (P : ℝ) ^ a ≤ (p : ℝ) := hpa.le
  have hQreal : (Q : ℝ) ≤ (P : ℝ) ^ b := by
    calc
      (Q : ℝ) ≤ (Nat.floor ((P : ℝ) ^ b) : ℝ) := by exact_mod_cast hQ
      _ ≤ (P : ℝ) ^ b := Nat.floor_le hPb0
  have hdiv :
      (Q : ℝ) / (p : ℝ) ≤ (P : ℝ) ^ b / (P : ℝ) ^ a := by
    exact div_le_div₀ (by positivity) hQreal hPapos hpapos
  have hdiv' :
      (Q : ℝ) / (p : ℝ) ≤ (P : ℝ) ^ (b - a) := by
    rw [Real.rpow_sub hPpos]
    exact hdiv
  have hcast : ((Q / p : ℕ) : ℝ) ≤ (Q : ℝ) / (p : ℝ) := Nat.cast_div_le
  exact Nat.le_floor (hcast.trans hdiv')

end FordTerminalPrimeScale

#print axioms FordTerminalPrimeScale.terminal_prime_scale
#print axioms FordTerminalPrimeScale.floor_quotient_shortening
