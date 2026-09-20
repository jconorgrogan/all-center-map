import Mathlib

noncomputable section
namespace FordNaturalScaleBounds

/-- A real lower bound on a natural scale is transferred exactly through `Nat.floor`. -/
theorem nat_le_floor_rpow
    {P k : ℕ} {a : ℝ}
    (hreal : (k : ℝ) ≤ (P : ℝ) ^ a) :
    k ≤ Nat.floor ((P : ℝ) ^ a) := by
  exact Nat.le_floor hreal

/-- The floor at exponent `b` dominates the product of the floor at `a`
with a natural multiplier controlled by the increment `delta`. -/
theorem floor_product_le
    {P C : ℕ} {a b delta : ℝ}
    (hP : 1 ≤ P) (hC : 1 ≤ C)
    (hdelta : 0 < delta) (hsep : a + delta ≤ b)
    (hCscale : (C : ℝ) ≤ (P : ℝ) ^ delta) :
    C * Nat.floor ((P : ℝ) ^ a) ≤ Nat.floor ((P : ℝ) ^ b) := by
  have hPpos : 0 < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hP1 : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  have hPnonneg : (0 : ℝ) ≤ (P : ℝ) := hPpos.le
  have hX0 : 0 ≤ (P : ℝ) ^ a := Real.rpow_nonneg hPnonneg _
  have hY0 : 0 ≤ (P : ℝ) ^ b := Real.rpow_nonneg hPnonneg _
  have hfloor : (Nat.floor ((P : ℝ) ^ a) : ℝ) ≤ (P : ℝ) ^ a :=
    Nat.floor_le hX0
  have hC1 : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
  have hC0 : 0 ≤ (C : ℝ) := by linarith
  have hmul :
      ((C * Nat.floor ((P : ℝ) ^ a) : ℕ) : ℝ) ≤
        (P : ℝ) ^ b := by
    calc
      ((C * Nat.floor ((P : ℝ) ^ a) : ℕ) : ℝ) =
          (C : ℝ) * Nat.floor ((P : ℝ) ^ a) := by norm_num
      _ ≤ (C : ℝ) * (P : ℝ) ^ a :=
        mul_le_mul_of_nonneg_left hfloor hC0
      _ ≤ (P : ℝ) ^ delta * (P : ℝ) ^ a :=
        mul_le_mul_of_nonneg_right hCscale hX0
      _ = (P : ℝ) ^ (delta + a) := (Real.rpow_add hPpos delta a).symm
      _ ≤ (P : ℝ) ^ b := by
        apply Real.rpow_le_rpow_of_exponent_le hP1
        linarith [hsep, hdelta]
  exact Nat.le_floor hmul

/-- If the real exponent is at least `1/(k+1)`, the exact floor scale
supports the native source-size inequality. -/
theorem floor_source_power_lower
    {P k : ℕ} {a : ℝ}
    (hP : 1 ≤ P) (hk : 1 ≤ k)
    (ha : (1 : ℝ) / (k + 1 : ℝ) ≤ a) :
    P ≤ (Nat.floor ((P : ℝ) ^ a) + 1) ^ (k + 1) := by
  have hP1 : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  have hP0 : (0 : ℝ) ≤ (P : ℝ) := by positivity
  have hk1 : 0 < (k + 1 : ℝ) := by positivity
  have hexp : (1 : ℝ) ≤ a * (k + 1 : ℝ) := by
    exact (div_le_iff₀ hk1).mp ha
  have hpow :
      (P : ℝ) ≤ ((P : ℝ) ^ a) ^ (k + 1 : ℕ) := by
    calc
      (P : ℝ) = (P : ℝ) ^ (1 : ℝ) := by simp
      _ ≤ (P : ℝ) ^ (a * (k + 1 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hP1 hexp
      _ = ((P : ℝ) ^ a) ^ (k + 1 : ℕ) := by
        calc
          (P : ℝ) ^ (a * (k + 1 : ℝ)) =
              ((P : ℝ) ^ a) ^ (k + 1 : ℝ) :=
            Real.rpow_mul hP0 a (k + 1)
          _ = ((P : ℝ) ^ a) ^ (k + 1 : ℕ) := by
            simpa [Nat.cast_add] using
              (Real.rpow_natCast ((P : ℝ) ^ a) (k + 1))
  have hfloor :
      (P : ℝ) ^ a ≤
        ((Nat.floor ((P : ℝ) ^ a) + 1 : ℕ) : ℝ) := by
    simpa [Nat.cast_add] using (Nat.lt_floor_add_one ((P : ℝ) ^ a)).le
  have hpowfloor :
      ((P : ℝ) ^ a) ^ (k + 1 : ℕ) ≤
        (((Nat.floor ((P : ℝ) ^ a) + 1 : ℕ) : ℝ) ^ (k + 1 : ℕ)) := by
    exact pow_le_pow_left₀ (by positivity) hfloor (k + 1)
  have hnat :
      (P : ℝ) ≤
        (((Nat.floor ((P : ℝ) ^ a) + 1) ^ (k + 1) : ℕ) : ℝ) := by
    calc
      (P : ℝ) ≤ ((P : ℝ) ^ a) ^ (k + 1 : ℕ) := hpow
      _ ≤ (((Nat.floor ((P : ℝ) ^ a) + 1 : ℕ) : ℝ) ^ (k + 1 : ℕ)) := hpowfloor
      _ = (((Nat.floor ((P : ℝ) ^ a) + 1) ^ (k + 1) : ℕ) : ℝ) := by norm_num
  exact_mod_cast hnat

end FordNaturalScaleBounds

#print axioms FordNaturalScaleBounds.nat_le_floor_rpow
#print axioms FordNaturalScaleBounds.floor_product_le
#print axioms FordNaturalScaleBounds.floor_source_power_lower
