import FordWeakPolicyIntegerBridge

noncomputable section
set_option autoImplicit false
namespace FordJ2GeometricAlgebra

def countExponent (s k r d : ℕ) : ℕ :=
  2 * s - d + (r - d) * (r - d - 1) / 2 + r * d + (k - d)

theorem triangular_cast (r : ℕ) :
    ((r * (r - 1) / 2 : ℕ) : ℝ) = (r : ℝ) * ((r : ℝ) - 1) / 2 := by
  have h := Nat.mul_div_cancel' (Nat.two_dvd_mul_sub_one r)
  by_cases hr : r = 0
  · subst r; norm_num
  have hr1 : 1 ≤ r := by omega
  have hc : (2 : ℝ) * ((r * (r - 1) / 2 : ℕ) : ℝ) =
      (r : ℝ) * ((r : ℝ) - 1) := by
    exact_mod_cast h
  linarith

theorem countExponent_zero (s k r : ℕ) :
    (countExponent s k r 0 : ℝ) =
      2 * (s : ℝ) + (r : ℝ) * ((r : ℝ) - 1) / 2 + (k : ℝ) := by
  simp only [countExponent, Nat.sub_zero, Nat.mul_zero, Nat.add_zero,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, triangular_cast]

theorem countExponent_one {s k r : ℕ} (hs : 1 ≤ s) (hk : 1 ≤ k)
    (hr : 2 ≤ r) :
    (countExponent s k r 1 : ℝ) =
      2 * (s : ℝ) + (r : ℝ) * ((r : ℝ) - 1) / 2 + (k : ℝ) - 1 := by
  have hs2 : 1 ≤ 2 * s := by omega
  have hr1 : 1 ≤ r := by omega
  simp only [countExponent, Nat.mul_one, Nat.cast_add,
    Nat.cast_sub hs2, Nat.cast_sub hk, Nat.cast_mul, Nat.cast_ofNat,
    triangular_cast, Nat.cast_sub hr1]
  ring

def lambda (s k Delta : ℝ) : ℝ := 2 * s - k * (k + 1) / 2 + Delta
def eZero (s k r : ℝ) : ℝ := 2 * s + r * (r - 1) / 2 + k

theorem cancellation {s k r Delta : ℝ} (hk : k ≠ 0) (hr : r ≠ 0) :
    k / 2 - k * r * MAPFordWeakPolicy.fordPhi1 k Delta (k - r) +
      (eZero s k r - 1 - lambda s k Delta) * (1 / r) / 2 = 0 := by
  simp only [MAPFordWeakPolicy.fordPhi1, eZero, lambda]
  have hkr : k - (k - r) = r := by ring
  rw [hkr]
  field_simp
  <;> ring

theorem delta_next (s k r Delta : ℝ) :
    MAPFordWeakPolicy.fordDeltaNext k Delta (k - r) =
      Delta - k + MAPFordWeakPolicy.fordPhi1 k Delta (k - r) *
        (eZero s k r - lambda s k Delta) := by
  unfold MAPFordWeakPolicy.fordDeltaNext eZero lambda
  have hkr : k - (k - r) = r := by ring
  rw [hkr]
  ring

theorem terminal_exponent (s k r Delta : ℝ) :
    MAPFordWeakPolicy.fordPhi1 k Delta (k - r) * eZero s k r + k +
      (1 - MAPFordWeakPolicy.fordPhi1 k Delta (k - r)) * lambda s k Delta =
      lambda (s + k) k (MAPFordWeakPolicy.fordDeltaNext k Delta (k - r)) := by
  rw [delta_next s k r Delta]
  unfold lambda
  ring

end FordJ2GeometricAlgebra

#print axioms FordJ2GeometricAlgebra.countExponent_zero
#print axioms FordJ2GeometricAlgebra.countExponent_one
#print axioms FordJ2GeometricAlgebra.cancellation
#print axioms FordJ2GeometricAlgebra.delta_next
#print axioms FordJ2GeometricAlgebra.terminal_exponent
