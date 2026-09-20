import Mathlib

noncomputable section
set_option autoImplicit false
namespace FordDifferencingScalarAbsorption

/-- Scalar normalization used after the literal J and terminal K bounds.
The scale Y is bounded by the divisor Z; neither count bound is asserted here. -/
theorem sqrt_absorb {J K C X D Y Z : ℝ}
    (hJ0 : 0 ≤ J) (hK0 : 0 ≤ K) (hC : 0 ≤ C) (hX : 0 ≤ X)
    (hD : 0 ≤ D) (hY : 0 ≤ Y) (hZ : 0 < Z)
    (hJ : J ≤ C * X) (hK : K ≤ D * C * X * Y ^ 2) (hYZ : Y ≤ Z) :
    2 / Z * Real.sqrt (J * K) ≤ 2 * Real.sqrt D * C * X := by
  have hsD := Real.sq_sqrt hD
  have hb : J * K ≤ (Real.sqrt D * C * X * Y) ^ 2 := by
    calc
      J * K ≤ (C * X) * (D * C * X * Y ^ 2) :=
        mul_le_mul hJ hK hK0 (mul_nonneg hC hX)
      _ = (Real.sqrt D) ^ 2 * C ^ 2 * X ^ 2 * Y ^ 2 := by rw [hsD]; ring
      _ = (Real.sqrt D * C * X * Y) ^ 2 := by ring
  have hs : Real.sqrt (J * K) ≤ Real.sqrt D * C * X * Y :=
    (Real.sqrt_le_left (by positivity)).mpr hb
  calc
    2 / Z * Real.sqrt (J * K) ≤ 2 / Z * (Real.sqrt D * C * X * Y) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ 2 / Z * (Real.sqrt D * C * X * Z) := by gcongr
    _ = 2 * Real.sqrt D * C * X := by field_simp

theorem max_absorb {L F A J K C X D Y Z : ℝ}
    (hF : 0 ≤ F) (hA : 0 ≤ A)
    (hJ0 : 0 ≤ J) (hK0 : 0 ≤ K) (hC : 0 ≤ C) (hX : 0 ≤ X)
    (hD : 0 ≤ D) (hY : 0 ≤ Y) (hZ : 0 < Z)
    (hJ : J ≤ C * X) (hK : K ≤ D * C * X * Y ^ 2) (hYZ : Y ≤ Z)
    (hL : L ≤ F * max (A * J) (2 / Z * Real.sqrt (J * K))) :
    L ≤ F * C * X * max A (2 * Real.sqrt D) := by
  have hs := sqrt_absorb hJ0 hK0 hC hX hD hY hZ hJ hK hYZ
  calc
    L ≤ F * max (A * J) (2 / Z * Real.sqrt (J * K)) := hL
    _ ≤ F * max (A * (C * X)) (2 * Real.sqrt D * C * X) := by
      exact mul_le_mul_of_nonneg_left
        (max_le_max (mul_le_mul_of_nonneg_left hJ hA) hs) hF
    _ = F * C * X * max A (2 * Real.sqrt D) := by
      rw [show A * (C * X) = A * (C * X) by rfl,
        show 2 * Real.sqrt D * C * X = (2 * Real.sqrt D) * (C * X) by ring,
        ← max_mul_of_nonneg _ _ (mul_nonneg hC hX)]
      ring

end FordDifferencingScalarAbsorption
#print axioms FordDifferencingScalarAbsorption.sqrt_absorb
#print axioms FordDifferencingScalarAbsorption.max_absorb
