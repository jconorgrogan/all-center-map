import GuthMaynardEnergy119FloorCutoff
import GuthMaynardEnergy119WeightedHolder

open scoped BigOperators
noncomputable section
namespace GuthMaynardEnergy119WeightedFloor
open GuthMaynardEnergy119FloorCutoff GuthMaynardEnergy119WeightedHolder

/-- Exact floor-cutoff and harmonic losses in the high-gcd Cauchy step. -/
theorem weighted_floor_sum_le
    {N T R E B F : ℝ} (H : ℕ)
    (hT : 0 < T) (hscale : T ≤ N^2)
    (hR : 0 ≤ R) (hE : 0 ≤ E) (hB : 0 ≤ B) (hF : 0 ≤ F) :
    (∑ d ∈ Finset.Icc (Nat.floor (N^2/T)+1) H,
      Real.sqrt (R*N^2/(d : ℝ)^2+B/(d : ℝ))*
        Real.sqrt (E*N^2/(d : ℝ)^2+F/(d : ℝ))) ≤
      2*(1+Real.log (max 1 (H : ℝ)))*
        Real.sqrt (R*T+B)*Real.sqrt (E*T+F) := by
  let D := Nat.floor (N^2/T)
  let L := 1+Real.log (max 1 (H : ℝ))
  have hL : 1 ≤ L := by
    have hh := Real.log_nonneg (le_max_left (1 : ℝ) (H : ℝ))
    dsimp [L]
    linarith
  have hL0 : 0 ≤ L := by linarith
  obtain ⟨hD,hDinv⟩ := floor_cutoff_bounds hT hscale
  have hN2 : N^2 ≠ 0 := ne_of_gt (lt_of_lt_of_le hT hscale)
  have hNne : N ≠ 0 := by intro hh; simp [hh] at hN2
  have hfirst : R*N^2/(D : ℝ) ≤ 2*R*T := by
    have hh := mul_le_mul_of_nonneg_left hDinv (mul_nonneg hR (sq_nonneg N))
    calc
      _ = R*N^2*(D : ℝ)⁻¹ := by ring
      _ ≤ R*N^2*(2*T/N^2) := hh
      _ = _ := by field_simp [hNne]
  have hsecond : E*N^2/(D : ℝ) ≤ 2*E*T := by
    have hh := mul_le_mul_of_nonneg_left hDinv (mul_nonneg hE (sq_nonneg N))
    calc
      _ = E*N^2*(D : ℝ)⁻¹ := by ring
      _ ≤ E*N^2*(2*T/N^2) := hh
      _ = _ := by field_simp [hNne]
  have hX : R*N^2/(D : ℝ)+B*L ≤ 2*L*(R*T+B) := by
    have hh := mul_le_mul_of_nonneg_right hL (mul_nonneg hR hT.le)
    have hbL := mul_nonneg hB hL0
    nlinarith
  have hY : E*N^2/(D : ℝ)+F*L ≤ 2*L*(E*T+F) := by
    have hh := mul_le_mul_of_nonneg_right hL (mul_nonneg hE hT.le)
    have hfL := mul_nonneg hF hL0
    nlinarith
  have hw := weighted_holder_tail_le (H := H) hD
    (mul_nonneg hR (sq_nonneg N)) hB (mul_nonneg hE (sq_nonneg N)) hF
  calc
    _ ≤ Real.sqrt (R*N^2/(D : ℝ)+B*L)*
        Real.sqrt (E*N^2/(D : ℝ)+F*L) := hw
    _ ≤ Real.sqrt (2*L*(R*T+B))*Real.sqrt (2*L*(E*T+F)) :=
      mul_le_mul (Real.sqrt_le_sqrt hX) (Real.sqrt_le_sqrt hY)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ 2*L),
        Real.sqrt_mul (by positivity : 0 ≤ 2*L)]
      calc
        _ = (Real.sqrt (2*L))^2*Real.sqrt (R*T+B)*Real.sqrt (E*T+F) := by ring
        _ = _ := by rw [Real.sq_sqrt (by positivity : 0 ≤ 2*L)]

end GuthMaynardEnergy119WeightedFloor
#print axioms GuthMaynardEnergy119WeightedFloor.weighted_floor_sum_le
