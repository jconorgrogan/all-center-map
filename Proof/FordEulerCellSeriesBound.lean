import FordEulerCellAnalytic
import FordEulerPowerTail

noncomputable section
namespace FordEulerCellSeriesBound
open FordEulerCellAnalytic

theorem summable_cell {a : ℝ} {s : ℂ}
    (ha : 0 < a) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Summable (fun n : ℕ => cell (a + n) s) := by
  have hp := (FordEulerPowerTail.summable_power ha hs).mul_left ‖s‖
  apply hp.of_norm_bounded
  intro n
  exact FordEulerCellBound.norm_cell_le (by positivity) hs hs1

theorem norm_tsum_cell_le {a : ℝ} {s : ℂ}
    (ha : 0 < a) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖∑' n : ℕ, cell (a + n) s‖ ≤
      ‖s‖ * (a ^ (-s.re - 1) + a ^ (-s.re) / s.re) := by
  have hp := (FordEulerPowerTail.summable_power ha hs).mul_left ‖s‖
  have hb : ∀ n : ℕ, ‖cell (a + n) s‖ ≤ ‖s‖ * (a + n) ^ (-s.re - 1) := by
    intro n
    exact FordEulerCellBound.norm_cell_le (by positivity) hs hs1
  calc
    _ ≤ ∑' n : ℕ, ‖s‖ * (a + n) ^ (-s.re - 1) := tsum_of_norm_bounded hp.hasSum hb
    _ = ‖s‖ * (∑' n : ℕ, (a + n) ^ (-s.re - 1)) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (FordEulerPowerTail.tsum_power_le ha hs) (norm_nonneg s)

theorem norm_cellSeries_le {M : ℕ} {u : ℝ} {s : ℂ}
    (hM : 1 ≤ M) (hu : 0 ≤ u) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖cellSeries M u s‖ ≤ ‖s‖ *
      (((M : ℝ) + u) ^ (-s.re - 1) + ((M : ℝ) + u) ^ (-s.re) / s.re) := by
  exact norm_tsum_cell_le (by positivity) hs hs1

end FordEulerCellSeriesBound
#print axioms FordEulerCellSeriesBound.summable_cell
#print axioms FordEulerCellSeriesBound.norm_tsum_cell_le
#print axioms FordEulerCellSeriesBound.norm_cellSeries_le
