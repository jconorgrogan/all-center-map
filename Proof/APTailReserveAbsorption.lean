import APMovingEdgeStrip
import ZeroDensityArithmetic

/-!
# The explicit positive reserve in the AP Perron tail

At the smallest legal aperture,

`T * Y = X^(13/15-reserve/2) * X^(2/15+epsilon)`

has exponent at least `1 + epsilon/2`.  Hence every endpointwise Perron tail
of size `X polylog / T`, after division by `Y`, has a fixed negative power of
`X`, which absorbs every prescribed logarithmic loss.
-/

namespace MAPAPTailReserveAbsorption

open Filter
open MAPFixedScaleAPZeroRoute

noncomputable section

/-- Exact exponent reserve used by the aligned AP route. -/
theorem tail_exponent_le_neg_half
    {epsilon reserve : ℝ} (hreserve : reserve ≤ epsilon) :
    1 - (13 / 15 - reserve / 2) - (2 / 15 + epsilon) ≤
      -epsilon / 2 := by
  linarith

/-- The endpointwise `X/(T Y)` factor has the explicit `X^(-epsilon/2)`
gain at every legal aperture. -/
theorem tail_power_ratio_le
    {X epsilon reserve : ℝ} (hX : 1 ≤ X)
    (hreserve : reserve ≤ epsilon) :
    Real.rpow X 1 /
        (apZeroHeight reserve X * Real.rpow X (2 / 15 + epsilon)) ≤
      Real.rpow X (-epsilon / 2) := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hheight : apZeroHeight reserve X =
      Real.rpow X (13 / 15 - reserve / 2) := rfl
  rw [hheight]
  have hdenpos : 0 < Real.rpow X (13 / 15 - reserve / 2) *
      Real.rpow X (2 / 15 + epsilon) :=
    mul_pos (Real.rpow_pos_of_pos hX0 _) (Real.rpow_pos_of_pos hX0 _)
  calc
    Real.rpow X 1 /
        (Real.rpow X (13 / 15 - reserve / 2) *
          Real.rpow X (2 / 15 + epsilon)) =
      Real.rpow X 1 /
        Real.rpow X ((13 / 15 - reserve / 2) +
          (2 / 15 + epsilon)) := by
        congr 1
        exact (Real.rpow_add hX0 _ _).symm
    _ = Real.rpow X
        (1 - ((13 / 15 - reserve / 2) +
          (2 / 15 + epsilon))) :=
      (Real.rpow_sub hX0 _ _).symm
    _ =
      Real.rpow X
        (1 - (13 / 15 - reserve / 2) - (2 / 15 + epsilon)) := by
        congr 1
        ring
    _ ≤ Real.rpow X (-epsilon / 2) :=
      Real.rpow_le_rpow_of_exponent_le hX
        (tail_exponent_le_neg_half hreserve)

/-- A fixed negative power of `X` absorbs an arbitrary real polylogarithmic
loss, with the target inverse-log power retained explicitly. -/
theorem eventually_tail_power_mul_polylog_le
    (A B epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ X : ℝ in atTop,
      Real.rpow X (-epsilon / 2) * Real.rpow (Real.log X) B ≤
        Real.rpow (Real.log X) (-A) := by
  have heta : 0 < epsilon / 2 := half_pos hepsilon
  have hpoly := ZeroDensityArithmetic.polylog_absorption
    (A + B) (epsilon / 2) heta
  filter_upwards [hpoly, eventually_ge_atTop (Real.exp 1)] with X hpolyX hX
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlog : 1 ≤ Real.log X :=
    (Real.le_log_iff_exp_le hX0).2 hX
  have hlog0 : 0 < Real.log X := zero_lt_one.trans_le hlog
  have hmult := mul_le_mul_of_nonneg_right hpolyX
    (mul_nonneg (Real.rpow_nonneg hX0.le (-epsilon / 2))
      (Real.rpow_nonneg hlog0.le (-A)))
  calc
    Real.rpow X (-epsilon / 2) * Real.rpow (Real.log X) B =
      Real.rpow X (-epsilon / 2) *
        (Real.rpow (Real.log X) (A + B) *
          Real.rpow (Real.log X) (-A)) := by
        congr 1
        calc
          Real.rpow (Real.log X) B =
              Real.rpow (Real.log X) ((A + B) + (-A)) := by
                congr 1
                ring
          _ = Real.rpow (Real.log X) (A + B) *
              Real.rpow (Real.log X) (-A) :=
                Real.rpow_add hlog0 _ _
    _ = (Real.rpow (Real.log X) (A + B) *
          (Real.rpow X (-epsilon / 2) *
            Real.rpow (Real.log X) (-A))) := by ring
    _ ≤ Real.rpow X (epsilon / 2) *
        (Real.rpow X (-epsilon / 2) *
          Real.rpow (Real.log X) (-A)) := hmult
    _ = Real.rpow (Real.log X) (-A) := by
      calc
        Real.rpow X (epsilon / 2) *
            (Real.rpow X (-epsilon / 2) *
              Real.rpow (Real.log X) (-A)) =
          (Real.rpow X (epsilon / 2) *
            Real.rpow X (-epsilon / 2)) *
              Real.rpow (Real.log X) (-A) := by ring
        _ = Real.rpow X (epsilon / 2 + (-epsilon / 2)) *
              Real.rpow (Real.log X) (-A) := by
          congr 1
          exact (Real.rpow_add hX0 _ _).symm
        _ = Real.rpow (Real.log X) (-A) := by
          have hzero : epsilon / 2 + (-epsilon / 2) = 0 := by ring
          rw [hzero]
          have hone : Real.rpow X 0 = 1 := Real.rpow_zero X
          rw [hone, one_mul]

/-- The exact manuscript reserve `min epsilon (1/10)` always retains at
least half of `epsilon`. -/
theorem eventually_literal_tail_ratio_mul_polylog_le
    (A B epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ X : ℝ in atTop,
      (Real.rpow X 1 /
          (apZeroHeight (min epsilon (1 / 10)) X *
            Real.rpow X (2 / 15 + epsilon))) *
          Real.rpow (Real.log X) B ≤
        Real.rpow (Real.log X) (-A) := by
  have htrade := eventually_tail_power_mul_polylog_le A B epsilon hepsilon
  filter_upwards [htrade, eventually_ge_atTop (1 : ℝ)] with X htradeX hX
  have hratio := tail_power_ratio_le hX (min_le_left epsilon (1 / 10))
  calc
    (Real.rpow X 1 /
        (apZeroHeight (min epsilon (1 / 10)) X *
          Real.rpow X (2 / 15 + epsilon))) *
        Real.rpow (Real.log X) B ≤
      Real.rpow X (-epsilon / 2) * Real.rpow (Real.log X) B :=
        mul_le_mul_of_nonneg_right hratio
          (Real.rpow_nonneg (Real.log_nonneg hX) _)
    _ ≤ Real.rpow (Real.log X) (-A) := htradeX

end

end MAPAPTailReserveAbsorption
