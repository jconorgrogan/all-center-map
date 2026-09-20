import MRTProposition61TypeIINormalizedAnalyticV3
import MRTProposition61TypeIIDivisorNormalizationV3

/-! # Scalar parameter and logarithmic absorption for the Type-II ledger -/

namespace MRTProposition61TypeIIParameterAbsorptionV3

open Filter Asymptotics
open MAPDynamicHBSourceV3

noncomputable section

set_option maxHeartbeats 1200000

/-- Any fixed polynomial saving absorbs the complete fixed logarithmic loss,
with its constant chosen before `X`. -/
theorem eventually_const_polylog_mul_neg_rpow_le_log_decay
    (C k A a : ℝ) (hC : 0 ≤ C) (ha : 0 < a) :
    ∀ᶠ X : ℝ in atTop,
      C * Real.rpow (Real.log X) k * Real.rpow X (-a) ≤
        Real.rpow (Real.log X) (-A) := by
  have hsmall :=
    ((isLittleO_log_rpow_rpow_atTop (k + A) ha).const_mul_left C).eventuallyLE
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with X hsmall hX
  have hX0 : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos hX
  have hb : C * Real.rpow (Real.log X) (k + A) ≤ Real.rpow X a := by
    simpa only [Real.norm_of_nonneg (mul_nonneg hC (Real.rpow_nonneg hlog.le _)),
      Real.norm_of_nonneg (Real.rpow_nonneg hX0.le _)] using hsmall
  calc
    _ = (C * Real.rpow (Real.log X) (k + A) / Real.rpow X a) *
        Real.rpow (Real.log X) (-A) := by
      simp only [Real.rpow_eq_pow]
      rw [Real.rpow_add hlog, Real.rpow_neg hX0.le, Real.rpow_neg hlog.le]
      field_simp
    _ ≤ 1 * Real.rpow (Real.log X) (-A) :=
      mul_le_mul_of_nonneg_right ((div_le_one (Real.rpow_pos_of_pos hX0 a)).2 hb)
        (Real.rpow_nonneg hlog.le _)
    _ = _ := one_mul _

/-- The selected truncation obeys every truncation hypothesis of the actual
cell Perron theorem; neither the classifier nor that theorem imposes an upper
bound on this parameter. -/
theorem typeII_truncation_ge_one {X : ℝ} (hX : 1 ≤ X) :
    1 ≤ Real.rpow X (2 / 3 : ℝ) :=
  Real.one_le_rpow hX (by norm_num)

/-- Exact exponent margins for the actual base aperture `X^(2/15+reserve)/2`.
The collar comparison has the smallest power margin. -/
theorem typeII_parameter_exponent_margins
    {delta reserve : ℝ} (hdelta : delta ≤ 1 / 240) (hreserve : 0 ≤ reserve) :
    delta + 1 / 8 - (2 / 15 + reserve) ≤ -(1 / 240 : ℝ) ∧
      delta + 1 / 8 + 2 / 3 - 1 ≤ -(1 / 240 : ℝ) ∧
      delta + 1 / 8 - 1 ≤ -(1 / 240 : ℝ) ∧
      2 + 2 * (1 / 24 : ℝ) - 2 * (2 / 3) = (3 / 4 : ℝ) := by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · norm_num

/-- The five power ratios that occur literally in the eight-term endpoint
ledger, evaluated at the selected Perron height and the actual aperture. -/
theorem typeII_parameter_power_ratios
    {X delta reserve : ℝ} (hX : 1 ≤ X)
    (hdelta : delta ≤ 1 / 240)
    (hreserve0 : 0 ≤ reserve) (hreserve : reserve ≤ 1 / 1200) :
    let H := (1 / 2 : ℝ) * Real.rpow X (2 / 15 + reserve)
    let H₀ := Real.rpow X (delta + 1 / 8)
    let T := Real.rpow X (2 / 3 : ℝ)
    H₀ / H ≤ 2 * Real.rpow X (-delta) ∧
      H₀ * T / X ≤ Real.rpow X (-delta) ∧
      H₀ / X ≤ Real.rpow X (-delta) ∧
      T / X ≤ Real.rpow X (-delta) ∧
      H / X ≤ Real.rpow X (-delta) := by
  have hX0 : 0 < X := by linarith
  have hratio (a b : ℝ) (hab : a - b ≤ -delta) :
      Real.rpow X a / Real.rpow X b ≤ Real.rpow X (-delta) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_sub hX0]
    exact Real.rpow_le_rpow_of_exponent_le hX hab
  have hratio1 (a : ℝ) (ha : a - 1 ≤ -delta) :
      Real.rpow X a / X ≤ Real.rpow X (-delta) := by
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using hratio a 1 ha
  dsimp only
  constructor
  · calc
      _ = 2 * (Real.rpow X (delta + 1 / 8) /
          Real.rpow X (2 / 15 + reserve)) := by ring
      _ ≤ 2 * Real.rpow X (-delta) :=
        mul_le_mul_of_nonneg_left (hratio _ _ (by linarith)) (by norm_num)
  constructor
  · simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hX0]
    exact hratio1 _ (by linarith)
  constructor
  · exact hratio1 _ (by linarith)
  constructor
  · exact hratio1 _ (by linarith)
  · calc
      _ = (1 / 2 : ℝ) * (Real.rpow X (2 / 15 + reserve) / X) := by ring
      _ ≤ (1 / 2 : ℝ) * Real.rpow X (-delta) :=
        mul_le_mul_of_nonneg_left (hratio1 _ (by linarith)) (by norm_num)
      _ ≤ Real.rpow X (-delta) := by
        have hnonneg : 0 ≤ Real.rpow X (-delta) := Real.rpow_nonneg hX0.le _
        linarith

/-- Algebraic collar cancellation and the five power-ratio bounds reduce the
literal endpoint expression to three independently absorbable losses. -/
theorem endpoint_terms_le_three_losses
    {X Q q H H₀ U T G R : ℝ}
    (hX : 0 < X) (hQ : 1 ≤ Q) (hq : 0 ≤ q) (hqQ : q ≤ Q)
    (hH : 0 < H) (hH₀ : 0 ≤ H₀) (hU : 1 ≤ U) (hT : 0 ≤ T)
    (hG : 1 ≤ G) (hR : 0 ≤ R)
    (hqU : q * U ≤ H / Q)
    (hH₀H : H₀ / H ≤ 2 * R) (hH₀T : H₀ * T / X ≤ R)
    (hH₀X : H₀ / X ≤ R) (hTX : T / X ≤ R) (hHX : H / X ≤ R) :
    2 * q * U / ((1 / Real.sqrt Q) * H) + 4 * q * T / X +
      4 * q * U / X + 64 * Real.pi * R +
      16 * Real.pi * G * H₀ / ((1 / Real.sqrt Q) * H) +
      32 * Real.pi * G * H₀ * T / (U * X) +
      32 * Real.pi * G * H₀ / X + 128 * Real.pi ^ 2 / U ≤
        1000 * (1 + Real.pi ^ 2) * G *
          (Q * R + 1 / Real.sqrt Q + 1 / U) := by
  have hQ0 : 0 < Q := by linarith
  have hU0 : 0 < U := by linarith
  have hG0 : 0 ≤ G := by linarith
  have hs : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ0
  have hssq := Real.sq_sqrt hQ0.le
  have hsQ : Real.sqrt Q ≤ Q := by nlinarith [Real.sqrt_nonneg Q]
  have hQR : R ≤ Q * R := by nlinarith
  have hfirst : q * U / ((1 / Real.sqrt Q) * H) ≤ 1 / Real.sqrt Q := by
    calc
      _ = (q * U) * Real.sqrt Q / H := by field_simp
      _ ≤ (H / Q) * Real.sqrt Q / H := by gcongr
      _ = 1 / Real.sqrt Q := by
        field_simp
        nlinarith
  have hsecond : q * T / X ≤ Q * R := by
    calc
      _ = q * (T / X) := by ring
      _ ≤ Q * R := mul_le_mul hqQ hTX (div_nonneg hT hX.le) hQ0.le
  have hthird : q * U / X ≤ Q * R := by
    have hbase : q * U ≤ H := hqU.trans (div_le_self hH.le hQ)
    exact ((div_le_div_of_nonneg_right hbase hX.le).trans hHX).trans hQR
  have hfifth : H₀ / ((1 / Real.sqrt Q) * H) ≤ 2 * (Q * R) := by
    calc
      _ = (H₀ / H) * Real.sqrt Q := by field_simp
      _ ≤ (2 * R) * Q := mul_le_mul hH₀H hsQ hs.le (by positivity)
      _ = 2 * (Q * R) := by ring
  have hsixth : H₀ * T / (U * X) ≤ Q * R := by
    calc
      _ = (H₀ * T / X) / U := by ring
      _ ≤ R / U := div_le_div_of_nonneg_right hH₀T hU0.le
      _ ≤ R := div_le_self hR hU
      _ ≤ Q * R := hQR
  have hseventh : H₀ / X ≤ Q * R := hH₀X.trans hQR
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hpiLe : Real.pi ≤ 1 + Real.pi ^ 2 := by nlinarith [sq_nonneg (Real.pi - 1 / 2)]
  have hraw :
      2 * q * U / ((1 / Real.sqrt Q) * H) + 4 * q * T / X +
        4 * q * U / X + 64 * Real.pi * R +
        16 * Real.pi * G * H₀ / ((1 / Real.sqrt Q) * H) +
        32 * Real.pi * G * H₀ * T / (U * X) +
        32 * Real.pi * G * H₀ / X + 128 * Real.pi ^ 2 / U ≤
      (8 + 64 * Real.pi + 96 * Real.pi * G) * (Q * R) +
        2 * (1 / Real.sqrt Q) + 128 * Real.pi ^ 2 * (1 / U) := by
    have h1 := mul_le_mul_of_nonneg_left hfirst (by norm_num : (0 : ℝ) ≤ 2)
    have h2 := mul_le_mul_of_nonneg_left hsecond (by norm_num : (0 : ℝ) ≤ 4)
    have h3 := mul_le_mul_of_nonneg_left hthird (by norm_num : (0 : ℝ) ≤ 4)
    have h4 := mul_le_mul_of_nonneg_left hQR (show 0 ≤ 64 * Real.pi by positivity)
    have h5 := mul_le_mul_of_nonneg_left hfifth (show 0 ≤ 16 * Real.pi * G by positivity)
    have h6 := mul_le_mul_of_nonneg_left hsixth (show 0 ≤ 32 * Real.pi * G by positivity)
    have h7 := mul_le_mul_of_nonneg_left hseventh (show 0 ≤ 32 * Real.pi * G by positivity)
    calc
      _ = 2 * (q * U / ((1 / Real.sqrt Q) * H)) + 4 * (q * T / X) +
          4 * (q * U / X) + 64 * Real.pi * R +
          16 * Real.pi * G * (H₀ / ((1 / Real.sqrt Q) * H)) +
          32 * Real.pi * G * (H₀ * T / (U * X)) +
          32 * Real.pi * G * (H₀ / X) + 128 * Real.pi ^ 2 * (1 / U) := by ring
      _ ≤ _ := by linarith only [h1, h2, h3, h4, h5, h6, h7]
  let C := 1000 * (1 + Real.pi ^ 2) * G
  have hc1 : 8 + 64 * Real.pi + 96 * Real.pi * G ≤ C := by
    dsimp [C]
    have hpg : Real.pi ≤ Real.pi * G := by nlinarith
    have hp2g : (1 + Real.pi ^ 2) ≤ (1 + Real.pi ^ 2) * G := by nlinarith
    have hpig := mul_le_mul_of_nonneg_right hpiLe hG0
    nlinarith
  have hc2 : 2 ≤ C := by dsimp [C]; nlinarith [sq_nonneg Real.pi]
  have hc3 : 128 * Real.pi ^ 2 ≤ C := by
    dsimp [C]
    nlinarith [mul_le_mul_of_nonneg_left hG (sq_nonneg Real.pi)]
  calc
    _ ≤ _ := hraw
    _ ≤ C * (Q * R) + C * (1 / Real.sqrt Q) + C * (1 / U) := by
      gcongr
    _ = _ := by dsimp [C]; ring

end
end MRTProposition61TypeIIParameterAbsorptionV3

#print axioms MRTProposition61TypeIIParameterAbsorptionV3.eventually_const_polylog_mul_neg_rpow_le_log_decay
#print axioms MRTProposition61TypeIIParameterAbsorptionV3.typeII_parameter_exponent_margins

#print axioms MRTProposition61TypeIIParameterAbsorptionV3.typeII_parameter_power_ratios

#print axioms MRTProposition61TypeIIParameterAbsorptionV3.endpoint_terms_le_three_losses
