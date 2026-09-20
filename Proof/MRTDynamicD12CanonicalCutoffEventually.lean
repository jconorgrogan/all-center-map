import MRTDynamicD12ActiveCanonicalLedger

namespace MRTDynamicD12CanonicalCutoffEventually

open Filter
open MAPDynamicHBSourceV3

noncomputable section

set_option maxHeartbeats 400000

theorem eventually_two_le_floor_dynamicHBCutoff
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ X : ℝ in atTop,
      2 ≤ ⌊dynamicHBCutoff X (hbOrder delta)⌋₊ := by
  have hK : 0 < hbOrder delta := hbOrder_pos hdelta
  have hKreal : 0 < (hbOrder delta : ℝ) := by exact_mod_cast hK
  have hexp : 0 < ((hbOrder delta : ℝ)⁻¹) := by positivity
  have hbase : Tendsto (fun X : ℝ => 2 * X) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have hpow : Tendsto
      (fun X : ℝ => Real.rpow (2 * X) ((hbOrder delta : ℝ)⁻¹))
      atTop atTop :=
    (tendsto_rpow_atTop hexp).comp hbase
  filter_upwards [hpow.eventually (eventually_ge_atTop (2 : ℝ))] with X hX
  unfold dynamicHBCutoff
  exact Nat.le_floor hX

end
end MRTDynamicD12CanonicalCutoffEventually

#print axioms MRTDynamicD12CanonicalCutoffEventually.eventually_two_le_floor_dynamicHBCutoff
