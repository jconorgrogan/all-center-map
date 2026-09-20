import MRTProposition61TypeIIActualCellLedgerV3

/-! # Exact width of the two MRT outer components

The Type-II normalization must retain the short outer-component length.
Replacing it by `X` loses the saving needed in equation (3.5).  These lemmas
record the literal width and its conversion to the stationary-width scale.
-/

namespace MRTProposition61TypeIIEndpointWidthV3

open MAPMRTCorollary53Source

noncomputable section

theorem componentEndpoints_sub_eq_outerUpper_sub_outerLower
    (X beta eta : ℝ) (component : OuterComponent) :
    (componentEndpoints X beta eta component).2 -
        (componentEndpoints X beta eta component).1 =
      outerUpper X beta eta - outerLower X beta eta := by
  cases component <;> simp [componentEndpoints] <;> ring

/-- Each oriented component has length at most the upper collar endpoint.
This is the sharp bound used before the `U=|beta|H` cancellation. -/
theorem componentEndpoints_sub_le_abs_mul_div
    {X beta eta : ℝ} (hX : 0 ≤ X) (heta : 0 ≤ eta)
    (component : OuterComponent) :
    (componentEndpoints X beta eta component).2 -
        (componentEndpoints X beta eta component).1 ≤
      |beta| * X / eta := by
  rw [componentEndpoints_sub_eq_outerUpper_sub_outerLower]
  unfold outerUpper outerLower
  have hlower : 0 ≤ eta * |beta| * X := by positivity
  linarith

/-- In stationary-width variables, the exact outer collar costs
`U*X/(eta*H)`, not `X`. -/
theorem componentEndpoints_sub_le_stationaryWidth_mul
    {X H beta eta : ℝ} (hX : 0 ≤ X) (heta : 0 ≤ eta)
    (hH : 0 < H) (component : OuterComponent) :
    (componentEndpoints X beta eta component).2 -
        (componentEndpoints X beta eta component).1 ≤
      stationaryWidth beta H * X / (eta * H) := by
  have hwidth := componentEndpoints_sub_le_abs_mul_div
    (beta := beta) hX heta component
  calc
    _ ≤ |beta| * X / eta := hwidth
    _ = stationaryWidth beta H * X / (eta * H) := by
      unfold stationaryWidth
      field_simp

end
end MRTProposition61TypeIIEndpointWidthV3

#print axioms MRTProposition61TypeIIEndpointWidthV3.componentEndpoints_sub_eq_outerUpper_sub_outerLower
#print axioms MRTProposition61TypeIIEndpointWidthV3.componentEndpoints_sub_le_abs_mul_div
#print axioms MRTProposition61TypeIIEndpointWidthV3.componentEndpoints_sub_le_stationaryWidth_mul
