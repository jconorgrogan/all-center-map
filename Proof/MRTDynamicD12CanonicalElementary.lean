import MRTProposition61TypeIIEndpointWidthV3

namespace MRTDynamicD12CanonicalElementary

open MAPMRTCorollary53Source MRTProposition61TypeIIEndpointWidthV3
noncomputable section

theorem canonical_component_length_bounds
    {X Q beta : ℝ} (hX : 0 ≤ X) (hQ : 1 ≤ Q) (component : OuterComponent) :
    0 ≤ (componentEndpoints X beta (1 / Real.sqrt Q) component).2 -
      (componentEndpoints X beta (1 / Real.sqrt Q) component).1 ∧
    (componentEndpoints X beta (1 / Real.sqrt Q) component).2 -
      (componentEndpoints X beta (1 / Real.sqrt Q) component).1 ≤
        |beta| * X * Real.sqrt Q := by
  have hs : 1 ≤ Real.sqrt Q := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hQ
  have hspos : 0 < Real.sqrt Q := by linarith
  have hepos : 0 < 1 / Real.sqrt Q := by positivity
  have heone : 1 / Real.sqrt Q ≤ 1 := (div_le_one hspos).2 hs
  have hA : 0 ≤ |beta| * X := mul_nonneg (abs_nonneg _) hX
  have hlo : (1 / Real.sqrt Q) * |beta| * X ≤ |beta| * X := by
    have hh := mul_le_mul_of_nonneg_right heone hA
    nlinarith
  have hhi : |beta| * X ≤ |beta| * X / (1 / Real.sqrt Q) := by
    apply (le_div_iff₀ hepos).2
    have hh := mul_le_mul_of_nonneg_left heone hA
    nlinarith
  rw [componentEndpoints_sub_eq_outerUpper_sub_outerLower]
  unfold outerUpper outerLower
  constructor
  · linarith
  · have hn : 0 ≤ (1 / Real.sqrt Q) * |beta| * X := by positivity
    have heq : |beta| * X / (1 / Real.sqrt Q) = |beta| * X * Real.sqrt Q := by
      field_simp
    rw [heq]
    linarith

theorem canonical_aperture_bounds
    {X reserve : ℝ} (hX : 1 ≤ X) (hr0 : 0 ≤ reserve)
    (hr1 : reserve ≤ 1 / 1200) :
    (1 / 2 : ℝ) * Real.rpow X (2 / 15 : ℝ) ≤
      (1 / 2 : ℝ) * Real.rpow X (2 / 15 + reserve) ∧
    (1 / 2 : ℝ) * Real.rpow X (2 / 15 + reserve) ≤
      (1 / 2 : ℝ) * Real.rpow X (2 / 15 + 1 / 1200 : ℝ) := by
  constructor <;> apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  · exact Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  · exact Real.rpow_le_rpow_of_exponent_le hX (by linarith)

theorem canonical_truncation_le_X
    {X q Q lambda : ℝ} (hX : 1 ≤ X) (hq : 1 ≤ q) (hQ : 1 ≤ Q)
    (hlambda : 0 ≤ lambda) (hcap : lambda ≤ 1 / (q * Q)) :
    lambda * Real.rpow X (23 / 24 : ℝ) ≤ X := by
  have hqQ : 1 ≤ q * Q := one_le_mul_of_one_le_of_one_le hq hQ
  have hqQpos : 0 < q * Q := by linarith
  have hlone : lambda ≤ 1 := hcap.trans ((div_le_one hqQpos).2 hqQ)
  have hpow : Real.rpow X (23 / 24 : ℝ) ≤ X := by
    simpa only [Real.rpow_one] using!
      Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (23 / 24 : ℝ) ≤ 1)
  calc
    _ ≤ 1 * X := mul_le_mul hlone hpow
      (Real.rpow_nonneg (by linarith) _) (by norm_num)
    _ = X := one_mul X

end
end MRTDynamicD12CanonicalElementary

#print axioms MRTDynamicD12CanonicalElementary.canonical_component_length_bounds
#print axioms MRTDynamicD12CanonicalElementary.canonical_aperture_bounds
#print axioms MRTDynamicD12CanonicalElementary.canonical_truncation_le_X
