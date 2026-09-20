import FordWEnvelopeScalar

open FordWEnvelopeScalar

namespace FordEnvelopeRescale
noncomputable section

theorem min_max_rescale {j : ℕ} {lambda : ℝ} (hlambda : 0 < lambda) :
    min (mu2 * (j : ℝ))
        (max 0 (max (lambda - (1 - mu2) * (j : ℝ))
          ((1 - mu1) * (j : ℝ) - lambda))) =
      lambda * envelope ((j : ℝ) / lambda) := by
  unfold envelope
  rw [mul_min_of_nonneg _ _ hlambda.le,
    mul_max_of_nonneg _ _ hlambda.le, mul_max_of_nonneg _ _ hlambda.le]
  have hmul0 : lambda * (0 : ℝ) = 0 := by ring
  have hfirst : lambda * (mu2 * ((j : ℝ) / lambda)) = mu2 * (j : ℝ) := by
    field_simp
  have hsecond :
      lambda * (1 - (1 - mu2) * ((j : ℝ) / lambda)) =
        lambda - (1 - mu2) * (j : ℝ) := by
    field_simp
  have hthird :
      lambda * ((1 - mu1) * ((j : ℝ) / lambda) - 1) =
        (1 - mu1) * (j : ℝ) - lambda := by
    field_simp
  rw [hfirst, hmul0, hsecond, hthird]

end
end FordEnvelopeRescale

#print axioms FordEnvelopeRescale.min_max_rescale
