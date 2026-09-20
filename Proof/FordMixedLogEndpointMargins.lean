import FordMixedLogBounds

noncomputable section
namespace FordMixedLogEndpointMargins

open FordMixedReciprocalIntegral FordMixedKernelBounds FordMixedLogBounds

/-- The scalar coefficient carried by the tail shifts. -/
def endpointCoeff (hs : List ℝ) : ℝ :=
  riseCoeff 1 hs * shiftProd hs

/-- The signed logarithmic phase increment at a positive base. -/
def endpointIncrement (t : ℝ) (hs : List ℝ) (y : ℝ) : ℝ :=
  t * signedMixedDiff (1 :: hs) y

lemma endpoint_bounds
    (hs : List ℝ) {t x H : ℝ} (ht : 0 ≤ t) (hx : 0 < x) (hH : 0 ≤ H)
    (hsteps : ∀ q ∈ hs, 0 ≤ q) :
    t * endpointCoeff hs /
        (x + H + 1 + shiftSum hs) ^ (hs.length + 1) ≤
      endpointIncrement t hs (x + H) ∧
      endpointIncrement t hs x ≤
        t * endpointCoeff hs / x ^ (hs.length + 1) := by
  have hlow := signedMixedDiff_bounds (hs := hs) (x := x + H) (h := 1)
    (by linarith : 0 < x + H) (by norm_num : (0 : ℝ) ≤ 1) hsteps
  have hupper := signedMixedDiff_bounds (hs := hs) (x := x) (h := 1)
    hx (by norm_num : (0 : ℝ) ≤ 1) hsteps
  have hxp : 0 < x + H := by linarith
  have hlow' := mul_le_mul_of_nonneg_left hlow.1 ht
  have hupper' := mul_le_mul_of_nonneg_left hupper.2 ht
  constructor
  · convert hlow' using 1 <;> simp [endpointIncrement, endpointCoeff,
      shiftSum, shiftProd] <;> ring
  · convert hupper' using 1 <;> simp [endpointIncrement, endpointCoeff,
      shiftSum, shiftProd] <;> ring

/-- Numeric endpoint margins sufficient for the full-period Kusmin bound. -/
theorem endpoint_margin_pair
    (hs : List ℝ) {t x H δ : ℝ}
    (ht : 0 ≤ t) (hx : 0 < x) (hH : 0 ≤ H)
    (hsteps : ∀ q ∈ hs, 0 ≤ q) (hδ : 0 < δ)
    (hδlo : δ ≤ t * endpointCoeff hs /
        (x + H + 1 + shiftSum hs) ^ (hs.length + 1))
    (hδhi : t * endpointCoeff hs / x ^ (hs.length + 1) ≤
        2 * Real.pi - δ) :
    δ ≤ endpointIncrement t hs (x + H) ∧
      endpointIncrement t hs x ≤ 2 * Real.pi - δ := by
  have hb := endpoint_bounds hs ht hx hH hsteps
  exact ⟨hδlo.trans hb.1, hb.2.trans hδhi⟩

end FordMixedLogEndpointMargins

#print axioms FordMixedLogEndpointMargins.endpoint_bounds
#print axioms FordMixedLogEndpointMargins.endpoint_margin_pair
