import MRTEquation81AveragingBilinear
import MRTEquation81Schur

/-!
# MRT equation (81)

This closes the averaging/Schur step from the literal Cauchy envelope.  The
external citation [23, Theorem 5.2] is not an axiom: the needed Schur estimate
was proved from Tonelli and `2ab ≤ a²+b²` in `MRTSchurTest`.
-/

namespace MAPMRTEquation81

open MeasureTheory
open MAPMRTEquation81AveragingBilinear MAPMRTEquation81Schur

noncomputable section

/-- Equation (81), in multiplication-only `ENNReal` form.  Writing
`A_R(t)=∫_{t-R}^{t+R}F`, this says

`(2R)² B_R(F) ≤ 18(4R) ∫ A_R²`.

Thus division by the box mass gives the manuscript scale `O(R⁻¹)∫A_R²`.
The finiteness hypothesis is automatic for the compactly supported continuous
Dirichlet-polynomial amplitude used in the source, and is stated explicitly at
this analytic boundary. -/
theorem equation81_averaging_schur
    {R : ℝ} {F : ℝ → ENNReal} (hR : 0 < R) (hF : Measurable F)
    (hAfin : ∀ x, equation81Average R F x ≠ ⊤) :
    (ENNReal.ofReal (2 * R)) ^ 2 * equation81Bilinear R F ≤
      18 * ENNReal.ofReal (4 * R) *
        (∫⁻ x : ℝ, (equation81Average R F x) ^ 2) := by
  let A : ℝ → NNReal := fun x ↦ (equation81Average R F x).toNNReal
  have hAmeas : Measurable fun x ↦ (A x : ENNReal) := by
    have hto : Measurable fun x ↦ (equation81Average R F x).toNNReal :=
      (measurable_equation81Average hF).ennreal_toNNReal
    have hcoe : Measurable fun x ↦ ((A x : NNReal) : ENNReal) :=
      hto.coe_nnreal_ennreal
    exact hcoe
  have hschur := equation81_kernel_schur (A := A) hR hAmeas
  have hschur' :
      equation81Bilinear R (equation81Average R F) ≤
        2 * ENNReal.ofReal (4 * R) *
          (∫⁻ x : ℝ, (equation81Average R F x) ^ 2) := by
    unfold equation81Bilinear
    simpa only [A, ENNReal.coe_toNNReal (hAfin _)] using hschur
  calc
    (ENNReal.ofReal (2 * R)) ^ 2 * equation81Bilinear R F ≤
        9 * equation81Bilinear R (equation81Average R F) :=
      equation81_bilinear_averaging hR hF
    _ ≤ 9 * (2 * ENNReal.ofReal (4 * R) *
        (∫⁻ x : ℝ, (equation81Average R F x) ^ 2)) :=
      mul_le_mul_left' hschur' 9
    _ = 18 * ENNReal.ofReal (4 * R) *
        (∫⁻ x : ℝ, (equation81Average R F x) ^ 2) := by ring

#print axioms equation81_averaging_schur

end
end MAPMRTEquation81
