import FordBilinearAssembly
import FordPowerBox
open scoped BigOperators
noncomputable section
namespace FordBilinearBox

/-- The actual polynomial bilinear estimate on the full literal frequency box. -/
theorem polynomial_bilinear_box {B : Type*} [Fintype B]
    (r k M s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (gamma : Fin k → ℝ) (bval : B → ℝ) :
    ∃ eps : B → ℂ, (∀ b, ‖eps b‖ = 1) ∧
      ‖∑ b : B, ∑ a : Fin M,
        FordPolynomialPhase.e (∑ j : Fin k,
          gamma j * bval b ^ (j.val + 1) *
            ((a.val + 1 : ℕ) : ℝ) ^ (j.val + 1))‖ ^ (r * (2 * s)) ≤
      (Fintype.card B : ℝ) ^ ((r - 1) * (2 * s)) *
        ((M : ℝ) ^ (r * (2 * s - 2)) *
          (MAPFordCompleteSystemMoment.completeMoment r k M : ℝ) *
            ∑ c ∈ FordPowerBox.coordinateBox r k M, ‖∑ b : B, eps b *
              FordPolynomialPhase.e (∑ j : Fin k,
                gamma j * bval b ^ (j.val + 1) * (c j : ℝ))‖ ^ (2 * s)) := by
  exact FordBilinearAssembly.polynomial_bilinear_holder r k M s hr hs gamma bval
    (FordPowerBox.coordinateBox r k M) (FordPowerBox.powerMap_mem_coordinateBox hr)

end FordBilinearBox
#print axioms FordBilinearBox.polynomial_bilinear_box
