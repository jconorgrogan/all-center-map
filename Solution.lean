import MAPReleaseEndpoint

/-!
# Solution surface for the all-center MAP endpoint

This theorem is supplied by the verified zero-argument endpoint in Proof/.
The release uses the exact proven Lean v4.30.0-rc2 / Mathlib pin.
-/

namespace AllCenterMAP

open MeasureTheory Metric Set
open scoped BigOperators ArithmeticFunction

noncomputable section

def primeExponentialSum (X : ℝ) (alpha : UnitAddCircle) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
    (ArithmeticFunction.vonMangoldt n : ℂ) * fourier (n : ℤ) alpha

def majorArcs (X : ℝ) (B D : ℕ) : Set UnitAddCircle :=
  {alpha | ∃ q a : ℕ,
    1 ≤ q ∧
    (q : ℝ) ≤ (Real.log X) ^ B ∧
    a < q ∧
    a.Coprime q ∧
    dist alpha ((↑((a : ℝ) / (q : ℝ)) : UnitAddCircle)) ≤
      (Real.log X) ^ D / X}

def minorArcs (X : ℝ) (B D : ℕ) : Set UnitAddCircle :=
  (majorArcs X B D)ᶜ

def centeredArc (H : ℝ) (center : UnitAddCircle) : Set UnitAddCircle :=
  closedBall center ((2 * H)⁻¹)

theorem map_two_fifteenths :
    ∀ A epsilon : ℝ, 0 < A → 0 < epsilon →
      ∃ B D : ℕ, 1 ≤ B ∧ 1 ≤ D ∧
        ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
          ∀ X H : ℝ, X0 ≤ X →
            Real.rpow X (2 / 15 + epsilon) ≤ H →
            ∀ center : UnitAddCircle,
              (∫ alpha in centeredArc H center ∩ minorArcs X B D,
                  ‖primeExponentialSum X alpha‖ ^ 2
                    ∂AddCircle.haarAddCircle) ≤
                C * X * Real.rpow (Real.log X) (-A) := by
  exact MAPReleaseEndpoint.zero_argument_map_two_fifteenths

end


end AllCenterMAP

