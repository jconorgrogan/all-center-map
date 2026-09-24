import Mathlib

/-!
# All-center MAP at the `2/15` scale

This is the statement surface for Theorem 1.1.
The Challenge hole is the Comparator protocol statement.
The Solution supplies the proved endpoint.
-/

namespace AllCenterMAP

open MeasureTheory Metric Set
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- The finite von Mangoldt exponential sum on `X < n <= 2X`. -/
def primeExponentialSum (X : ℝ) (alpha : UnitAddCircle) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
    (ArithmeticFunction.vonMangoldt n : ℂ) * fourier (n : ℤ) alpha

/-- Reduced rational major arcs with logarithmic denominator and width cutoffs. -/
def majorArcs (X : ℝ) (B D : ℕ) : Set UnitAddCircle :=
  {alpha | ∃ q a : ℕ,
    1 ≤ q ∧
    (q : ℝ) ≤ (Real.log X) ^ B ∧
    a < q ∧
    a.Coprime q ∧
    dist alpha ((↑((a : ℝ) / (q : ℝ)) : UnitAddCircle)) ≤
      (Real.log X) ^ D / X}

/-- The complement of the logarithmic major arcs. -/
def minorArcs (X : ℝ) (B D : ℕ) : Set UnitAddCircle :=
  (majorArcs X B D)ᶜ

/-- The closed circle arc of radius `1 / (2H)` centered at `center`. -/
def centeredArc (H : ℝ) (center : UnitAddCircle) : Set UnitAddCircle :=
  closedBall center ((2 * H)⁻¹)

/--
For every requested logarithmic saving and aperture reserve, fixed positive
integer cutoffs control the normalized Haar mass of the minor-arc part of the
von Mangoldt polynomial on every circle arc at the `2/15` scale.

The quantifier order is part of the claim: `B`, `D`, `C`, and `X0` are chosen
before `X`, `H`, and `center`.
-/
theorem map_two_fifteenths :
    ∀ A epsilon : ℝ, 0 < A → 0 < epsilon →
      ∃ B D : ℕ, 1 ≤ B ∧ 1 ≤ D ∧
        ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
          ∀ X H : ℝ, X0 ≤ X →
            Real.rpow X (2 / 15 + epsilon) ≤ H →
            ∀ center : UnitAddCircle,
              (∫ alpha in centeredArc H center ∩ minorArcs X B D,
                  ‖primeExponentialSum X alpha‖ ^ 2
                    ∂(@AddCircle.haarAddCircle 1 ⟨Real.zero_lt_one⟩)) ≤
                C * X * Real.rpow (Real.log X) (-A) := by
  sorry

end

end AllCenterMAP

