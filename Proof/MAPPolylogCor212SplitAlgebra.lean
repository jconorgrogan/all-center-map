import Mathlib

/-!
# Scalar normalization for the literal Corollary 2.12 source

This file contains only the small nonnegative algebra which previously made the
analytic source module expensive to elaborate.  In particular `E` may contain
the literal `card / cutoff^2` contribution and `P` the principal annular decay;
neither is altered here.
-/

namespace MAPPolylogCor212SplitAlgebra

noncomputable section

/-- Absorb the inner `L^405` contribution and the outer pointwise `L^8`
loss into one global `L^413` multiplier.  The error and principal terms retain
the same global multiplier. -/
theorem normalize_literal_inner_outer
    {C K M L A E P F : ℝ}
    (hC : 0 ≤ C) (hK : 0 < K) (hM : 0 < M)
    (hL : 1 ≤ L) (hA : 0 ≤ A) (hE : 0 ≤ E) (hP : 0 ≤ P)
    (hF : F ≤ K * M * A * L ^ 405) :
    125 * (C * L ^ 2) ^ 4 * (F + E + P) ≤
      (125 * C ^ 4 * (K * M + 1)) * L ^ 413 * (A + E + P) := by
  let D : ℝ := K * M + 1
  have hD : 1 ≤ D := by dsimp [D]; nlinarith [mul_pos hK hM]
  have hL405 : 1 ≤ L ^ 405 := one_le_pow₀ hL
  have houter : 0 ≤ 125 * (C * L ^ 2) ^ 4 := by positivity
  have hAterm : K * M * A * L ^ 405 ≤ D * L ^ 405 * A := by
    have hcoef : K * M ≤ D := by dsimp [D]; linarith
    calc
      K * M * A * L ^ 405 = (K * M) * L ^ 405 * A := by ring
      _ ≤ D * L ^ 405 * A := by gcongr
  have hEterm : E ≤ D * L ^ 405 * E := by
    calc
      E = 1 * 1 * E := by ring
      _ ≤ D * L ^ 405 * E := by gcongr
  have hPterm : P ≤ D * L ^ 405 * P := by
    calc
      P = 1 * 1 * P := by ring
      _ ≤ D * L ^ 405 * P := by gcongr
  have hinner : F + E + P ≤ D * L ^ 405 * (A + E + P) := by
    calc
      F + E + P ≤ K * M * A * L ^ 405 + E + P :=
        add_le_add (add_le_add hF le_rfl) le_rfl
      _ ≤ D * L ^ 405 * A + D * L ^ 405 * E +
          D * L ^ 405 * P :=
        add_le_add (add_le_add hAterm hEterm) hPterm
      _ = D * L ^ 405 * (A + E + P) := by ring
  calc
    125 * (C * L ^ 2) ^ 4 * (F + E + P) ≤
        125 * (C * L ^ 2) ^ 4 *
          (D * L ^ 405 * (A + E + P)) :=
      mul_le_mul_of_nonneg_left hinner houter
    _ = (125 * C ^ 4 * (K * M + 1)) * L ^ 413 *
          (A + E + P) := by
      dsimp [D]
      rw [show (C * L ^ 2) ^ 4 = C ^ 4 * L ^ 8 by ring]
      have hpow : L ^ 8 * L ^ 405 = L ^ 413 := by
        rw [← pow_add]
      calc
        125 * (C ^ 4 * L ^ 8) *
            ((K * M + 1) * L ^ 405 * (A + E + P)) =
          125 * C ^ 4 * (K * M + 1) *
            (L ^ 8 * L ^ 405) * (A + E + P) := by ring
        _ = _ := by rw [hpow]

end
end MAPPolylogCor212SplitAlgebra

#print axioms MAPPolylogCor212SplitAlgebra.normalize_literal_inner_outer
