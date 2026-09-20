import APFoundation

/-!
# First external analytic input in the MRT major-arc proof

This is a source-faithful block form of uniform Siegel--Walfisz for `psi`.
It is strictly earlier than the rational additive-character estimate and the
small-`beta` prime-polynomial estimate: both still require deterministic
residue decomposition, the Ramanujan sum, and Abel summation.

The constants are existential.  This faithfully preserves the ineffectivity
which MRT explicitly attributes to Siegel's theorem; Lean's proposition does
not claim an algorithm for computing `C` or `X0`.
-/

namespace MAPPointwiseMajorArc

open Set

noncomputable section

/-- Uniform Siegel--Walfisz on one dyadic block, in the exact progression-psi
normalization already used by `APFoundation`. -/
def UniformSiegelWalfiszPsi : Prop :=
  ∀ A B : ℕ, ∃ C X0 : ℝ,
    0 < C ∧ 2 ≤ X0 ∧
      ∀ X : ℝ, X0 ≤ X →
      ∀ q a : ℕ,
        1 ≤ q →
        (q : ℝ) ≤ (Real.log X) ^ B →
        a < q → a.Coprime q →
      ∀ t : ℝ, t ∈ Set.Icc X (2 * X) →
        |APFoundation.progressionPsi t q a -
            t / (q.totient : ℝ)| ≤
          C * X / (Real.log X) ^ A

/-- Exact elimination rule for one requested pair of logarithmic exponents.
This theorem only unpacks the quantifier order; it adds no analytic content. -/
theorem UniformSiegelWalfiszPsi.specialize
    (hSW : UniformSiegelWalfiszPsi) (A B : ℕ) :
    ∃ C X0 : ℝ,
      0 < C ∧ 2 ≤ X0 ∧
        ∀ X : ℝ, X0 ≤ X →
        ∀ q a : ℕ,
          1 ≤ q →
          (q : ℝ) ≤ (Real.log X) ^ B →
          a < q → a.Coprime q →
        ∀ t : ℝ, t ∈ Set.Icc X (2 * X) →
          |APFoundation.progressionPsi t q a -
              t / (q.totient : ℝ)| ≤
            C * X / (Real.log X) ^ A :=
  hSW A B

end

end MAPPointwiseMajorArc

