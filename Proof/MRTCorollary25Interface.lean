import FarAnnulusMRTConnector

/-!
# Exact imported interface for MRT Corollary 2.5

Source: K. Matomäki, M. Radziwiłł, T. Tao,
*Correlations of the von Mangoldt and divisor functions I: Long shift ranges*,
Proc. London Math. Soc. 118 (2019), Corollary 2.5, printed pp. 17--18
and lines 884--916 of the pinned text extraction `references/mrt_2019/mrt.txt`.

This module does not assert the published theorem as a Lean axiom.  It gives
its exact typed strength, so every internal MAP bridge can take precisely this
published result as a premise rather than assuming a downstream far-annulus
estimate.
-/

namespace MAPMRTCorollary25

open scoped BigOperators
open MixedMeanFrontend

noncomputable section

/-- Metadata for the exact external theorem being imported. -/
def sourceTitle : String :=
  "Matomaki--Radziwill--Tao (2019), Corollary 2.5 (Truncating a Dirichlet series)"

/-- The finite Dirichlet polynomial representing `D[f](1/2+it)` under the
support hypothesis `supp f ⊆ [X/C,CX]`.  The upper endpoint is rounded up only
to make the sum a literal `Finset`; the support hypothesis makes that choice
harmless. -/
def halfLineDirichletPolynomial
    (X C : ℝ) (f : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (Nat.ceil (C * X)),
    (f n / (Real.sqrt (n : ℝ) : ℂ)) * mellinPhase n t

/-- Restriction of an arithmetic function to the real interval `[X1,X2]`.
This matches the closed interval in the published Corollary 2.5. -/
def intervalCutoff (X1 X2 : ℝ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  if X1 ≤ (n : ℝ) ∧ (n : ℝ) ≤ X2 then f n else 0

/-- Literal support condition in `[X/C,CX]`. -/
def SupportedNear (X C : ℝ) (f : ℕ → ℂ) : Prop :=
  ∀ n : ℕ, (n : ℝ) < X / C ∨ C * X < (n : ℝ) → f n = 0

/-- Exact theorem-shaped premise for MRT Corollary 2.5.

The constant `K` depends only on `C`; it is uniform in `X,T,X1,X2,t,f` and in
the displayed pointwise coefficient bound `B`.  The arbitrary complex-valued
`f` includes character twists, so no extra character hypothesis is needed. -/
def MRTCorollary25 : Prop :=
  ∀ C : ℝ, 1 < C →
    ∃ K : ℝ, 0 < K ∧
      ∀ (X T X1 X2 t B : ℝ) (f : ℕ → ℂ),
        1 ≤ X → 1 ≤ T → 0 ≤ B →
        SupportedNear X C f →
        (∀ n : ℕ, ‖f n‖ ≤ B) →
        ‖halfLineDirichletPolynomial X C (intervalCutoff X1 X2 f) t‖ ≤
          K * ((∫ u in (-T)..T,
              ‖halfLineDirichletPolynomial X C f (t + u)‖ /
                (1 + |u|)) +
            B * Real.sqrt X * Real.log (2 + T) / T)

/-- Named application theorem.  This is only elimination of the exact
published premise above; it introduces no estimate beyond Corollary 2.5. -/
theorem cutoffRemoval_of_MRTCorollary25
    (hMRT : MRTCorollary25)
    {C : ℝ} (hC : 1 < C) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (X T X1 X2 t B : ℝ) (f : ℕ → ℂ),
        1 ≤ X → 1 ≤ T → 0 ≤ B →
        SupportedNear X C f →
        (∀ n : ℕ, ‖f n‖ ≤ B) →
        ‖halfLineDirichletPolynomial X C (intervalCutoff X1 X2 f) t‖ ≤
          K * ((∫ u in (-T)..T,
              ‖halfLineDirichletPolynomial X C f (t + u)‖ /
                (1 + |u|)) +
            B * Real.sqrt X * Real.log (2 + T) / T) :=
  hMRT C hC

/-- The deterministic exponent arithmetic used in MRT Section 6 after taking
`Tcut = lambda * X^(1-eps/10)`: if the divisor bound supplies
`B ≤ X^(eps/10)`, then the bare Perron error is bounded by the displayed
`X^(eps/5)` numerator.  Logarithms and the positive `lambda` denominator are
kept outside this purely multiplicative identity. -/
theorem cutoffError_exponent_identity
    (X eps : ℝ) (hX : 0 < X) :
    X ^ (eps / 10) * Real.sqrt X /
        X ^ (1 - eps / 10) =
      X ^ (-1 / 2 + eps / 5) := by
  calc
    X ^ (eps / 10) * Real.sqrt X / X ^ (1 - eps / 10) =
        X ^ (eps / 10 + 1 / 2) / X ^ (1 - eps / 10) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_add hX]
    _ = X ^ ((eps / 10 + 1 / 2) - (1 - eps / 10)) := by
      exact (Real.rpow_sub hX (eps / 10 + 1 / 2) (1 - eps / 10)).symm
    _ = X ^ (-1 / 2 + eps / 5) := by
      congr 1
      ring

end
end MAPMRTCorollary25

#print axioms MAPMRTCorollary25.cutoffRemoval_of_MRTCorollary25
#print axioms MAPMRTCorollary25.cutoffError_exponent_identity
