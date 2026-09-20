import FullMAP

/-!
# Literal certification endpoint for the all-center MAP package

`FullMAP.Q4PlusFamily` records only the upper half of the manuscript's Q4
asymptotic.  This module exposes the two-sided statement that must actually be
proved and shows that it projects to the older public endpoint.

No analytic estimate is assumed or proved here.  The purpose of this file is
to ensure that a future headline proof has the correct theorem surface.
-/

namespace PrimePairEndpoints

/-- The two-sided Q4 estimate asserted by the paper. -/
def Q4TwoSidedFamily : Prop :=
  ∀ A ε : ℝ, 0 < A → 0 < ε →
    ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
      ∀ X H h₀ : ℝ, X₀ ≤ X →
        LegalParameters ε X H h₀ →
        |q4Quantity X H h₀ - X ^ 2 * singularSquareMain H h₀| ≤
          C * H * X ^ 2 * Real.rpow (Real.log X) (-A)

/-- The corrected four-component endpoint that full certification must
inhabit.  In particular it does not weaken the paper's Q4 equality to a
one-sided upper estimate. -/
def CertifiedMAPEndpoint : Prop :=
  AllCenterLocalMAP ∧ VarianceFamily ∧
    Q4TwoSidedFamily ∧ DensityOnePrimePairFamily

theorem q4TwoSidedFamily_implies_q4PlusFamily
    (hQ4 : Q4TwoSidedFamily) : Q4PlusFamily := by
  intro A ε hA hε
  obtain ⟨C, X₀, hC, hX₀, hbound⟩ := hQ4 A ε hA hε
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro X H h₀ hX hlegal
  have habs := hbound X H h₀ hX hlegal
  have hupper :
      q4Quantity X H h₀ - X ^ 2 * singularSquareMain H h₀ ≤
        C * H * X ^ 2 * Real.rpow (Real.log X) (-A) :=
    (abs_le.mp habs).2
  linarith

/-- Final assembly after the three genuine analytic obligations have been
proved.  Density one is not a fourth analytic input: it is the already checked
finite Chebyshev consequence of the variance theorem. -/
theorem certifiedMAPEndpoint_of_map_variance_q4TwoSided
    (hMAP : AllCenterLocalMAP)
    (hVariance : VarianceFamily)
    (hQ4 : Q4TwoSidedFamily) : CertifiedMAPEndpoint := by
  exact ⟨hMAP, hVariance, hQ4,
    varianceFamily_implies_densityOne hVariance⟩

/-- Compatibility with the package's older, weaker endpoint. -/
theorem certifiedMAPEndpoint_implies_fullUnconditionalMAPEndpoint
    (h : CertifiedMAPEndpoint) : FullUnconditionalMAPEndpoint := by
  rcases h with ⟨hMAP, hVariance, hQ4, hDensity⟩
  exact ⟨hMAP, hVariance,
    q4TwoSidedFamily_implies_q4PlusFamily hQ4, hDensity⟩

end PrimePairEndpoints
