import JutilaCollarA5Budget
import APRegularNearCGLJutilaFineMeshRoute

/-!
# Weakest live Jutila collar source

The live MAP endpoint never needs Jutila's ungapped count of every zero.
It needs only the regular part of one primitive inducer after Appendix B has
supplied a gap.  This module exposes the remaining p.53 selected-system
estimate at exactly that strength and passes it through the certified A.5
source-box and exponent weld.

The published full Jutila theorem remains available as a compatibility route;
it is not a premise of this module.
-/

namespace MAPJutilaGappedCollarSourceAdapter

open Filter
open scoped BigOperators
open DirichletZeros MAPAPWeightedZeroMassIntegration
open MAPJutilaCollarMeshCutoff MAPJutilaCollarA5Budget

noncomputable section

/-- Multiplicity-weighted regular cumulative divisor of one primitive
character.  The extra `4/5` predicate makes this definition literally the
cumulative support used by the live regular-near mass. -/
def primitiveRegularCumulativeCount {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma T : ℝ) : ℕ :=
  ∑ rho ∈ (zeroSupport chi 0 T).filter (fun rho =>
      (4 / 5 < rho.re ∧
        ¬ (chi ≠ 1 ∧ chi ^ 2 = 1 ∧ rho.im = 0)) ∧
      sigma ≤ rho.re),
    zeroMultiplicity chi 0 T rho

/-- The exact source surface left after the deterministic Jutila work.

`selected` is the larger parity class after equation (3.1), with the harmless
factor two absorbed into its normalization.  The first inequality is the exact
source-box aggregation interface: A.5 certifies the cap on each literal box,
while identifying the finite occupied-box system with Jutila's selected system
still belongs to this source-facing premise.  The second is precisely the
remaining p.53 selected-system detector/correlation bound after the detector
logarithms have spent `4/560` in the exponent.

The gap and logarithmic absorption hypotheses are included because this is a
live-branch source, not a restatement of the stronger ungapped Theorem 1. -/
def JutilaGappedCollarP53Eventually : Prop :=
  ∃ Cp R₀ : ℝ, 0 < Cp ∧ 2 ≤ R₀ ∧
    ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
      (T sigma omega : ℝ),
      chi.IsPrimitive → 1 ≤ T →
      279 / 280 ≤ sigma → sigma ≤ 1 →
      0 ≤ omega → omega ≤ 1 - sigma →
      R₀ ≤ (q : ℝ) * T →
      Real.log ((q : ℝ) * T) ≤
        Real.rpow ((q : ℝ) * T) (a5FiberGapBudget * omega) →
      (∀ rho : ℂ,
        rho ∈ (zeroSupport chi 0 T).filter (fun rho =>
          (4 / 5 < rho.re ∧
            ¬ (chi ≠ 1 ∧ chi ^ 2 = 1 ∧ rho.im = 0)) ∧
          sigma ≤ rho.re) →
        rho.re ≤ 1 - omega) →
      ∃ selected : ℝ, 0 ≤ selected ∧
        (primitiveRegularCumulativeCount chi sigma T : ℝ) ≤
          153 * Real.log ((q : ℝ) * T) * selected ∧
        selected ≤ Cp * Real.rpow ((q : ℝ) * T)
          ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
            (1 - sigma))

/-- The gapped p.53 source gives the exact `21/10` count required at one
live collar point.  All source-box, multiplicity, parity, logarithm, and
exponent bookkeeping is discharged here. -/
theorem primitiveRegularCumulativeCount_le_of_gappedP53
    (hsource : JutilaGappedCollarP53Eventually) :
    ∃ C R₀ : ℝ, 0 < C ∧ 2 ≤ R₀ ∧
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
        (T sigma omega : ℝ),
        chi.IsPrimitive → 1 ≤ T →
        279 / 280 ≤ sigma → sigma ≤ 1 →
        0 ≤ omega → omega ≤ 1 - sigma →
        R₀ ≤ (q : ℝ) * T →
        Real.log ((q : ℝ) * T) ≤
          Real.rpow ((q : ℝ) * T) (a5FiberGapBudget * omega) →
        (∀ rho : ℂ,
          rho ∈ (zeroSupport chi 0 T).filter (fun rho =>
            (4 / 5 < rho.re ∧
              ¬ (chi ≠ 1 ∧ chi ^ 2 = 1 ∧ rho.im = 0)) ∧
            sigma ≤ rho.re) →
          rho.re ≤ 1 - omega) →
        (primitiveRegularCumulativeCount chi sigma T : ℝ) ≤
          C * Real.rpow ((q : ℝ) * T)
            ((21 / 10) * (1 - sigma)) := by
  obtain ⟨Cp, R₀, hCp, hR₀, hp53⟩ := hsource
  refine ⟨153 * Cp, R₀, by positivity, hR₀, ?_⟩
  intro q _inst chi T sigma omega hprim hT hsigmaLow hsigmaHigh
    homega hgap hscale hlog hregularGap
  obtain ⟨selected, hselected0, hcompress, hselected⟩ :=
    hp53 q chi T sigma omega hprim hT hsigmaLow hsigmaHigh
      homega hgap hscale hlog hregularGap
  have hD : 1 < (q : ℝ) * T := lt_of_lt_of_le (by norm_num) (hR₀.trans hscale)
  exact total_le_final_density_of_A5_and_p53
    hD hsigmaHigh hgap hCp.le hselected0 hlog hcompress hselected

end

end MAPJutilaGappedCollarSourceAdapter

#print axioms MAPJutilaGappedCollarSourceAdapter.primitiveRegularCumulativeCount_le_of_gappedP53
