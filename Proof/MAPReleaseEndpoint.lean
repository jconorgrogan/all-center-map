import FordAllCenterMAP

noncomputable section
namespace MAPReleaseEndpoint
open MeasureTheory Metric Set PrimePairEndpoints

/-- Literal positive-cutoff all-center MAP statement, without source premises.
This declaration is the proof-facing release boundary. -/
theorem zero_argument_map_two_fifteenths :
    ∀ A epsilon : ℝ, 0 < A → 0 < epsilon →
      ∃ B D : ℕ, 1 ≤ B ∧ 1 ≤ D ∧
        ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
          ∀ X H : ℝ, X0 ≤ X →
            Real.rpow X (2 / 15 + epsilon) ≤ H →
            ∀ center : UnitAddCircle,
              (∫ alpha in centeredArc H center ∩ minorArcs X B D,
                  ‖primeExponentialSum X alpha‖ ^ 2
                    ∂AddCircle.haarAddCircle) ≤
                C * X * Real.rpow (Real.log X) (-A) :=
  FordAllCenterMAP.positiveCutoffAllCenterLocalMAP

end MAPReleaseEndpoint
#print axioms MAPReleaseEndpoint.zero_argument_map_two_fifteenths
