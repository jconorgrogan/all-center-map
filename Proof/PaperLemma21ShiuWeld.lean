import NonzeroDeterminantSectorGate
import PaperLemma21IntegrationScaffold

/-!
# Exact Shiu-to-Lemma-2.1 weld

This module connects the globally aggregated positive and negative determinant
sectors to the literal surface of manuscript Lemma 2.1.  It leaves precisely
the specialized dyadic Shiu progression theorem as its analytic premise.
-/

namespace MAPMixedMeanCompletion

open ShiuFoundation MixedMeanMajorantWeld MAPNonzeroSectorGate

/-- Once the specialized dyadic Shiu theorem is supplied, the manuscript's
literal mixed-mean Lemma 2.1 follows with no further analytic premises. -/
theorem paperMixedMeanLemma21_of_dyadicTauSquareShiuTarget
    (hShiu : DyadicTauSquareShiuTarget) (c : ℝ) (a k : ℕ) :
    PaperMixedMeanLemma21 c a k := by
  apply paperMixedMeanLemma21_of_nonzeroTauSurvivorMass_bound c a k
  intro hc hk
  have hraw :=
    signedFrequency_tauMass_raw_bound hShiu c k hc hk
  simpa [nonzeroTauSurvivorMass] using hraw

end MAPMixedMeanCompletion

#print axioms MAPMixedMeanCompletion.paperMixedMeanLemma21_of_dyadicTauSquareShiuTarget
