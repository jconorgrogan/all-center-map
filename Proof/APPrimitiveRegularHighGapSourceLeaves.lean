import APPrimitiveRegularHighGapFromFordRaw
import KhaleAppendixBLemma41NaturalScales
import KhaleZetaLogDerivativeSharp

/-!
# Source-opened Khale input for the MAP high-zero gap

This file records the shortest source-faithful route currently available to
`PrimitiveRegularHighGap`.  It deliberately bypasses the full Appendix-B.2
corollary and McCurley's finite-height patch: MAP only needs Khale's
large-height calculation, while Koukoulopoulos and compactness handle its
complement.

The remaining hypotheses are actual source theorems, not renamed MAP
endpoints:

* Ford's explicit Hurwitz-zeta estimate (equation (1.2));
* Khale's finite-selected-set Lemma 4.1;
* the real-axis zeta logarithmic-derivative inequality used in Ford's
  Lemma 3.1.

All specialization to the four ordinates, trigonometric positivity,
exact-height correction, the final Appendix-B arithmetic, and the passage to
the eventual polylogarithmic-conductor gap are proved in imported modules.
-/

namespace MAPAPPrimitiveRegularHighGapSourceLeaves

open MAPKhaleAppendixBSource
open MAPKhaleLemma41PointwiseSource
open MAPKhaleAppendixBLemma41NaturalScales
open MAPKhaleZetaLogDerivativeSharp
open MAPAPRegularNearAppendixBAdapter

noncomputable section

/-- The shortest source-opened constructor for the exact high-gap proposition
consumed by MAP.  In particular, it assumes neither `AppendixBTheoremB1` nor
`AppendixBCorollary104` nor McCurley's theorem. -/
theorem primitiveRegularHighGap_of_pointwise_khale
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hKhale41 : KhaleLemma41FiniteSelectedEstimate)
    (hZeta : FordLemma31ZetaLogDerivativeBound) :
    PrimitiveRegularHighGap :=
  MAPAPPrimitiveRegularHighGapFromFordRaw.primitiveRegularHighGap_of_ford_naturalScales
    hFord
    (appendixBLemma41TrigNaturalScales_of_source hKhale41 hZeta)

/-- MAP-facing constructor requiring normalized-zeta monotonicity only on the
tiny interval actually reached by Appendix B. -/
theorem primitiveRegularHighGap_of_pointwise_khale_nearOne_zeta
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hKhale41 : KhaleLemma41FiniteSelectedEstimate)
    (hZeta : NormalizedRiemannZetaDerivativeNonnegativeNearOne) :
    PrimitiveRegularHighGap :=
  primitiveRegularHighGap_of_pointwise_khale hFord hKhale41
    (fordLemma31ZetaLogDerivativeBound_of_normalized_derivative_nearOne hZeta)

/-- Same MAP-facing constructor with the zeta input opened all the way to the
two literal Dirichlet-series sum--integral inequalities. -/
theorem primitiveRegularHighGap_of_pointwise_khale_sumIntegral_zeta
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hKhale41 : KhaleLemma41FiniteSelectedEstimate)
    (hZeta : MAPKhaleZetaNearOneSourceReduction.NearOneZetaSumIntegralBounds) :
    PrimitiveRegularHighGap :=
  primitiveRegularHighGap_of_pointwise_khale hFord hKhale41
    (fordLemma31ZetaLogDerivativeBound_of_sumIntegral hZeta)

/-- The still smaller Appendix-B-facing seam: only the four literal
large-height rows which MAP uses, together with the elementary real-axis zeta
bound.  This is useful when formalizing Khale's Lemma 4.1 directly at its four
applications rather than in its stronger arbitrary-selected-set form. -/
theorem primitiveRegularHighGap_of_four_khale_rows
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hRows :
      MAPKhaleAppendixBLemma62NaturalScaleWeld.AppendixBLemma62FourNaturalScaleBounds)
    (hZeta :
      MAPKhaleAppendixBLemma62NaturalScaleWeld.AppendixBLemma41ZetaLogDerivativeBound) :
    PrimitiveRegularHighGap :=
  MAPAPPrimitiveRegularHighGapFromFordRaw.primitiveRegularHighGap_of_ford_lemma62
    hFord hRows hZeta

end
end MAPAPPrimitiveRegularHighGapSourceLeaves

#print axioms MAPAPPrimitiveRegularHighGapSourceLeaves.primitiveRegularHighGap_of_pointwise_khale
#print axioms MAPAPPrimitiveRegularHighGapSourceLeaves.primitiveRegularHighGap_of_four_khale_rows
#print axioms MAPAPPrimitiveRegularHighGapSourceLeaves.primitiveRegularHighGap_of_pointwise_khale_nearOne_zeta
#print axioms MAPAPPrimitiveRegularHighGapSourceLeaves.primitiveRegularHighGap_of_pointwise_khale_sumIntegral_zeta
