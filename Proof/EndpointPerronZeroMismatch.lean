import APLiteralTailContract

/-!
# The endpoint-zero/Perron-zero mismatch as an isolated AP source

The literal AP remainder contains one zero term which is not part of either
the left or horizontal contour estimates.  This file names that term, proves
its exact window identity, and states its source-faithful family-square
obligation with the same normalization and quantifier order as
`APExplicitFormulaTailFamilySquare`.

No estimate for this term is asserted here.  In particular, the definition
below does not hide the required analytic bound in a deterministic wrapper.
-/

namespace MAPEndpointPerronZeroMismatch

open MeasureTheory Set
open scoped BigOperators ENNReal
open APFoundation APExplicitFormulaMajorantAdapter
open MAPEndpointRegularizedZeroPrimitive
open PrimitiveTruncatedExplicitFormulaBridge
open MAPAPLiteralTailContract

noncomputable section

variable {q : ℕ} [NeZero q]

/-- The exact zero component occurring in
`literalEndpointRemainderMajorant`: the full closed-rectangle endpoint
primitive at the real endpoint, minus the positive-left-edge Perron residue
sum at the corresponding half integer. -/
def endpointPerronZeroMismatch
    (chi : DirichletCharacter ℂ q) (sigma T t : ℝ) : ℂ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact
    endpointMultiplicityWeightedZeroTerm chi.primitiveCharacter 0 T t -
      multiplicityWeightedPerronZeroSum chi.primitiveCharacter sigma T
        (halfIntegerPoint ⌊t⌋₊)

/-- The named mismatch is literally the zero norm left unevaluated in the
pointwise AP remainder majorant. -/
theorem norm_endpointPerronZeroMismatch_eq_literal_zero_component
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    (sigma T t : ℝ) :
    ‖endpointPerronZeroMismatch chi sigma T t‖ =
      ‖endpointMultiplicityWeightedZeroTerm chi.primitiveCharacter 0 T t -
        multiplicityWeightedPerronZeroSum chi.primitiveCharacter sigma T
          (halfIntegerPoint ⌊t⌋₊)‖ := by
  rfl

/-- Exact endpoint-window identity.  It shows that the unresolved mismatch
has two and only two pieces: the full zero-field integral and the change of
the Perron residue sum between the two half-integer endpoints.  This is an
identity, not an estimate. -/
theorem endpointPerronZeroMismatch_window_eq_integral_sub_perronWindow
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    {sigma T x Y : ℝ}
    (hx : 0 < x) (hxY : 0 < x + Y) :
    endpointPerronZeroMismatch chi sigma T (x + Y) -
        endpointPerronZeroMismatch chi sigma T x =
      (∫ t : ℝ in x..x + Y,
          actualZeroField chi.primitiveCharacter 0 T t) -
        (multiplicityWeightedPerronZeroSum chi.primitiveCharacter sigma T
            (halfIntegerPoint ⌊x + Y⌋₊) -
          multiplicityWeightedPerronZeroSum chi.primitiveCharacter sigma T
            (halfIntegerPoint ⌊x⌋₊)) := by
  have hprimitive :
      endpointMultiplicityWeightedZeroTerm chi.primitiveCharacter 0 T (x + Y) -
          endpointMultiplicityWeightedZeroTerm chi.primitiveCharacter 0 T x =
        ∫ t : ℝ in x..x + Y,
          actualZeroField chi.primitiveCharacter 0 T t := by
    symm
    simpa only [actualZeroField, endpointMultiplicityWeightedZeroTerm] using
      intervalIntegral_finiteZeroField_endpoint
        (DirichletZeros.zeroSupport chi.primitiveCharacter 0 T)
        (DirichletZeros.zeroMultiplicity chi.primitiveCharacter 0 T)
        (fun rho hrho => actualZero_re_nonneg chi.primitiveCharacter hrho)
        hx hxY
  unfold endpointPerronZeroMismatch
  calc
    (endpointMultiplicityWeightedZeroTerm chi.primitiveCharacter 0 T (x + Y) -
          multiplicityWeightedPerronZeroSum chi.primitiveCharacter sigma T
            (halfIntegerPoint ⌊x + Y⌋₊)) -
        (endpointMultiplicityWeightedZeroTerm chi.primitiveCharacter 0 T x -
          multiplicityWeightedPerronZeroSum chi.primitiveCharacter sigma T
            (halfIntegerPoint ⌊x⌋₊)) =
      (endpointMultiplicityWeightedZeroTerm chi.primitiveCharacter 0 T (x + Y) -
          endpointMultiplicityWeightedZeroTerm chi.primitiveCharacter 0 T x) -
        (multiplicityWeightedPerronZeroSum chi.primitiveCharacter sigma T
            (halfIntegerPoint ⌊x + Y⌋₊) -
          multiplicityWeightedPerronZeroSum chi.primitiveCharacter sigma T
            (halfIntegerPoint ⌊x⌋₊)) := by ring
    _ = (∫ t : ℝ in x..x + Y,
          actualZeroField chi.primitiveCharacter 0 T t) -
        (multiplicityWeightedPerronZeroSum chi.primitiveCharacter sigma T
            (halfIntegerPoint ⌊x + Y⌋₊) -
          multiplicityWeightedPerronZeroSum chi.primitiveCharacter sigma T
            (halfIntegerPoint ⌊x⌋₊)) := by rw [hprimitive]

/-- The legal-aperture supremum of the normalized mismatch window square.
It deliberately mirrors `literalRemainderMaxSq`; no measurability of the
uncountable supremum is postulated. -/
def endpointPerronZeroMismatchMaxSq
    (chi : DirichletCharacter ℂ q)
    (sigma T epsilon X x : ℝ) : ℝ≥0∞ :=
  ⨆ (Y : ℝ) (_hYlow : Real.rpow X (2 / 15 + epsilon) ≤ Y)
      (_hYhigh : Y ≤ X),
    ENNReal.ofReal
      ‖(endpointPerronZeroMismatch chi sigma T (x + Y) -
          endpointPerronZeroMismatch chi sigma T x) / Y‖ ^ 2

/- The former fixed-height family-square staging proposition was rejected:
its prescribed height can coincide with a zero ordinate.  Corrected
common-height source contracts live in `APCorrectedPaperEdgeTail`. -/

end
end MAPEndpointPerronZeroMismatch

#print axioms MAPEndpointPerronZeroMismatch.norm_endpointPerronZeroMismatch_eq_literal_zero_component
#print axioms MAPEndpointPerronZeroMismatch.endpointPerronZeroMismatch_window_eq_integral_sub_perronWindow
