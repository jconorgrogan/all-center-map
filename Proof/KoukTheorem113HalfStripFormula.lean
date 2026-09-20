import KoukTheorem113AmbientFormula
import KoukNegativeHalfStripEmpty

/-!
# The exact full-support formula on the `Re s = -1/2` contour

The canonical `-1/2` left edge has an empty negative-strip divisor for every
primitive character.  This module removes that term from the literal source
remainder and exposes the simpler exact formula used for quantitative work.
-/

namespace KoukTheorem113HalfStripFormula

open Set
open scoped BigOperators
open APFoundation APExplicitFormulaMajorantAdapter
open DirichletZeros PrimitiveTruncatedExplicitFormulaBridge
open TruncatedTwistedPerron
open MAPEndpointRegularizedZeroPrimitive
open KoukTheorem113EndpointKernel KoukTheorem113ExactFormula
open KoukTheorem113FullSupportFormula KoukTheorem113AmbientFormula
open KoukNegativeHalfPlaneNonvanishing KoukNegativeHalfStripEmpty

noncomputable section

/-- Primitive full-support remainder after fixing the left edge at `-1/2`.
The auxiliary negative-strip zero sum is absent because it is empty. -/
def primitiveHalfStripEndpointRemainder
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (N : ℕ) (c T : ℝ) : ℂ :=
  endpointVerticalLineIntegral chi (halfIntegerPoint N)
      (negativeHalfIntegerEdge 0) T -
    endpointHorizontalBoundaryIntegral chi (halfIntegerPoint N)
      (negativeHalfIntegerEdge 0) c T +
    endpointRightReplacementCorrection chi c T +
    insideKernelError chi N c T -
    coefficientTail chi (halfIntegerPoint N) c T (Finset.Icc 1 N) -
    principalEndpointUnit chi

theorem primitiveFullSupportEndpointRemainder_negativeHalf_eq
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprimitive : chi.IsPrimitive) (N : ℕ) (c T : ℝ) :
    primitiveFullSupportEndpointRemainder chi N
        (negativeHalfIntegerEdge 0) c T =
      primitiveHalfStripEndpointRemainder chi N c T := by
  unfold primitiveFullSupportEndpointRemainder
    primitiveHalfStripEndpointRemainder
  rw [negativeStripZeroSupport_negativeHalf_eq_empty chi hprimitive T]
  simp

/-- Exact primitive Theorem 11.3 formula on the canonical half-strip
rectangle, with literal full zero support and no hidden residue sector. -/
theorem twistedMangoldtPrefix_eq_residueMain_sub_fullZero_add_halfStripRemainder
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprimitive : chi.IsPrimitive) (N : ℕ) {c T : ℝ}
    (hc : 1 < c) (hT : 0 < T)
    (hbottomNonzero : ∀ r ∈ Set.Icc (negativeHalfIntegerEdge 0) c,
      regularizedLFunction chi
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0)
    (htopNonzero : ∀ r ∈ Set.Icc (negativeHalfIntegerEdge 0) c,
      regularizedLFunction chi
        ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    twistedMangoldtSum chi (Finset.Icc 1 N) =
      residueMain chi (halfIntegerPoint N) -
        ∑ rho ∈ zeroSupport chi 0 T,
          (zeroMultiplicity chi 0 T rho : ℂ) *
            endpointPerronKernel (halfIntegerPoint N) rho +
        primitiveHalfStripEndpointRemainder chi N c T := by
  have hleft : ∀ t ∈ Set.Icc (-T) T,
      regularizedLFunction chi
        (((negativeHalfIntegerEdge 0 : ℝ) : ℂ) +
          (t : ℂ) * Complex.I) ≠ 0 :=
    by
      intro t _ht
      exact regularizedLFunction_ne_zero_on_negativeHalfIntegerLine
        chi hprimitive 0 t
  have hbase :=
    twistedMangoldtPrefix_eq_residueMain_sub_fullZero_add_remainder
      chi N (sigma := negativeHalfIntegerEdge 0) (c := c) (T := T)
      (by norm_num [negativeHalfIntegerEdge])
      (by norm_num [negativeHalfIntegerEdge]) hc hT
      hleft hbottomNonzero htopNonzero
  rw [primitiveFullSupportEndpointRemainder_negativeHalf_eq
    chi hprimitive N c T] at hbase
  exact hbase

/-- Ambient endpoint remainder using the canonical primitive half-strip
contour. -/
def ambientHalfStripKoukRemainder
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (t c T : ℝ) : ℂ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let N := ⌊t⌋₊
  let u := halfIntegerPoint N
  exact
    residueMain chi.primitiveCharacter u - principalCoefficient chi * t +
      endpointMultiplicityWeightedZeroTerm chi.primitiveCharacter 0 T t -
      endpointMultiplicityWeightedZeroTerm chi.primitiveCharacter 0 T u +
      primitiveHalfStripEndpointRemainder chi.primitiveCharacter N c T -
      imprimitiveMangoldtCorrection chi (Finset.Icc 1 N)

theorem ambientFullSupportKoukRemainder_negativeHalf_eq
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (t c T : ℝ) :
    ambientFullSupportKoukRemainder chi t
        (negativeHalfIntegerEdge 0) c T =
      ambientHalfStripKoukRemainder chi t c T := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  simp only [ambientFullSupportKoukRemainder, ambientHalfStripKoukRemainder]
  rw [primitiveFullSupportEndpointRemainder_negativeHalf_eq
    chi.primitiveCharacter chi.primitiveCharacter_isPrimitive ⌊t⌋₊ c T]

/-- Exact ambient full-support endpoint formula on the canonical half-strip
contour. -/
theorem ambientTwistedPsi_eq_principal_sub_fullZero_add_halfStripRemainder
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    [NeZero chi.conductor] {t c T : ℝ}
    (hc : 1 < c) (hT : 0 < T)
    (hbottomNonzero : ∀ r ∈ Set.Icc (negativeHalfIntegerEdge 0) c,
      regularizedLFunction chi.primitiveCharacter
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0)
    (htopNonzero : ∀ r ∈ Set.Icc (negativeHalfIntegerEdge 0) c,
      regularizedLFunction chi.primitiveCharacter
        ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    ambientTwistedPsi chi t =
      principalCoefficient chi * t -
        endpointMultiplicityWeightedZeroTerm
          chi.primitiveCharacter 0 T t +
        ambientHalfStripKoukRemainder chi t c T := by
  have hleft : ∀ u ∈ Set.Icc (-T) T,
      regularizedLFunction chi.primitiveCharacter
        (((negativeHalfIntegerEdge 0 : ℝ) : ℂ) +
          (u : ℂ) * Complex.I) ≠ 0 :=
    by
      intro u _hu
      exact regularizedLFunction_ne_zero_on_negativeHalfIntegerLine
        chi.primitiveCharacter chi.primitiveCharacter_isPrimitive 0 u
  have hbase :=
    ambientTwistedPsi_eq_principal_sub_fullZero_add_koukRemainder
      chi (t := t) (sigma := negativeHalfIntegerEdge 0) (c := c) (T := T)
      (by norm_num [negativeHalfIntegerEdge])
      (by norm_num [negativeHalfIntegerEdge]) hc hT
      hleft hbottomNonzero htopNonzero
  rw [ambientFullSupportKoukRemainder_negativeHalf_eq chi t c T] at hbase
  exact hbase

end
end KoukTheorem113HalfStripFormula

#print axioms KoukTheorem113HalfStripFormula.twistedMangoldtPrefix_eq_residueMain_sub_fullZero_add_halfStripRemainder
#print axioms KoukTheorem113HalfStripFormula.ambientTwistedPsi_eq_principal_sub_fullZero_add_halfStripRemainder
