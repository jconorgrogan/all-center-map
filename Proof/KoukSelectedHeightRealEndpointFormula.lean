import KoukTheorem113HalfStripFormula
import KoukFullStripGoodHeightAperture
import KoukRightReplacementCorrectionBound

/-!
# Real-endpoint selected-height form of Koukoulopoulos 11.3

The contour shift is already certified for an arbitrary positive real endpoint.
The only Perron input needed to avoid the half-integer displacement is the
literal difference between the arithmetic prefix and the right-line integral
at that same real endpoint.  This module isolates that exact source term and
proves the full-support endpoint identity around it.
-/

namespace KoukSelectedHeightRealEndpointFormula

open Set
open APFoundation APExplicitFormulaMajorantAdapter DirichletZeros
open PrimitiveTruncatedExplicitFormulaBridge
open TruncatedTwistedPerron
open KoukTheorem113EndpointKernel KoukTheorem113ExactFormula
open KoukTheorem113Residues KoukTheorem113FullSupportFormula
open MAPEndpointRegularizedZeroPrimitive

noncomputable section

/-- The exact finite-height Perron error at the requested real endpoint. -/
def realEndpointPerronError
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (t c T : ℝ) : ℂ :=
  twistedMangoldtSum chi (Finset.Icc 1 ⌊t⌋₊) -
    rightLineIntegral chi t c T

/-- The narrow source lemma still required from the real-endpoint Perron
argument in Koukoulopoulos, Theorem 11.3.  It contains no zero-density,
functional-equation, or AP input. -/
def UniformRealEndpointPerronBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
      (t T : ℝ),
      Real.exp 2 ≤ t → 2 ≤ T → T ≤ t →
        ‖realEndpointPerronError chi t
            (1 + (Real.log t)⁻¹) T‖ ≤
          C * t * (Real.log (t + 2)) ^ 2 / T

/-- Exact primitive real-endpoint formula on the canonical half-strip. -/
theorem twistedMangoldtPrefix_eq_residueMain_sub_fullZero_add_realRemainder
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprimitive : chi.IsPrimitive)
    {t c T : ℝ} (ht : 0 < t) (hc : 1 < c) (hT : 0 < T)
    (hbottomNonzero : ∀ r ∈ Set.Icc
      (KoukNegativeHalfPlaneNonvanishing.negativeHalfIntegerEdge 0) c,
      regularizedLFunction chi
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0)
    (htopNonzero : ∀ r ∈ Set.Icc
      (KoukNegativeHalfPlaneNonvanishing.negativeHalfIntegerEdge 0) c,
      regularizedLFunction chi
        ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    twistedMangoldtSum chi (Finset.Icc 1 ⌊t⌋₊) =
      residueMain chi t -
        endpointMultiplicityWeightedZeroTerm chi 0 T t +
        (realEndpointPerronError chi t c T +
          endpointVerticalLineIntegral chi t
            (KoukNegativeHalfPlaneNonvanishing.negativeHalfIntegerEdge 0) T -
          endpointHorizontalBoundaryIntegral chi t
            (KoukNegativeHalfPlaneNonvanishing.negativeHalfIntegerEdge 0) c T +
          endpointRightReplacementCorrection chi c T -
          principalEndpointUnit chi) := by
  have hleft : ∀ u ∈ Set.Icc (-T) T,
      regularizedLFunction chi
        ((KoukNegativeHalfPlaneNonvanishing.negativeHalfIntegerEdge 0 : ℂ) +
          (u : ℂ) * Complex.I) ≠ 0 := by
    intro u _hu
    simpa [KoukNegativeHalfPlaneNonvanishing.negativeHalfIntegerEdge] using
      (KoukNegativeHalfPlaneNonvanishing.regularizedLFunction_ne_zero_on_negativeHalfIntegerLine
        chi hprimitive 0 u)
  have hshift :=
    endpointVerticalLineIntegral_eq_main_sub_zero_add_left_sub_horizontal
      chi ht (sigma :=
        KoukNegativeHalfPlaneNonvanishing.negativeHalfIntegerEdge 0)
        (c := c) (T := T)
        (by norm_num
          [KoukNegativeHalfPlaneNonvanishing.negativeHalfIntegerEdge])
        hc hT hleft hbottomNonzero htopNonzero
  have hsplit := endpointZeroSum_negativeRectangle_eq_full_add_negativeStrip
    chi (x := t) (sigma :=
      KoukNegativeHalfPlaneNonvanishing.negativeHalfIntegerEdge 0)
      (T := T) (by norm_num
        [KoukNegativeHalfPlaneNonvanishing.negativeHalfIntegerEdge])
  have hempty := KoukNegativeHalfStripEmpty.negativeStripZeroSupport_negativeHalf_eq_empty
    chi hprimitive T
  have hprincipal := endpointPrincipalResidue_eq_residueMain_sub_unit
    chi (x := t)
  have hzeroEndpoint :=
    KoukTheorem113AmbientFormula.endpointKernelZeroSum_eq_endpointMultiplicityWeightedZeroTerm
      chi (T := T) (u := t) ht
  have hright := rightLineIntegral_eq_endpointVertical_add_replacement
    chi ht hc (T := T)
  unfold realEndpointPerronError
  rw [hright, hshift, hsplit, hempty, Finset.sum_empty, add_zero]
  rw [hzeroEndpoint]
  classical
  by_cases hchi : chi = 1
  · simp only [hchi, if_true, residueMain, principalEndpointUnit]
    rw [endpointPerronKernel_of_ne one_ne_zero]
    rw [Complex.cpow_one]
    ring
  · simp [hchi, residueMain, principalEndpointUnit]
    ring

/-- Ambient selected-height real-endpoint remainder, with the bad Euler
factors kept literal. -/
def ambientSelectedRealEndpointRemainder
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (t c T : ℝ) : ℂ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact
    realEndpointPerronError chi.primitiveCharacter t c T +
      endpointVerticalLineIntegral chi.primitiveCharacter t
        (KoukNegativeHalfPlaneNonvanishing.negativeHalfIntegerEdge 0) T -
      endpointHorizontalBoundaryIntegral chi.primitiveCharacter t
        (KoukNegativeHalfPlaneNonvanishing.negativeHalfIntegerEdge 0) c T +
      endpointRightReplacementCorrection chi.primitiveCharacter c T -
      principalEndpointUnit chi.primitiveCharacter -
      imprimitiveMangoldtCorrection chi (Finset.Icc 1 ⌊t⌋₊)

/-- Exact ambient full-support formula at one selected legal height. -/
theorem ambientTwistedPsi_eq_principal_sub_fullZero_add_selectedRealRemainder
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    [NeZero chi.conductor] {t c T : ℝ}
    (ht : 0 < t) (hc : 1 < c) (hT : 0 < T)
    (hbottomNonzero : ∀ r ∈ Set.Icc
      (KoukNegativeHalfPlaneNonvanishing.negativeHalfIntegerEdge 0) c,
      regularizedLFunction chi.primitiveCharacter
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0)
    (htopNonzero : ∀ r ∈ Set.Icc
      (KoukNegativeHalfPlaneNonvanishing.negativeHalfIntegerEdge 0) c,
      regularizedLFunction chi.primitiveCharacter
        ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    ambientTwistedPsi chi t =
      principalCoefficient chi * t -
        endpointMultiplicityWeightedZeroTerm
          chi.primitiveCharacter 0 T t +
        ambientSelectedRealEndpointRemainder chi t c T := by
  have hprimitive :=
    twistedMangoldtPrefix_eq_residueMain_sub_fullZero_add_realRemainder
      chi.primitiveCharacter chi.primitiveCharacter_isPrimitive
      ht hc hT hbottomNonzero htopNonzero
  unfold ambientTwistedPsi ambientSelectedRealEndpointRemainder
  rw [APFoundation.twistedMangoldtSum_eq_primitive_sub_correction]
  rw [hprimitive, residueMain_primitiveCharacter]
  have hmain : residueMain chi t = principalCoefficient chi * t := by
    classical
    by_cases hchi : chi = 1 <;>
      simp [residueMain, principalCoefficient, hchi]
  rw [hmain]
  ring

/-- Formula uniqueness identifies the selected real-contour remainder with
the canonical full-support endpoint residual. -/
theorem ambientSelectedRealEndpointRemainder_eq_fullSupportResidual
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    [NeZero chi.conductor] {t c T : ℝ}
    (ht : 0 < t) (hc : 1 < c) (hT : 0 < T)
    (hbottomNonzero : ∀ r ∈ Set.Icc
      (KoukNegativeHalfPlaneNonvanishing.negativeHalfIntegerEdge 0) c,
      regularizedLFunction chi.primitiveCharacter
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0)
    (htopNonzero : ∀ r ∈ Set.Icc
      (KoukNegativeHalfPlaneNonvanishing.negativeHalfIntegerEdge 0) c,
      regularizedLFunction chi.primitiveCharacter
        ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    ambientSelectedRealEndpointRemainder chi t c T =
      ambientTwistedPsi chi t -
        (principalCoefficient chi * t -
          endpointMultiplicityWeightedZeroTerm
            chi.primitiveCharacter 0 T t) := by
  rw [ambientTwistedPsi_eq_principal_sub_fullZero_add_selectedRealRemainder
    chi ht hc hT hbottomNonzero htopNonzero]
  ring

end

end KoukSelectedHeightRealEndpointFormula

#print axioms KoukSelectedHeightRealEndpointFormula.twistedMangoldtPrefix_eq_residueMain_sub_fullZero_add_realRemainder
#print axioms KoukSelectedHeightRealEndpointFormula.ambientTwistedPsi_eq_principal_sub_fullZero_add_selectedRealRemainder
