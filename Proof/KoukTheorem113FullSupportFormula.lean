import KoukTheorem113ExactFormula
import MellinDetectorLeaf

/-!
# Full-support form of the exact Koukoulopoulos endpoint formula

The negative-left rectangle crosses the trivial-zero strip.  This module
splits its divisor exactly into the displayed closed nonnegative-real-part
support and the literal negative strip.  Multiplicities are transported from
analytic orders; no zero is silently dropped or counted twice.
-/

namespace KoukTheorem113FullSupportFormula

open Set
open scoped BigOperators
open DirichletZeros PrimitiveExplicitFormulaSpine
open PrimitiveTruncatedExplicitFormulaBridge TruncatedTwistedPerron
open KoukTheorem113EndpointKernel KoukTheorem113ExactFormula
open MAPMellinDetectorLeaf

noncomputable section

/-- Zeros crossed to the left of the displayed full support.  For
`sigma ≤ 0` this is exactly the negative-real-part part of the rectangle,
including any trivial zeros on the selected height range. -/
def negativeStripZeroSupport {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma T : ℝ) : Finset ℂ :=
  zeroSupport chi sigma T \ zeroSupport chi 0 T

/-- The displayed full support is contained in every rectangle with a
nonpositive left edge. -/
theorem fullZeroSupport_subset_negativeRectangle
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma T : ℝ} (hsigma : sigma ≤ 0) :
    zeroSupport chi 0 T ⊆ zeroSupport chi sigma T :=
  zeroSupport_mono chi hsigma le_rfl

/-- Multiplicity on the displayed full support is independent of the
negative rectangle used in the contour move. -/
theorem zeroMultiplicity_negativeRectangle_eq_full
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma T : ℝ} {rho : ℂ} (hsigma : sigma ≤ 0)
    (hrho : rho ∈ zeroSupport chi 0 T) :
    zeroMultiplicity chi sigma T rho = zeroMultiplicity chi 0 T rho := by
  have hfull : rho ∈ zeroRectangle 0 T :=
    mem_zeroRectangle_of_mem_zeroSupport chi 0 T hrho
  have hnegative : rho ∈ zeroRectangle sigma T :=
    zeroRectangle_mono hsigma le_rfl hfull
  exact zeroMultiplicity_eq_of_mem_rectangles chi hnegative hfull

/-- Exact divisor split into the displayed full support and the negative
strip crossed only for the far-left contour. -/
theorem endpointZeroSum_negativeRectangle_eq_full_add_negativeStrip
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x sigma T : ℝ} (hsigma : sigma ≤ 0) :
    (∑ rho ∈ zeroSupport chi sigma T,
        (zeroMultiplicity chi sigma T rho : ℂ) *
          endpointPerronKernel x rho) =
      (∑ rho ∈ zeroSupport chi 0 T,
        (zeroMultiplicity chi 0 T rho : ℂ) *
          endpointPerronKernel x rho) +
      ∑ rho ∈ negativeStripZeroSupport chi sigma T,
        (zeroMultiplicity chi sigma T rho : ℂ) *
          endpointPerronKernel x rho := by
  classical
  let outer := zeroSupport chi sigma T
  let inner := zeroSupport chi 0 T
  let f : ℂ → ℂ := fun rho =>
    (zeroMultiplicity chi sigma T rho : ℂ) *
      endpointPerronKernel x rho
  have hsub : inner ⊆ outer :=
    fullZeroSupport_subset_negativeRectangle chi hsigma
  have hinner : (∑ rho ∈ inner, f rho) =
      ∑ rho ∈ inner,
        (zeroMultiplicity chi 0 T rho : ℂ) *
          endpointPerronKernel x rho := by
    apply Finset.sum_congr rfl
    intro rho hrho
    simp only [f, zeroMultiplicity_negativeRectangle_eq_full
      chi hsigma hrho]
  have hsdiff := Finset.sum_sdiff_eq_sub (f := f) hsub
  simp only [negativeStripZeroSupport]
  change (∑ rho ∈ outer, f rho) =
    (∑ rho ∈ inner,
      (zeroMultiplicity chi 0 T rho : ℂ) *
        endpointPerronKernel x rho) +
      ∑ rho ∈ outer \ inner, f rho
  rw [← hinner, hsdiff]
  ring

/-- The harmless `+1` needed to replace the exact principal residue `x-1`
by the conventional main term `x`. -/
def principalEndpointUnit {q : ℕ}
    (chi : DirichletCharacter ℂ q) : ℂ :=
  @ite ℂ (chi = 1) (Classical.propDecidable _) 1 0

theorem endpointPrincipalResidue_eq_residueMain_sub_unit
    {q : ℕ} (chi : DirichletCharacter ℂ q) {x : ℝ} :
    (@ite ℂ (chi = 1) (Classical.propDecidable _)
      (endpointPerronKernel x 1) 0) =
      residueMain chi x - principalEndpointUnit chi := by
  classical
  by_cases hchi : chi = 1
  · simp only [hchi, if_true, residueMain, principalEndpointUnit]
    rw [endpointPerronKernel_of_ne one_ne_zero]
    simp
  · simp [hchi, residueMain, principalEndpointUnit]

/-- Literal primitive remainder after displaying exactly the full
`0 ≤ Re rho ≤ 1` zero support. -/
def primitiveFullSupportEndpointRemainder
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (N : ℕ) (sigma c T : ℝ) : ℂ :=
  endpointVerticalLineIntegral chi (halfIntegerPoint N) sigma T -
    endpointHorizontalBoundaryIntegral chi (halfIntegerPoint N) sigma c T +
    endpointRightReplacementCorrection chi c T +
    insideKernelError chi N c T -
    coefficientTail chi (halfIntegerPoint N) c T (Finset.Icc 1 N) -
    principalEndpointUnit chi -
    ∑ rho ∈ negativeStripZeroSupport chi sigma T,
      (zeroMultiplicity chi sigma T rho : ℂ) *
        endpointPerronKernel (halfIntegerPoint N) rho

/-- Exact primitive Theorem 11.3 skeleton with the displayed zero sum on the
full nonnegative-real-part support.  The remaining source work is solely a
quantitative bound for the literal remainder above. -/
theorem twistedMangoldtPrefix_eq_residueMain_sub_fullZero_add_remainder
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (N : ℕ) {sigma c T : ℝ} (hsigma : sigma ≤ 0)
    (hsigma1 : sigma < 1) (hc : 1 < c) (hT : 0 < T)
    (hleftNonzero : ∀ t ∈ Set.Icc (-T) T,
      regularizedLFunction chi
        ((sigma : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hbottomNonzero : ∀ r ∈ Set.Icc sigma c,
      regularizedLFunction chi
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0)
    (htopNonzero : ∀ r ∈ Set.Icc sigma c,
      regularizedLFunction chi
        ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    APFoundation.twistedMangoldtSum chi (Finset.Icc 1 N) =
      residueMain chi (halfIntegerPoint N) -
        ∑ rho ∈ zeroSupport chi 0 T,
          (zeroMultiplicity chi 0 T rho : ℂ) *
            endpointPerronKernel (halfIntegerPoint N) rho +
        primitiveFullSupportEndpointRemainder chi N sigma c T := by
  rw [twistedMangoldtPrefix_eq_endpoint_negativeRectangle chi N
    hsigma1 hc hT hleftNonzero hbottomNonzero htopNonzero]
  rw [endpointZeroSum_negativeRectangle_eq_full_add_negativeStrip
    chi hsigma]
  unfold primitiveFullSupportEndpointRemainder
  classical
  by_cases hchi : chi = 1
  · simp only [hchi, if_true, residueMain, principalEndpointUnit]
    rw [endpointPerronKernel_of_ne one_ne_zero]
    simp
    ring
  · simp only [hchi, if_false, residueMain, principalEndpointUnit]
    ring

end
end KoukTheorem113FullSupportFormula

#print axioms KoukTheorem113FullSupportFormula.endpointZeroSum_negativeRectangle_eq_full_add_negativeStrip
#print axioms KoukTheorem113FullSupportFormula.twistedMangoldtPrefix_eq_residueMain_sub_fullZero_add_remainder
