import KoukTheorem113FullSupportFormula
import EndpointRegularizedZeroPrimitive

/-!
# Ambient full-support endpoint formula

This is the exact source-facing form consumed by the AP endpoint layer.  It
passes from an ambient character to its primitive inducer, keeps the literal
bad-Euler-factor correction, and moves from the half-integer Perron endpoint
to the requested real endpoint without changing the full zero support.
-/

namespace KoukTheorem113AmbientFormula

open Set
open scoped BigOperators
open APFoundation APExplicitFormulaMajorantAdapter
open DirichletZeros PrimitiveTruncatedExplicitFormulaBridge
open MAPEndpointRegularizedZeroPrimitive
open KoukTheorem113EndpointKernel KoukTheorem113FullSupportFormula

noncomputable section

variable {q : ℕ} [NeZero q]

/-- Exact ambient Kouk remainder before estimates. -/
def ambientFullSupportKoukRemainder
    (chi : DirichletCharacter ℂ q) (t sigma c T : ℝ) : ℂ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let N := ⌊t⌋₊
  let u := halfIntegerPoint N
  exact
    residueMain chi.primitiveCharacter u - principalCoefficient chi * t +
      endpointMultiplicityWeightedZeroTerm chi.primitiveCharacter 0 T t -
      endpointMultiplicityWeightedZeroTerm chi.primitiveCharacter 0 T u +
      primitiveFullSupportEndpointRemainder
        chi.primitiveCharacter N sigma c T -
      imprimitiveMangoldtCorrection chi (Finset.Icc 1 N)

/-- The multiplicity-weighted endpoint-kernel sum is exactly the endpoint
primitive already used by the AP full-support connector. -/
theorem endpointKernelZeroSum_eq_endpointMultiplicityWeightedZeroTerm
    (chi : DirichletCharacter ℂ q) {T u : ℝ} (hu : 0 < u) :
    (∑ rho ∈ zeroSupport chi 0 T,
        (zeroMultiplicity chi 0 T rho : ℂ) *
          endpointPerronKernel u rho) =
      endpointMultiplicityWeightedZeroTerm chi 0 T u := by
  classical
  unfold endpointMultiplicityWeightedZeroTerm endpointFiniteZeroPrimitive
  apply Finset.sum_congr rfl
  intro rho _hrho
  rw [endpointPerronKernel_eq_endpointRegularizedZeroTerm hu]

/-- Exact ambient Theorem 11.3 endpoint formula on a legal negative-left
primitive rectangle.  The displayed zero support is literally
`zeroSupport chi.primitiveCharacter 0 T`. -/
theorem ambientTwistedPsi_eq_principal_sub_fullZero_add_koukRemainder
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    {t sigma c T : ℝ} (hsigma : sigma ≤ 0) (hsigma1 : sigma < 1)
    (hc : 1 < c) (hT : 0 < T)
    (hleftNonzero : ∀ u ∈ Set.Icc (-T) T,
      regularizedLFunction chi.primitiveCharacter
        ((sigma : ℂ) + (u : ℂ) * Complex.I) ≠ 0)
    (hbottomNonzero : ∀ r ∈ Set.Icc sigma c,
      regularizedLFunction chi.primitiveCharacter
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0)
    (htopNonzero : ∀ r ∈ Set.Icc sigma c,
      regularizedLFunction chi.primitiveCharacter
        ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    ambientTwistedPsi chi t =
      principalCoefficient chi * t -
        endpointMultiplicityWeightedZeroTerm
          chi.primitiveCharacter 0 T t +
        ambientFullSupportKoukRemainder chi t sigma c T := by
  let N := ⌊t⌋₊
  let u := halfIntegerPoint N
  have hprimitive :=
    twistedMangoldtPrefix_eq_residueMain_sub_fullZero_add_remainder
      chi.primitiveCharacter N hsigma hsigma1 hc hT
        hleftNonzero hbottomNonzero htopNonzero
  have hzero :=
    endpointKernelZeroSum_eq_endpointMultiplicityWeightedZeroTerm
      chi.primitiveCharacter (T := T) (u := u) (halfIntegerPoint_pos N)
  unfold ambientTwistedPsi
  rw [APFoundation.twistedMangoldtSum_eq_primitive_sub_correction]
  rw [hprimitive]
  rw [hzero]
  simp only [ambientFullSupportKoukRemainder, N, u]
  ring

/-- Formula uniqueness identifies the Kouk remainder with any other exact
full-support endpoint remainder at the same endpoint and height. -/
theorem ambientKoukRemainder_eq_of_formula
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    {t sigma c T : ℝ} (R : ℂ)
    (hkouk : ambientTwistedPsi chi t =
      principalCoefficient chi * t -
        endpointMultiplicityWeightedZeroTerm
          chi.primitiveCharacter 0 T t +
        ambientFullSupportKoukRemainder chi t sigma c T)
    (hR : ambientTwistedPsi chi t =
      principalCoefficient chi * t -
        endpointMultiplicityWeightedZeroTerm
          chi.primitiveCharacter 0 T t + R) :
    ambientFullSupportKoukRemainder chi t sigma c T = R := by
  linear_combination hR - hkouk

end
end KoukTheorem113AmbientFormula

#print axioms KoukTheorem113AmbientFormula.ambientTwistedPsi_eq_principal_sub_fullZero_add_koukRemainder
#print axioms KoukTheorem113AmbientFormula.ambientKoukRemainder_eq_of_formula
