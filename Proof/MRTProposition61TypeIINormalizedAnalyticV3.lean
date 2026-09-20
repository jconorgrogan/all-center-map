import MRTProposition61TypeIIActiveAggregateBoundV3
import MRTProposition61TypeIIActualEndpointLedgerV3

/-! # Exact normalization of the active Type-II analytic cell

Both the actual long interval and the coefficient energies are retained.
The Perron integral is evaluated exactly; no analytic budget is assumed.
-/

namespace MRTProposition61TypeIINormalizedAnalyticV3

open scoped BigOperators
open MeasureTheory
open MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTCorollary25TypeD1LiteralWeld MAPMRTCorollary25Minkowski
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPDynamicHBSourceV3 MAPDynamicHBCanonicalPerronConstantV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicSupportV3 MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicRegroupingV3 MRTLemma215DynamicTypeIIDyadicV3
open MRTProposition61TypeIIActiveAggregateBoundV3
open MRTProposition61TypeIILemma210InstantiationV3
open MontgomeryVaughanFiniteReduction RamachandraShiftedCoefficientEnergy

noncomputable section

/-- Literal normalized ledger, with the cancellation of the two powers of
stationary width in the Perron error made explicit. -/
theorem normalized_activeTypeIICellAnalyticRHS_eq
    (p : Corollary53Input) (T theta C : ℝ) {K k : ℕ}
    (hX : 0 < p.X) (hq : 0 < (p.q : ℝ))
    (hU : 0 < stationaryWidth p.beta p.H) (hT : 0 ≤ T)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff p.X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff p.X K⌋₊))) (k + 1))
    (left suffix : List NatDyadicFactor)
    (leftCell : Fin (sourceDyadicCount (factorUpperProduct left)))
    (suffixCell : Fin (sourceDyadicCount (factorUpperProduct suffix)))
    (component : OuterComponent) :
    let N : ℕ := 2 ^ (leftCell : ℕ)
    let M : ℕ := 2 ^ (suffixCell : ℕ)
    let U := stationaryWidth p.beta p.H
    let L := (componentEndpoints p.X p.beta p.eta component).2 -
      (componentEndpoints p.X p.beta p.eta component).1
    (divisorCount p.q : ℝ) ^ 4 / (p.q * U ^ 2) *
        activeTypeIICellAnalyticRHSV3 p T theta C
          logIndex zbag mbag left suffix leftCell suffixCell component =
      16 * canonicalPerronKFour ^ 2 * (divisorCount p.q : ℝ) ^ 4 *
        Real.log (1 + T) ^ 2 * p.X *
        (((p.q * (2 * U) + 8 * Real.pi * N) *
          (p.q * (L + 2 * T + 2 * U) + 8 * Real.pi * M)) /
            (p.q * U * p.X)) *
        coefficientEnergy (criticalDyadicCoefficient
          (scaledTypeIIPrefixCell zbag mbag left leftCell)) N *
        coefficientEnergy (criticalDyadicCoefficient
          (factorListDyadicCell suffix suffixCell)) M +
      8 * canonicalPerronKFour ^ 2 * (divisorCount p.q : ℝ) ^ 4 *
        L / p.q * (Fintype.card (DirichletCharacter ℂ p.q) : ℝ) ^ 2 *
        C ^ 2 * Real.rpow (4 * (N : ℝ) * M) theta ^ 2 *
        ((N : ℝ) * M) * (Real.log (2 + T) / T) ^ 2 := by
  dsimp only
  unfold activeTypeIICellAnalyticRHSV3
  dsimp only
  rw [integral_perronWeight hT]
  have hsqrt : Real.sqrt
      (((2 ^ (leftCell : ℕ) : ℕ) : ℝ) *
        ((2 ^ (suffixCell : ℕ) : ℕ) : ℝ)) ^ 2 =
      (((2 ^ (leftCell : ℕ) : ℕ) : ℝ) *
        ((2 ^ (suffixCell : ℕ) : ℕ) : ℝ)) := Real.sq_sqrt (by positivity)
  simp only [mul_pow, div_pow]
  rw [hsqrt]
  field_simp [hX.ne', hq.ne', hU.ne']
  <;> ring

end
end MRTProposition61TypeIINormalizedAnalyticV3

#print axioms MRTProposition61TypeIINormalizedAnalyticV3.normalized_activeTypeIICellAnalyticRHS_eq
