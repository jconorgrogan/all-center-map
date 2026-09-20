import MRTDynamicD12PerBagLedger
import MRTDynamicD12CoefficientCap
import MRTDynamicD12ParameterPackage

namespace MRTDynamicD12CanonicalSourceLedger

open scoped BigOperators
open MeasureTheory
open MAPMRTCorollary53Source MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicSupportV3 MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicRegroupingV3 MRTLemma215ScaleClassifierV3
open MRTDynamicD12LiteralMass MRTDynamicD12MomentSource
open MRTDynamicD12FactorExtraction MAPMRTCorollary25Minkowski
open MRTDynamicD12PerBagLedger MRTDynamicD12CoefficientCap
open MRTDynamicD12ParameterPackage

noncomputable section
set_option maxHeartbeats 1400000

/-- Literal raw Perron ledger, not an assumed envelope. -/
def rawLedger (p : Corollary53Input) (P T Bcoeff : ℝ) (Y : ℕ)
    (delta kappa Cm : ℝ) (Em : ℕ) (component : OuterComponent) : ℝ :=
  2 * kappa ^ 2 *
    ((∫ u in (-P)..P, perronWeight u) ^ 2 *
      (Cm * ((p.q : ℝ) * stationaryWidth p.beta p.H + Real.rpow p.X delta) *
        stationaryWidth p.beta p.H * ((p.q : ℝ) * T) *
          (1 + Real.log (8 * p.X)) ^ Em) +
      ((componentEndpoints p.X p.beta p.eta component).2 -
        (componentEndpoints p.X p.beta p.eta component).1) *
      (2 * stationaryWidth p.beta p.H *
        (Fintype.card (DirichletCharacter ℂ p.q) : ℝ) *
        (Bcoeff * Real.sqrt (Y : ℝ) * Real.log (2 + P) / P)) ^ 2)

/-- Constants are fixed before B and the input. The concrete package removes
all annulus/moment premises and the coefficient cap removes the pointwise
coefficient premise. Only the actual one/two-tail source classification remains. -/
theorem exists_canonical_source_ledger
    (K : ℕ) (hK : 1 ≤ K) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ D : ℝ, 0 < D ∧
    ∃ kappa1 Cm1 : ℝ, 0 < kappa1 ∧ 0 < Cm1 ∧ ∃ Em1 : ℕ,
    ∃ kappa2 Cm2 : ℝ, 0 < kappa2 ∧ 0 < Cm2 ∧ ∃ Em2 : ℕ,
      ∀ {p : Corollary53Input} [NeZero p.q] {B Cc : ℕ} {reserve delta : ℝ}
        {k : ℕ},
        Corollary53Admissible 1 1 p → 3 ≤ p.X → 0 ≤ delta → delta ≤ 1 → k < K →
        ∀ (pack : D12ParameterPackage p.X p B Cc reserve)
          (component : OuterComponent)
          (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
          (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff p.X)))) k)
          (mbag : Sym (Option (Fin
            (sourceDyadicCount ⌊dynamicHBCutoff p.X K⌋₊))) (k + 1))
          (s : ℕ),
        s = largestSmallPrefix
          (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
          (Real.rpow p.X delta) →
        ((∀ beta : NatDyadicFactor,
          (sortedComponentFactorList logIndex zbag mbag).drop s = [beta] →
          IsSourceSmoothFactor p.X logIndex beta → 2 ≤ beta.length →
          componentIntegral p.X p.H 1 p.q
            (dynamicD12FactorizedCoeff delta logIndex zbag mbag)
            p.beta p.eta component ≤
            rawLedger p pack.P pack.Tmom (D * Real.rpow p.X epsilon)
              (factorLowerProduct (sortedComponentFactorList logIndex zbag mbag))
              delta kappa1 Cm1 Em1 component) ∧
        (∀ beta gamma : NatDyadicFactor,
          (sortedComponentFactorList logIndex zbag mbag).drop s = [beta, gamma] →
          IsSourceSmoothFactor p.X logIndex beta → 2 ≤ beta.length →
          IsSourceSmoothFactor p.X logIndex gamma → 2 ≤ gamma.length →
          componentIntegral p.X p.H 1 p.q
            (dynamicD12FactorizedCoeff delta logIndex zbag mbag)
            p.beta p.eta component ≤
            rawLedger p pack.P pack.Tmom (D * Real.rpow p.X epsilon)
              (factorLowerProduct (sortedComponentFactorList logIndex zbag mbag))
              delta kappa2 Cm2 Em2 component)) := by
  obtain ⟨D, hD, hcoeff⟩ := exists_d12_component_coefficient_cap K hK epsilon hepsilon
  obtain ⟨kappa1, Cm1, hk1, hc1, Em1, kappa2, Cm2, hk2, hc2, Em2, hledger⟩ :=
    exists_d12_perBag_ledger K hK
  refine ⟨D, hD, kappa1, Cm1, hk1, hc1, Em1, kappa2, Cm2, hk2, hc2, Em2, ?_⟩
  intro p inst B Cc reserve delta k hp hX hdelta hdelta1 hk pack component
    logIndex zbag mbag s hs
  have hU : pack.U = stationaryWidth p.beta p.H := by
    simpa only [stationaryWidth] using pack.hU
  have hband : ∀ t ∈ Set.Icc
      ((componentEndpoints p.X p.beta p.eta component).1 -
        (pack.P + stationaryWidth p.beta p.H))
      ((componentEndpoints p.X p.beta p.eta component).2 +
        (pack.P + stationaryWidth p.beta p.H)),
      pack.rho ≤ |t| ∧ |t| ≤ pack.Tmom := by
    simpa only [← pack.hpeta, hU] using pack.hband component
  have hlen :
      ((componentEndpoints p.X p.beta p.eta component).2 +
        (pack.P + stationaryWidth p.beta p.H)) -
      ((componentEndpoints p.X p.beta p.eta component).1 -
        (pack.P + stationaryWidth p.beta p.H)) + 1 ≤ pack.Tmom := by
    simpa only [← pack.hpeta, hU] using pack.hlength component
  have hc : ∀ n : ℕ,
      ‖dynamicPreliminaryComponent (some logIndex) zbag mbag n‖ ≤
        D * Real.rpow p.X epsilon := by
    intro n
    exact hcoeff (delta := delta) (H₀ := 0) hX hdelta hk logIndex zbag mbag n
  obtain ⟨hone, htwo⟩ := hledger (p := p) (H₀ := 0)
    (P := pack.P) (T := pack.Tmom) (rho := pack.rho)
    (exponent := (B : ℝ)) (Bcoeff := D * Real.rpow p.X epsilon)
    hp hX hdelta hdelta1 hk
    (show 0 ≤ pack.P by linarith [pack.hPone]) pack.hPone
    (mul_nonneg hD.le (Real.rpow_nonneg (by linarith [hX]) epsilon))
    pack.hrho_pos pack.hrhoT pack.hXrho pack.hmoment
    component hband hlen logIndex zbag mbag s hs
  constructor
  · intro beta htail hbeta hlength
    exact hone beta htail hbeta hlength hc
  · intro beta gamma htail hbeta hblen hgamma hglen
    exact htwo beta gamma htail hbeta hblen hgamma hglen hc

end
end MRTDynamicD12CanonicalSourceLedger

#print axioms MRTDynamicD12CanonicalSourceLedger.exists_canonical_source_ledger
