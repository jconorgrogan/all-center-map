import MRTDynamicD12AnnulusMomentAssembly

/-! The actual per-bag D12 ledger. Geometry and the pointwise coefficient cap
are explicit inputs; the theorem only dispatches the literal one/two-tail
moment producers. -/
namespace MRTDynamicD12PerBagLedger

open scoped BigOperators ArithmeticFunction
open ArithmeticFunction MeasureTheory
open MAPMRTCorollary25Minkowski MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicFactorExtractionV3 MRTLemma215DynamicRegroupingV3
open MRTDynamicD12MomentSource MRTDynamicD12LiteralMass
open MRTDynamicD12AnnulusMomentAssembly MRTDynamicD12FactorExtraction
open MRTLemma215DynamicSupportV3 MRTLemma215ScaleClassifierV3

noncomputable section
set_option maxHeartbeats 1400000

theorem exists_d12_perBag_ledger (K : ℕ) (hK : 1 ≤ K) :
    ∃ κ₁ Cm₁ : ℝ, 0 < κ₁ ∧ 0 < Cm₁ ∧ ∃ Em₁ : ℕ,
    ∃ κ₂ Cm₂ : ℝ, 0 < κ₂ ∧ 0 < Cm₂ ∧ ∃ Em₂ : ℕ,
      ∀ {p : Corollary53Input} [NeZero p.q]
        {delta H₀ P T rho exponent Bcoeff : ℝ} {k : ℕ},
        Corollary53Admissible 1 1 p → 3 ≤ p.X → 0 ≤ delta → delta ≤ 1 →
        k < K → 0 ≤ P → 1 ≤ P → 0 ≤ Bcoeff → 0 < rho → rho ≤ T →
        2 * p.X ≤ rho ^ 2 →
        DynamicD12MomentRange (8 * p.X) T exponent p.q (hbFactorCutoff p.X) →
        (component : OuterComponent) →
        (∀ t ∈ Set.Icc
          ((componentEndpoints p.X p.beta p.eta component).1 -
            (P + stationaryWidth p.beta p.H))
          ((componentEndpoints p.X p.beta p.eta component).2 +
            (P + stationaryWidth p.beta p.H)),
          rho ≤ |t| ∧ |t| ≤ T) →
        ((componentEndpoints p.X p.beta p.eta component).2 +
            (P + stationaryWidth p.beta p.H)) -
          ((componentEndpoints p.X p.beta p.eta component).1 -
            (P + stationaryWidth p.beta p.H)) + 1 ≤ T →
        (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X))) →
        (zbag : Sym (Option (Fin (sourceDyadicCount
          (hbFactorCutoff p.X)))) k) →
        (mbag : Sym (Option (Fin
          (sourceDyadicCount ⌊dynamicHBCutoff p.X K⌋₊))) (k + 1)) →
        (s : ℕ) →
        s = largestSmallPrefix
          (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
          (Real.rpow p.X delta) →
        ((∀ beta : NatDyadicFactor,
          (sortedComponentFactorList logIndex zbag mbag).drop s = [beta] →
          IsSourceSmoothFactor p.X logIndex beta → 2 ≤ beta.length →
          (∀ n : ℕ, ‖dynamicPreliminaryComponent (some logIndex) zbag mbag n‖ ≤ Bcoeff) →
          componentIntegral p.X p.H 1 p.q
            (dynamicD12FactorizedCoeff delta logIndex zbag mbag)
            p.beta p.eta component ≤
          2 * κ₁ ^ 2 *
            ((∫ u in (-P)..P, perronWeight u) ^ 2 *
              (Cm₁ * ((p.q : ℝ) * stationaryWidth p.beta p.H +
                Real.rpow p.X delta) * stationaryWidth p.beta p.H *
                ((p.q : ℝ) * T) * (1 + Real.log (8 * p.X)) ^ Em₁) +
              ((componentEndpoints p.X p.beta p.eta component).2 -
                (componentEndpoints p.X p.beta p.eta component).1) *
              (2 * stationaryWidth p.beta p.H *
                (Fintype.card (DirichletCharacter ℂ p.q) : ℝ) *
                (Bcoeff * Real.sqrt (factorLowerProduct
                  (sortedComponentFactorList logIndex zbag mbag)) *
                  Real.log (2 + P) / P)) ^ 2)) ∧
        (∀ beta gamma : NatDyadicFactor,
          (sortedComponentFactorList logIndex zbag mbag).drop s = [beta, gamma] →
          IsSourceSmoothFactor p.X logIndex beta → 2 ≤ beta.length →
          IsSourceSmoothFactor p.X logIndex gamma → 2 ≤ gamma.length →
          (∀ n : ℕ, ‖dynamicPreliminaryComponent (some logIndex) zbag mbag n‖ ≤ Bcoeff) →
          componentIntegral p.X p.H 1 p.q
            (dynamicD12FactorizedCoeff delta logIndex zbag mbag)
            p.beta p.eta component ≤
          2 * κ₂ ^ 2 *
            ((∫ u in (-P)..P, perronWeight u) ^ 2 *
              (Cm₂ * ((p.q : ℝ) * stationaryWidth p.beta p.H +
                Real.rpow p.X delta) * stationaryWidth p.beta p.H *
                ((p.q : ℝ) * T) * (1 + Real.log (8 * p.X)) ^ Em₂) +
              ((componentEndpoints p.X p.beta p.eta component).2 -
                (componentEndpoints p.X p.beta p.eta component).1) *
              (2 * stationaryWidth p.beta p.H *
                (Fintype.card (DirichletCharacter ℂ p.q) : ℝ) *
                (Bcoeff * Real.sqrt (factorLowerProduct
                  (sortedComponentFactorList logIndex zbag mbag)) *
                  Real.log (2 + P) / P)) ^ 2))) := by
  obtain ⟨κ₁, Cm₁, hκ₁, hCm₁, Em₁, hone⟩ :=
    componentIntegral_d12_one_le_uniform_moment K hK
  obtain ⟨κ₂, Cm₂, hκ₂, hCm₂, Em₂, htwo⟩ :=
    componentIntegral_d12_two_le_uniform_moment K hK
  refine ⟨κ₁, Cm₁, hκ₁, hCm₁, Em₁, κ₂, Cm₂, hκ₂, hCm₂, Em₂, ?_⟩
  intro p inst delta H₀ P T rho exponent Bcoeff k hp hX hdelta hdelta1 hk
    hP hP1 hBcoeff hrho hrhoT hXrho hrange component hband hlen
    logIndex zbag mbag s hs
  constructor
  · intro beta htail hbeta hbetaLen hcoeff
    exact hone (H₀ := H₀) hp hX hdelta hdelta1 hk hP hP1 hBcoeff hrho hrhoT
      hXrho hrange component hband hlen logIndex zbag mbag s hs beta
      htail hbeta hbetaLen hcoeff
  · intro beta gamma htail hbeta hbetaLen hgamma hgammaLen hcoeff
    exact htwo (H₀ := H₀) hp hX hdelta hdelta1 hk hP hP1 hBcoeff hrho hrhoT
      hXrho hrange component hband hlen logIndex zbag mbag s hs beta gamma
      htail hbeta hbetaLen hgamma hgammaLen hcoeff

end
end MRTDynamicD12PerBagLedger

#print axioms MRTDynamicD12PerBagLedger.exists_d12_perBag_ledger
