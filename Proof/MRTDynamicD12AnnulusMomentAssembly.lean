import MRTDynamicD12CarrierIdentities
import MRTDynamicD12AnnulusGeometry
import MRTDynamicD12CoefficientBound
import MRTDynamicD12PerronMassAssembly
import MRTDynamicD12SourceSupport
import MRTLemma215OpenIntervalCutoffV3

/-! Actual d1/d2 annulus-to-moment assembly.  The enlarged signed interval is
kept in the hypotheses so this weld cannot silently recenter the component. -/
namespace MRTDynamicD12AnnulusMomentAssembly

open scoped BigOperators ArithmeticFunction
open ArithmeticFunction MeasureTheory
open MAPMRTCorollary53Source MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTCorollary25Minkowski MAPMRTProposition51Source
open MAPMRTProposition61TypeD1FirstInequality
open MAPDynamicHBSourceV3 MAPHBPerronSourceData
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicFactorExtractionV3 MRTLemma215DynamicSupportV3
open MRTLemma215DynamicRegroupingV3 MRTLemma215DynamicTypeIIFiniteEnvelopeV3
open MRTLemma215DynamicHighPacketCertificateV3
open MRTLemma215ScaleClassifierV3
open MRTDynamicD12UniformFullMoment MRTDynamicD12FactorExtraction
open MRTDynamicD12LiteralMass MRTDynamicD12MomentSource
open MRTDynamicD12ShortPrefix
open MRTDynamicD12CarrierIdentities MRTDynamicD12AnnulusGeometry
open MRTDynamicD12CoefficientBound MRTDynamicD12PerronMassAssembly
open MRTDynamicD12SourceSupport MRTLemma215OpenIntervalCutoffV3

noncomputable section

set_option maxHeartbeats 1400000

/-- One active d1 bag after the Perron transfer and the exact one-shell
carrier identity.  The moment theorem is applied on the original component
enlarged to `[a-P-U,b+P+U]`; `hband` is therefore source-indexed and signed. -/
theorem componentIntegral_d12_one_le_uniform_moment
    (K : ℕ) (hK : 1 ≤ K) :
    ∃ κ Cm : ℝ, 0 < κ ∧ 0 < Cm ∧ ∃ Em : ℕ,
      ∀ {p : Corollary53Input} [NeZero p.q]
        {delta H₀ P T rho exponent Bcoeff : ℝ} {k : ℕ},
        Corollary53Admissible 1 1 p →
        3 ≤ p.X → 0 ≤ delta → delta ≤ 1 → k < K →
        0 ≤ P → 1 ≤ P → 0 ≤ Bcoeff →
        0 < rho → rho ≤ T → 2 * p.X ≤ rho ^ 2 →
        DynamicD12MomentRange (8 * p.X) T exponent p.q
          (hbFactorCutoff p.X) →
        (component : OuterComponent) →
        (∀ t ∈ Set.Icc
          ((componentEndpoints p.X p.beta p.eta component).1 - (P +
            stationaryWidth p.beta p.H))
          ((componentEndpoints p.X p.beta p.eta component).2 + (P +
            stationaryWidth p.beta p.H)),
          rho ≤ |t| ∧ |t| ≤ T) →
        ((componentEndpoints p.X p.beta p.eta component).2 + (P +
            stationaryWidth p.beta p.H)) -
          ((componentEndpoints p.X p.beta p.eta component).1 - (P +
            stationaryWidth p.beta p.H)) + 1 ≤ T →
        (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X))) →
        (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff p.X)))) k) →
        (mbag : Sym (Option (Fin
          (sourceDyadicCount ⌊dynamicHBCutoff p.X K⌋₊))) (k + 1)) →
        (s : ℕ) →
        s = largestSmallPrefix
          (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
          (Real.rpow p.X delta) →
        (beta : NatDyadicFactor) →
        (sortedComponentFactorList logIndex zbag mbag).drop s = [beta] →
        IsSourceSmoothFactor p.X logIndex beta → 2 ≤ beta.length →
        (∀ n : ℕ,
          ‖dynamicPreliminaryComponent (some logIndex) zbag mbag n‖ ≤
            Bcoeff) →
          componentIntegral p.X p.H 1 p.q
            (dynamicD12FactorizedCoeff delta logIndex zbag mbag)
            p.beta p.eta component ≤
          2 * κ ^ 2 *
            ((∫ u in (-P)..P, perronWeight u) ^ 2 *
              (Cm * ((p.q : ℝ) * stationaryWidth p.beta p.H +
                Real.rpow p.X delta) * stationaryWidth p.beta p.H *
                ((p.q : ℝ) * T) * (1 + Real.log (8 * p.X)) ^ Em) +
              ((componentEndpoints p.X p.beta p.eta component).2 -
                (componentEndpoints p.X p.beta p.eta component).1) *
              (2 * stationaryWidth p.beta p.H *
                (Fintype.card (DirichletCharacter ℂ p.q) : ℝ) *
                (Bcoeff * Real.sqrt (factorLowerProduct
                  (sortedComponentFactorList logIndex zbag mbag)) *
                  Real.log (2 + P) / P)) ^ 2) := by
  obtain ⟨κ, hκ, htransfer⟩ :=
    exists_d12_component_cutoff_transfer K hK
  obtain ⟨Cm, hCm, Em, hmoment⟩ :=
    exists_uniform_factoredD12Moment K
  refine ⟨κ, Cm, hκ, hCm, Em, ?_⟩
  intro p inst delta H₀ P T rho exponent Bcoeff k hp hX hdelta hdelta1 hk
    hP hP1 hBcoeff hrho hrhoT hXrho hrange component hband hlen
    logIndex zbag mbag s hs beta htail hbeta hbetaLen hcoeff
  rcases hp with ⟨hHone, hHX, hq, hcop, heta, hetaOne, hbetabound,
    hetaBound, hbetane, hsourceMask⟩
  have hX1 : 1 ≤ p.X := by linarith
  have hX0 : 0 ≤ p.X := by linarith
  have hU : 0 ≤ stationaryWidth p.beta p.H := by
    unfold stationaryWidth
    positivity
  have hY : 1 ≤ (factorLowerProduct
      (sortedComponentFactorList logIndex zbag mbag) : ℝ) := by
    have hone : ∀ f ∈ sortedComponentFactorList logIndex zbag mbag, 1 ≤ f.length :=
      fun f hf => dynamicComponentFactorList_length_one logIndex zbag mbag hf
    exact_mod_cast factorLowerProduct_one _ hone
  have hsupport := dynamicPreliminaryComponent_supportedNear_fixedOrder
    hX1 hK hk logIndex zbag mbag
  have hcoeff' : ∀ n : ℕ,
      ‖dynamicPreliminaryComponent (some logIndex) zbag mbag n‖ ≤ Bcoeff := hcoeff
  have htrans := htransfer (X := p.X) (H := p.H) (beta := p.beta)
    (eta := p.eta) (Y := (factorLowerProduct
      (sortedComponentFactorList logIndex zbag mbag) : ℝ)) (P := P)
    (B := Bcoeff) (q := p.q)
    (f := dynamicPreliminaryComponent (some logIndex) zbag mbag)
    hX0 (by linarith) heta hetaOne
    hY hP1 hBcoeff hsupport hcoeff' component
  let a' := (componentEndpoints p.X p.beta p.eta component).1 - P
  let b' := (componentEndpoints p.X p.beta p.eta component).2 + P
  have hab' : a' ≤ b' := by
    dsimp [a', b']
    have hab := componentEndpoints_mono (beta := p.beta) hX0 heta hetaOne component
    linarith
  have hlen' : (b' + stationaryWidth p.beta p.H) -
      (a' - stationaryWidth p.beta p.H) + 1 ≤ T := by
    dsimp [a', b']
    linarith [hlen]
  have hband' : ∀ t ∈ Set.Icc (a' - stationaryWidth p.beta p.H)
      (b' + stationaryWidth p.beta p.H),
      rho ≤ |t| ∧ |t| ≤ T := by
    intro t ht
    apply hband t
    simpa [a', b', add_assoc, add_left_comm, add_comm] using ht
  have hM := hmoment (X := p.X) (delta := delta)
    (U := stationaryWidth p.beta p.H) (T := T) (rho := rho)
    (a := a') (b := b') (exponent := exponent) (k := k) (q := p.q)
    hX hdelta hdelta1 hk hU hrange hrho hrhoT hXrho hab' hlen' hband'
    logIndex zbag mbag beta none hbeta hbetaLen
    (by intro f hf; exact False.elim (by simpa using hf))
  have hsmall : classifierShortPrefix (delta := delta) logIndex zbag mbag =
      List.take s (sortedComponentFactorList logIndex zbag mbag) := by
    rw [classifierShortPrefix_eq_take, hs]
  have hsource := dynamicD12FactorizedCoeff_eq_masked
    (X := p.X) hX1 delta hK logIndex zbag mbag
  have hmask := maskedDynamicComponentV3_eq_intervalCutoff hX0
    logIndex zbag mbag
  have hmass : ∀ t : ℝ,
      characterMovingMass (fun chi : DirichletCharacter ℂ p.q => fun v =>
        ‖halfLineDirichletPolynomial
          (factorLowerProduct (sortedComponentFactorList logIndex zbag mbag) : ℝ)
          ((2 : ℝ) ^ (2 * K))
          (characterTwist (fun n => chi n)
            (dynamicPreliminaryComponent (some logIndex) zbag mbag)) v‖)
        (stationaryWidth p.beta p.H) t =
      factoredTypeD12Mass
        (shortPrefixNormField p.q
          (factorUpperProduct
            (List.take s (sortedComponentFactorList logIndex zbag mbag)))
          (shortPrefixCoefficient zbag mbag
            (List.take s (sortedComponentFactorList logIndex zbag mbag))))
        (sourceSmoothNorm p.q beta) (optionalSmoothNorm p.q none)
        (stationaryWidth p.beta p.H) t := by
    intro t
    exact perron_full_carrier_eq_factored_one hX1 hK hk logIndex zbag mbag s beta
      htail (U := stationaryWidth p.beta p.H) t
  have hmassInt :
      (∫ t in a'..b',
        (characterMovingMass (fun chi : DirichletCharacter ℂ p.q => fun v =>
          ‖halfLineDirichletPolynomial
            (factorLowerProduct (sortedComponentFactorList logIndex zbag mbag) : ℝ)
            ((2 : ℝ) ^ (2 * K))
            (characterTwist (fun n => chi n)
              (dynamicPreliminaryComponent (some logIndex) zbag mbag)) v‖)
          (stationaryWidth p.beta p.H) t) ^ 2) ≤
      Cm * ((p.q : ℝ) * stationaryWidth p.beta p.H + Real.rpow p.X delta) *
        stationaryWidth p.beta p.H * ((p.q : ℝ) * T) *
        (1 + Real.log (8 * p.X)) ^ Em := by
    rw [hsmall] at hM
    convert hM using 1
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp
    rw [hmass t]
  have hrewrite :
      componentIntegral p.X p.H 1 p.q
        (dynamicD12FactorizedCoeff delta logIndex zbag mbag)
        p.beta p.eta component =
      componentIntegral p.X p.H 1 p.q
        (intervalCutoff (openSourceLeft p.X) (2 * p.X)
          (dynamicPreliminaryComponent (some logIndex) zbag mbag))
        p.beta p.eta component := by
    rw [hsource, hmask]
  rw [hrewrite]
  have htransfer' := htrans
  dsimp only at htransfer'
  have hupper := htransfer'
  calc
    _ ≤ 2 * κ ^ 2 *
        ((∫ u in (-P)..P, perronWeight u) ^ 2 *
          (∫ s in a'..b',
            (characterMovingMass (fun chi : DirichletCharacter ℂ p.q => fun v =>
              ‖halfLineDirichletPolynomial
                (factorLowerProduct (sortedComponentFactorList logIndex zbag mbag) : ℝ)
                ((2 : ℝ) ^ (2 * K))
                (characterTwist (fun n => chi n)
                  (dynamicPreliminaryComponent (some logIndex) zbag mbag)) v‖)
              (stationaryWidth p.beta p.H) s) ^ 2) +
          ((componentEndpoints p.X p.beta p.eta component).2 -
            (componentEndpoints p.X p.beta p.eta component).1) *
          (2 * stationaryWidth p.beta p.H *
            (Fintype.card (DirichletCharacter ℂ p.q) : ℝ) *
            (Bcoeff * Real.sqrt (factorLowerProduct
              (sortedComponentFactorList logIndex zbag mbag)) *
              Real.log (2 + P) / P)) ^ 2) := hupper
    _ ≤ _ := by
      gcongr

end
end MRTDynamicD12AnnulusMomentAssembly

#print axioms MRTDynamicD12AnnulusMomentAssembly.componentIntegral_d12_one_le_uniform_moment

namespace MRTDynamicD12AnnulusMomentAssembly

open scoped BigOperators ArithmeticFunction
open ArithmeticFunction MeasureTheory
open MAPMRTCorollary53Source MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTCorollary25Minkowski MAPMRTProposition51Source
open MAPMRTProposition61TypeD1FirstInequality
open MAPDynamicHBSourceV3 MAPHBPerronSourceData
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicFactorExtractionV3 MRTLemma215DynamicSupportV3
open MRTLemma215DynamicRegroupingV3 MRTLemma215DynamicTypeIIFiniteEnvelopeV3
open MRTLemma215DynamicHighPacketCertificateV3 MRTLemma215ScaleClassifierV3
open MRTDynamicD12UniformFullMoment MRTDynamicD12FactorExtraction
open MRTDynamicD12LiteralMass MRTDynamicD12MomentSource MRTDynamicD12ShortPrefix
open MRTDynamicD12CarrierIdentities MRTDynamicD12AnnulusGeometry
open MRTDynamicD12CoefficientBound MRTDynamicD12PerronMassAssembly
open MRTDynamicD12SourceSupport MRTLemma215OpenIntervalCutoffV3

noncomputable section

/-- The corresponding active d2 bag with its second literal smooth shell. -/
theorem componentIntegral_d12_two_le_uniform_moment
    (K : ℕ) (hK : 1 ≤ K) :
    ∃ κ Cm : ℝ, 0 < κ ∧ 0 < Cm ∧ ∃ Em : ℕ,
      ∀ {p : Corollary53Input} [NeZero p.q]
        {delta H₀ P T rho exponent Bcoeff : ℝ} {k : ℕ},
        Corollary53Admissible 1 1 p →
        3 ≤ p.X → 0 ≤ delta → delta ≤ 1 → k < K →
        0 ≤ P → 1 ≤ P → 0 ≤ Bcoeff →
        0 < rho → rho ≤ T → 2 * p.X ≤ rho ^ 2 →
        DynamicD12MomentRange (8 * p.X) T exponent p.q
          (hbFactorCutoff p.X) →
        (component : OuterComponent) →
        (∀ t ∈ Set.Icc
          ((componentEndpoints p.X p.beta p.eta component).1 - (P +
            stationaryWidth p.beta p.H))
          ((componentEndpoints p.X p.beta p.eta component).2 + (P +
            stationaryWidth p.beta p.H)),
          rho ≤ |t| ∧ |t| ≤ T) →
        ((componentEndpoints p.X p.beta p.eta component).2 + (P +
            stationaryWidth p.beta p.H)) -
          ((componentEndpoints p.X p.beta p.eta component).1 - (P +
            stationaryWidth p.beta p.H)) + 1 ≤ T →
        (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X))) →
        (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff p.X)))) k) →
        (mbag : Sym (Option (Fin
          (sourceDyadicCount ⌊dynamicHBCutoff p.X K⌋₊))) (k + 1)) →
        (s : ℕ) →
        s = largestSmallPrefix
          (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
          (Real.rpow p.X delta) →
        (beta gamma : NatDyadicFactor) →
        (sortedComponentFactorList logIndex zbag mbag).drop s = [beta, gamma] →
        IsSourceSmoothFactor p.X logIndex beta → 2 ≤ beta.length →
        IsSourceSmoothFactor p.X logIndex gamma → 2 ≤ gamma.length →
        (∀ n : ℕ,
          ‖dynamicPreliminaryComponent (some logIndex) zbag mbag n‖ ≤ Bcoeff) →
          componentIntegral p.X p.H 1 p.q
            (dynamicD12FactorizedCoeff delta logIndex zbag mbag)
            p.beta p.eta component ≤
          2 * κ ^ 2 *
            ((∫ u in (-P)..P, perronWeight u) ^ 2 *
              (Cm * ((p.q : ℝ) * stationaryWidth p.beta p.H +
                Real.rpow p.X delta) * stationaryWidth p.beta p.H *
                ((p.q : ℝ) * T) * (1 + Real.log (8 * p.X)) ^ Em) +
              ((componentEndpoints p.X p.beta p.eta component).2 -
                (componentEndpoints p.X p.beta p.eta component).1) *
              (2 * stationaryWidth p.beta p.H *
                (Fintype.card (DirichletCharacter ℂ p.q) : ℝ) *
                (Bcoeff * Real.sqrt (factorLowerProduct
                  (sortedComponentFactorList logIndex zbag mbag)) *
                  Real.log (2 + P) / P)) ^ 2) := by
  obtain ⟨κ, hκ, htransfer⟩ :=
    exists_d12_component_cutoff_transfer K hK
  obtain ⟨Cm, hCm, Em, hmoment⟩ := exists_uniform_factoredD12Moment K
  refine ⟨κ, Cm, hκ, hCm, Em, ?_⟩
  intro p inst delta H₀ P T rho exponent Bcoeff k hp hX hdelta hdelta1 hk
    hP hP1 hBcoeff hrho hrhoT hXrho hrange component hband hlen
    logIndex zbag mbag s hs beta gamma htail hbeta hbetaLen hgamma hgammaLen hcoeff
  rcases hp with ⟨hHone, hHX, hq, hcop, heta, hetaOne, hbetabound,
    hetaBound, hbetane, hsourceMask⟩
  have hX1 : 1 ≤ p.X := by linarith
  have hX0 : 0 ≤ p.X := by linarith
  have hU : 0 ≤ stationaryWidth p.beta p.H := by
    unfold stationaryWidth
    positivity
  have hY : 1 ≤ (factorLowerProduct
      (sortedComponentFactorList logIndex zbag mbag) : ℝ) := by
    have hone : ∀ f ∈ sortedComponentFactorList logIndex zbag mbag, 1 ≤ f.length :=
      fun f hf => dynamicComponentFactorList_length_one logIndex zbag mbag hf
    exact_mod_cast factorLowerProduct_one _ hone
  have hsupport := dynamicPreliminaryComponent_supportedNear_fixedOrder
    hX1 hK hk logIndex zbag mbag
  have htrans := htransfer (X := p.X) (H := p.H) (beta := p.beta)
    (eta := p.eta) (Y := (factorLowerProduct
      (sortedComponentFactorList logIndex zbag mbag) : ℝ)) (P := P)
    (B := Bcoeff) (q := p.q)
    (f := dynamicPreliminaryComponent (some logIndex) zbag mbag)
    hX0 (by linarith) heta hetaOne hY hP1 hBcoeff hsupport hcoeff component
  let a' := (componentEndpoints p.X p.beta p.eta component).1 - P
  let b' := (componentEndpoints p.X p.beta p.eta component).2 + P
  have hab' : a' ≤ b' := by
    dsimp [a', b']
    have hab := componentEndpoints_mono (beta := p.beta) hX0 heta hetaOne component
    linarith
  have hlen' : (b' + stationaryWidth p.beta p.H) -
      (a' - stationaryWidth p.beta p.H) + 1 ≤ T := by
    dsimp [a', b']
    linarith [hlen]
  have hband' : ∀ t ∈ Set.Icc (a' - stationaryWidth p.beta p.H)
      (b' + stationaryWidth p.beta p.H), rho ≤ |t| ∧ |t| ≤ T := by
    intro t ht
    apply hband t
    simpa [a', b', add_assoc, add_left_comm, add_comm] using ht
  have hM := hmoment (X := p.X) (delta := delta)
    (U := stationaryWidth p.beta p.H) (T := T) (rho := rho)
    (a := a') (b := b') (exponent := exponent) (k := k) (q := p.q)
    hX hdelta hdelta1 hk hU hrange hrho hrhoT hXrho hab' hlen' hband'
    logIndex zbag mbag beta (some gamma) hbeta hbetaLen
    (by intro f hf; cases hf; exact ⟨hgamma, hgammaLen⟩)
  have hsmall : classifierShortPrefix (delta := delta) logIndex zbag mbag =
      List.take s (sortedComponentFactorList logIndex zbag mbag) := by
    rw [classifierShortPrefix_eq_take, hs]
  have hsource := dynamicD12FactorizedCoeff_eq_masked
    (X := p.X) hX1 delta hK logIndex zbag mbag
  have hmask := maskedDynamicComponentV3_eq_intervalCutoff hX0
    logIndex zbag mbag
  have hmass : ∀ t : ℝ,
      characterMovingMass (fun chi : DirichletCharacter ℂ p.q => fun v =>
        ‖halfLineDirichletPolynomial
          (factorLowerProduct (sortedComponentFactorList logIndex zbag mbag) : ℝ)
          ((2 : ℝ) ^ (2 * K))
          (characterTwist (fun n => chi n)
            (dynamicPreliminaryComponent (some logIndex) zbag mbag)) v‖)
        (stationaryWidth p.beta p.H) t =
      factoredTypeD12Mass
        (shortPrefixNormField p.q
          (factorUpperProduct
            (List.take s (sortedComponentFactorList logIndex zbag mbag)))
          (shortPrefixCoefficient zbag mbag
            (List.take s (sortedComponentFactorList logIndex zbag mbag))))
        (sourceSmoothNorm p.q beta) (optionalSmoothNorm p.q (some gamma))
        (stationaryWidth p.beta p.H) t := by
    intro t
    exact perron_full_carrier_eq_factored_two hX1 hK hk logIndex zbag mbag s beta gamma
      htail (U := stationaryWidth p.beta p.H) t
  have hmassInt :
      (∫ t in a'..b',
        (characterMovingMass (fun chi : DirichletCharacter ℂ p.q => fun v =>
          ‖halfLineDirichletPolynomial
            (factorLowerProduct (sortedComponentFactorList logIndex zbag mbag) : ℝ)
            ((2 : ℝ) ^ (2 * K))
            (characterTwist (fun n => chi n)
              (dynamicPreliminaryComponent (some logIndex) zbag mbag)) v‖)
          (stationaryWidth p.beta p.H) t) ^ 2) ≤
      Cm * ((p.q : ℝ) * stationaryWidth p.beta p.H + Real.rpow p.X delta) *
        stationaryWidth p.beta p.H * ((p.q : ℝ) * T) *
        (1 + Real.log (8 * p.X)) ^ Em := by
    rw [hsmall] at hM
    convert hM using 1
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp
    rw [hmass t]
  have hrewrite :
      componentIntegral p.X p.H 1 p.q
        (dynamicD12FactorizedCoeff delta logIndex zbag mbag)
        p.beta p.eta component =
      componentIntegral p.X p.H 1 p.q
        (intervalCutoff (openSourceLeft p.X) (2 * p.X)
          (dynamicPreliminaryComponent (some logIndex) zbag mbag))
        p.beta p.eta component := by
    rw [hsource, hmask]
  rw [hrewrite]
  have htransfer' := htrans
  dsimp only at htransfer'
  calc
    _ ≤ 2 * κ ^ 2 *
        ((∫ u in (-P)..P, perronWeight u) ^ 2 *
          (∫ s in a'..b',
            (characterMovingMass (fun chi : DirichletCharacter ℂ p.q => fun v =>
              ‖halfLineDirichletPolynomial
                (factorLowerProduct (sortedComponentFactorList logIndex zbag mbag) : ℝ)
                ((2 : ℝ) ^ (2 * K))
                (characterTwist (fun n => chi n)
                  (dynamicPreliminaryComponent (some logIndex) zbag mbag)) v‖)
              (stationaryWidth p.beta p.H) s) ^ 2) +
          ((componentEndpoints p.X p.beta p.eta component).2 -
            (componentEndpoints p.X p.beta p.eta component).1) *
          (2 * stationaryWidth p.beta p.H *
            (Fintype.card (DirichletCharacter ℂ p.q) : ℝ) *
            (Bcoeff * Real.sqrt (factorLowerProduct
              (sortedComponentFactorList logIndex zbag mbag)) *
              Real.log (2 + P) / P)) ^ 2) := htransfer'
    _ ≤ _ := by
      gcongr

#print axioms MRTDynamicD12AnnulusMomentAssembly.componentIntegral_d12_two_le_uniform_moment

end
end MRTDynamicD12AnnulusMomentAssembly
