import MRTLemma215DynamicPacketCriticalLineV3

/-! # Open-left clipped packet component integrals -/

namespace MRTLemma215DynamicPacketComponentIntegralV3

set_option maxHeartbeats 800000

open scoped BigOperators
open MeasureTheory
open MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTCorollary25TypeD1LiteralWeld
open MAPMRTCorollary25TypeD1IntegratedWeld
open MAPMRTCorollary25Minkowski
open MAPFarAnnulusMRT MAPFarAnnulusSourceToModel
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MRTLemma215DynamicPacketCriticalLineV3
open MRTLemma215DynamicHighPacketIndexV3
open MRTLemma215DynamicHighPacketAggregateV3
open MRTLemma215DynamicHighPacketFlattenV3

noncomputable section

theorem characterWindow_intervalConvolution_eq_movingMass_open
    {X L H beta : ℝ} {q N M : ℕ} {alpha gamma : ℕ → ℂ}
    (hN : 1 ≤ N) (hM : 1 ≤ M)
    (halpha : SupportedNatDyadic N alpha)
    (hgamma : SupportedNatDyadic M gamma) (t : ℝ) :
    characterWindow X 1 q
        (intervalCutoff L (2 * X)
          (literalDirichletConvolution alpha gamma)) beta H t =
      characterMovingMass
        (typeD1ClippedNorm (N : ℝ) (M : ℝ) L (2 * X)
          (fun chi : DirichletCharacter ℂ q ↦ fun n ↦ chi n)
          alpha gamma) (stationaryWidth beta H) t := by
  unfold characterWindow characterMovingMass movingIntegral stationaryWidth
    typeD1ClippedNorm
  apply Finset.sum_congr rfl
  intro chi hchi
  apply intervalIntegral.integral_congr
  intro s hs
  change ‖criticalDirichletPolynomial X 1 q
      (intervalCutoff L (2 * X) (literalDirichletConvolution alpha gamma))
      chi s‖ =
    ‖halfLineDirichletPolynomial ((N : ℝ) * M) 4
      (intervalCutoff L (2 * X)
        (characterTwist (fun n => chi n)
          (literalDirichletConvolution alpha gamma))) s‖
  rw [criticalDirichletPolynomial_intervalConvolution_eq_clipped_open
    hN hM halpha hgamma chi s]

theorem componentIntegral_intervalConvolution_eq_clipped_open
    {X L H beta eta : ℝ} {q N M : ℕ} {alpha gamma : ℕ → ℂ}
    (hN : 1 ≤ N) (hM : 1 ≤ M)
    (halpha : SupportedNatDyadic N alpha)
    (hgamma : SupportedNatDyadic M gamma)
    (component : OuterComponent) :
    componentIntegral X H 1 q
        (intervalCutoff L (2 * X)
          (literalDirichletConvolution alpha gamma))
        beta eta component =
      ∫ t in (componentEndpoints X beta eta component).1..
        (componentEndpoints X beta eta component).2,
        (characterMovingMass
          (typeD1ClippedNorm (N : ℝ) (M : ℝ) L (2 * X)
            (fun chi : DirichletCharacter ℂ q ↦ fun n ↦ chi n)
            alpha gamma) (stationaryWidth beta H) t) ^ 2 := by
  unfold componentIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  change characterWindow X 1 q
      (intervalCutoff L (2 * X) (literalDirichletConvolution alpha gamma))
      beta H t ^ 2 =
    characterMovingMass
      (typeD1ClippedNorm (N : ℝ) (M : ℝ) L (2 * X)
        (fun chi : DirichletCharacter ℂ q ↦ fun n ↦ chi n)
        alpha gamma) (stationaryWidth beta H) t ^ 2
  rw [characterWindow_intervalConvolution_eq_movingMass_open
    hN hM halpha hgamma t]

/-- Packet specialization, now a short wrapper around the generic component
identity rather than a repeated expansion of the nested integrals. -/
theorem componentIntegral_branchHighPacket_eq_clipped
    {X H beta eta delta H₀ : ℝ}
    {hX : 2 ≤ X} {hdelta : 0 < delta}
    {K q : ℕ} {branch : Fin K}
    (packet : DynamicBranchHighPacketIndexV3 (H₀ := H₀) hX hdelta branch)
    (L : ℝ) (component : OuterComponent) :
    componentIntegral X H 1 q
        (intervalCutoff L (2 * X) (branchHighPacketConvolutionV3 packet))
        beta eta component =
      ∫ t in (componentEndpoints X beta eta component).1..
        (componentEndpoints X beta eta component).2,
        (characterMovingMass
          (typeD1ClippedNorm
            (highPacketLongLengthV3 (branchHighPacketToGlobalV3 packet) : ℝ)
            (highPacketShortLengthV3 (branchHighPacketToGlobalV3 packet) : ℝ)
            L (2 * X)
            (fun chi : DirichletCharacter ℂ q ↦ fun n ↦ chi n)
            (highPacketLongCoeffV3 (branchHighPacketToGlobalV3 packet))
            (highPacketShortCoeffV3 (branchHighPacketToGlobalV3 packet)))
          (stationaryWidth beta H) t) ^ 2 := by
  let gp := branchHighPacketToGlobalV3 packet
  have hgeom := highPacket_geometryV3 gp
  have hsupp := highPacket_supportV3 gp
  rw [show intervalCutoff L (2 * X) (branchHighPacketConvolutionV3 packet) =
      intervalCutoff L (2 * X)
        (literalDirichletConvolution (highPacketLongCoeffV3 gp)
          (highPacketShortCoeffV3 gp)) by
    funext n
    unfold intervalCutoff
    split_ifs
    · exact branchHighPacketConvolution_apply_eq_literal_long_short packet n
    · rfl]
  exact componentIntegral_intervalConvolution_eq_clipped_open
    (by omega) (by omega) hsupp.2 hsupp.1 component

end
end MRTLemma215DynamicPacketComponentIntegralV3

#print axioms MRTLemma215DynamicPacketComponentIntegralV3.characterWindow_intervalConvolution_eq_movingMass_open
#print axioms MRTLemma215DynamicPacketComponentIntegralV3.componentIntegral_intervalConvolution_eq_clipped_open
#print axioms MRTLemma215DynamicPacketComponentIntegralV3.componentIntegral_branchHighPacket_eq_clipped
