import MRTDynamicD12GlobalScalarBridgeV3
import MRTDynamicD12CanonicalScalarEnvelope
import MRTDynamicD12CanonicalCutoffEventually
import MRTDynamicD12CanonicalPerBagThreeTerm
import MRTDynamicD12ParameterPackage
import MRTDynamicD12ModulusSavings
import MRTDynamicD12CanonicalApertureQuotient

namespace MRTDynamicD12CanonicalProducer

open Filter
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPDynamicHBSourceV3 MAPAllCenterApertureTransfer
open MAPFarSourceWeldScaffold MAPMRTProposition51Supported
open MRTDynamicD12LiteralMass MRTDynamicD12ParameterPackage
open MRTDynamicD12CanonicalSourceLedger
open MRTDynamicD12ActiveCanonicalLedger
open MRTDynamicD12CanonicalScalarEnvelope
open MRTDynamicD12CanonicalCutoffEventually
open MRTDynamicD12CanonicalPerBagThreeTerm
open MRTDynamicD12GlobalScalarBridgeV3
open MRTDynamicD12ModulusSavings
open MRTProposition61TypeIIEndpointWidthV3
open MRTLemma215DynamicTypeIIGlobalCountV3
open MRTLemma215DynamicSupportV3 MRTLemma215DynamicRegroupingV3
open MRTDynamicD12CutoffPruning
open MAPFinishDynamicLowTypes
open MRTDynamicD12CanonicalApertureQuotient

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
local instance (P : Prop) : Decidable P := Classical.propDecidable P

private theorem baseAperture_eventually_gt_one
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ X : ℝ in atTop, 1 < baseAperture epsilon X := by
  have hrho : 0 < 2 / 15 + apertureReserve epsilon := by
    have h := apertureReserve_pos hepsilon
    linarith
  have hpow := (tendsto_rpow_atTop hrho).eventually
    (eventually_gt_atTop (2 : ℝ))
  filter_upwards [hpow] with X hX
  change 2 < Real.rpow X (2 / 15 + apertureReserve epsilon) at hX
  change 1 < (1 / 2 : ℝ) * Real.rpow X
    (2 / 15 + apertureReserve epsilon)
  have hh := mul_lt_mul_of_pos_left hX
    (by norm_num : (0 : ℝ) < 1 / 2)
  linarith

theorem exists_d12_canonical_perbag
    (delta epsilon : ℝ) (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 240) (hepsilon : 0 < epsilon) :
    D12CanonicalPerBagThreeTerm delta epsilon hdelta hepsilon := by
  obtain ⟨D, hD, kappa1, Cm1, hk1, hCm1, Em1,
      kappa2, Cm2, hk2, hCm2, Em2, hsource⟩ :=
    exists_active_canonical_source_ledger delta (1 / 1000 : ℝ)
      hdelta hdeltaUpper (by norm_num)
  obtain ⟨Cd, hCd, hCdall⟩ :=
    exists_uniform_d12_modulus_constant
  obtain ⟨Bmin, hBmin⟩ := exists_d12_parameter_package
  let C₁ : ℝ :=
    288 * kappa1 ^ 2 * Cm1 * Cd * 5 ^ Em1 +
      72 * kappa1 ^ 2 * D ^ 2 * Cd * 5 ^ Em1 + 1
  let C₂ : ℝ :=
    288 * kappa2 ^ 2 * Cm2 * Cd * 5 ^ Em2 +
      72 * kappa2 ^ 2 * D ^ 2 * Cd * 5 ^ Em2 + 1
  let C : ℝ := max C₁ C₂
  let E : ℕ := max (Em1 + 2) (Em2 + 2)
  refine ⟨C, ?_, E, Bmin, ?_⟩
  · dsimp [C, C₁, C₂]
    have h1 : 0 < C₁ := by positivity
    have h2 : 0 < C₂ := by positivity
    exact lt_of_lt_of_le h1 (le_max_left _ _)
  intro B hB
  obtain ⟨Ccmin, hCcmin⟩ := hBmin B hB
  refine ⟨Ccmin, ?_⟩
  intro Cc hCc
  filter_upwards [hCcmin Cc hCc,
      eventually_two_le_floor_dynamicHBCutoff hdelta,
      eventually_ge_atTop (3 : ℝ), baseAperture_eventually_gt_one hepsilon]
      with X hpackX hcutX hX3 hbase
  have hlog : 1 ≤ Real.log X := log_one_le hX3
  intro q a beta
  dsimp only
  intro hq hqQ ha hcop hbeta hfar
  let Q : ℝ := (Real.log X) ^ B
  let H : ℝ := baseAperture epsilon X
  let eta : ℝ := 1 / Real.sqrt Q
  let p := mapCorollary53Input X H q a beta eta
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    exact one_le_pow₀ hlog
  have hHone : 1 < H := by simpa [H] using hbase
  have hHX : H ≤ X := by
    dsimp [H]
    exact (MAPMRTProposition51Supported.baseAperture_le_half_of_one_le
      (epsilon := epsilon) (by linarith : 1 ≤ X)).trans (by linarith)
  have hq₀ : q ≠ 0 := by omega
  letI : NeZero q := ⟨hq₀⟩
  have hp : Corollary53Admissible 1 1 p := by
    simpa [p, Q, H, eta] using
      MAPFarSourceWeldScaffold.selectedMapInput_admissible_one hlog hQ hHone hHX
        hq hcop hbeta hfar
  have hbetaNe : p.beta ≠ 0 := by
    intro hz
    have hfar0 : 2 * (Real.log X) ^ Cc <
        stationaryWidth p.beta p.H := by simpa [p, H] using hfar
    rw [hz] at hfar0
    simp [stationaryWidth] at hfar0
    have hCc0 : 0 ≤ (Real.log X) ^ Cc := by positivity
    linarith
  letI : NeZero p.q := ⟨hq₀⟩
  have hXp : 2 ≤ p.X := by
    simpa [p] using (show 2 ≤ X by linarith)
  let reserve : ℝ := apertureReserve epsilon
  have hr0 : 0 ≤ reserve := by
    dsimp [reserve]
    exact (apertureReserve_pos hepsilon).le
  have hr : reserve ≤ 1 / 1200 := by
    dsimp [reserve, apertureReserve]
    exact min_le_right _ _
  have hHdef : p.H = (1 / 2 : ℝ) *
      Real.rpow p.X (2 / 15 + reserve) := by
    dsimp [p, H, reserve, baseAperture]
    rfl
  have heta : p.eta = 1 / Real.sqrt ((Real.log p.X) ^ B) := by
    rfl
  have hpX : p.X = X := by rfl
  obtain ⟨pack⟩ := hpackX p hp hpX reserve hr0 hr hHdef heta hqQ hbeta hfar hXp
  have hUone : 1 ≤ stationaryWidth p.beta p.H := by
    have hfar' : 2 * (Real.log p.X) ^ Cc <
        stationaryWidth p.beta p.H := by simpa [p, H] using hfar
    have hpowCc : 1 ≤ (Real.log p.X) ^ Cc := by
      exact one_le_pow₀ (by simpa [hpX] using hlog)
    linarith
  have hD4 : 0 ≤ (divisorCount p.q : ℝ) ^ 4 := by positivity
  have hD4bound : (divisorCount p.q : ℝ) ^ 4 ≤
      Cd * Real.rpow (p.q : ℝ) (1 / 8 : ℝ) :=
    hCdall p.q (by exact_mod_cast (show 1 ≤ p.q by exact hq))
  have hQpack : pack.Q = Q := by
    simpa [Q, hpX] using pack.hQ
  have hUeq : stationaryWidth p.beta p.H = |p.beta| * p.H := by
    rfl
  have hPle : pack.P ≤ X := by
    rw [pack.hP]
    have hpow : Real.rpow X (23 / 24 : ℝ) ≤ X := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by linarith)
          (by norm_num : (23 / 24 : ℝ) ≤ 1)
    have hden1 : (1 : ℝ) ≤ (p.q : ℝ) * Q := by
      have hq1 : (1 : ℝ) ≤ (p.q : ℝ) := by exact_mod_cast hq
      nlinarith
    have hdenpos : 0 < (p.q : ℝ) * Q := by positivity
    have hbeta1 : |p.beta| ≤ 1 :=
      hbeta.trans ((div_le_iff₀ hdenpos).2 (by nlinarith))
    exact (mul_le_mul_of_nonneg_left hpow (abs_nonneg _)).trans
      (by nlinarith [hbeta1, hpow])
  have hDelta0 (component : OuterComponent) : 0 ≤
      (componentEndpoints p.X p.beta p.eta component).2 -
        (componentEndpoints p.X p.beta p.eta component).1 := by
    have heta0 : 0 ≤ p.eta := by rw [heta]; positivity
    have heta1 : p.eta ≤ 1 := by
      have hsq : 1 ≤ Real.sqrt Q := Real.one_le_sqrt.2 hQ
      have := (div_le_one (Real.sqrt_pos.2 (by positivity))).2 hsq
      simpa [eta, p] using this
    have hprod : 0 ≤ |p.beta| * p.X :=
      mul_nonneg (abs_nonneg _) (by linarith [hXp])
    have hsqeta : p.eta * p.eta ≤ 1 := by
      nlinarith [sq_nonneg (1 - p.eta)]
    cases component <;>
      simp [componentEndpoints, outerUpper, outerLower]
    all_goals
      apply (le_div_iff₀ (by rw [heta]; positivity)).2
      have hm := mul_le_mul_of_nonneg_right hsqeta hprod
      convert hm using 1 <;> ring
  have hDelta (component : OuterComponent) :
      (componentEndpoints p.X p.beta p.eta component).2 -
        (componentEndpoints p.X p.beta p.eta component).1 ≤
      |p.beta| * p.X * Real.sqrt Q := by
    have hh := componentEndpoints_sub_le_stationaryWidth_mul
      (X := p.X) (H := p.H) (beta := p.beta) (eta := p.eta)
      (by linarith [hXp]) (by rw [heta]; positivity)
      (by rw [hHdef]; positivity) component
    have heta' : p.eta = 1 / Real.sqrt Q := by
      calc
        p.eta = pack.eta := pack.hpeta
        _ = 1 / Real.sqrt pack.Q := pack.heta
        _ = 1 / Real.sqrt Q := by rw [hQpack]
    rw [hUeq, heta'] at hh
    rw [heta']
    calc
      _ ≤ |p.beta| * p.H * p.X / ((1 / Real.sqrt Q) * p.H) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hh
      _ = |p.beta| * p.X * Real.sqrt Q := by
        have hHpos : 0 < p.H := by positivity
        have hQpos : 0 < Q := by positivity
        field_simp [hHpos.ne', (Real.sqrt_pos.2 hQpos).ne']
  have hXdeltaH :
      Real.rpow p.X delta / p.H ≤
        2 * Real.rpow p.X (delta - 2 / 15 : ℝ) := by
    rw [hHdef]
    exact rpow_div_canonical_aperture_le (by linarith [hXp]) hr0
  have hHupper : p.H ≤ (1 / 2 : ℝ) *
      Real.rpow p.X (2 / 15 + 1 / 1200 : ℝ) := by
    rw [hHdef]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith [hXp]) (by linarith))
      (by norm_num)
  intro branch logIndex zbag mbag component
  let Y : ℕ := factorLowerProduct
    (sortedComponentFactorList logIndex zbag mbag)
  by_cases hprod : 2 * p.X < (Y : ℝ)
  · have hzero := componentIntegral_d12_eq_zero_of_lower_gt_twoX
      (X := p.X) (H := p.H) (beta := p.beta) (eta := p.eta)
      (q := p.q) (delta := delta) (K := hbOrder delta)
      (k := (branch : ℕ)) (by linarith [hXp])
      (hbOrder_one hdelta) branch.isLt logIndex zbag mbag hprod component
    change dynamicLowNormalizationV3 p *
      (if dynamicD12IsActive delta (Real.rpow p.X (delta + 1 / 8))
          logIndex zbag mbag then
        componentIntegral p.X p.H 1 p.q
          (dynamicD12FactorizedCoeff delta logIndex zbag mbag)
          p.beta p.eta component else 0) ≤ _
    split <;> simp [hzero]
    · have hC0 : 0 ≤ C := by dsimp [C]; positivity
      have hlog0 : 0 ≤ Real.log X ^ E := by positivity
      have hW0 : 0 ≤ d12ThreeTermEnvelope delta B X := by
        dsimp [d12ThreeTermEnvelope]
        positivity
      exact mul_nonneg (mul_nonneg hC0 hlog0) hW0
    · have hC0 : 0 ≤ C := by dsimp [C]; positivity
      have hlog0 : 0 ≤ Real.log X ^ E := by positivity
      have hW0 : 0 ≤ d12ThreeTermEnvelope delta B X := by
        dsimp [d12ThreeTermEnvelope]
        positivity
      exact mul_nonneg (mul_nonneg hC0 hlog0) hW0
  · have hY : (Y : ℝ) ≤ 2 * X := by
      have := le_of_not_gt hprod
      simpa [hpX] using this
    have hD4 : 0 ≤ (divisorCount p.q : ℝ) ^ 4 := by positivity
    have hD4bound : (divisorCount p.q : ℝ) ^ 4 ≤
        Cd * Real.rpow (p.q : ℝ) (1 / 8 : ℝ) :=
      hCdall p.q (by exact_mod_cast (show 1 ≤ p.q by exact hq))
    have hDelta0' := hDelta0 component
    have hDelta' := hDelta component
    have hXdeltaH' := hXdeltaH
    have hHupper' := hHupper
    have hcommon :
        ∀ (kappa Cm : ℝ) (Em : ℕ), 0 < kappa → 0 < Cm →
          dynamicLowNormalizationV3 p *
              rawLedger p pack.P pack.Tmom (D * Real.rpow p.X (1 / 1000 : ℝ))
                Y delta kappa Cm Em component ≤
            (288 * kappa ^ 2 * Cm * Cd * 5 ^ Em +
                72 * kappa ^ 2 * D ^ 2 * Cd * 5 ^ Em + 1) *
              Real.log p.X ^ (Em + 2) * d12ThreeTermEnvelope delta B X := by
      intro kappa Cm Em hkappa hCm
      have hs := normalized_rawLedger_le_three_terms
        (p := p) (X := p.X) (Q := pack.Q) (lambda := |p.beta|)
        (H := p.H) (U := stationaryWidth p.beta p.H)
        (P := pack.P) (T := pack.Tmom) (D4 := (divisorCount p.q : ℝ) ^ 4)
        (Cd := Cd) (D := D) (Bcoeff := D * Real.rpow p.X (1 / 1000 : ℝ))
        (kappa := kappa) (Cm := Cm) (Y := Y) (delta := delta) (Em := Em)
        (hpX := hpX) (hX := by linarith [hXp])
        (hlog := by simpa [hpX] using hlog)
        (hQ := by simpa [hQpack] using pack.hQone)
        (hqQ := by simpa [hQpack] using hqQ)
        (hbeta := rfl) (hlambda := abs_pos.mpr hbetaNe)
        (hH := hHdef) (hreserve0 := hr0) (hreserve := hr)
        (hUstat := hUeq) (hUlambda := by simpa [hUeq])
        (hHid := rfl) (hUone := hUone)
        (heta := by simpa [pack.hpeta, hQpack] using heta)
        (hP := by simpa [hQpack] using pack.hP)
        (hT := by simpa [hQpack] using pack.hTmom)
        (hPone := pack.hPone) (hP_le_X := hPle)
        (hBcoeff := rfl) (hD := hD) (hkappa := hkappa) (hCm := hCm)
        (hD4 := hD4) (hCd := le_of_lt hCd)
        (hlambdaCap := by
          rw [show p.beta = beta by rfl, show p.q = q by rfl, hQpack]
          simpa [Q] using hbeta)
        (hD4bound := hD4bound) (hY := hY) (component := component)
        (hDelta0 := hDelta0') (hDelta := by
          rw [hQpack]
          exact hDelta')
        (hXdeltaH := hXdeltaH') (hHupper := hHupper')
      simpa [dynamicLowNormalizationV3, hQpack, hUeq,
        d12ThreeTermEnvelope, p, Q, H, eta] using hs
    have hs1 := hcommon kappa1 Cm1 Em1 hk1 hCm1
    have hs2 := hcommon kappa2 Cm2 Em2 hk2 hCm2
    have hR1 : 0 ≤ rawLedger p pack.P pack.Tmom
        (D * Real.rpow p.X (1 / 1000 : ℝ)) Y delta kappa1 Cm1 Em1 component := by
      unfold rawLedger
      have hPpos : 0 < pack.P := by
        rw [pack.hP]
        exact mul_pos (abs_pos.mpr hbetaNe) (Real.rpow_pos_of_pos (by linarith [hXp]) _)
      have hTpos : 0 ≤ pack.Tmom := by rw [pack.hTmom]; positivity
      have hY0 : 0 ≤ (Y : ℝ) := by positivity
      have hwidth0 := hDelta0 component
      have hLpos : 0 ≤ 1 + Real.log (8 * p.X) := by
        have : 0 ≤ Real.log (8 * p.X) := Real.log_nonneg (by linarith [hXp])
        linarith
      have hq0 : 0 ≤ (p.q : ℝ) := by positivity
      have hU0 : 0 ≤ stationaryWidth p.beta p.H := by linarith [hUone]
      have hD0 : 0 ≤ D := le_of_lt hD
      have hK0 : 0 ≤ kappa1 := le_of_lt hk1
      have hCm0 : 0 ≤ Cm1 := le_of_lt hCm1
      have hmainInner : 0 ≤ Cm1 * ((p.q : ℝ) * stationaryWidth p.beta p.H +
          Real.rpow p.X delta) * stationaryWidth p.beta p.H *
          ((p.q : ℝ) * pack.Tmom) * (1 + Real.log (8 * p.X)) ^ Em1 := by
        have hsum : 0 ≤ (p.q : ℝ) * stationaryWidth p.beta p.H +
            Real.rpow p.X delta :=
          add_nonneg (mul_nonneg hq0 hU0)
            (Real.rpow_nonneg (by linarith [hXp]) _)
        have hqT : 0 ≤ (p.q : ℝ) * pack.Tmom := mul_nonneg hq0 hTpos
        have hLpow : 0 ≤ (1 + Real.log (8 * p.X)) ^ Em1 :=
          pow_nonneg hLpos _
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (mul_nonneg hCm0 hsum) hU0) hqT) hLpow
      exact mul_nonneg (by positivity)
        (add_nonneg
          (mul_nonneg (sq_nonneg _) hmainInner)
          (mul_nonneg hwidth0 (sq_nonneg _)))
    have hR2 : 0 ≤ rawLedger p pack.P pack.Tmom
        (D * Real.rpow p.X (1 / 1000 : ℝ)) Y delta kappa2 Cm2 Em2 component := by
      unfold rawLedger
      have hPpos : 0 < pack.P := by
        rw [pack.hP]
        exact mul_pos (abs_pos.mpr hbetaNe) (Real.rpow_pos_of_pos (by linarith [hXp]) _)
      have hTpos : 0 ≤ pack.Tmom := by rw [pack.hTmom]; positivity
      have hY0 : 0 ≤ (Y : ℝ) := by positivity
      have hwidth0 := hDelta0 component
      have hLpos : 0 ≤ 1 + Real.log (8 * p.X) := by
        have : 0 ≤ Real.log (8 * p.X) := Real.log_nonneg (by linarith [hXp])
        linarith
      have hq0 : 0 ≤ (p.q : ℝ) := by positivity
      have hU0 : 0 ≤ stationaryWidth p.beta p.H := by linarith [hUone]
      have hD0 : 0 ≤ D := le_of_lt hD
      have hK0 : 0 ≤ kappa2 := le_of_lt hk2
      have hCm0 : 0 ≤ Cm2 := le_of_lt hCm2
      have hmainInner : 0 ≤ Cm2 * ((p.q : ℝ) * stationaryWidth p.beta p.H +
          Real.rpow p.X delta) * stationaryWidth p.beta p.H *
          ((p.q : ℝ) * pack.Tmom) * (1 + Real.log (8 * p.X)) ^ Em2 := by
        have hsum : 0 ≤ (p.q : ℝ) * stationaryWidth p.beta p.H +
            Real.rpow p.X delta :=
          add_nonneg (mul_nonneg hq0 hU0)
            (Real.rpow_nonneg (by linarith [hXp]) _)
        have hqT : 0 ≤ (p.q : ℝ) * pack.Tmom := mul_nonneg hq0 hTpos
        have hLpow : 0 ≤ (1 + Real.log (8 * p.X)) ^ Em2 :=
          pow_nonneg hLpos _
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (mul_nonneg hCm0 hsum) hU0) hqT) hLpow
      exact mul_nonneg (by positivity)
        (add_nonneg
          (mul_nonneg (sq_nonneg _) hmainInner)
          (mul_nonneg hwidth0 (sq_nonneg _)))
    have hN : 0 ≤ dynamicLowNormalizationV3 p := by
      unfold dynamicLowNormalizationV3
      have hqpos : 0 < (p.q : ℝ) := by exact_mod_cast hq
      have hUpos : 0 < stationaryWidth p.beta p.H := by linarith [hUone]
      positivity
    have hI := hsource (p := p) (B := B) (Cc := Cc)
      hp (by linarith [hXp]) pack hcutX component
      logIndex zbag mbag branch.isLt
    have hI' :
        (if dynamicD12IsActive delta (Real.rpow p.X (delta + 1 / 8))
            logIndex zbag mbag then
          componentIntegral p.X p.H 1 p.q
            (dynamicD12FactorizedCoeff delta logIndex zbag mbag)
            p.beta p.eta component else 0) ≤
        max 0 (max
          (rawLedger p pack.P pack.Tmom
            (D * Real.rpow p.X (1 / 1000 : ℝ)) Y delta kappa1 Cm1 Em1 component)
          (rawLedger p pack.P pack.Tmom
            (D * Real.rpow p.X (1 / 1000 : ℝ)) Y delta kappa2 Cm2 Em2 component)) := by
      simpa [Y] using hI
    have hW : 0 ≤ d12ThreeTermEnvelope delta B X := by
      dsimp [d12ThreeTermEnvelope]
      positivity
    have hL : 1 ≤ Real.log p.X := by simpa [hpX] using hlog
    have hN1 := hcommon kappa1 Cm1 Em1 hk1 hCm1
    have hN2 := hcommon kappa2 Cm2 Em2 hk2 hCm2
    have hbound := normalized_active_component_of_scalar_bounds
      (N := dynamicLowNormalizationV3 p)
      (I := if dynamicD12IsActive delta (Real.rpow p.X (delta + 1 / 8))
          logIndex zbag mbag then
        componentIntegral p.X p.H 1 p.q
          (dynamicD12FactorizedCoeff delta logIndex zbag mbag)
          p.beta p.eta component else 0)
      (R₁ := rawLedger p pack.P pack.Tmom
        (D * Real.rpow p.X (1 / 1000 : ℝ)) Y delta kappa1 Cm1 Em1 component)
      (R₂ := rawLedger p pack.P pack.Tmom
        (D * Real.rpow p.X (1 / 1000 : ℝ)) Y delta kappa2 Cm2 Em2 component)
      (C₁ := C₁) (C₂ := C₂) (L := Real.log p.X)
      (W := d12ThreeTermEnvelope delta B X)
      (E₁ := Em1 + 2) (E₂ := Em2 + 2)
      hN hI' hR1 hR2 hL hW (by positivity) (by positivity) hN1 hN2
    simpa [p, Q, H, eta, C, E, C₁, C₂, d12ThreeTermEnvelope,
      hpX, hQpack] using hbound

end
end MRTDynamicD12CanonicalProducer

#print axioms MRTDynamicD12CanonicalProducer.exists_d12_canonical_perbag
