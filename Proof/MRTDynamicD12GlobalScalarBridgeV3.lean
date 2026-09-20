import MRTDynamicD12GlobalAggregation
import MRTDynamicD12ScalarAbsorptionV3
import MRTProposition61D12OnlyUniformCertificateV3

/-!
# Global D12 aggregation followed by scalar absorption

This is the consumer adapter for the literal per-bag three-term estimate.
For a fixed `delta`, the finite aggregation first chooses its constants `C,E`;
only after those constants are fixed does the scalar lemma choose `B₀`.  The
source producer is an explicit premise and is not asserted here.
-/

namespace MRTDynamicD12GlobalScalarBridgeV3

open Filter
open MRTDynamicD12GlobalAggregation
open MRTDynamicD12ScalarAbsorptionV3
open MRTProposition61D12OnlyUniformCertificateV3
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPDynamicHBSourceV3 MAPDynamicHBSourcePacketBoundRefinedV3
open MAPFinishDynamicLowTypes MAPFinishDynamicLowTypesRefinedV3
open MRTDynamicD12LiteralMass
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicTypeIIGlobalCountV3
open MAPAllCenterApertureTransfer MAPFarSourceWeldScaffold
open Real

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

set_option maxHeartbeats 1200000

private theorem baseAperture_eventually_gt_one_local
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ X : ℝ in atTop, 1 < baseAperture epsilon X := by
  have hrho : 0 < 2 / 15 + apertureReserve epsilon := by
    have hreserve := apertureReserve_pos hepsilon
    linarith
  have hpow := (tendsto_rpow_atTop hrho).eventually
    (eventually_gt_atTop (2 : ℝ))
  filter_upwards [hpow] with X hX
  change 2 < Real.rpow X (2 / 15 + apertureReserve epsilon) at hX
  change 1 < (1 / 2 : ℝ) * Real.rpow X (2 / 15 + apertureReserve epsilon)
  have hh := mul_lt_mul_of_pos_left hX (by norm_num : (0 : ℝ) < 1 / 2)
  nlinarith [hh]

/-- The exact scalar envelope supplied separately for every active source bag.
The `if` and the three terms are literal; no source mass estimate is hidden in
this definition. -/
def d12ThreeTermEnvelope (delta : ℝ) (B : ℕ) (X : ℝ) : ℝ :=
  X * Real.rpow ((Real.log X) ^ B) (-3 / 8 : ℝ) +
    Real.rpow X (1 + delta - 2 / 15) *
      Real.rpow ((Real.log X) ^ B) (5 / 8 : ℝ) +
    Real.rpow X (439 / 2000 : ℝ) *
      Real.rpow ((Real.log X) ^ B) (13 / 8 : ℝ)

/-- Source-facing contract for the per-bag producer.  It is uniform in `B`
and carries the exact classifier used by the global aggregation theorem. -/
def D12LiteralPerBagThreeTerm (delta : ℝ) (hdelta : 0 < delta) (B : ℕ) : Prop :=
  ∀ {p : Corollary53Input} [NeZero p.q] {H₀ : ℝ},
    Corollary53Admissible 1 1 p → 3 ≤ p.X →
    (∀ (branch : Fin (hbOrder delta))
      (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
      (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff p.X))))
        (branch : ℕ))
      (mbag : Sym (Option (Fin
        (sourceDyadicCount ⌊dynamicHBCutoff p.X (hbOrder delta)⌋₊)))
        ((branch : ℕ) + 1))
      (component : OuterComponent),
      dynamicLowNormalizationV3 p *
          (if dynamicD12IsActive delta H₀ logIndex zbag mbag then
            componentIntegral p.X p.H 1 p.q
              (dynamicD12FactorizedCoeff delta logIndex zbag mbag)
              p.beta p.eta component
              else 0) ≤ d12ThreeTermEnvelope delta B p.X)

/-! The corrected source contract below is the one intended for the actual
producer.  It quantifies only over the canonical packet constructed from
`X,epsilon,q,a,beta,B`; arbitrary `p`, `H`, and `eta` are deliberately absent.
-/

def D12CanonicalPerBagThreeTerm
    (delta epsilon : ℝ) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ E : ℕ, ∃ Bmin : ℕ,
    ∀ B : ℕ, Bmin ≤ B →
      ∃ Cc₀ : ℕ, ∀ Cc : ℕ, Cc₀ ≤ Cc →
        ∀ᶠ X : ℝ in atTop,
          ∀ q a : ℕ, ∀ beta : ℝ,
            let Q := (Real.log X) ^ B
            let H := baseAperture epsilon X
            let eta := 1 / Real.sqrt Q
            let p := mapCorollary53Input X H q a beta eta
            1 ≤ q → (q : ℝ) ≤ Q → a < q → a.Coprime q →
            |beta| ≤ 1 / ((q : ℝ) * Q) →
            2 * (Real.log X) ^ Cc < stationaryWidth beta H →
            ∀ (branch : Fin (hbOrder delta))
              (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
              (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff p.X))))
                (branch : ℕ))
              (mbag : Sym (Option (Fin
                (sourceDyadicCount ⌊dynamicHBCutoff p.X (hbOrder delta)⌋₊)))
                ((branch : ℕ) + 1))
              (component : OuterComponent),
              dynamicLowNormalizationV3 p *
                  (if dynamicD12IsActive delta
                      (Real.rpow X (delta + 1 / 8)) logIndex zbag mbag then
                    componentIntegral p.X p.H 1 p.q
                      (dynamicD12FactorizedCoeff delta logIndex zbag mbag)
                      p.beta p.eta component
                  else 0) ≤
                C * Real.log X ^ E * d12ThreeTermEnvelope delta B X

/-- Canonical finite aggregation plus scalar absorption.  This is guarded by
the corrected producer contract above and makes no source closure claim. -/
theorem uniformD12NormalizedBudget_of_canonical_perbag
    (hperbag : ∀ (delta epsilon : ℝ) (hdelta : 0 < delta)
      (hepsilon : 0 < epsilon), delta ≤ 1 / 240 →
      D12CanonicalPerBagThreeTerm delta epsilon hdelta hepsilon) :
    ∀ (delta : ℝ) (hdelta : 0 < delta), delta ≤ 1 / 240 →
      UniformD12NormalizedBudget delta hdelta := by
  intro delta hdelta hdeltaUpper A epsilon hA hepsilon
  obtain ⟨Cp, hCp, Ep, Bmin, hproducer⟩ :=
    hperbag delta epsilon hdelta hepsilon hdeltaUpper
  obtain ⟨Cg, hCg, Eg, hglobal⟩ :=
    exists_normalized_d12_global_of_perbag delta hdelta
  obtain ⟨Bscalar, hBscalar⟩ := exists_d12_scalar_absorption
    (2 * Cg * Cp) (Eg + Ep) A delta (by positivity) hA hdelta hdeltaUpper
  let B₀ : ℕ := max Bmin Bscalar
  refine ⟨B₀, ?_⟩
  intro B hB
  have hBmin : Bmin ≤ B := by
    dsimp [B₀] at hB ⊢
    exact le_trans (le_max_left _ _) hB
  have hBscalar' : Bscalar ≤ B := by
    dsimp [B₀] at hB ⊢
    exact le_trans (le_max_right _ _) hB
  obtain ⟨Cc₀, hCc₀⟩ := hproducer B hBmin
  refine ⟨Cc₀, ?_⟩
  intro Cc hCc
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.mp
    (hBscalar B hBscalar')
  obtain ⟨X₂, hX₂⟩ := Filter.eventually_atTop.mp (hCc₀ Cc hCc)
  obtain ⟨X₃, hX₃⟩ := Filter.eventually_atTop.mp
    (baseAperture_eventually_gt_one_local hepsilon)
  let X₀ : ℝ := max 3 (max X₁ (max X₂ X₃))
  refine ⟨X₀, ?_, ?_⟩
  · dsimp [X₀]
    exact le_max_left _ _
  · intro X hXX₀
    have hOuter : max X₁ (max X₂ X₃) ≤ X :=
      (le_max_right 3 _).trans hXX₀
    have hX₁X : X₁ ≤ X := (le_max_left X₁ _).trans hOuter
    have hX₂X : X₂ ≤ X :=
      (le_max_left X₂ X₃ |>.trans (le_max_right X₁ _)).trans hOuter
    have hX₃X : X₃ ≤ X :=
      (le_max_right X₂ X₃ |>.trans (le_max_right X₁ _)).trans hOuter
    have hX3 : 3 ≤ X := (le_max_left 3 _).trans hXX₀
    have hscalar := hX₁ X hX₁X
    have hsource := hX₂ X hX₂X
    have hlog : 1 ≤ Real.log X :=
      MRTLemma215DynamicTypeIIGlobalCountV3.log_one_le hX3
    have hHone : 1 < baseAperture epsilon X := hX₃ X hX₃X
    have hHX : baseAperture epsilon X ≤ X := by
      have hh := MAPMRTProposition51Supported.baseAperture_le_half_of_one_le
        (epsilon := epsilon) (by linarith : 1 ≤ X)
      linarith
    dsimp only
    intro q a beta hq hqQ ha hcop hbeta hfar
    let Q := (Real.log X) ^ B
    let H := baseAperture epsilon X
    let eta := 1 / Real.sqrt Q
    let p := mapCorollary53Input X H q a beta eta
    have hq₀ : q ≠ 0 := by omega
    letI : NeZero q := ⟨hq₀⟩
    letI : NeZero (mapCorollary53Input X H q a beta eta).q := ⟨hq₀⟩
    have hQ : 1 ≤ Q := by
      dsimp [Q]
      exact one_le_pow₀ hlog
    have hp : Corollary53Admissible 1 1 p := by
      simpa [p, Q, H, eta] using
        selectedMapInput_admissible_one hlog hQ hHone hHX
          hq hcop hbeta hfar
    have hXp : 2 ≤ p.X := by
      simpa [p] using (show 2 ≤ X by linarith [hX3])
    have hbag : ∀ (branch : Fin (hbOrder delta))
        (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
        (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff p.X))))
          (branch : ℕ))
        (mbag : Sym (Option (Fin
          (sourceDyadicCount ⌊dynamicHBCutoff p.X (hbOrder delta)⌋₊)))
          ((branch : ℕ) + 1))
        (component : OuterComponent),
        dynamicLowNormalizationV3 p *
            (if dynamicD12IsActive delta
                (Real.rpow p.X (delta + 1 / 8)) logIndex zbag mbag then
              componentIntegral p.X p.H 1 p.q
                (dynamicD12FactorizedCoeff delta logIndex zbag mbag)
                p.beta p.eta component
            else 0) ≤
          Cp * Real.log p.X ^ Ep * d12ThreeTermEnvelope delta B p.X := by
      simpa [p, Q, H, eta] using
        hsource q a beta hq hqQ ha hcop hbeta hfar
    let Ebag : ℝ := Cp * Real.log p.X ^ Ep *
      d12ThreeTermEnvelope delta B p.X
    have hEbag : 0 ≤ Ebag := by
      dsimp [Ebag, d12ThreeTermEnvelope]
      positivity
    have hglobal' := hglobal (p := p)
      (H₀ := Real.rpow p.X (delta + 1 / 8))
      (Ebag := Ebag) hp (by simpa [p] using hX3) hEbag hbag
    have hmass : dynamicLowNormalizationV3 p *
        (∑ component : OuterComponent,
          dynamicAllD12MassRefinedV3 p delta
            (Real.rpow p.X (delta + 1 / 8)) hXp hdelta component) ≤
        X * Real.rpow (Real.log X) (-A) / 30 := by
      calc
        _ ≤ 2 * Cg * Real.log p.X ^ Eg * Ebag := hglobal'
        _ ≤ X * Real.rpow (Real.log X) (-A) / 30 := by
          have hlogpos : 0 < Real.log X := by linarith
          have hrewrite :
              2 * Cg * Real.log p.X ^ Eg * Ebag =
                (2 * Cg * Cp) * Real.rpow (Real.log X)
                    ((Eg + Ep : ℕ) : ℝ) *
                  d12ThreeTermEnvelope delta B X := by
            calc
              _ = 2 * Cg * Cp *
                  (Real.log X ^ Eg * Real.log X ^ Ep) *
                    d12ThreeTermEnvelope delta B X := by
                dsimp [Ebag]
                rw [show p.X = X by rfl]
                ring
              _ = 2 * Cg * Cp * Real.log X ^ (Eg + Ep) *
                    d12ThreeTermEnvelope delta B X := by
                rw [← pow_add]
              _ = _ := by
                exact congrArg
                  (fun z : ℝ => 2 * Cg * Cp * z *
                    d12ThreeTermEnvelope delta B X)
                  (Real.rpow_natCast (Real.log X) (Eg + Ep)).symm
          rw [hrewrite]
          simpa [d12ThreeTermEnvelope] using hscalar
    exact ⟨hq₀, hp, hXp, hmass⟩

theorem uniformD12NormalizedBudget_of_literal_perbag
    (hperbag : ∀ (delta : ℝ) (hdelta : 0 < delta),
      delta ≤ 1 / 240 → ∀ B : ℕ,
        D12LiteralPerBagThreeTerm delta hdelta B) :
    ∀ (delta : ℝ) (hdelta : 0 < delta), delta ≤ 1 / 240 →
      UniformD12NormalizedBudget delta hdelta := by
  intro delta hdelta hdeltaUpper A epsilon hA hepsilon
  obtain ⟨C, hC, E, hglobal⟩ :=
    exists_normalized_d12_global_of_perbag delta hdelta
  obtain ⟨B₀, hB₀⟩ := exists_d12_scalar_absorption
    (2 * C) E A delta (by linarith) hA hdelta hdeltaUpper
  refine ⟨B₀, ?_⟩
  intro B hB
  refine ⟨0, ?_⟩
  intro Cc hCc
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.mp (hB₀ B hB)
  obtain ⟨X₂, hX₂⟩ := Filter.eventually_atTop.mp
    (baseAperture_eventually_gt_one_local hepsilon)
  let X₀ : ℝ := max 3 (max X₁ X₂)
  refine ⟨X₀, ?_, ?_⟩
  · dsimp [X₀]
    exact le_max_left _ _
  · intro X hXX₀
    have hOuter : max X₁ X₂ ≤ X :=
      (le_max_right 3 _).trans hXX₀
    have hX₁X : X₁ ≤ X := (le_max_left X₁ X₂).trans hOuter
    have hX₂X : X₂ ≤ X := (le_max_right X₁ X₂).trans hOuter
    have hX3 : 3 ≤ X := (le_max_left 3 _).trans hXX₀
    have hscalar := hX₁ X hX₁X
    have hlog : 1 ≤ Real.log X :=
      MRTLemma215DynamicTypeIIGlobalCountV3.log_one_le hX3
    have hHone : 1 < baseAperture epsilon X := hX₂ X hX₂X
    have hHX : baseAperture epsilon X ≤ X := by
      have hh := MAPMRTProposition51Supported.baseAperture_le_half_of_one_le
        (epsilon := epsilon) (by linarith : 1 ≤ X)
      linarith
    dsimp only
    intro q a beta hq hqQ ha hcop hbeta hfar
    let Q := (Real.log X) ^ B
    let H := baseAperture epsilon X
    let eta := 1 / Real.sqrt Q
    let p := mapCorollary53Input X H q a beta eta
    have hq₀ : q ≠ 0 := by omega
    letI : NeZero q := ⟨hq₀⟩
    letI : NeZero (mapCorollary53Input X H q a beta eta).q := ⟨hq₀⟩
    have hQ : 1 ≤ Q := by
      dsimp [Q]
      exact one_le_pow₀ hlog
    have hp : Corollary53Admissible 1 1 p := by
      simpa [p, Q, H, eta] using
        selectedMapInput_admissible_one hlog hQ
          hHone hHX
          hq hcop hbeta hfar
    have hXp : 2 ≤ p.X := by
      simpa [p] using (show 2 ≤ X by linarith [hX3])
    have hbag : ∀ (branch : Fin (hbOrder delta))
        (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
        (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff p.X))))
          (branch : ℕ))
        (mbag : Sym (Option (Fin
          (sourceDyadicCount ⌊dynamicHBCutoff p.X (hbOrder delta)⌋₊)))
          ((branch : ℕ) + 1))
        (component : OuterComponent),
        dynamicLowNormalizationV3 p *
            (if dynamicD12IsActive delta
                (Real.rpow p.X (delta + 1 / 8))
                logIndex zbag mbag then
              componentIntegral p.X p.H 1 p.q
                (dynamicD12FactorizedCoeff delta logIndex zbag mbag)
                p.beta p.eta component
            else 0) ≤ d12ThreeTermEnvelope delta B p.X := by
        exact hperbag delta hdelta hdeltaUpper B hp
          (by simpa [p] using hX3)
    let Ebag : ℝ := d12ThreeTermEnvelope delta B p.X
    have hEbag : 0 ≤ Ebag := by
      dsimp [Ebag, d12ThreeTermEnvelope]
      positivity
    have hglobal' := hglobal (p := p)
      (H₀ := Real.rpow p.X (delta + 1 / 8))
        (Ebag := Ebag) hp (by simpa [p] using hX3) hEbag hbag
    have hmass : dynamicLowNormalizationV3 p *
        (∑ component : OuterComponent,
          dynamicAllD12MassRefinedV3 p delta
            (Real.rpow p.X (delta + 1 / 8)) hXp hdelta component) ≤
        X * Real.rpow (Real.log X) (-A) / 30 := by
      calc
        _ ≤ 2 * C * Real.log p.X ^ E * Ebag := hglobal'
        _ ≤ X * Real.rpow (Real.log X) (-A) / 30 := by
          simpa [Ebag, d12ThreeTermEnvelope, p, Q, H, eta] using hscalar
    refine ⟨hq₀, ?_, hXp, hmass⟩
    exact hp

end
end MRTDynamicD12GlobalScalarBridgeV3

#print axioms MRTDynamicD12GlobalScalarBridgeV3.uniformD12NormalizedBudget_of_literal_perbag
#print axioms MRTDynamicD12GlobalScalarBridgeV3.uniformD12NormalizedBudget_of_canonical_perbag
