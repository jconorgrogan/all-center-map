import MRTProposition61HighEnvelopeSplitV3
import MRTProposition61HighAdoptedThirtiethV3
import MRTProposition61HighCertificateBridgeV3
import MRTLemma215DynamicTypeIIParameterGeometryV3
import MAPFarSourceWeldScaffold
import AllCenterApertureTransfer

/-!
# Uniform instantiation of the adopted high field

This module supplies the source-facing part of
`MRTProposition61HighCertificateBridgeV3.UniformActivePacketCertificateBridge`.
The constants are chosen before `X`, `q`, `a`, and `beta`.  The returned
certificate prerequisites include the literal classifier geometry,
component-size bound, free-T truncation lower bound, and the actual
`activeCertificateHighSlot` estimate.  The small remainder, D12/low field,
and ordinary error remain explicit obligations of the consumer.
-/

namespace MRTProposition61HighUniformBridgeInstantiationV3

open Filter
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPDynamicHBSourceV3 MAPDynamicHBScaledPacketSourceRefinedV3
open MAPDynamicHBSourcePacketBoundRefinedV3
open MAPAllCenterApertureTransfer
open MAPFarSourceWeldScaffold
open MRTLemma215HBExpansion MRTLemma215DyadicPartition MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicTypeIIGlobalCountV3 MAPMRTProposition51Supported
open MRTLemma215DynamicTypeIIParameterGeometryV3
open MRTProposition61HighEnvelopeSplitV3
open MRTProposition61HighAdoptedThirtiethV3
open MRTProposition61HighCertificateBridgeV3
open MAPFinishDynamicLowTypes

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

def UniformHighMassInstantiation (delta : ℝ) (hdelta : 0 < delta) : Prop :=
  ∀ A epsilon : ℝ, 0 < A → 0 < epsilon →
    ∃ B D Cc : ℕ, ∃ Cred X₀ : ℝ,
      0 < Cred ∧ 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X →
        1 ≤ Real.log X ∧
        1 < baseAperture epsilon X ∧
        baseAperture epsilon X ≤ X ∧
        ∀ q a : ℕ, ∀ beta : ℝ,
          let Q := (Real.log X) ^ B
          let H := baseAperture epsilon X
          let eta := 1 / Real.sqrt Q
          let p := mapCorollary53Input X H q a beta eta
          1 ≤ q → (q : ℝ) ≤ Q → a < q → a.Coprime q →
          |beta| ≤ 1 / ((q : ℝ) * Q) →
          2 * (Real.log X) ^ Cc < stationaryWidth beta H →
          ∃ hq₀ : q ≠ 0, ∃ hp : Corollary53Admissible 1 1 p,
            ∃ hXp : 2 ≤ p.X,
              (Real.rpow X delta * (2 * Real.rpow X ((8 : ℝ)⁻¹)) ≤
                2 * highClassifierH0 p.X delta) ∧
              (∀ (rawBranch : Fin (hbOrder delta))
                (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
                (zbag : Sym (Option
                  (Fin (sourceDyadicCount (hbFactorCutoff p.X)))) (rawBranch : ℕ))
                (mbag : Sym (Option (Fin (sourceDyadicCount
                  ⌊dynamicHBCutoff p.X (hbOrder delta)⌋₊))) ((rawBranch : ℕ) + 1)),
                (2 : ℝ) ^ (dynamicComponentFactorList logIndex zbag mbag).length *
                  Real.rpow p.X delta ≤ p.X) ∧
              1 ≤ selectedHighTruncation p ∧
              @activeCertificateHighSlot p ⟨hq₀⟩ delta hXp hdelta ≤
                X * Real.rpow (Real.log X) (-A) / 30 ∧
              @activeCertificateHighSlot p ⟨hq₀⟩ delta hXp hdelta ≤
                X * Real.rpow (Real.log X) (-A) / 5

private theorem baseAperture_eventually_gt_one
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ X : ℝ in atTop, 1 < baseAperture epsilon X := by
  have hrho : 0 < 2 / 15 + apertureReserve epsilon := by
    have hreserve := apertureReserve_pos hepsilon
    linarith
  have hpow := (tendsto_rpow_atTop hrho).eventually
    (eventually_gt_atTop (2 : ℝ))
  filter_upwards [hpow] with X hX
  change 2 < Real.rpow X (2 / 15 + apertureReserve epsilon) at hX
  change 1 < (1 / 2 : ℝ) * Real.rpow X
    (2 / 15 + apertureReserve epsilon)
  have hh := mul_lt_mul_of_pos_left hX (by norm_num : (0 : ℝ) < 1 / 2)
  nlinarith [hh]

theorem uniform_high_mass_instantiation
    (delta : ℝ) (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 240) :
    UniformHighMassInstantiation delta hdelta := by
  intro A epsilon hA hepsilon
  obtain ⟨B₀, hB₀⟩ :=
    exists_refined_high_budget_threshold delta A hdelta hdeltaUpper
  obtain ⟨Cc₀, hCc₀⟩ := hB₀ B₀ le_rfl
  obtain ⟨Xh, hXh3, hXh⟩ := hCc₀ Cc₀ le_rfl
  obtain ⟨Xg, hXg⟩ :=
    exists_actual_typeII_parameter_geometry_threshold delta hdelta hdeltaUpper
  obtain ⟨Xb, hXb⟩ := Filter.eventually_atTop.mp
    (baseAperture_eventually_gt_one hepsilon)
  let X₀ : ℝ := max 2 (max Xh (max Xg Xb))
  refine ⟨B₀, 0, Cc₀, 1, X₀, by norm_num, ?_, ?_⟩
  · dsimp [X₀]
    exact le_max_left _ _
  · intro X hXX₀
    have hXh' : Xh ≤ X := le_trans (le_max_left Xh (max Xg Xb))
      (le_max_right 2 (max Xh (max Xg Xb)) |>.trans hXX₀)
    have hXg' : Xg ≤ X := le_trans
      (le_trans (le_max_left Xg Xb) (le_max_right Xh (max Xg Xb)))
      (le_max_right 2 (max Xh (max Xg Xb)) |>.trans hXX₀)
    have hXb' : Xb ≤ X := le_trans (le_max_right Xg Xb)
      (le_max_right Xh (max Xg Xb) |>.trans
        (le_max_right 2 (max Xh (max Xg Xb)) |>.trans hXX₀))
    have hgeom := hXg X hXg'
    obtain ⟨hX3, hK, hcutoff, hclassifier, hglobal, hsize⟩ := hgeom
    have hbase := hXb X hXb'
    refine ⟨log_one_le hX3, hbase, ?_, ?_⟩
    · have hXone : 1 ≤ X := by linarith
      have hhalf := baseAperture_le_half_of_one_le (epsilon := epsilon) hXone
      linarith
    · intro q a beta
      dsimp only
      intro hq hqQ ha hcop hbeta hfar
      let Q : ℝ := (Real.log X) ^ B₀
      let H : ℝ := baseAperture epsilon X
      let eta : ℝ := 1 / Real.sqrt Q
      let p := mapCorollary53Input X H q a beta eta
      have hlog : 1 ≤ Real.log X := log_one_le hX3
      have hQ : 1 ≤ Q := by
        dsimp [Q]
        exact one_le_pow₀ hlog
      have hHone : 1 < H := by simpa [H] using hbase
      have hHX : H ≤ X := by
        dsimp [H]
        exact (baseAperture_le_half_of_one_le (epsilon := epsilon)
          (by linarith : 1 ≤ X)).trans (by linarith)
      have hq0 : q ≠ 0 := by omega
      letI : NeZero q := ⟨hq0⟩
      have hp : Corollary53Admissible 1 1 p := by
        simpa [p, Q, H, eta] using
          (selectedMapInput_admissible_one hlog hQ hHone hHX hq hcop hbeta hfar)
      letI : NeZero p.q := ⟨hq0⟩
      have hXp : 2 ≤ p.X := by
        simpa [p] using (show 2 ≤ X by linarith [hX3])
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
      have heta : p.eta = 1 / Real.sqrt ((Real.log p.X) ^ B₀) := by
        rfl
      have hpX : p.X = X := by rfl
      have hhigh := hXh X hXh' p hp hpX reserve hr0 hr hHdef heta hqQ hbeta hfar hXp
      have hT : 1 ≤ selectedHighTruncation p := by
        have hfar' : 2 * (Real.log p.X) ^ Cc₀ <
            stationaryWidth p.beta p.H := by
          simpa [p, H] using hfar
        have hlogp : 1 ≤ Real.log p.X := by simpa [hpX] using hlog
        have hU : 1 ≤ stationaryWidth p.beta p.H := by
          nlinarith [hfar',
            (one_le_pow₀ hlogp : 1 ≤ (Real.log p.X) ^ Cc₀)]
        simpa [selectedHighTruncation, highFreeTruncation, p, H, reserve] using
          (highFreeTruncation_ge_one_of_H (by linarith : 1 ≤ X) hU hHdef hr)
      have h30 : activeCertificateHighSlot p delta hXp hdelta ≤
          X * Real.rpow (Real.log X) (-A) / 30 := by
        simpa [activeCertificateHighSlot, hpX] using hhigh
      have h5 : activeCertificateHighSlot p delta hXp hdelta ≤
          X * Real.rpow (Real.log X) (-A) / 5 :=
        h30.trans (thirtieth_scalar_le_fifth (by linarith : 0 ≤ X)
          (Real.rpow_nonneg (by linarith : 0 ≤ Real.log X) _))
      refine ⟨hq0, hp, hXp, ?_, ?_, hT, h30, h5⟩
      · simpa [p, highClassifierH0, hpX] using hclassifier
      · intro rawBranch logIndex zbag mbag
        simpa [p] using hsize rawBranch logIndex zbag mbag

end
end MRTProposition61HighUniformBridgeInstantiationV3

#print axioms MRTProposition61HighUniformBridgeInstantiationV3.uniform_high_mass_instantiation
