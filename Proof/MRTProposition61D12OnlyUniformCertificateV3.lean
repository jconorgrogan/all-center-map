import MRTProposition61HighUniformBridgeInstantiationV3
import MRTProposition61TypeIIUniformBudgetV3
import MRTOrdinarySlidingMassBudgetUniform
import MAPSmallRemainderTermwiseFifthV3
import MRTProposition61HighCertificateBridgeV3
import MAPFinishDynamicLowTypesRefinedV3

/-!
# D12-only uniform certificate producer

This module isolates the only source-facing premise not supplied by the
existing high, Type-II, small-remainder, and ordinary-error producers.  All
logarithmic thresholds are synchronized by maxima before the final `X₀` is
chosen.  The D12 premise is stated at the actual normalized mass and at the
same classifier `H₀ = X^(delta+1/8)` used by the Type-II producer.
-/

namespace MRTProposition61D12OnlyUniformCertificateV3

open Filter
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPDynamicHBSourceV3 MAPDynamicHBSourcePacketBoundRefinedV3
open MAPFinishDynamicLowTypes MAPFinishDynamicLowTypesRefinedV3
open MRTLemma215HBExpansion MRTLemma215DyadicPartition
open MRTProposition61HighCertificateBridgeV3
open MRTProposition61HighUniformBridgeInstantiationV3
open MRTProposition61TypeIIUniformBudgetV3
open MAPMRTOrdinarySlidingMassBudgetUniform
open MAPSmallRemainderTermwiseFifthV3
open MRTProposition61HighEnvelopeSplitV3
open MRTProposition61HighAdoptedThirtiethV3
open MRTLemma215DynamicTypeIIParameterGeometryV3
open MRTLemma215DynamicTypeIIGlobalCountV3
open MAPAllCenterApertureTransfer MAPFarSourceWeldScaffold

noncomputable section

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

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

/-- The sole unresolved uniform source premise: the actual normalized D12
mass is at most one thirtieth of the public logarithmic budget. -/
def UniformD12NormalizedBudget (delta : ℝ) (hdelta : 0 < delta) : Prop :=
  ∀ A epsilon : ℝ, 0 < A → 0 < epsilon →
    ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∃ Cc₀ : ℕ, ∀ Cc : ℕ, Cc₀ ≤ Cc →
        ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
          ∀ q a : ℕ, ∀ beta : ℝ,
            let Q := (Real.log X) ^ B
            let H := MAPAllCenterApertureTransfer.baseAperture epsilon X
            let eta := 1 / Real.sqrt Q
            let p := mapCorollary53Input X H q a beta eta
            1 ≤ q → (q : ℝ) ≤ Q → a < q → a.Coprime q →
            |beta| ≤ 1 / ((q : ℝ) * Q) →
            2 * (Real.log X) ^ Cc < stationaryWidth beta H →
            ∃ hq₀ : q ≠ 0, ∃ hp : Corollary53Admissible 1 1 p,
              ∃ hXp : 2 ≤ p.X,
                dynamicLowNormalizationV3 p *
                    (∑ component : OuterComponent,
                      dynamicAllD12MassRefinedV3 p delta
                        (Real.rpow p.X (delta + 1 / 8)) hXp
                        hdelta component) ≤
                  X * Real.rpow (Real.log X) (-A) / 30

/-- A D12 normalized budget plus the existing producers gives the explicit
 uniform active bridge.  The constructor leaves no analytic field as an
 implicit premise: only the D12 mass enters `hd12`. -/
theorem uniform_active_bridge_of_d12_only
    (hd12 : ∀ delta : ℝ, (hdelta : 0 < delta) → delta ≤ 1 / 240 →
      UniformD12NormalizedBudget delta hdelta) :
    UniformActivePacketCertificateBridge := by
  intro A epsilon hA hepsilon
  let delta : ℝ := 1 / 480
  have hdelta : 0 < delta := by dsimp [delta]; norm_num
  have hdeltaUpper : delta ≤ 1 / 240 := by dsimp [delta]; norm_num
  obtain ⟨Bh, hBh⟩ :=
    exists_refined_high_budget_threshold delta A hdelta hdeltaUpper
  obtain ⟨Bt, hBt⟩ :=
    exists_refined_typeII_budget_threshold delta A hdelta hdeltaUpper
  obtain ⟨Bo, hBo⟩ := exists_ordinary_error_budget_threshold A
  obtain ⟨Bs, hBs⟩ := exists_small_remainder_termwise_fifth_halfRange A
  obtain ⟨Bd, hBd⟩ := hd12 delta hdelta hdeltaUpper A epsilon hA hepsilon
  obtain ⟨Xg, hXg⟩ :=
    exists_actual_typeII_parameter_geometry_threshold delta hdelta hdeltaUpper
  obtain ⟨Xb, hXb⟩ := Filter.eventually_atTop.mp
    (baseAperture_eventually_gt_one_local hepsilon)
  let B : ℕ := max (max Bh Bt) (max Bo (max Bs Bd))
  have hBhB : Bh ≤ B := by dsimp [B]; omega
  have hBtB : Bt ≤ B := by dsimp [B]; omega
  have hBoB : Bo ≤ B := by dsimp [B]; omega
  have hBsB : Bs ≤ B := by dsimp [B]; omega
  have hBdB : Bd ≤ B := by dsimp [B]; omega
  obtain ⟨Ch, hCh⟩ := hBh B hBhB
  obtain ⟨Ct, hCt⟩ := hBt B hBtB
  obtain ⟨Co, hCo⟩ := hBo B hBoB
  obtain ⟨Cs, hCs⟩ := hBs B hBsB
  obtain ⟨Cd, hCd⟩ := hBd B hBdB
  let Cc : ℕ := max (max Ch Ct) (max Co (max Cs Cd))
  have hChC : Ch ≤ Cc := by dsimp [Cc]; omega
  have hCtC : Ct ≤ Cc := by dsimp [Cc]; omega
  have hCoC : Co ≤ Cc := by dsimp [Cc]; omega
  have hCsC : Cs ≤ Cc := by dsimp [Cc]; omega
  have hCdC : Cd ≤ Cc := by dsimp [Cc]; omega
  obtain ⟨Xh, hXh3, hXh⟩ := hCh Cc hChC
  obtain ⟨Xt, hXt3, hXt⟩ := hCt Cc hCtC
  obtain ⟨Xo, hXo3, hXo⟩ := hCo Cc hCoC
  obtain ⟨Xs, hXs3, hXs⟩ := hCs Cc hCsC
  obtain ⟨Xd, hXd3, hXd⟩ := hCd Cc hCdC
  let X₀ : ℝ := max 3 (max Xg (max Xb (max Xh (max Xt (max Xo (max Xs Xd))))))
  refine ⟨delta, hdelta, hdeltaUpper, B, 0, Cc, 1, X₀,
    by norm_num, ?_, ?_⟩
  · dsimp [X₀]
    exact (by norm_num : (2 : ℝ) ≤ 3).trans (le_max_left _ _)
  · intro X hXX₀
    have hOuter : max Xg (max Xb (max Xh (max Xt (max Xo (max Xs Xd))))) ≤ X :=
      (le_max_right 3 _).trans hXX₀
    have hXg' : Xg ≤ X := (le_max_left Xg _).trans hOuter
    have hXb' : Xb ≤ X :=
      (le_max_left Xb _ |>.trans (le_max_right Xg _)).trans hOuter
    have hXh' : Xh ≤ X :=
      (le_max_left Xh _ |>.trans (le_max_right Xb _)
        |>.trans (le_max_right Xg _)).trans hOuter
    have hXt' : Xt ≤ X :=
      (le_max_left Xt _ |>.trans (le_max_right Xh _)
        |>.trans (le_max_right Xb _)
        |>.trans (le_max_right Xg _)).trans hOuter
    have hXo' : Xo ≤ X :=
      (le_max_left Xo _ |>.trans (le_max_right Xt _)
        |>.trans (le_max_right Xh _)
        |>.trans (le_max_right Xb _)
        |>.trans (le_max_right Xg _)).trans hOuter
    have hXs' : Xs ≤ X :=
      (le_max_left Xs _ |>.trans (le_max_right Xo _)
        |>.trans (le_max_right Xt _)
        |>.trans (le_max_right Xh _)
        |>.trans (le_max_right Xb _)
        |>.trans (le_max_right Xg _)).trans hOuter
    have hXd' : Xd ≤ X :=
      (le_max_right Xs Xd |>.trans (le_max_right Xo _)
        |>.trans (le_max_right Xt _)
        |>.trans (le_max_right Xh _)
        |>.trans (le_max_right Xb _)
        |>.trans (le_max_right Xg _)).trans hOuter
    have htype := hXt X hXt'
    have hord := hXo X hXo'
    have hsmall := hXs X hXs'
    have hd := hXd X hXd'
    obtain ⟨hX3, hK, hcutoff, hclassifier, hglobal, hsize⟩ := hXg X hXg'
    have hbase := hXb X hXb'
    have hlog : 1 ≤ Real.log X := log_one_le hX3
    have hHone : 1 < MAPAllCenterApertureTransfer.baseAperture epsilon X := hbase
    have hHX : MAPAllCenterApertureTransfer.baseAperture epsilon X ≤ X := by
      have hh := MAPMRTProposition51Supported.baseAperture_le_half_of_one_le
        (epsilon := epsilon) (by linarith : 1 ≤ X)
      linarith
    refine ⟨hlog, hHone, hHX, ?_⟩
    dsimp only
    intro q a beta hq hqQ ha hcop hbeta hfar
    have hq₀ : q ≠ 0 := by omega
    letI : NeZero q := ⟨hq₀⟩
    letI : NeZero (mapCorollary53Input X
      (MAPAllCenterApertureTransfer.baseAperture epsilon X) q a beta
      (1 / Real.sqrt ((Real.log X) ^ B))).q := ⟨hq₀⟩
    let Q := (Real.log X) ^ B
    let H := MAPAllCenterApertureTransfer.baseAperture epsilon X
    let eta := 1 / Real.sqrt Q
    let p := mapCorollary53Input X H q a beta eta
    letI : NeZero p.q := ⟨hq₀⟩
    have hQ : 1 ≤ Q := one_le_pow₀ hlog
    have hp : Corollary53Admissible 1 1 p := by
      simpa [p, Q, H, eta] using
        selectedMapInput_admissible_one hlog hQ hHone hHX hq hcop hbeta hfar
    have hXp : 2 ≤ p.X := by
      simpa [p] using! (show 2 ≤ X by linarith [hX3])
    have hpX : p.X = X := by rfl
    let reserve := apertureReserve epsilon
    have hreserve : 0 ≤ reserve := (apertureReserve_pos hepsilon).le
    have hreserve' : reserve ≤ 1 / 1200 := by
      dsimp [reserve, apertureReserve]; exact min_le_right _ _
    have hHdef : p.H = (1 / 2 : ℝ) *
        Real.rpow p.X (2 / 15 + apertureReserve epsilon) := by
      dsimp [p, H, reserve, baseAperture]; rfl
    have heta : p.eta = 1 / Real.sqrt ((Real.log p.X) ^ B) := by rfl
    have hhigh := hXh X hXh' p hp rfl reserve hreserve hreserve' hHdef heta hqQ hbeta hfar hXp
    have htype' := htype p hp hpX reserve hreserve hreserve' hHdef heta hqQ hbeta hfar hXp
    have hord' := hord p hp hpX heta hfar
    have hHalf : p.H ≤ p.X / 2 := by
      simpa [p, H] using! MAPMRTProposition51Supported.baseAperture_le_half_of_one_le
        (epsilon := epsilon) (by linarith : 1 ≤ X)
    have hsmall' := hsmall p hp hpX rfl hHalf heta hqQ hbeta hfar
    obtain ⟨_, _, _, hd12'⟩ := hd q a beta hq hqQ ha hcop hbeta hfar
    have htype'' : dynamicLowNormalizationV3 p *
        (∑ component : OuterComponent,
          dynamicAllTypeIIMassRefinedV3 p delta
            (highClassifierH0 p.X delta) hXp hdelta component) ≤
        X * Real.rpow (Real.log X) (-A) / 30 := by
      simpa [highClassifierH0] using! htype'
    have hlow := dynamicV3_refined_low_types_of_typeII_and_d12_budgets
      hp hXp hdelta htype'' hd12'
    have hT : 1 ≤ selectedHighTruncation p := by
      have hfar' : 2 * (Real.log p.X)^Cc < stationaryWidth p.beta p.H := by
        simpa [p, H] using! hfar
      have hlogp : 1 ≤ Real.log p.X := by simpa [p] using! hlog
      have hU : 1 ≤ stationaryWidth p.beta p.H := by
        nlinarith [hfar', (one_le_pow₀ hlogp : 1 ≤ (Real.log p.X)^Cc)]
      simpa [selectedHighTruncation, highFreeTruncation, p, H, reserve] using!
        highFreeTruncation_ge_one_of_H (by linarith : 1 ≤ X) hU hHdef hreserve'
    have h30 : activeCertificateHighSlot p delta hXp hdelta ≤
        X * Real.rpow (Real.log X) (-A) / 30 := by
      simpa [activeCertificateHighSlot, p, hpX] using hhigh
    have h5 : activeCertificateHighSlot p delta hXp hdelta ≤
        X * Real.rpow (Real.log X) (-A) / 5 :=
      h30.trans (thirtieth_scalar_le_fifth (by linarith : 0 ≤ X)
        (Real.rpow_nonneg (by linarith : 0 ≤ Real.log X) _))
    refine ⟨hq₀, hp, hXp, ?_⟩
    change Nonempty (@ActivePacketCertificateBridge delta p ⟨hq₀⟩ hp hXp
      (1 * X * Real.rpow (Real.log X) (-A)))
    refine ⟨hdelta, ?_, ?_, ?_, hT, ?_, (by simpa using hlow),
      (by simpa using h5), ?_⟩
    · rfl
    · simpa [p, highClassifierH0] using! hclassifier
    · simpa [p] using! hsize
    · simpa [MAPSmallRemainderMassBudgetV3.dynamicV3Normalization,
        dynamicLowNormalizationV3] using! hsmall'
    · simpa [p] using! hord'

end
end MRTProposition61D12OnlyUniformCertificateV3

#print axioms MRTProposition61D12OnlyUniformCertificateV3.uniform_active_bridge_of_d12_only
