import MRTProposition61HighActiveMixedLedgerV3
import MRTProposition61HighActiveCountBudgetV3
import MRTProposition61HighGeometricSavingsV3
import MRTProposition61HighPolylogBudgetV3
import MRTProposition61HighTruncationParametersV3
import MRTLemma215DynamicHighUniformScaledCoefficientsV3
import MRTLemma215DynamicHighParameterScalesV3
import MRTProposition61TypeIIDivisorNormalizationV3
import MRTProposition61TypeIIEndpointWidthV3
import MRTLemma215DynamicTypeIIParameterGeometryV3
import MAPFinishDynamicLowTypes
import MAPDynamicHBCanonicalPerronConstantV3

/-!
# Per-packet mixed and sharp-max error bounds for the adopted high field

The adopted high contribution is the active-mask free-T mixed total plus the
sharp-maximum Perron errors at `T = (U/H) X^(23/24)` and
`H₀ = X^(delta+1/8)`. Original L1 convolution interfaces and the `T = X`
constructor field are not used. `H^{-2}` is applied once, via
`dynamicLowNormalizationV3 = d(q)^4 / (q U^2)`.

This module splits the uniform envelope into two per-packet lemmas so the
sixteen × two-component sum can retain `D` and `perronCellScale^2` until
after the sum, then inserts `D ≤ C_d Q^(1/8)` and
`h + 2θ + 2σ ≤ 1/2` with `θ = σ = 1/24`.
-/

namespace MRTProposition61HighEnvelopeSplitV3

open scoped BigOperators
open Filter
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPMRTProposition51Source
open MAPDynamicHBSourceV3
open MAPDynamicHBScaledPacketSourceV3
open MAPDynamicHBScaledPacketSourceRefinedV3
open MAPDynamicHBSourcePacketBoundRefinedV3
open MAPDynamicHBCanonicalPerronConstantV3
open MAPFinishDynamicLowTypes
open MAPMRTCorollary25Minkowski
open MRTLemma215DynamicHighPacketIndexV3
open MRTLemma215DynamicHighCellPruningV3
open MRTLemma215DynamicHighParameterScalesV3
open MRTLemma215DynamicHighUniformScaledCoefficientsV3
open MRTLemma215DynamicHighSharpCoefficientBoundV3
open MRTLemma215DynamicTypeIIParameterGeometryV3
open MRTProposition61HighActivePacketDataV3
open MRTProposition61HighActiveMixedLedgerV3
open MRTProposition61HighActiveCountBudgetV3
open MRTProposition61HighGeometricSavingsV3
open MRTProposition61HighTruncationParametersV3
open MRTProposition61HighPolylogBudgetV3
open MRTProposition61HighFreePerronV3
open MRTProposition61TypeIIDivisorNormalizationV3
open MRTProposition61TypeIIEndpointWidthV3

noncomputable section

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-- Paper-compatible free truncation `T=(U/H) X^(23/24)`. -/
def highFreeTruncation (X H U : ℝ) : ℝ :=
  (U / H) * Real.rpow X (23 / 24 : ℝ)

/-- Classifier geometry saturating `X^delta * 2 X^(1/8) = 2 H₀`. -/
def highClassifierH0 (X delta : ℝ) : ℝ :=
  Real.rpow X (delta + 1 / 8)

def highThreeLosses (X U Q delta : ℝ) : ℝ :=
  Q * Real.rpow X (-delta) + 1 / Real.sqrt Q + Q / U

def highActiveErrorTotal (p : Corollary53Input) {delta H₀ : ℝ}
    (T : ℝ) (hX : 2 ≤ p.X) (hdelta : 0 < delta) : ℝ :=
  ∑ component : OuterComponent,
    ∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
      freePacketErrorRefinedV3 p T hX hdelta component packet

/-- Literal high mixed-plus-error mass in the adopted active expanded core. -/
def highActivePacketMass (p : Corollary53Input) [NeZero p.q] {delta H₀ : ℝ}
    (T : ℝ) (hX : 2 ≤ p.X) (hdelta : 0 < delta) : ℝ :=
  activeIndexedMixedTotal (H₀ := H₀) T hX hdelta +
    highActiveErrorTotal (H₀ := H₀) p T hX hdelta

def selectedHighTruncation (p : Corollary53Input) : ℝ :=
  highFreeTruncation p.X p.H (stationaryWidth p.beta p.H)

/-- High mass at the shared Type-II classifier `H₀` and free truncation. -/
def selectedHighMass (p : Corollary53Input) [NeZero p.q]
    (delta : ℝ) (hX : 2 ≤ p.X) (hdelta : 0 < delta) : ℝ :=
  highActivePacketMass (H₀ := highClassifierH0 p.X delta) p
    (selectedHighTruncation p) hX hdelta

def highMixedLogExponent (delta : ℝ) (a : ℕ) : ℕ :=
  4 * a + 2 * max 2 ((2 * hbOrder delta) * (2 * hbOrder delta)) + 2

theorem high_truncation_exponent :
    (23 / 24 : ℝ) = 1 - (1 / 24 : ℝ) := by norm_num

theorem high_power_sum_le_half {reserve : ℝ}
    (hr : reserve ≤ 1 / 1200) :
    2 / 15 + reserve + (1 / 6 : ℝ) ≤ 1 / 2 := by linarith

theorem perronCellScale_sq_log {T : ℝ} (hT : 0 ≤ T) :
    perronCellScale canonicalPerronKFour T ^ 2 =
      8 * canonicalPerronKFour ^ 2 * Real.log (1 + T) ^ 2 := by
  unfold perronCellScale
  rw [integral_perronWeight hT]
  have hsqrt : Real.sqrt (2 : ℝ) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  calc
    (Real.sqrt 2 * canonicalPerronKFour * (2 * Real.log (1 + T))) ^ 2
        = Real.sqrt 2 ^ 2 * canonicalPerronKFour ^ 2 *
            (2 * Real.log (1 + T)) ^ 2 := by ring
    _ = (2 : ℝ) * canonicalPerronKFour ^ 2 *
            (4 * Real.log (1 + T) ^ 2) := by
          rw [hsqrt]; ring
    _ = 8 * canonicalPerronKFour ^ 2 * Real.log (1 + T) ^ 2 := by ring

theorem highFreeTruncation_ge_one_of_H
    {X H U reserve : ℝ} (hX : 1 ≤ X) (hU : 1 ≤ U)
    (hH : H = (1 / 2 : ℝ) * Real.rpow X (2 / 15 + reserve))
    (hr : reserve ≤ 1 / 1200) :
    1 ≤ highFreeTruncation X H U := by
  have hbase := highFreeTruncation_ge_one (sigma := (1 / 24 : ℝ))
    hX hU hr (by norm_num)
  unfold highFreeTruncation
  rw [hH, high_truncation_exponent]
  exact hbase

theorem highFreeTruncation_le_X_of_width
    {X H U : ℝ} (hX : 1 ≤ X) (hH : 0 < H) (hUH : U ≤ H) (hU : 0 ≤ U) :
    highFreeTruncation X H U ≤ X := by
  have hfrac : U / H ≤ 1 := (div_le_one hH).2 hUH
  have hpow : Real.rpow X (23 / 24 : ℝ) ≤ X := by
    have h := Real.rpow_le_rpow_of_exponent_le hX
      (show (23 / 24 : ℝ) ≤ 1 by norm_num)
    simpa [Real.rpow_one] using h
  calc
    highFreeTruncation X H U
        = (U / H) * Real.rpow X (23 / 24 : ℝ) := rfl
    _ ≤ 1 * Real.rpow X (23 / 24 : ℝ) :=
      mul_le_mul_of_nonneg_right hfrac (Real.rpow_nonneg (by linarith) _)
    _ = Real.rpow X (23 / 24 : ℝ) := one_mul _
    _ ≤ X := hpow

theorem log_one_add_truncation_le
    {X T : ℝ} (hX : 3 ≤ X) (hlog : 1 ≤ Real.log X)
    (hT : 0 ≤ T) (hTX : T ≤ X) :
    0 ≤ Real.log (1 + T) ∧ Real.log (1 + T) ≤ 3 * Real.log X := by
  have hX0 : 0 < X := by linarith
  have hpos : (0 : ℝ) < 1 + T := by linarith
  have hle : 1 + T ≤ 4 * X := by linarith
  have hlogT : Real.log (1 + T) ≤ Real.log (4 * X) :=
    Real.log_le_log hpos hle
  have h4 : Real.log (4 : ℝ) ≤ 2 := by
    have hmul : Real.log (4 : ℝ) = Real.log 2 + Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
    have h2 : Real.log (2 : ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith
  have h4X : Real.log (4 * X) = Real.log 4 + Real.log X :=
    Real.log_mul (by norm_num) hX0.ne'
  have hnonneg : 0 ≤ Real.log (1 + T) :=
    Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + T)
  refine ⟨hnonneg, ?_⟩
  calc
    Real.log (1 + T) ≤ Real.log 4 + Real.log X := by
      simpa [h4X] using hlogT
    _ ≤ 2 + Real.log X := by linarith
    _ ≤ 3 * Real.log X := by nlinarith

theorem log_two_add_truncation_le
    {X T : ℝ} (hX : 3 ≤ X) (hlog : 1 ≤ Real.log X)
    (hT : 0 ≤ T) (hTX : T ≤ X) :
    0 ≤ Real.log (2 + T) ∧ Real.log (2 + T) ≤ 3 * Real.log X := by
  have hX0 : 0 < X := by linarith
  have hpos : (0 : ℝ) < 2 + T := by linarith
  have hle : 2 + T ≤ 4 * X := by linarith
  have hlogT : Real.log (2 + T) ≤ Real.log (4 * X) :=
    Real.log_le_log hpos hle
  have h4 : Real.log (4 : ℝ) ≤ 2 := by
    have hmul : Real.log (4 : ℝ) = Real.log 2 + Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
    have h2 : Real.log (2 : ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith
  have h4X : Real.log (4 * X) = Real.log 4 + Real.log X :=
    Real.log_mul (by norm_num) hX0.ne'
  have hnonneg : 0 ≤ Real.log (2 + T) :=
    Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 + T)
  refine ⟨hnonneg, ?_⟩
  calc
    Real.log (2 + T) ≤ Real.log 4 + Real.log X := by
      simpa [h4X] using hlogT
    _ ≤ 2 + Real.log X := by linarith
    _ ≤ 3 * Real.log X := by nlinarith

theorem log_two_mul_prod_le
    {X M N : ℝ} (hX : 0 < X) (hlog : 1 ≤ Real.log X)
    (hM : 2 ≤ M) (hN : 2 ≤ N) (hprod : M * N ≤ 2 * X) :
    0 ≤ Real.log (2 * M * N) ∧
      Real.log (2 * M * N) ≤ 3 * Real.log X := by
  have hMN : (0 : ℝ) < M * N :=
    mul_pos (lt_of_lt_of_le (by norm_num) hM) (lt_of_lt_of_le (by norm_num) hN)
  have harg : (0 : ℝ) < 2 * M * N := by nlinarith
  have hle : 2 * M * N ≤ 4 * X := by nlinarith
  have hlogle : Real.log (2 * M * N) ≤ Real.log (4 * X) :=
    Real.log_le_log harg hle
  have h4 : Real.log (4 : ℝ) ≤ 2 := by
    have hmul : Real.log (4 : ℝ) = Real.log 2 + Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
    have h2 : Real.log (2 : ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith
  have h4X : Real.log (4 * X) = Real.log 4 + Real.log X :=
    Real.log_mul (by norm_num) hX.ne'
  have hnonneg : 0 ≤ Real.log (2 * M * N) :=
    Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ 2 * M * N)
  refine ⟨hnonneg, ?_⟩
  calc
    Real.log (2 * M * N) ≤ Real.log 4 + Real.log X := by
      simpa [h4X] using hlogle
    _ ≤ 2 + Real.log X := by linarith
    _ ≤ 3 * Real.log X := by nlinarith

theorem high_component_collar
    {X H beta eta q Q : ℝ}
    (hX : 0 ≤ X) (hH : 0 < H) (heta : 0 < eta) (hQ : 0 < Q)
    (hetaQ : eta = 1 / Real.sqrt Q)
    (hqu : q * stationaryWidth beta H ≤ H / Q)
    (hq0 : 0 ≤ q) (component : OuterComponent) :
    q * ((componentEndpoints X beta eta component).2 -
      (componentEndpoints X beta eta component).1) ≤
      X / Real.sqrt Q := by
  have hL := componentEndpoints_sub_le_stationaryWidth_mul
    (beta := beta) hX heta.le hH component
  have hden : 0 < eta * H := mul_pos heta hH
  have hQeta : Q * eta = Real.sqrt Q := by
    rw [hetaQ]
    have hne : Real.sqrt Q ≠ 0 := (Real.sqrt_pos.2 hQ).ne'
    have hdiv : Q / Real.sqrt Q = Real.sqrt Q := by
      field_simp [hne]
      exact (Real.sq_sqrt hQ.le).symm
    simpa [div_eq_mul_inv] using hdiv
  calc
    _ ≤ q * (stationaryWidth beta H * X / (eta * H)) :=
      mul_le_mul_of_nonneg_left hL hq0
    _ = (q * stationaryWidth beta H) * X / (eta * H) := by ring
    _ ≤ (H / Q) * X / (eta * H) := by
      have hmul := mul_le_mul_of_nonneg_right hqu (div_nonneg hX hden.le)
      convert hmul using 1 <;> ring
    _ = X / (Q * eta) := by
      field_simp [hH.ne', hQ.ne', heta.ne']
    _ = X / Real.sqrt Q := by rw [hQeta]

theorem admissible_abs_beta_le_one
    {p : Corollary53Input} (hp : Corollary53Admissible 1 1 p) :
    |p.beta| ≤ 1 :=
  ((by simpa using hp.2.2.2.2.2.2.1 : |p.beta| ≤ p.eta).trans hp.2.2.2.2.2.1)

theorem stationaryWidth_le_H
    {p : Corollary53Input} (hp : Corollary53Admissible 1 1 p)
    (hH : 0 ≤ p.H) :
    stationaryWidth p.beta p.H ≤ p.H :=
  mul_le_of_le_one_left hH (admissible_abs_beta_le_one hp)

theorem freePacketErrorRefinedV3_nonneg
    {p : Corollary53Input} {delta H₀ T : ℝ}
    (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta) (hT : 0 < T)
    (component : OuterComponent)
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) :
    0 ≤ freePacketErrorRefinedV3 p T hX hdelta component packet := by
  unfold freePacketErrorRefinedV3 perronCellError
  have hab := componentEndpoints_mono (beta := p.beta)
    (by linarith : 0 ≤ p.X) hp.2.2.2.2.1 hp.2.2.2.2.2.1 component
  have hK : 0 ≤ canonicalPerronKFour ^ 2 := sq_nonneg _
  have hlen : 0 ≤
      (componentEndpoints p.X p.beta p.eta component).2 -
        (componentEndpoints p.X p.beta p.eta component).1 := sub_nonneg.mpr hab
  positivity

theorem highActiveErrorTotal_nonneg
    {p : Corollary53Input} {delta H₀ T : ℝ}
    (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta) (hT : 0 < T) :
    0 ≤ highActiveErrorTotal (H₀ := H₀) p T hX hdelta := by
  unfold highActiveErrorTotal
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun packet _ =>
      freePacketErrorRefinedV3_nonneg hp hX hdelta hT _ packet

theorem normalized_active_mixed_le_mass
    {p : Corollary53Input} [NeZero p.q] {delta H₀ T : ℝ}
    (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta) (hT : 0 < T) :
    dynamicLowNormalizationV3 p *
        activeIndexedMixedTotal (H₀ := H₀) T hX hdelta ≤
      dynamicLowNormalizationV3 p *
        highActivePacketMass (H₀ := H₀) p T hX hdelta := by
  have hnorm : 0 ≤ dynamicLowNormalizationV3 p := by
    unfold dynamicLowNormalizationV3
    positivity
  have herr := highActiveErrorTotal_nonneg (H₀ := H₀) hp hX hdelta hT
  unfold highActivePacketMass
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right herr) hnorm

theorem outerComponent_card : Fintype.card OuterComponent = 2 := by decide

/-- Unfold the `let U,L,M,N` surface of the mixed source so later lemmas
never `simpa` against those binders. -/
theorem explicit_activeHighMixed_bound (delta : ℝ) (hdelta : 0 < delta) :
    ∃ a : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (p : Corollary53Input) [NeZero p.q] (hp : Corollary53Admissible 1 1 p)
        (H₀ T : ℝ) (hX : 2 ≤ p.X) (hT : 1 ≤ T)
        (hU : 1 ≤ stationaryWidth p.beta p.H) (component : OuterComponent)
        (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta),
        packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta →
        dynamicLowNormalizationV3 p *
          activeHighPacketMixedMass p T hX hdelta component packet ≤
        perronCellScale canonicalPerronKFour T ^ 2 *
          dynamicBranchHighWeightRefinedV3 (H₀ := H₀) hX hdelta packet.1 *
          ((divisorCount p.q : ℝ) ^ 4 * (p.q : ℝ) * C *
            Real.log (2 *
              (highPacketShortLengthV3 (allPacketGlobalV3 packet) : ℝ) *
              (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ)) ^
              highMixedLogExponent delta a *
            (2 * ((componentEndpoints p.X p.beta p.eta component).2 -
                  (componentEndpoints p.X p.beta p.eta component).1) +
              4 * T + 4 * stationaryWidth p.beta p.H +
              (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ) +
              2 * p.X / stationaryWidth p.beta p.H)) := by
  obtain ⟨a, C, hC, hmixed⟩ :=
    exists_uniform_activeHighMixed_normalized_bound delta hdelta
  refine ⟨a, C, hC, ?_⟩
  intro p _ hp H₀ T hX hT hU component packet hactive
  have h := hmixed p hp H₀ T hX hT hU component packet hactive
  -- Zeta-reduce the source `let U,L,M,N` binders, then match public aliases.
  dsimp only at h
  simpa [dynamicLowNormalizationV3, highMixedLogExponent] using h

/-- Selected free truncation as the `1-σ` form consumed by the Perron lemma. -/
theorem selectedT_eq_free_sigma
    {X H U T : ℝ} (hT : T = (U / H) * Real.rpow X (23 / 24 : ℝ)) :
    T = (U / H) * Real.rpow X (1 - (1 / 24 : ℝ)) := by
  rw [hT, high_truncation_exponent]

theorem normalized_perronCellError_selectedT_le
    {q : ℕ} {D N M B U a b K X H eta sigma T : ℝ}
    (hT : T = (U / H) * Real.rpow X (1 - sigma))
    (hq : 0 < (q : ℝ)) (hD : 0 ≤ D) (hX : 0 < X)
    (hH : 0 < H) (hU : 0 < U) (heta : 0 < eta)
    (hab : a ≤ b) (hNM0 : 0 ≤ N * M)
    (hproduct : N * M ≤ 2 * X) (hL : b - a ≤ U * X / (eta * H)) :
    D / ((q : ℝ) * U ^ 2) * perronCellError q N M T B U a b K ≤
      16 * K ^ 2 * D * (q : ℝ) * H / (eta * U) * B ^ 2 *
        Real.rpow X (2 * sigma) * Real.log (2 + T) ^ 2 := by
  have hsrc :=
    normalized_perronCellError_freeT_le (q := q) (D := D) (N := N) (M := M)
      (B := B) (U := U) (a := a) (b := b) (K := K) (X := X) (H := H)
      (eta := eta) (sigma := sigma)
      hq hD hX hH hU heta hab hNM0 hproduct hL
  dsimp only at hsrc
  simpa [hT] using hsrc

/-! ## Per-packet mixed lemma -/

/-- One active packet, one outer component: keep `D` and `perronCellScale^2`. -/
theorem normalized_activeHighPacketMixedMass_le
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ T Q reserve Cmix : ℝ} {a : ℕ}
    (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 240)
    (hlog : 1 ≤ Real.log p.X)
    (hQ : 1 ≤ Q) (hqQ : (p.q : ℝ) ≤ Q)
    (hH : p.H = (1 / 2 : ℝ) * Real.rpow p.X (2 / 15 + reserve))
    (heta : p.eta = 1 / Real.sqrt Q)
    (hU : 1 ≤ stationaryWidth p.beta p.H)
    (hqu : (p.q : ℝ) * stationaryWidth p.beta p.H ≤ p.H / Q)
    (hr : reserve ≤ 1 / 1200)
    (hTge : 1 ≤ T)
    (hTdef : T = (stationaryWidth p.beta p.H / p.H) *
      Real.rpow p.X (23 / 24 : ℝ))
    (hCmix : 0 < Cmix)
    (hgeom : Real.rpow p.X delta * (2 * Real.rpow p.X ((8 : ℝ)⁻¹)) ≤ 2 * H₀)
    (component : OuterComponent)
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta)
    (hactive : packet ∈
      activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta)
    (hmixed :
      dynamicLowNormalizationV3 p *
          activeHighPacketMixedMass p T hX hdelta component packet ≤
        perronCellScale canonicalPerronKFour T ^ 2 *
          dynamicBranchHighWeightRefinedV3 (H₀ := H₀) hX hdelta packet.1 *
          ((divisorCount p.q : ℝ) ^ 4 * (p.q : ℝ) * Cmix *
            Real.log (2 *
              (highPacketShortLengthV3 (allPacketGlobalV3 packet) : ℝ) *
              (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ)) ^
              highMixedLogExponent delta a *
            (2 * ((componentEndpoints p.X p.beta p.eta component).2 -
                  (componentEndpoints p.X p.beta p.eta component).1) +
              4 * T + 4 * stationaryWidth p.beta p.H +
              (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ) +
              2 * p.X / stationaryWidth p.beta p.H))) :
    dynamicLowNormalizationV3 p *
        activeHighPacketMixedMass p T hX hdelta component packet ≤
      perronCellScale canonicalPerronKFour T ^ 2 *
        dynamicBranchHighWeightRefinedV3 (H₀ := H₀) hX hdelta packet.1 *
        ((divisorCount p.q : ℝ) ^ 4 * Cmix *
          ((3 : ℝ) ^ highMixedLogExponent delta a *
            Real.log p.X ^ highMixedLogExponent delta a) *
          9 * p.X *
          (Q * Real.rpow p.X (-delta) + 1 / Real.sqrt Q +
            Q / stationaryWidth p.beta p.H)) := by
  have hX0 : 0 < p.X := by linarith
  have hX1 : 1 ≤ p.X := by linarith
  have hqNat : 1 ≤ p.q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne p.q)
  have hq : 1 ≤ (p.q : ℝ) := by exact_mod_cast hqNat
  have hq0 : 0 < (p.q : ℝ) := by linarith
  have hQ0 : 0 < Q := by linarith
  have hUval : 0 < stationaryWidth p.beta p.H := by linarith
  have hH0 : 0 < p.H := by
    rw [hH]
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hX0 _)
  have heta0 : 0 < p.eta := by
    rw [heta]
    exact one_div_pos.mpr (Real.sqrt_pos.2 hQ0)
  have hnz := (mem_activeScaledHighPacketsRefinedV3 packet).mp hactive
  have hprod := scaledHighPacket_nonzero_product_boundsRefinedV3 packet hnz
  set M : ℝ := (highPacketShortLengthV3 (allPacketGlobalV3 packet) : ℝ)
  set N : ℝ := (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ)
  set U := stationaryWidth p.beta p.H
  set L := (componentEndpoints p.X p.beta p.eta component).2 -
    (componentEndpoints p.X p.beta p.eta component).1
  set E := highMixedLogExponent delta a
  set D := (divisorCount p.q : ℝ) ^ 4
  set losses := Q * Real.rpow p.X (-delta) + 1 / Real.sqrt Q + Q / U
  have hM : 2 ≤ M := by
    dsimp [M]
    exact_mod_cast (highPacket_geometryV3 (allPacketGlobalV3 packet)).1
  have hN2 : 2 ≤ N := by
    dsimp [N]
    exact_mod_cast (highPacket_geometryV3 (allPacketGlobalV3 packet)).2.1
  have hprod' : M * N ≤ 2 * p.X := by
    simpa [M, N, mul_comm] using hprod.2
  have hNle : N ≤ Real.rpow p.X (7 / 8 : ℝ) :=
    le_of_lt (highPacketLongLength_lt_rpow hX hdelta hgeom
      (allPacketGlobalV3 packet) (by simpa [mul_comm] using hprod.2))
  have hcollar := high_component_collar
    (X := p.X) (H := p.H) (beta := p.beta) (eta := p.eta)
    (q := (p.q : ℝ)) (Q := Q)
    hX0.le hH0 heta0 hQ0 heta hqu (by linarith) component
  have hgeomS := high_free_core_le_three_losses
    (X := p.X) (H := p.H) (U := U) (q := (p.q : ℝ)) (Q := Q)
    (L := L) (N := N) (delta := delta) (reserve := reserve)
    hX1 hU hq hqQ hdeltaUpper hr hH hqu hcollar hNle
  have hlogMN := log_two_mul_prod_le hX0 hlog hM hN2 hprod'
  have hpowE : Real.log (2 * M * N) ^ E ≤ (3 * Real.log p.X) ^ E :=
    pow_le_pow_left₀ hlogMN.1 hlogMN.2 E
  have h3E : (3 * Real.log p.X) ^ E = (3 : ℝ) ^ E * Real.log p.X ^ E :=
    mul_pow _ _ _
  have hw0 : 0 ≤
      dynamicBranchHighWeightRefinedV3 (H₀ := H₀) hX hdelta packet.1 :=
    dynamicBranchHighWeightRefinedV3_nonneg hX hdelta packet.1
  have hsc0 : 0 ≤ perronCellScale canonicalPerronKFour T ^ 2 := sq_nonneg _
  have hD0 : 0 ≤ D := by positivity
  have hcore : (p.q : ℝ) * (2 * L + 4 * T + 4 * U + N + 2 * p.X / U) ≤
      9 * p.X * losses := by
    rw [hTdef]
    simpa [U, L, losses, highThreeLosses] using hgeomS
  have hfac0 : 0 ≤ D * Cmix * Real.log (2 * M * N) ^ E :=
    mul_nonneg (mul_nonneg hD0 hCmix.le) (pow_nonneg hlogMN.1 _)
  have hnine : 0 ≤ 9 * p.X * losses := by
    have : 0 ≤ losses := by
      dsimp [losses]
      positivity
    positivity
  have hcomb :
      D * (p.q : ℝ) * Cmix * Real.log (2 * M * N) ^ E *
          (2 * L + 4 * T + 4 * U + N + 2 * p.X / U) ≤
        D * Cmix * ((3 : ℝ) ^ E * Real.log p.X ^ E) *
          9 * p.X * losses := by
    calc
      D * (p.q : ℝ) * Cmix * Real.log (2 * M * N) ^ E *
          (2 * L + 4 * T + 4 * U + N + 2 * p.X / U)
          = (D * Cmix * Real.log (2 * M * N) ^ E) *
              ((p.q : ℝ) * (2 * L + 4 * T + 4 * U + N + 2 * p.X / U)) := by
            ring
      _ ≤ (D * Cmix * Real.log (2 * M * N) ^ E) * (9 * p.X * losses) :=
        mul_le_mul_of_nonneg_left hcore hfac0
      _ ≤ (D * Cmix * ((3 : ℝ) ^ E * Real.log p.X ^ E)) *
            (9 * p.X * losses) := by
        have hlogE : Real.log (2 * M * N) ^ E ≤
            (3 : ℝ) ^ E * Real.log p.X ^ E := hpowE.trans (le_of_eq h3E)
        have hmid : D * Cmix * Real.log (2 * M * N) ^ E ≤
            D * Cmix * ((3 : ℝ) ^ E * Real.log p.X ^ E) :=
          mul_le_mul_of_nonneg_left hlogE (mul_nonneg hD0 hCmix.le)
        exact mul_le_mul_of_nonneg_right hmid hnine
      _ = D * Cmix * ((3 : ℝ) ^ E * Real.log p.X ^ E) *
          9 * p.X * losses := by ring
  have hscw : 0 ≤ perronCellScale canonicalPerronKFour T ^ 2 *
      dynamicBranchHighWeightRefinedV3 (H₀ := H₀) hX hdelta packet.1 :=
    mul_nonneg hsc0 hw0
  calc
    dynamicLowNormalizationV3 p *
        activeHighPacketMixedMass p T hX hdelta component packet
        ≤ perronCellScale canonicalPerronKFour T ^ 2 *
            dynamicBranchHighWeightRefinedV3 (H₀ := H₀) hX hdelta packet.1 *
            (D * (p.q : ℝ) * Cmix * Real.log (2 * M * N) ^ E *
              (2 * L + 4 * T + 4 * U + N + 2 * p.X / U)) := by
          dsimp only [D, U, L, M, N, E]
          exact hmixed
    _ ≤ perronCellScale canonicalPerronKFour T ^ 2 *
          dynamicBranchHighWeightRefinedV3 (H₀ := H₀) hX hdelta packet.1 *
          (D * Cmix * ((3 : ℝ) ^ E * Real.log p.X ^ E) *
            9 * p.X * losses) :=
        mul_le_mul_of_nonneg_left hcomb hscw
    _ = perronCellScale canonicalPerronKFour T ^ 2 *
          dynamicBranchHighWeightRefinedV3 (H₀ := H₀) hX hdelta packet.1 *
          (D * Cmix * ((3 : ℝ) ^ E * Real.log p.X ^ E) * 9 * p.X *
            (Q * Real.rpow p.X (-delta) + 1 / Real.sqrt Q + Q / U)) := by
          rfl

/-! ## Per-packet sharp-max error lemma -/

/-- One active packet, one outer component: sharp max, free `T`, retain `D`. -/
theorem normalized_freePacketErrorRefinedV3_le
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ T Q reserve Csh : ℝ}
    (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (hX3 : 3 ≤ p.X) (hlog : 1 ≤ Real.log p.X)
    (hQ : 1 ≤ Q) (hqQ : (p.q : ℝ) ≤ Q)
    (hH : p.H = (1 / 2 : ℝ) * Real.rpow p.X (2 / 15 + reserve))
    (heta : p.eta = 1 / Real.sqrt Q)
    (hU : 1 ≤ stationaryWidth p.beta p.H)
    (hr : reserve ≤ 1 / 1200)
    (hTge : 1 ≤ T)
    (hTdef : T = (stationaryWidth p.beta p.H / p.H) *
      Real.rpow p.X (23 / 24 : ℝ))
    (hCsh : 0 < Csh)
    (component : OuterComponent)
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta)
    (hactive : packet ∈
      activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta)
    (hB : sharpPacketConvolutionBoundRefinedV3 packet ≤
      Csh * Real.rpow p.X (1 / 24 : ℝ)) :
    dynamicLowNormalizationV3 p *
        freePacketErrorRefinedV3 p T hX hdelta component packet ≤
      16 * canonicalPerronKFour ^ 2 * (divisorCount p.q : ℝ) ^ 4 *
        (1 / 2 : ℝ) * Csh ^ 2 * 9 *
        Real.rpow Q (3 / 2 : ℝ) * Real.rpow p.X (1 / 2 : ℝ) *
        Real.log p.X ^ 2 := by
  have hX0 : 0 < p.X := by linarith
  have hX1 : 1 ≤ p.X := by linarith
  have hq0 : 0 < (p.q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p.q)
  have hQ0 : 0 < Q := by linarith
  have hU0 : 0 < stationaryWidth p.beta p.H := by linarith
  have hH0 : 0 < p.H := by
    rw [hH]
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hX0 _)
  have heta0 : 0 < p.eta := by
    rw [heta]
    exact one_div_pos.mpr (Real.sqrt_pos.2 hQ0)
  have hUH : stationaryWidth p.beta p.H ≤ p.H :=
    stationaryWidth_le_H hp hH0.le
  have hTle : T ≤ p.X := by
    have hfrac : stationaryWidth p.beta p.H / p.H ≤ 1 :=
      (div_le_one hH0).2 hUH
    have hpow : Real.rpow p.X (23 / 24 : ℝ) ≤ p.X := by
      have h := Real.rpow_le_rpow_of_exponent_le hX1
        (show (23 / 24 : ℝ) ≤ 1 by norm_num)
      simpa [Real.rpow_one] using h
    calc
      T = (stationaryWidth p.beta p.H / p.H) *
          Real.rpow p.X (23 / 24 : ℝ) := hTdef
      _ ≤ 1 * Real.rpow p.X (23 / 24 : ℝ) :=
        mul_le_mul_of_nonneg_right hfrac (Real.rpow_nonneg hX0.le _)
      _ = Real.rpow p.X (23 / 24 : ℝ) := one_mul _
      _ ≤ p.X := hpow
  have hT0 : 0 ≤ T := by linarith
  have hlog2 := log_two_add_truncation_le hX3 hlog hT0 hTle
  have hnz := (mem_activeScaledHighPacketsRefinedV3 packet).mp hactive
  have hprod := scaledHighPacket_nonzero_product_boundsRefinedV3 packet hnz
  set N : ℝ := (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ)
  set M : ℝ := (highPacketShortLengthV3 (allPacketGlobalV3 packet) : ℝ)
  set B := sharpPacketConvolutionBoundRefinedV3 packet
  set U := stationaryWidth p.beta p.H
  set aa := (componentEndpoints p.X p.beta p.eta component).1
  set bb := (componentEndpoints p.X p.beta p.eta component).2
  set D := (divisorCount p.q : ℝ) ^ 4
  have hab : aa ≤ bb :=
    componentEndpoints_mono (beta := p.beta)
      (by linarith : 0 ≤ p.X) hp.2.2.2.2.1 hp.2.2.2.2.2.1 component
  have hNM0 : 0 ≤ N * M := by
    have hN0 : 0 ≤ N := by
      dsimp [N]
      exact_mod_cast (Nat.zero_le (highPacketLongLengthV3 (allPacketGlobalV3 packet)))
    have hM0 : 0 ≤ M := by
      dsimp [M]
      exact_mod_cast (Nat.zero_le (highPacketShortLengthV3 (allPacketGlobalV3 packet)))
    exact mul_nonneg hN0 hM0
  have hproduct : N * M ≤ 2 * p.X := by
    simpa [N, M] using hprod.2
  have hL : bb - aa ≤ U * p.X / (p.eta * p.H) := by
    simpa [aa, bb, U] using
      (componentEndpoints_sub_le_stationaryWidth_mul
        (beta := p.beta) hX0.le hp.2.2.2.2.1.le hH0 component)
  have hB0 : 0 ≤ B := sharpPacketConvolutionBoundRefinedV3_nonneg packet
  have hD0 : 0 ≤ D := by positivity
  have hTsigma : T = (U / p.H) * Real.rpow p.X (1 - (1 / 24 : ℝ)) :=
    selectedT_eq_free_sigma (X := p.X) (H := p.H) (U := U) hTdef
  have herr := normalized_perronCellError_selectedT_le
    (q := p.q) (D := D) (N := N) (M := M) (B := B) (U := U)
    (a := aa) (b := bb) (K := canonicalPerronKFour)
    (X := p.X) (H := p.H) (eta := p.eta) (sigma := (1 / 24 : ℝ)) (T := T)
    hTsigma hq0 hD0 hX0 hH0 hU0 heta0 hab hNM0 hproduct hL
  have hUinv : p.H / (p.eta * U) ≤ p.H / p.eta := by
    have hden : p.eta ≤ p.eta * U := by
      simpa [mul_one] using mul_le_mul_of_nonneg_left hU heta0.le
    exact div_le_div_of_nonneg_left hH0.le heta0 hden
  have hqHeta : (p.q : ℝ) * (p.H / p.eta) ≤
      Q * ((1 / 2 : ℝ) * Real.rpow p.X (2 / 15 + reserve)) * Real.sqrt Q := by
    have hsqrt : 1 / p.eta = Real.sqrt Q := by
      rw [heta]; simp
    have hrewrite : (p.q : ℝ) * (p.H / p.eta) =
        (p.q : ℝ) * p.H * (1 / p.eta) := by
      field_simp [heta0.ne']
    calc
      (p.q : ℝ) * (p.H / p.eta)
          = (p.q : ℝ) * p.H * (1 / p.eta) := hrewrite
      _ ≤ Q * p.H * (1 / p.eta) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hqQ hH0.le) (by positivity)
      _ = Q * p.H * Real.sqrt Q := by rw [hsqrt]
      _ ≤ Q * ((1 / 2 : ℝ) * Real.rpow p.X (2 / 15 + reserve)) *
            Real.sqrt Q := by
        simpa [hH]
  have hB2 : B ^ 2 ≤ Csh ^ 2 * Real.rpow p.X (1 / 12 : ℝ) := by
    have hpow := pow_le_pow_left₀ hB0 hB 2
    have hr :
        (Csh * Real.rpow p.X (1 / 24 : ℝ)) ^ 2 =
          Csh ^ 2 * Real.rpow p.X (1 / 12 : ℝ) := by
      have hm := Real.rpow_mul_natCast hX0.le (1 / 24 : ℝ) 2
      have hexp : (1 / 24 : ℝ) * 2 = (1 / 12 : ℝ) := by norm_num
      calc
        (Csh * Real.rpow p.X (1 / 24 : ℝ)) ^ 2 =
            Csh ^ 2 * (Real.rpow p.X (1 / 24 : ℝ)) ^ 2 := by ring
        _ = Csh ^ 2 * Real.rpow p.X ((1 / 24 : ℝ) * 2) := by
          exact congrArg (fun z : ℝ => Csh ^ 2 * z) hm.symm
        _ = Csh ^ 2 * Real.rpow p.X (1 / 12 : ℝ) := by rw [hexp]
    exact hpow.trans (le_of_eq hr)
  have hsig : Real.rpow p.X (2 * (1 / 24 : ℝ)) =
      Real.rpow p.X (1 / 12 : ℝ) := by norm_num
  have hprodPow : Real.rpow p.X (1 / 12 : ℝ) * Real.rpow p.X (1 / 12 : ℝ) =
      Real.rpow p.X (1 / 6 : ℝ) := by
    calc
      _ = Real.rpow p.X ((1 / 12 : ℝ) + 1 / 12) :=
        (Real.rpow_add hX0 (1 / 12 : ℝ) (1 / 12 : ℝ)).symm
      _ = Real.rpow p.X (1 / 6 : ℝ) := by congr 1 <;> norm_num
  have hhalf : Real.rpow p.X (2 / 15 + reserve) * Real.rpow p.X (1 / 6 : ℝ) ≤
      Real.rpow p.X (1 / 2 : ℝ) := by
    have hadd := (Real.rpow_add hX0 (2 / 15 + reserve) (1 / 6 : ℝ)).symm
    have hle := Real.rpow_le_rpow_of_exponent_le hX1 (high_power_sum_le_half hr)
    exact hadd.trans_le hle
  have hlogT : Real.log (2 + T) ^ 2 ≤ 9 * Real.log p.X ^ 2 := by
    have hpow := pow_le_pow_left₀ hlog2.1 hlog2.2 2
    have h3 : (3 * Real.log p.X) ^ 2 = 9 * Real.log p.X ^ 2 := by ring
    exact h3 ▸ hpow
  have hQ32 : Q * Real.sqrt Q = Real.rpow Q (3 / 2 : ℝ) := by
    calc
      Q * Real.sqrt Q
          = Real.rpow Q 1 * Real.rpow Q (1 / 2 : ℝ) := by
            exact congrArg₂ (fun a b : ℝ => a * b)
              (Real.rpow_one Q).symm (Real.sqrt_eq_rpow Q)
      _ = Real.rpow Q (1 + 1 / 2) :=
        (Real.rpow_add hQ0 1 (1 / 2 : ℝ)).symm
      _ = Real.rpow Q (3 / 2 : ℝ) := by congr 1 <;> norm_num
  have hfree :
      freePacketErrorRefinedV3 p T hX hdelta component packet =
        perronCellError p.q N M T B U aa bb canonicalPerronKFour := rfl
  have hnorm_eq : dynamicLowNormalizationV3 p = D / ((p.q : ℝ) * U ^ 2) := rfl
  have hk0 : 0 ≤ 16 * canonicalPerronKFour ^ 2 * D := by
    have := canonicalPerronKFour_pos
    positivity
  have hB20 : 0 ≤ B ^ 2 := sq_nonneg _
  have hx12 : 0 ≤ Real.rpow p.X (1 / 12 : ℝ) := Real.rpow_nonneg hX0.le _
  have hlog20 : 0 ≤ Real.log (2 + T) ^ 2 := sq_nonneg _
  have hqHU : (p.q : ℝ) * p.H / (p.eta * U) ≤ (p.q : ℝ) * (p.H / p.eta) := by
    have : (p.q : ℝ) * p.H / (p.eta * U) =
        (p.q : ℝ) * (p.H / (p.eta * U)) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hUinv hq0.le
  have hstep1 :
      16 * canonicalPerronKFour ^ 2 * D * (p.q : ℝ) * p.H /
          (p.eta * U) * B ^ 2 *
          Real.rpow p.X (2 * (1 / 24 : ℝ)) * Real.log (2 + T) ^ 2 ≤
        16 * canonicalPerronKFour ^ 2 * D *
          ((p.q : ℝ) * (p.H / p.eta)) * B ^ 2 *
          Real.rpow p.X (1 / 12 : ℝ) * (9 * Real.log p.X ^ 2) := by
    rw [hsig]
    have hleft :
        16 * canonicalPerronKFour ^ 2 * D * (p.q : ℝ) * p.H / (p.eta * U) ≤
          16 * canonicalPerronKFour ^ 2 * D * ((p.q : ℝ) * (p.H / p.eta)) := by
      have : 16 * canonicalPerronKFour ^ 2 * D * (p.q : ℝ) * p.H / (p.eta * U) =
          (16 * canonicalPerronKFour ^ 2 * D) *
            ((p.q : ℝ) * p.H / (p.eta * U)) := by ring
      have : (16 * canonicalPerronKFour ^ 2 * D) *
          ((p.q : ℝ) * (p.H / p.eta)) =
          16 * canonicalPerronKFour ^ 2 * D *
            ((p.q : ℝ) * (p.H / p.eta)) := by ring
      calc
        16 * canonicalPerronKFour ^ 2 * D * (p.q : ℝ) * p.H / (p.eta * U)
            = (16 * canonicalPerronKFour ^ 2 * D) *
                ((p.q : ℝ) * p.H / (p.eta * U)) := by ring
        _ ≤ (16 * canonicalPerronKFour ^ 2 * D) *
              ((p.q : ℝ) * (p.H / p.eta)) :=
          mul_le_mul_of_nonneg_left hqHU hk0
        _ = 16 * canonicalPerronKFour ^ 2 * D *
              ((p.q : ℝ) * (p.H / p.eta)) := by ring
    have hmid := mul_le_mul_of_nonneg_right hleft hB20
    have hmid2 := mul_le_mul_of_nonneg_right hmid hx12
    exact mul_le_mul hmid2 hlogT hlog20 (by
      have := canonicalPerronKFour_pos
      positivity)
  have hstep2 :
      16 * canonicalPerronKFour ^ 2 * D *
          ((p.q : ℝ) * (p.H / p.eta)) * B ^ 2 *
          Real.rpow p.X (1 / 12 : ℝ) * (9 * Real.log p.X ^ 2) ≤
        16 * canonicalPerronKFour ^ 2 * D *
          (Q * ((1 / 2 : ℝ) * Real.rpow p.X (2 / 15 + reserve)) *
            Real.sqrt Q) *
          (Csh ^ 2 * Real.rpow p.X (1 / 12 : ℝ)) *
          Real.rpow p.X (1 / 12 : ℝ) * (9 * Real.log p.X ^ 2) := by
    have hleft :
        16 * canonicalPerronKFour ^ 2 * D *
            ((p.q : ℝ) * (p.H / p.eta)) * B ^ 2 ≤
          16 * canonicalPerronKFour ^ 2 * D *
            (Q * ((1 / 2 : ℝ) * Real.rpow p.X (2 / 15 + reserve)) *
              Real.sqrt Q) *
            (Csh ^ 2 * Real.rpow p.X (1 / 12 : ℝ)) := by
      have h1 := mul_le_mul_of_nonneg_left hqHeta hk0
      have hQterm : 0 ≤ Q * ((1 / 2 : ℝ) * Real.rpow p.X
          (2 / 15 + reserve)) * Real.sqrt Q := by
        exact mul_nonneg
          (mul_nonneg hQ0.le
            (mul_nonneg (by norm_num) (Real.rpow_nonneg hX0.le _)))
          (Real.sqrt_nonneg _)
      have hcoef : 0 ≤ 16 * canonicalPerronKFour ^ 2 * D *
          (Q * ((1 / 2 : ℝ) * Real.rpow p.X (2 / 15 + reserve)) *
            Real.sqrt Q) := by
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hD0) hQterm
      have h2 := mul_le_mul h1 hB2 hB20 hcoef
      convert h2 using 1 <;> ring
    have hlog9 : 0 ≤ 9 * Real.log p.X ^ 2 := by positivity
    have hmid := mul_le_mul_of_nonneg_right hleft hx12
    exact mul_le_mul_of_nonneg_right hmid hlog9
  have hstep3 :
      16 * canonicalPerronKFour ^ 2 * D *
          (Q * ((1 / 2 : ℝ) * Real.rpow p.X (2 / 15 + reserve)) *
            Real.sqrt Q) *
          (Csh ^ 2 * Real.rpow p.X (1 / 12 : ℝ)) *
          Real.rpow p.X (1 / 12 : ℝ) * (9 * Real.log p.X ^ 2) ≤
        16 * canonicalPerronKFour ^ 2 * D * (1 / 2 : ℝ) * Csh ^ 2 * 9 *
          Real.rpow Q (3 / 2 : ℝ) * Real.rpow p.X (1 / 2 : ℝ) *
          Real.log p.X ^ 2 := by
    have hcs : 0 ≤ Csh ^ 2 := sq_nonneg _
    have hk := canonicalPerronKFour_pos
    have hrewritten :
        16 * canonicalPerronKFour ^ 2 * D *
            (Q * ((1 / 2 : ℝ) * Real.rpow p.X (2 / 15 + reserve)) *
              Real.sqrt Q) *
            (Csh ^ 2 * Real.rpow p.X (1 / 12 : ℝ)) *
            Real.rpow p.X (1 / 12 : ℝ) * (9 * Real.log p.X ^ 2) =
          16 * canonicalPerronKFour ^ 2 * D * (1 / 2 : ℝ) * Csh ^ 2 * 9 *
            (Q * Real.sqrt Q) *
            (Real.rpow p.X (2 / 15 + reserve) * Real.rpow p.X (1 / 6 : ℝ)) *
            Real.log p.X ^ 2 := by
            calc
              _ = 16 * canonicalPerronKFour ^ 2 * D * (1 / 2 : ℝ) * Csh ^ 2 * 9 *
                    (Q * Real.sqrt Q) *
                    (Real.rpow p.X (2 / 15 + reserve) *
                      (Real.rpow p.X (1 / 12 : ℝ) * Real.rpow p.X (1 / 12 : ℝ))) *
                    Real.log p.X ^ 2 := by ring
              _ = _ := by rw [hprodPow]
    have hpowX :
        16 * canonicalPerronKFour ^ 2 * D * (1 / 2 : ℝ) * Csh ^ 2 * 9 *
            (Q * Real.sqrt Q) *
            (Real.rpow p.X (2 / 15 + reserve) * Real.rpow p.X (1 / 6 : ℝ)) *
            Real.log p.X ^ 2 ≤
          16 * canonicalPerronKFour ^ 2 * D * (1 / 2 : ℝ) * Csh ^ 2 * 9 *
            (Q * Real.sqrt Q) * Real.rpow p.X (1 / 2 : ℝ) *
            Real.log p.X ^ 2 := by
      have hpre : 0 ≤
          16 * canonicalPerronKFour ^ 2 * D * (1 / 2 : ℝ) * Csh ^ 2 * 9 *
            (Q * Real.sqrt Q) := by positivity
      have hlog0 : 0 ≤ Real.log p.X ^ 2 := sq_nonneg _
      have hmid := mul_le_mul_of_nonneg_left hhalf hpre
      exact mul_le_mul_of_nonneg_right hmid hlog0
    have hpowQ :
        16 * canonicalPerronKFour ^ 2 * D * (1 / 2 : ℝ) * Csh ^ 2 * 9 *
            (Q * Real.sqrt Q) * Real.rpow p.X (1 / 2 : ℝ) *
            Real.log p.X ^ 2 =
          16 * canonicalPerronKFour ^ 2 * D * (1 / 2 : ℝ) * Csh ^ 2 * 9 *
            Real.rpow Q (3 / 2 : ℝ) * Real.rpow p.X (1 / 2 : ℝ) *
            Real.log p.X ^ 2 := by
      rw [hQ32]
    exact (le_of_eq hrewritten).trans (hpowX.trans (le_of_eq hpowQ))
  calc
    dynamicLowNormalizationV3 p *
        freePacketErrorRefinedV3 p T hX hdelta component packet
        = D / ((p.q : ℝ) * U ^ 2) *
            perronCellError p.q N M T B U aa bb canonicalPerronKFour := by
          rw [hnorm_eq, hfree]
    _ ≤ 16 * canonicalPerronKFour ^ 2 * D * (p.q : ℝ) * p.H /
          (p.eta * U) * B ^ 2 *
          Real.rpow p.X (2 * (1 / 24 : ℝ)) * Real.log (2 + T) ^ 2 := herr
    _ ≤ 16 * canonicalPerronKFour ^ 2 * D *
          ((p.q : ℝ) * (p.H / p.eta)) * B ^ 2 *
          Real.rpow p.X (1 / 12 : ℝ) * (9 * Real.log p.X ^ 2) := hstep1
    _ ≤ 16 * canonicalPerronKFour ^ 2 * D *
          (Q * ((1 / 2 : ℝ) * Real.rpow p.X (2 / 15 + reserve)) *
            Real.sqrt Q) *
          (Csh ^ 2 * Real.rpow p.X (1 / 12 : ℝ)) *
          Real.rpow p.X (1 / 12 : ℝ) * (9 * Real.log p.X ^ 2) := hstep2
    _ ≤ 16 * canonicalPerronKFour ^ 2 * D * (1 / 2 : ℝ) * Csh ^ 2 * 9 *
          Real.rpow Q (3 / 2 : ℝ) * Real.rpow p.X (1 / 2 : ℝ) *
          Real.log p.X ^ 2 := hstep3

/-! ## Sixteen × two-component mixed sum, retaining `D` and `perronCellScale^2` -/

theorem normalized_active_mixed_sixteen_sum_le
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ T Q reserve Cmix Cw : ℝ} {a R : ℕ}
    (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 240)
    (hlog : 1 ≤ Real.log p.X)
    (hQ : 1 ≤ Q) (hqQ : (p.q : ℝ) ≤ Q)
    (hH : p.H = (1 / 2 : ℝ) * Real.rpow p.X (2 / 15 + reserve))
    (heta : p.eta = 1 / Real.sqrt Q)
    (hU : 1 ≤ stationaryWidth p.beta p.H)
    (hqu : (p.q : ℝ) * stationaryWidth p.beta p.H ≤ p.H / Q)
    (hr : reserve ≤ 1 / 1200)
    (hTge : 1 ≤ T)
    (hTdef : T = (stationaryWidth p.beta p.H / p.H) *
      Real.rpow p.X (23 / 24 : ℝ))
    (hCmix : 0 < Cmix) (hCw : 0 < Cw)
    (hgeom : Real.rpow p.X delta * (2 * Real.rpow p.X ((8 : ℝ)⁻¹)) ≤ 2 * H₀)
    (hweight :
      (∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
        dynamicBranchHighWeightRefinedV3 (H₀ := H₀) hX hdelta packet.1) ≤
      Cw * Real.log p.X ^ R)
    (hmixed :
      ∀ (component : OuterComponent)
        (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta),
        packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta →
        dynamicLowNormalizationV3 p *
            activeHighPacketMixedMass p T hX hdelta component packet ≤
          perronCellScale canonicalPerronKFour T ^ 2 *
            dynamicBranchHighWeightRefinedV3 (H₀ := H₀) hX hdelta packet.1 *
            ((divisorCount p.q : ℝ) ^ 4 * (p.q : ℝ) * Cmix *
              Real.log (2 *
                (highPacketShortLengthV3 (allPacketGlobalV3 packet) : ℝ) *
                (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ)) ^
                highMixedLogExponent delta a *
              (2 * ((componentEndpoints p.X p.beta p.eta component).2 -
                    (componentEndpoints p.X p.beta p.eta component).1) +
                4 * T + 4 * stationaryWidth p.beta p.H +
                (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ) +
                2 * p.X / stationaryWidth p.beta p.H))) :
    dynamicLowNormalizationV3 p *
        activeIndexedMixedTotal (H₀ := H₀) T hX hdelta ≤
      (16 : ℝ) * 2 * perronCellScale canonicalPerronKFour T ^ 2 *
        Cmix *
        ((3 : ℝ) ^ highMixedLogExponent delta a *
          Real.log p.X ^ highMixedLogExponent delta a) *
        9 * p.X *
        (Q * Real.rpow p.X (-delta) + 1 / Real.sqrt Q +
          Q / stationaryWidth p.beta p.H) *
        (divisorCount p.q : ℝ) ^ 4 *
        (Cw * Real.log p.X ^ R) := by
  set E := highMixedLogExponent delta a
  set D := (divisorCount p.q : ℝ) ^ 4
  set U := stationaryWidth p.beta p.H
  set losses := Q * Real.rpow p.X (-delta) + 1 / Real.sqrt Q + Q / U
  have hrest0 : 0 ≤
      D * Cmix * ((3 : ℝ) ^ E * Real.log p.X ^ E) * 9 * p.X * losses := by
    have hD0 : 0 ≤ D := by positivity
    have hE : 0 ≤ (3 : ℝ) ^ E := by positivity
    have hlogE : 0 ≤ Real.log p.X ^ E := pow_nonneg (by linarith) _
    have hloss : 0 ≤ losses := by
      dsimp [losses]
      positivity
    positivity
  have hsc0 : 0 ≤ perronCellScale canonicalPerronKFour T ^ 2 := sq_nonneg _
  have hone (component : OuterComponent)
      (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta)
      (hactive : packet ∈
        activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta) :
      dynamicLowNormalizationV3 p *
          activeHighPacketMixedMass p T hX hdelta component packet ≤
        perronCellScale canonicalPerronKFour T ^ 2 *
          dynamicBranchHighWeightRefinedV3 (H₀ := H₀) hX hdelta packet.1 *
          (D * Cmix * ((3 : ℝ) ^ E * Real.log p.X ^ E) *
            9 * p.X * losses) := by
    have hpkt :=
      normalized_activeHighPacketMixedMass_le hp hX hdelta hdeltaUpper
        hlog hQ hqQ hH heta hU hqu hr hTge hTdef hCmix hgeom
        component packet hactive (hmixed component packet hactive)
    dsimp only [D, E, U, losses]
    exact hpkt
  have hsumP (component : OuterComponent) :
      (∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
          dynamicLowNormalizationV3 p *
            activeHighPacketMixedMass p T hX hdelta component packet) ≤
        perronCellScale canonicalPerronKFour T ^ 2 *
          (D * Cmix * ((3 : ℝ) ^ E * Real.log p.X ^ E) * 9 * p.X * losses) *
          (Cw * Real.log p.X ^ R) := by
    have hle := Finset.sum_le_sum fun packet hpkt => hone component packet hpkt
    have hfactor :
        (∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
          perronCellScale canonicalPerronKFour T ^ 2 *
            dynamicBranchHighWeightRefinedV3 (H₀ := H₀) hX hdelta packet.1 *
            (D * Cmix * ((3 : ℝ) ^ E * Real.log p.X ^ E) *
              9 * p.X * losses)) =
          (perronCellScale canonicalPerronKFour T ^ 2 *
            (D * Cmix * ((3 : ℝ) ^ E * Real.log p.X ^ E) *
              9 * p.X * losses)) *
          ∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
            dynamicBranchHighWeightRefinedV3 (H₀ := H₀) hX hdelta packet.1 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro packet _
      ring
    have hscw0 : 0 ≤ perronCellScale canonicalPerronKFour T ^ 2 *
        (D * Cmix * ((3 : ℝ) ^ E * Real.log p.X ^ E) * 9 * p.X * losses) :=
      mul_nonneg hsc0 hrest0
    calc
      _ ≤ _ := hle
      _ = (perronCellScale canonicalPerronKFour T ^ 2 *
            (D * Cmix * ((3 : ℝ) ^ E * Real.log p.X ^ E) *
              9 * p.X * losses)) *
          ∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
            dynamicBranchHighWeightRefinedV3 (H₀ := H₀) hX hdelta packet.1 :=
        hfactor
      _ ≤ (perronCellScale canonicalPerronKFour T ^ 2 *
            (D * Cmix * ((3 : ℝ) ^ E * Real.log p.X ^ E) *
              9 * p.X * losses)) *
          (Cw * Real.log p.X ^ R) :=
        mul_le_mul_of_nonneg_left hweight hscw0
      _ = perronCellScale canonicalPerronKFour T ^ 2 *
            (D * Cmix * ((3 : ℝ) ^ E * Real.log p.X ^ E) *
              9 * p.X * losses) *
            (Cw * Real.log p.X ^ R) := by ring
  have hsumC :
      (∑ component : OuterComponent,
        ∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
          dynamicLowNormalizationV3 p *
            activeHighPacketMixedMass p T hX hdelta component packet) ≤
      ∑ component : OuterComponent,
        perronCellScale canonicalPerronKFour T ^ 2 *
          (D * Cmix * ((3 : ℝ) ^ E * Real.log p.X ^ E) *
            9 * p.X * losses) * (Cw * Real.log p.X ^ R) := by
    apply Finset.sum_le_sum
    intro component _
    exact hsumP component
  have hconst :
      (∑ _c : OuterComponent,
          perronCellScale canonicalPerronKFour T ^ 2 *
            (D * Cmix * ((3 : ℝ) ^ E * Real.log p.X ^ E) *
              9 * p.X * losses) *
            (Cw * Real.log p.X ^ R)) =
        2 * perronCellScale canonicalPerronKFour T ^ 2 *
          (D * Cmix * ((3 : ℝ) ^ E * Real.log p.X ^ E) *
            9 * p.X * losses) *
          (Cw * Real.log p.X ^ R) := by
    simp [Finset.sum_const, Finset.card_univ, outerComponent_card, nsmul_eq_mul]
    ring
  have h16 :
      dynamicLowNormalizationV3 p *
          (16 * ∑ component : OuterComponent,
            ∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
              activeHighPacketMixedMass p T hX hdelta component packet) =
        16 * ∑ component : OuterComponent,
          ∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
            dynamicLowNormalizationV3 p *
              activeHighPacketMixedMass p T hX hdelta component packet := by
    calc
      dynamicLowNormalizationV3 p *
          (16 * ∑ component : OuterComponent,
            ∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
              activeHighPacketMixedMass p T hX hdelta component packet) =
        16 * (dynamicLowNormalizationV3 p *
          ∑ component : OuterComponent,
            ∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
              activeHighPacketMixedMass p T hX hdelta component packet) := by
        ring
      _ = 16 * ∑ component : OuterComponent,
            (dynamicLowNormalizationV3 p *
              ∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
                activeHighPacketMixedMass p T hX hdelta component packet) := by
        rw [Finset.mul_sum]
      _ = 16 * ∑ component : OuterComponent,
            ∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
              dynamicLowNormalizationV3 p *
                activeHighPacketMixedMass p T hX hdelta component packet := by
        simp_rw [Finset.mul_sum]
  have hnorm0 : 0 ≤ (16 : ℝ) := by norm_num
  calc
    dynamicLowNormalizationV3 p *
        activeIndexedMixedTotal (H₀ := H₀) T hX hdelta =
      dynamicLowNormalizationV3 p *
        (16 * ∑ component : OuterComponent,
          ∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
            activeHighPacketMixedMass p T hX hdelta component packet) := by
      rw [activeIndexedMixedTotal_eq_sixteen_active_sum (H₀ := H₀) T hX hdelta]
    _ = 16 * ∑ component : OuterComponent,
          ∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
            dynamicLowNormalizationV3 p *
              activeHighPacketMixedMass p T hX hdelta component packet := h16
    _ ≤ 16 * (2 * perronCellScale canonicalPerronKFour T ^ 2 *
          (D * Cmix * ((3 : ℝ) ^ E * Real.log p.X ^ E) *
            9 * p.X * losses) *
          (Cw * Real.log p.X ^ R)) :=
      mul_le_mul_of_nonneg_left (hsumC.trans (le_of_eq hconst)) hnorm0
    _ = (16 : ℝ) * 2 * perronCellScale canonicalPerronKFour T ^ 2 *
          Cmix * ((3 : ℝ) ^ E * Real.log p.X ^ E) * 9 * p.X * losses * D *
          (Cw * Real.log p.X ^ R) := by
        dsimp [D, E, losses, U]
        ring

/-! ## Two-component sharp-max error sum, retaining `D` -/

theorem normalized_highActiveErrorTotal_le
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ T Q reserve Csh Cw : ℝ} {R : ℕ}
    (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (hX3 : 3 ≤ p.X) (hlog : 1 ≤ Real.log p.X)
    (hQ : 1 ≤ Q) (hqQ : (p.q : ℝ) ≤ Q)
    (hH : p.H = (1 / 2 : ℝ) * Real.rpow p.X (2 / 15 + reserve))
    (heta : p.eta = 1 / Real.sqrt Q)
    (hU : 1 ≤ stationaryWidth p.beta p.H)
    (hr : reserve ≤ 1 / 1200)
    (hTge : 1 ≤ T)
    (hTdef : T = (stationaryWidth p.beta p.H / p.H) *
      Real.rpow p.X (23 / 24 : ℝ))
    (hCsh : 0 < Csh) (hCw : 0 < Cw)
    (hcard :
      ((activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta).card : ℝ) ≤
        Cw * Real.log p.X ^ R)
    (hB :
      ∀ (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta),
        packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta →
        sharpPacketConvolutionBoundRefinedV3 packet ≤
          Csh * Real.rpow p.X (1 / 24 : ℝ)) :
    dynamicLowNormalizationV3 p *
        highActiveErrorTotal (H₀ := H₀) p T hX hdelta ≤
      2 * (Cw * Real.log p.X ^ R) *
        (16 * canonicalPerronKFour ^ 2 * (divisorCount p.q : ℝ) ^ 4 *
          (1 / 2 : ℝ) * Csh ^ 2 * 9 *
          Real.rpow Q (3 / 2 : ℝ) * Real.rpow p.X (1 / 2 : ℝ) *
          Real.log p.X ^ 2) := by
  set D := (divisorCount p.q : ℝ) ^ 4
  set pktBound :=
    16 * canonicalPerronKFour ^ 2 * D * (1 / 2 : ℝ) * Csh ^ 2 * 9 *
      Real.rpow Q (3 / 2 : ℝ) * Real.rpow p.X (1 / 2 : ℝ) *
      Real.log p.X ^ 2
  have hpkt0 : 0 ≤ pktBound := by
    have := canonicalPerronKFour_pos
    dsimp [pktBound, D]
    positivity
  have hone (component : OuterComponent)
      (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta)
      (hactive : packet ∈
        activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta) :
      dynamicLowNormalizationV3 p *
          freePacketErrorRefinedV3 p T hX hdelta component packet ≤
        pktBound := by
    have hpkt :=
      normalized_freePacketErrorRefinedV3_le hp hX hdelta hX3 hlog hQ hqQ
        hH heta hU hr hTge hTdef hCsh component packet hactive
        (hB packet hactive)
    dsimp only [pktBound, D]
    exact hpkt
  have hsumP (component : OuterComponent) :
      (∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
          dynamicLowNormalizationV3 p *
            freePacketErrorRefinedV3 p T hX hdelta component packet) ≤
        ((activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta).card : ℝ) *
          pktBound := by
    have hle := Finset.sum_le_sum fun packet hpkt => hone component packet hpkt
    calc
      _ ≤ ∑ _packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
            pktBound := hle
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  have hsumC :
      (∑ component : OuterComponent,
        ∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
          dynamicLowNormalizationV3 p *
            freePacketErrorRefinedV3 p T hX hdelta component packet) ≤
      ∑ component : OuterComponent,
        ((activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta).card : ℝ) *
          pktBound := by
    apply Finset.sum_le_sum
    intro component _
    exact hsumP component
  have hconst :
      (∑ _c : OuterComponent,
          ((activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta).card : ℝ) *
            pktBound) =
        2 * ((activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta).card : ℝ) *
          pktBound := by
    simp [Finset.sum_const, Finset.card_univ, outerComponent_card, nsmul_eq_mul]
    ring
  have h16 :
      dynamicLowNormalizationV3 p *
          highActiveErrorTotal (H₀ := H₀) p T hX hdelta =
        ∑ component : OuterComponent,
          ∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
            dynamicLowNormalizationV3 p *
              freePacketErrorRefinedV3 p T hX hdelta component packet := by
    unfold highActiveErrorTotal
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
  have hcard0 : 0 ≤
      ((activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta).card : ℝ) :=
    Nat.cast_nonneg _
  calc
    dynamicLowNormalizationV3 p *
        highActiveErrorTotal (H₀ := H₀) p T hX hdelta =
      ∑ component : OuterComponent,
        ∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
          dynamicLowNormalizationV3 p *
            freePacketErrorRefinedV3 p T hX hdelta component packet := h16
    _ ≤ 2 * ((activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta).card : ℝ) *
          pktBound := hsumC.trans (le_of_eq hconst)
    _ ≤ 2 * (Cw * Real.log p.X ^ R) * pktBound :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcard (by norm_num)) hpkt0
    _ = 2 * (Cw * Real.log p.X ^ R) *
          (16 * canonicalPerronKFour ^ 2 * (divisorCount p.q : ℝ) ^ 4 *
            (1 / 2 : ℝ) * Csh ^ 2 * 9 *
            Real.rpow Q (3 / 2 : ℝ) * Real.rpow p.X (1 / 2 : ℝ) *
            Real.log p.X ^ 2) := by
        dsimp [pktBound, D]

/-! ## Uniform scalar envelope for the adopted mixed-plus-error mass -/

theorem exists_uniform_normalized_high_le_scalar_envelope
    (delta : ℝ) (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 240) :
    ∃ Ctotal : ℝ, 0 < Ctotal ∧ ∃ P : ℕ, ∃ X₁ : ℝ, 3 ≤ X₁ ∧
      ∀ (p : Corollary53Input) [NeZero p.q]
        (hp : Corollary53Admissible 1 1 p) (Q reserve : ℝ)
        (hX₁ : X₁ ≤ p.X) (hX3 : 3 ≤ p.X) (hX2 : 2 ≤ p.X)
        (hlog : 1 ≤ Real.log p.X)
        (hQ : 1 ≤ Q) (hqQ : (p.q : ℝ) ≤ Q)
        (hH : p.H = (1 / 2 : ℝ) * Real.rpow p.X (2 / 15 + reserve))
        (heta : p.eta = 1 / Real.sqrt Q)
        (hU : 1 ≤ stationaryWidth p.beta p.H)
        (hqu : p.q * stationaryWidth p.beta p.H ≤ p.H / Q)
        (hr0 : 0 ≤ reserve) (hr : reserve ≤ 1 / 1200),
        let T := selectedHighTruncation p
        let H₀ := highClassifierH0 p.X delta
        dynamicLowNormalizationV3 p *
          highActivePacketMass (H₀ := H₀) p T hX2 hdelta ≤
          Ctotal * p.X * Real.log p.X ^ P *
            (Real.rpow Q (1 / 8 : ℝ) *
                (Q * Real.rpow p.X (-delta) + 1 / Real.sqrt Q +
                  Q / stationaryWidth p.beta p.H) +
              Real.rpow Q (13 / 8 : ℝ) * Real.rpow p.X (-(1 / 2 : ℝ))) := by
  classical
  obtain ⟨a, Cmix0, hCmix0, hmixed⟩ :=
    explicit_activeHighMixed_bound delta hdelta
  obtain ⟨Csh, Xsh, hCsh, hXsh, hsharp⟩ :=
    exists_active_sharpPacketConvolutionBoundRefinedV3 delta (1 / 24)
      hdelta (by norm_num)
  obtain ⟨Cw, hCw, R, hcount⟩ := exists_active_count_and_weight_polylog delta
  obtain ⟨Cd, hCd, hdiv⟩ :=
    exists_divisorCount_four_le_range_subpower (1 / 8) (by norm_num)
  let E : ℕ := highMixedLogExponent delta a
  let P : ℕ := R + E + 2
  let Cscale : ℝ := 8 * canonicalPerronKFour ^ 2
  let CmixConst : ℝ :=
    (16 : ℝ) * 2 * 9 * (Cscale * 9) * Cmix0 * Cw * (3 : ℝ) ^ E
  let CerrConst : ℝ :=
    (2 : ℝ) * Cw * 16 * canonicalPerronKFour ^ 2 * (1 / 2 : ℝ) * Csh ^ 2 * 9
  let Ctotal : ℝ := 1 + Cd * (CmixConst + CerrConst)
  have hCscale : 0 ≤ Cscale := by
    dsimp [Cscale]
    have := canonicalPerronKFour_pos
    positivity
  have hCmixConst : 0 ≤ CmixConst := by
    dsimp [CmixConst, Cscale]
    have := canonicalPerronKFour_pos
    positivity
  have hCerrConst : 0 ≤ CerrConst := by
    dsimp [CerrConst]
    have := canonicalPerronKFour_pos
    positivity
  have htotal : 0 < Ctotal := by
    dsimp [Ctotal]
    positivity
  refine ⟨Ctotal, htotal, P, max 3 Xsh, le_max_left _ _, ?_⟩
  intro p _ hp Q reserve hX₁ hX3 hX2 hlog hQ hqQ hH heta hU hqu hr0 hr
  dsimp only
  let T := selectedHighTruncation p
  let H₀ := highClassifierH0 p.X delta
  let U := stationaryWidth p.beta p.H
  let D := (divisorCount p.q : ℝ) ^ 4
  let losses := highThreeLosses p.X U Q delta
  have hX0 : 0 < p.X := by linarith
  have hX1 : 1 ≤ p.X := by linarith
  have hqNat : 1 ≤ p.q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne p.q)
  have hQ0 : 0 < Q := by linarith
  have hlog0 : 0 ≤ Real.log p.X := by linarith
  have hU0 : 0 < U := by dsimp [U]; linarith
  have hH0 : 0 < p.H := by
    rw [hH]
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hX0 _)
  have hUH : U ≤ p.H := by
    dsimp [U]
    exact stationaryWidth_le_H hp hH0.le
  have hTge : 1 ≤ T :=
    highFreeTruncation_ge_one_of_H hX1 hU hH hr
  have hTle : T ≤ p.X :=
    highFreeTruncation_le_X_of_width hX1 hH0 hUH (by linarith)
  have hT0 : 0 ≤ T := by linarith
  have hTdef : T = (U / p.H) * Real.rpow p.X (23 / 24 : ℝ) := rfl
  have hgeom : Real.rpow p.X delta *
      (2 * Real.rpow p.X ((8 : ℝ)⁻¹)) ≤ 2 * H₀ := by
    dsimp [H₀, highClassifierH0]
    simpa [one_div] using
      (typeII_parameter_geometry_eq (X := p.X) (delta := delta) hX0).le
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hloss : 0 ≤ losses := by
    dsimp [losses, highThreeLosses]
    positivity
  have hlog1 := log_one_add_truncation_le hX3 hlog hT0 hTle
  have hscale : perronCellScale canonicalPerronKFour T ^ 2 ≤
      Cscale * 9 * Real.log p.X ^ 2 := by
    have heq := perronCellScale_sq_log hT0
    have hsq : Real.log (1 + T) ^ 2 ≤ 9 * Real.log p.X ^ 2 := by
      have hpow := pow_le_pow_left₀ hlog1.1 hlog1.2 2
      have h3 : (3 * Real.log p.X) ^ 2 = 9 * Real.log p.X ^ 2 := by ring
      exact hpow.trans (le_of_eq h3)
    have hk0 : 0 ≤ 8 * canonicalPerronKFour ^ 2 := by
      have := canonicalPerronKFour_pos
      positivity
    calc
      perronCellScale canonicalPerronKFour T ^ 2
          = 8 * canonicalPerronKFour ^ 2 * Real.log (1 + T) ^ 2 := heq
      _ ≤ 8 * canonicalPerronKFour ^ 2 * (9 * Real.log p.X ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hk0
      _ = Cscale * 9 * Real.log p.X ^ 2 := by
        dsimp [Cscale]; ring
  have hcountp := hcount (X := p.X) (H₀ := H₀) hX3 hX2 hdelta
  have hdivp : D ≤ Cd * Real.rpow Q (1 / 8 : ℝ) :=
    hdiv p.q Q hqNat hqQ
  have hpowP : Real.log p.X ^ (R + 2) ≤ Real.log p.X ^ P :=
    pow_le_pow_right₀ hlog (by dsimp [P]; omega)
  have hXsh : Xsh ≤ p.X := (le_max_right 3 Xsh).trans hX₁
  have hmixed_sum :
      dynamicLowNormalizationV3 p *
          activeIndexedMixedTotal (H₀ := H₀) T hX2 hdelta ≤
        CmixConst * D * p.X * Real.log p.X ^ P * losses := by
    have hsum :=
      normalized_active_mixed_sixteen_sum_le (H₀ := H₀) (T := T)
        (Q := Q) (reserve := reserve) (Cmix := Cmix0) (Cw := Cw) (a := a)
        (R := R) hp hX2 hdelta hdeltaUpper hlog hQ hqQ hH heta hU hqu hr
        hTge hTdef hCmix0 hCw hgeom hcountp.2
        (fun component packet hactive =>
          hmixed p hp H₀ T hX2 hTge hU component packet hactive)
    have hscw0 : 0 ≤
        (16 : ℝ) * 2 * Cmix0 *
          ((3 : ℝ) ^ E * Real.log p.X ^ E) * 9 * p.X * losses * D *
          (Cw * Real.log p.X ^ R) := by
      dsimp [E, D, losses]
      positivity
    have hscale_sum :
        (16 : ℝ) * 2 * perronCellScale canonicalPerronKFour T ^ 2 *
            Cmix0 *
            ((3 : ℝ) ^ highMixedLogExponent delta a *
              Real.log p.X ^ highMixedLogExponent delta a) *
            9 * p.X *
            (Q * Real.rpow p.X (-delta) + 1 / Real.sqrt Q + Q / U) *
            D * (Cw * Real.log p.X ^ R) ≤
          (16 : ℝ) * 2 * (Cscale * 9 * Real.log p.X ^ 2) *
            Cmix0 *
            ((3 : ℝ) ^ E * Real.log p.X ^ E) *
            9 * p.X * losses * D * (Cw * Real.log p.X ^ R) := by
      have hleft := mul_le_mul_of_nonneg_right hscale hscw0
      have hL :
          (16 : ℝ) * 2 * perronCellScale canonicalPerronKFour T ^ 2 *
              Cmix0 *
              ((3 : ℝ) ^ highMixedLogExponent delta a *
                Real.log p.X ^ highMixedLogExponent delta a) *
              9 * p.X *
              (Q * Real.rpow p.X (-delta) + 1 / Real.sqrt Q + Q / U) *
              D * (Cw * Real.log p.X ^ R) =
            perronCellScale canonicalPerronKFour T ^ 2 *
              ((16 : ℝ) * 2 * Cmix0 *
                ((3 : ℝ) ^ E * Real.log p.X ^ E) * 9 * p.X * losses * D *
                (Cw * Real.log p.X ^ R)) := by
        dsimp [E, losses, highThreeLosses, U]; ring
      have hR :
          (16 : ℝ) * 2 * (Cscale * 9 * Real.log p.X ^ 2) *
              Cmix0 *
              ((3 : ℝ) ^ E * Real.log p.X ^ E) *
              9 * p.X * losses * D * (Cw * Real.log p.X ^ R) =
            (Cscale * 9 * Real.log p.X ^ 2) *
              ((16 : ℝ) * 2 * Cmix0 *
                ((3 : ℝ) ^ E * Real.log p.X ^ E) * 9 * p.X * losses * D *
                (Cw * Real.log p.X ^ R)) := by
        ring
      rw [hL, hR]
      exact hleft
    have hpowlog : Real.log p.X ^ 2 * Real.log p.X ^ E * Real.log p.X ^ R =
        Real.log p.X ^ P := by
      dsimp [P]
      rw [← pow_add, ← pow_add]
      congr 1
      ring
    calc
      _ ≤ _ := hsum
      _ ≤ (16 : ℝ) * 2 * (Cscale * 9 * Real.log p.X ^ 2) *
            Cmix0 * ((3 : ℝ) ^ E * Real.log p.X ^ E) *
            9 * p.X * losses * D * (Cw * Real.log p.X ^ R) := hscale_sum
      _ = CmixConst * D * p.X * Real.log p.X ^ P * losses := by
            dsimp [CmixConst, E]
            rw [← hpowlog]
            ring
  have herr_sum :
      dynamicLowNormalizationV3 p *
          highActiveErrorTotal (H₀ := H₀) p T hX2 hdelta ≤
        CerrConst * D * Real.rpow Q (3 / 2 : ℝ) *
          Real.rpow p.X (1 / 2 : ℝ) * Real.log p.X ^ P := by
    have hsum :=
      normalized_highActiveErrorTotal_le (H₀ := H₀) (T := T)
        (Q := Q) (reserve := reserve) (Csh := Csh) (Cw := Cw) (R := R)
        hp hX2 hdelta hX3 hlog hQ hqQ hH heta hU hr hTge hTdef hCsh hCw
        hcountp.1
        (fun packet hactive => hsharp hXsh hX2 packet hactive)
    have hpowlog : Real.log p.X ^ 2 * Real.log p.X ^ R =
        Real.log p.X ^ (R + 2) := by
      rw [← pow_add, add_comm]
    calc
      _ ≤ _ := hsum
      _ = CerrConst * D * Real.rpow Q (3 / 2 : ℝ) *
            Real.rpow p.X (1 / 2 : ℝ) * Real.log p.X ^ (R + 2) := by
            dsimp [CerrConst, D]
            rw [← hpowlog]
            ring
      _ ≤ CerrConst * D * Real.rpow Q (3 / 2 : ℝ) *
            Real.rpow p.X (1 / 2 : ℝ) * Real.log p.X ^ P := by
            have hC0 : 0 ≤ CerrConst * D * Real.rpow Q (3 / 2 : ℝ) *
                Real.rpow p.X (1 / 2 : ℝ) := by
              dsimp [CerrConst, D]
              have := canonicalPerronKFour_pos
              positivity
            exact mul_le_mul_of_nonneg_left hpowP hC0
  have hmass :
      dynamicLowNormalizationV3 p *
          highActivePacketMass (H₀ := H₀) p T hX2 hdelta =
        dynamicLowNormalizationV3 p *
            activeIndexedMixedTotal (H₀ := H₀) T hX2 hdelta +
          dynamicLowNormalizationV3 p *
            highActiveErrorTotal (H₀ := H₀) p T hX2 hdelta := by
    unfold highActivePacketMass
    ring
  have hQE : 0 ≤ Real.rpow Q (1 / 8 : ℝ) := Real.rpow_nonneg hQ0.le _
  have hQ32 : Real.rpow Q (3 / 2 : ℝ) * Real.rpow Q (1 / 8 : ℝ) =
      Real.rpow Q (13 / 8 : ℝ) := by
    calc
      Real.rpow Q (3 / 2 : ℝ) * Real.rpow Q (1 / 8 : ℝ) =
          Real.rpow Q ((3 / 2 : ℝ) + 1 / 8) :=
        (Real.rpow_add hQ0 (3 / 2 : ℝ) (1 / 8 : ℝ)).symm
      _ = Real.rpow Q (13 / 8 : ℝ) := by congr 1 <;> norm_num
  have hXhalf : p.X * Real.rpow p.X (-(1 / 2 : ℝ)) =
      Real.rpow p.X (1 / 2 : ℝ) := by
    calc
      p.X * Real.rpow p.X (-(1 / 2 : ℝ)) =
          Real.rpow p.X 1 * Real.rpow p.X (-(1 / 2 : ℝ)) := by
            exact congrArg (fun z : ℝ => z * Real.rpow p.X (-(1 / 2 : ℝ)))
              (Real.rpow_one p.X).symm
      _ = Real.rpow p.X (1 + -(1 / 2 : ℝ)) :=
        (Real.rpow_add hX0 1 (-(1 / 2 : ℝ))).symm
      _ = Real.rpow p.X (1 / 2 : ℝ) := by congr 1 <;> norm_num
  have hcm : Cd * CmixConst ≤ Ctotal := by
    dsimp [Ctotal]; nlinarith [hCd.le, hCmixConst, hCerrConst]
  have hce : Cd * CerrConst ≤ Ctotal := by
    dsimp [Ctotal]; nlinarith [hCd.le, hCmixConst, hCerrConst]
  have hS : 0 ≤ p.X * Real.log p.X ^ P := by positivity
  have h2 : 0 ≤ Real.rpow Q (1 / 8 : ℝ) * losses := by
    dsimp [losses, highThreeLosses]
    positivity
  have h3 : 0 ≤ Real.rpow Q (13 / 8 : ℝ) *
      Real.rpow p.X (-(1 / 2 : ℝ)) := by
    exact mul_nonneg (Real.rpow_nonneg hQ0.le _) (Real.rpow_nonneg hX0.le _)
  have hmixD :
      CmixConst * D * p.X * Real.log p.X ^ P * losses ≤
        CmixConst * (Cd * Real.rpow Q (1 / 8 : ℝ)) * p.X *
          Real.log p.X ^ P * losses := by
    have hmid : CmixConst * D ≤ CmixConst * (Cd * Real.rpow Q (1 / 8 : ℝ)) :=
      mul_le_mul_of_nonneg_left hdivp hCmixConst
    have hmid2 := mul_le_mul_of_nonneg_right hmid (by linarith : 0 ≤ p.X)
    have hmid3 := mul_le_mul_of_nonneg_right hmid2 (pow_nonneg hlog0 P)
    exact mul_le_mul_of_nonneg_right hmid3 hloss
  have herrD :
      CerrConst * D * Real.rpow Q (3 / 2 : ℝ) *
          Real.rpow p.X (1 / 2 : ℝ) * Real.log p.X ^ P ≤
        CerrConst * (Cd * Real.rpow Q (1 / 8 : ℝ)) *
          Real.rpow Q (3 / 2 : ℝ) * Real.rpow p.X (1 / 2 : ℝ) *
          Real.log p.X ^ P := by
    have hmid : CerrConst * D ≤ CerrConst * (Cd * Real.rpow Q (1 / 8 : ℝ)) :=
      mul_le_mul_of_nonneg_left hdivp hCerrConst
    have hq32 : 0 ≤ Real.rpow Q (3 / 2 : ℝ) := Real.rpow_nonneg hQ0.le _
    have hx12 : 0 ≤ Real.rpow p.X (1 / 2 : ℝ) := Real.rpow_nonneg hX0.le _
    have hmid2 := mul_le_mul_of_nonneg_right hmid hq32
    have hmid3 := mul_le_mul_of_nonneg_right hmid2 hx12
    exact mul_le_mul_of_nonneg_right hmid3 (pow_nonneg hlog0 _)
  have hrewritten :
      CmixConst * (Cd * Real.rpow Q (1 / 8 : ℝ)) * p.X *
          Real.log p.X ^ P * losses +
        CerrConst * (Cd * Real.rpow Q (1 / 8 : ℝ)) *
          Real.rpow Q (3 / 2 : ℝ) * Real.rpow p.X (1 / 2 : ℝ) *
          Real.log p.X ^ P =
        (Cd * CmixConst) * p.X * Real.log p.X ^ P *
          (Real.rpow Q (1 / 8 : ℝ) * losses) +
        (Cd * CerrConst) * p.X * Real.log p.X ^ P *
          (Real.rpow Q (13 / 8 : ℝ) * Real.rpow p.X (-(1 / 2 : ℝ))) := by
    calc
      _ = (Cd * CmixConst) * p.X * Real.log p.X ^ P *
            (Real.rpow Q (1 / 8 : ℝ) * losses) +
          (Cd * CerrConst) * Real.log p.X ^ P *
            (Real.rpow Q (3 / 2 : ℝ) * Real.rpow Q (1 / 8 : ℝ)) *
            Real.rpow p.X (1 / 2 : ℝ) := by ring
      _ = _ := by rw [hQ32, ← hXhalf]; ring
  have hcombine :
      (Cd * CmixConst) * p.X * Real.log p.X ^ P *
          (Real.rpow Q (1 / 8 : ℝ) * losses) +
        (Cd * CerrConst) * p.X * Real.log p.X ^ P *
          (Real.rpow Q (13 / 8 : ℝ) * Real.rpow p.X (-(1 / 2 : ℝ))) ≤
        Ctotal * p.X * Real.log p.X ^ P *
          (Real.rpow Q (1 / 8 : ℝ) * losses +
            Real.rpow Q (13 / 8 : ℝ) * Real.rpow p.X (-(1 / 2 : ℝ))) := by
    have hL := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcm hS) h2
    have hR := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hce hS) h3
    have hL' :
        (Cd * CmixConst) * p.X * Real.log p.X ^ P *
            (Real.rpow Q (1 / 8 : ℝ) * losses) ≤
          Ctotal * p.X * Real.log p.X ^ P *
            (Real.rpow Q (1 / 8 : ℝ) * losses) := by
      convert hL using 1 <;> ring
    have hR' :
        (Cd * CerrConst) * p.X * Real.log p.X ^ P *
            (Real.rpow Q (13 / 8 : ℝ) * Real.rpow p.X (-(1 / 2 : ℝ))) ≤
          Ctotal * p.X * Real.log p.X ^ P *
            (Real.rpow Q (13 / 8 : ℝ) * Real.rpow p.X (-(1 / 2 : ℝ))) := by
      convert hR using 1 <;> ring
    have hsum := add_le_add hL' hR'
    have hdist :
        Ctotal * p.X * Real.log p.X ^ P *
            (Real.rpow Q (1 / 8 : ℝ) * losses) +
          Ctotal * p.X * Real.log p.X ^ P *
            (Real.rpow Q (13 / 8 : ℝ) * Real.rpow p.X (-(1 / 2 : ℝ))) =
          Ctotal * p.X * Real.log p.X ^ P *
            (Real.rpow Q (1 / 8 : ℝ) * losses +
              Real.rpow Q (13 / 8 : ℝ) * Real.rpow p.X (-(1 / 2 : ℝ))) := by
      ring
    exact hsum.trans (le_of_eq hdist)
  calc
    dynamicLowNormalizationV3 p *
        highActivePacketMass (H₀ := H₀) p T hX2 hdelta =
      dynamicLowNormalizationV3 p *
          activeIndexedMixedTotal (H₀ := H₀) T hX2 hdelta +
        dynamicLowNormalizationV3 p *
          highActiveErrorTotal (H₀ := H₀) p T hX2 hdelta := hmass
    _ ≤ CmixConst * D * p.X * Real.log p.X ^ P * losses +
          CerrConst * D * Real.rpow Q (3 / 2 : ℝ) *
            Real.rpow p.X (1 / 2 : ℝ) * Real.log p.X ^ P :=
      add_le_add hmixed_sum herr_sum
    _ ≤ CmixConst * (Cd * Real.rpow Q (1 / 8 : ℝ)) * p.X *
          Real.log p.X ^ P * losses +
        CerrConst * (Cd * Real.rpow Q (1 / 8 : ℝ)) *
          Real.rpow Q (3 / 2 : ℝ) * Real.rpow p.X (1 / 2 : ℝ) *
          Real.log p.X ^ P :=
      add_le_add hmixD herrD
    _ = (Cd * CmixConst) * p.X * Real.log p.X ^ P *
          (Real.rpow Q (1 / 8 : ℝ) * losses) +
        (Cd * CerrConst) * p.X * Real.log p.X ^ P *
          (Real.rpow Q (13 / 8 : ℝ) * Real.rpow p.X (-(1 / 2 : ℝ))) :=
      hrewritten
    _ ≤ Ctotal * p.X * Real.log p.X ^ P *
          (Real.rpow Q (1 / 8 : ℝ) * losses +
            Real.rpow Q (13 / 8 : ℝ) * Real.rpow p.X (-(1 / 2 : ℝ))) :=
      hcombine
    _ = Ctotal * p.X * Real.log p.X ^ P *
          (Real.rpow Q (1 / 8 : ℝ) *
              (Q * Real.rpow p.X (-delta) + 1 / Real.sqrt Q + Q / U) +
            Real.rpow Q (13 / 8 : ℝ) * Real.rpow p.X (-(1 / 2 : ℝ))) := by
          dsimp [losses, highThreeLosses, U]

/-- Move `X` across the scalar envelope so the polylog `/30` can be multiplied. -/
theorem scalar_envelope_mul_X_eq
    (X C : ℝ) (P : ℕ) (Q U delta : ℝ) :
    C * X * Real.log X ^ P *
      (Real.rpow Q (1 / 8 : ℝ) *
          (Q * Real.rpow X (-delta) + 1 / Real.sqrt Q + Q / U) +
        Real.rpow Q (13 / 8 : ℝ) * Real.rpow X (-(1 / 2 : ℝ))) =
    X * (C * Real.rpow (Real.log X) P *
      (Real.rpow Q (1 / 8 : ℝ) *
          (Q * Real.rpow X (-delta) + 1 / Real.sqrt Q + Q / U) +
        Real.rpow Q (13 / 8 : ℝ) * Real.rpow X (-(1 / 2 : ℝ)))) := by
  have hP : Real.log X ^ P = Real.rpow (Real.log X) P :=
    (Real.rpow_natCast (Real.log X) P).symm
  rw [hP]
  ring

/-- Uniform `/30` producer for the literal high mixed-plus-error field. -/
theorem eventually_refined_high_budget_thirtieth
    (delta A : ℝ) (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 240) :
    ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∃ Cc₀ : ℕ, ∀ Cc : ℕ, Cc₀ ≤ Cc →
        ∀ᶠ X : ℝ in atTop,
          ∀ (p : Corollary53Input) [NeZero p.q]
            (hp : Corollary53Admissible 1 1 p) (hpX : p.X = X)
            (reserve : ℝ) (hr0 : 0 ≤ reserve) (hr : reserve ≤ 1 / 1200)
            (hH : p.H = (1 / 2 : ℝ) * Real.rpow p.X (2 / 15 + reserve))
            (heta : p.eta = 1 / Real.sqrt ((Real.log p.X) ^ B))
            (hqQ : (p.q : ℝ) ≤ (Real.log p.X) ^ B)
            (hbeta : |p.beta| ≤ 1 / ((p.q : ℝ) * (Real.log p.X) ^ B))
            (hfar : 2 * (Real.log p.X) ^ Cc < stationaryWidth p.beta p.H)
            (hXp : 2 ≤ p.X),
            dynamicLowNormalizationV3 p *
              selectedHighMass p delta hXp hdelta ≤
              p.X * Real.rpow (Real.log p.X) (-A) / 30 := by
  obtain ⟨C, hC, P, X₁, hX₁3, hsource⟩ :=
    exists_uniform_normalized_high_le_scalar_envelope delta hdelta hdeltaUpper
  obtain ⟨B₀, hB₀⟩ := eventually_high_scalar_envelope_le_thirtieth
    C (P : ℝ) A delta hC.le hdelta
  refine ⟨B₀, ?_⟩
  intro B hB
  obtain ⟨Cc₀, hCc₀⟩ := hB₀ B hB
  refine ⟨Cc₀, ?_⟩
  intro Cc hCc
  have hlogEvent : ∀ᶠ X : ℝ in atTop, 1 ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  filter_upwards [hCc₀ Cc hCc, hlogEvent,
    eventually_ge_atTop (max 3 X₁)] with X hscalar hlog hXmax
  intro p _ hp hpX reserve hr0 hr hH heta hqQ hbeta hfar hXp
  have hX3 : 3 ≤ p.X := by
    have : 3 ≤ X := (le_max_left 3 X₁).trans hXmax
    simpa only [hpX] using this
  have hX1p : X₁ ≤ p.X := by
    have : X₁ ≤ X := (le_max_right 3 X₁).trans hXmax
    simpa only [hpX] using this
  have hX0 : 0 < p.X := by linarith
  have hlogp : 1 ≤ Real.log p.X := by simpa only [hpX] using hlog
  have hQ : 1 ≤ (Real.log p.X) ^ B := one_le_pow₀ hlogp
  have hCcPow : 1 ≤ (Real.log p.X) ^ Cc := one_le_pow₀ hlogp
  have hU : 1 ≤ stationaryWidth p.beta p.H := by nlinarith [hfar, hCcPow]
  have hUpow : (Real.log p.X) ^ Cc ≤ stationaryWidth p.beta p.H := by
    nlinarith [hfar, hCcPow]
  have hq0 : 0 < (p.q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p.q)
  have hH0 : 0 < p.H := by
    rw [hH]
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hX0 _)
  have hqu : (p.q : ℝ) * stationaryWidth p.beta p.H ≤
      p.H / (Real.log p.X) ^ B := by
    unfold stationaryWidth
    calc
      _ = ((p.q : ℝ) * p.H) * |p.beta| := by ring
      _ ≤ ((p.q : ℝ) * p.H) * (1 / ((p.q : ℝ) * (Real.log p.X) ^ B)) :=
        mul_le_mul_of_nonneg_left hbeta (mul_nonneg hq0.le hH0.le)
      _ = _ := by field_simp
  have hs := hsource p hp ((Real.log p.X) ^ B) reserve hX1p hX3 hXp hlogp
    hQ hqQ hH heta hU hqu hr0 hr
  dsimp only at hs
  have hscalarp := hscalar (stationaryWidth p.beta p.H)
    (by simpa only [← hpX] using hUpow)
  dsimp only at hscalarp
  have hmul := mul_le_mul_of_nonneg_left hscalarp hX0.le
  have hsel : selectedHighMass p delta hXp hdelta =
      highActivePacketMass (H₀ := highClassifierH0 p.X delta) p
        (selectedHighTruncation p) hXp hdelta := rfl
  have hrearr :=
    scalar_envelope_mul_X_eq p.X C P ((Real.log p.X) ^ B)
      (stationaryWidth p.beta p.H) delta
  calc
    dynamicLowNormalizationV3 p * selectedHighMass p delta hXp hdelta
        = dynamicLowNormalizationV3 p *
            highActivePacketMass (H₀ := highClassifierH0 p.X delta) p
              (selectedHighTruncation p) hXp hdelta := by rw [hsel]
    _ ≤ C * p.X * Real.log p.X ^ P *
          (Real.rpow ((Real.log p.X) ^ B) (1 / 8 : ℝ) *
              ((Real.log p.X) ^ B * Real.rpow p.X (-delta) +
                1 / Real.sqrt ((Real.log p.X) ^ B) +
                (Real.log p.X) ^ B / stationaryWidth p.beta p.H) +
            Real.rpow ((Real.log p.X) ^ B) (13 / 8 : ℝ) *
              Real.rpow p.X (-(1 / 2 : ℝ))) := hs
    _ = p.X * (C * Real.rpow (Real.log p.X) P *
          (Real.rpow ((Real.log p.X) ^ B) (1 / 8 : ℝ) *
              ((Real.log p.X) ^ B * Real.rpow p.X (-delta) +
                1 / Real.sqrt ((Real.log p.X) ^ B) +
                (Real.log p.X) ^ B / stationaryWidth p.beta p.H) +
            Real.rpow ((Real.log p.X) ^ B) (13 / 8 : ℝ) *
              Real.rpow p.X (-(1 / 2 : ℝ)))) := hrearr
    _ ≤ p.X * (Real.rpow (Real.log p.X) (-A) / 30) := by
          simpa [hpX] using hmul
    _ = p.X * Real.rpow (Real.log p.X) (-A) / 30 := by ring

theorem exists_refined_high_budget_threshold
    (delta A : ℝ) (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 240) :
    ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∃ Cc₀ : ℕ, ∀ Cc : ℕ, Cc₀ ≤ Cc →
        ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
          ∀ (p : Corollary53Input) [NeZero p.q]
            (hp : Corollary53Admissible 1 1 p) (hpX : p.X = X)
            (reserve : ℝ) (hr0 : 0 ≤ reserve) (hr : reserve ≤ 1 / 1200)
            (hH : p.H = (1 / 2 : ℝ) * Real.rpow p.X (2 / 15 + reserve))
            (heta : p.eta = 1 / Real.sqrt ((Real.log p.X) ^ B))
            (hqQ : (p.q : ℝ) ≤ (Real.log p.X) ^ B)
            (hbeta : |p.beta| ≤ 1 / ((p.q : ℝ) * (Real.log p.X) ^ B))
            (hfar : 2 * (Real.log p.X) ^ Cc < stationaryWidth p.beta p.H)
            (hXp : 2 ≤ p.X),
            dynamicLowNormalizationV3 p *
              selectedHighMass p delta hXp hdelta ≤
              p.X * Real.rpow (Real.log p.X) (-A) / 30 := by
  obtain ⟨B₀, hB₀⟩ :=
    eventually_refined_high_budget_thirtieth delta A hdelta hdeltaUpper
  refine ⟨B₀, ?_⟩
  intro B hB
  obtain ⟨Cc₀, hCc₀⟩ := hB₀ B hB
  refine ⟨Cc₀, ?_⟩
  intro Cc hCc
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp (hCc₀ Cc hCc)
  refine ⟨max 3 X₀, le_max_left _ _, ?_⟩
  intro X hX
  exact hX₀ X ((le_max_right _ _).trans hX)

theorem eventually_refined_high_mixed_le_thirtieth
    (delta A : ℝ) (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 240) :
    ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∃ Cc₀ : ℕ, ∀ Cc : ℕ, Cc₀ ≤ Cc →
        ∀ᶠ X : ℝ in atTop,
          ∀ (p : Corollary53Input) [NeZero p.q]
            (hp : Corollary53Admissible 1 1 p) (hpX : p.X = X)
            (reserve : ℝ) (hr0 : 0 ≤ reserve) (hr : reserve ≤ 1 / 1200)
            (hH : p.H = (1 / 2 : ℝ) * Real.rpow p.X (2 / 15 + reserve))
            (heta : p.eta = 1 / Real.sqrt ((Real.log p.X) ^ B))
            (hqQ : (p.q : ℝ) ≤ (Real.log p.X) ^ B)
            (hbeta : |p.beta| ≤ 1 / ((p.q : ℝ) * (Real.log p.X) ^ B))
            (hfar : 2 * (Real.log p.X) ^ Cc < stationaryWidth p.beta p.H)
            (hXp : 2 ≤ p.X),
            dynamicLowNormalizationV3 p *
              activeIndexedMixedTotal
                (H₀ := highClassifierH0 p.X delta)
                (selectedHighTruncation p) hXp hdelta ≤
              p.X * Real.rpow (Real.log p.X) (-A) / 30 := by
  obtain ⟨B₀, hB₀⟩ :=
    eventually_refined_high_budget_thirtieth delta A hdelta hdeltaUpper
  refine ⟨B₀, ?_⟩
  intro B hB
  obtain ⟨Cc₀, hCc₀⟩ := hB₀ B hB
  refine ⟨Cc₀, ?_⟩
  intro Cc hCc
  have hlogEvent : ∀ᶠ X : ℝ in atTop, 1 ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  filter_upwards [hCc₀ Cc hCc, hlogEvent] with X hmass hlog
  intro p _ hp hpX reserve hr0 hr hH heta hqQ hbeta hfar hXp
  have hlogp : 1 ≤ Real.log p.X := by simpa only [hpX] using hlog
  have hCcPow : 1 ≤ (Real.log p.X) ^ Cc := one_le_pow₀ hlogp
  have hU : 1 ≤ stationaryWidth p.beta p.H := by nlinarith [hfar, hCcPow]
  have hTpos : 0 < selectedHighTruncation p :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (highFreeTruncation_ge_one_of_H (by linarith : 1 ≤ p.X) hU hH hr)
  have hmix := normalized_active_mixed_le_mass (H₀ := highClassifierH0 p.X delta)
    hp hXp hdelta hTpos
  have hsel : selectedHighMass p delta hXp hdelta =
      highActivePacketMass (H₀ := highClassifierH0 p.X delta) p
        (selectedHighTruncation p) hXp hdelta := rfl
  calc
    _ ≤ dynamicLowNormalizationV3 p *
          highActivePacketMass (H₀ := highClassifierH0 p.X delta) p
            (selectedHighTruncation p) hXp hdelta := hmix
    _ = dynamicLowNormalizationV3 p * selectedHighMass p delta hXp hdelta := by
        rw [hsel]
    _ ≤ _ := hmass p hp hpX reserve hr0 hr hH heta hqQ hbeta hfar hXp

/-- Active-certificate `/5` from the adopted `/30`; not the old `T=X` slot. -/
theorem thirtieth_scalar_le_fifth
    {X A : ℝ} (hX : 0 ≤ X)
    (hpow : 0 ≤ Real.rpow (Real.log X) (-A)) :
    X * Real.rpow (Real.log X) (-A) / 30 ≤
      X * Real.rpow (Real.log X) (-A) / 5 := by
  have hpos : 0 ≤ X * Real.rpow (Real.log X) (-A) := mul_nonneg hX hpow
  have hfrac : (1 : ℝ) / 30 ≤ (1 : ℝ) / 5 := by norm_num
  calc
    X * Real.rpow (Real.log X) (-A) / 30 =
        (X * Real.rpow (Real.log X) (-A)) * (1 / 30) := by ring
    _ ≤ (X * Real.rpow (Real.log X) (-A)) * (1 / 5) :=
      mul_le_mul_of_nonneg_left hfrac hpos
    _ = X * Real.rpow (Real.log X) (-A) / 5 := by ring

theorem exists_active_high_budget_fifth
    (delta A : ℝ) (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 240) :
    ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∃ Cc₀ : ℕ, ∀ Cc : ℕ, Cc₀ ≤ Cc →
        ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
          ∀ (p : Corollary53Input) [NeZero p.q]
            (hp : Corollary53Admissible 1 1 p) (hpX : p.X = X)
            (reserve : ℝ) (hr0 : 0 ≤ reserve) (hr : reserve ≤ 1 / 1200)
            (hH : p.H = (1 / 2 : ℝ) * Real.rpow p.X (2 / 15 + reserve))
            (heta : p.eta = 1 / Real.sqrt ((Real.log p.X) ^ B))
            (hqQ : (p.q : ℝ) ≤ (Real.log p.X) ^ B)
            (hbeta : |p.beta| ≤ 1 / ((p.q : ℝ) * (Real.log p.X) ^ B))
            (hfar : 2 * (Real.log p.X) ^ Cc < stationaryWidth p.beta p.H)
            (hXp : 2 ≤ p.X),
            dynamicLowNormalizationV3 p *
              selectedHighMass p delta hXp hdelta ≤
              p.X * Real.rpow (Real.log p.X) (-A) / 5 := by
  obtain ⟨B₀, hB₀⟩ :=
    exists_refined_high_budget_threshold delta A hdelta hdeltaUpper
  refine ⟨B₀, ?_⟩
  intro B hB
  obtain ⟨Cc₀, hCc₀⟩ := hB₀ B hB
  refine ⟨Cc₀, ?_⟩
  intro Cc hCc
  obtain ⟨X₀, hX₀3, hX₀⟩ := hCc₀ Cc hCc
  refine ⟨X₀, hX₀3, ?_⟩
  intro X hX p _ hp hpX reserve hr0 hr hH heta hqQ hbeta hfar hXp
  have h30 :=
    hX₀ X hX p hp hpX reserve hr0 hr hH heta hqQ hbeta hfar hXp
  have hX0 : 0 ≤ p.X := by linarith
  have hX1 : (1 : ℝ) < p.X := by linarith
  have hlog : 0 < Real.log p.X := Real.log_pos hX1
  have hrpow : 0 ≤ Real.rpow (Real.log p.X) (-A) :=
    Real.rpow_nonneg hlog.le _
  exact h30.trans (thirtieth_scalar_le_fifth hX0 hrpow)

end
end MRTProposition61HighEnvelopeSplitV3

#print axioms MRTProposition61HighEnvelopeSplitV3.normalized_activeHighPacketMixedMass_le

#print axioms MRTProposition61HighEnvelopeSplitV3.normalized_freePacketErrorRefinedV3_le

#print axioms MRTProposition61HighEnvelopeSplitV3.exists_uniform_normalized_high_le_scalar_envelope

#print axioms MRTProposition61HighEnvelopeSplitV3.exists_refined_high_budget_threshold

#print axioms MRTProposition61HighEnvelopeSplitV3.exists_active_high_budget_fifth
