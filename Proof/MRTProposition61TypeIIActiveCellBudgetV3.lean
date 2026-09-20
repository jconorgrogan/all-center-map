import MRTProposition61TypeIIParameterAbsorptionV3
import MRTProposition61TypeIIUniformEnergyV3
import MRTLemma215DynamicTypeIIFiniteEnvelopeV3
import MRTProposition61TypeIINormalizedAnalyticV3
import MRTProposition61TypeIIActualEndpointLedgerV3

/-! # Exact normalization of the active Type-II analytic cell

Both the actual long interval and the coefficient energies are retained.
The Perron integral is evaluated exactly; no analytic budget is assumed.
-/

namespace MRTProposition61TypeIIActiveCellBudgetV3

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

open MRTLemma215ScaleClassifierV3 MRTLemma215DynamicOutcomeWeldV3
open MRTLemma215DynamicTypeIIFactorizationV3
open MRTLemma215DynamicTypeIIFiniteEnvelopeV3
open MRTLemma215OpenIntervalCutoffV3
open MRTLemma215DynamicTypeIIMaskedPacketsV3
open MRTLemma215DynamicTypeIICellPruningV3
open MRTProposition61TypeIIUniformEnergyV3

set_option maxHeartbeats 1500000

noncomputable section

theorem actualTypeIICell_energy_product_le_fixedOrder_logPow
    {X : ℝ} {K k : ℕ} (hX : 1 ≤ X) (hk : k < K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (s : ℕ)
    (leftCell : Fin (sourceDyadicCount (factorUpperProduct
      (typeIIPrefixFactorList (sortedComponentFactorList logIndex zbag mbag) s))))
    (suffixCell : Fin (sourceDyadicCount (factorUpperProduct
      (typeIISuffixFactorList (sortedComponentFactorList logIndex zbag mbag) s))))
    (hnonzero : intervalCutoff (openSourceLeft X) (2 * X)
      (literalDirichletConvolution
        (scaledTypeIIPrefixCell zbag mbag
          (typeIIPrefixFactorList (sortedComponentFactorList logIndex zbag mbag) s)
          leftCell)
        (factorListDyadicCell
          (typeIISuffixFactorList (sortedComponentFactorList logIndex zbag mbag) s)
          suffixCell)) ≠ 0) :
    coefficientEnergy (criticalDyadicCoefficient
        (scaledTypeIIPrefixCell zbag mbag
          (typeIIPrefixFactorList (sortedComponentFactorList logIndex zbag mbag) s)
          leftCell)) (2 ^ (leftCell : ℕ)) *
      coefficientEnergy (criticalDyadicCoefficient
        (factorListDyadicCell
          (typeIISuffixFactorList (sortedComponentFactorList logIndex zbag mbag) s)
          suffixCell)) (2 ^ (suffixCell : ℕ)) ≤
      (((K ^ K * Nat.factorial K * Nat.factorial K : ℕ) : ℝ)) ^ 2 *
        (1 + Real.log (8 * X)) ^ (8 * K + 4 * K * K) := by
  have hprod := nonzero_intervalCutoff_literalConvolution_product_bounds
    (by linarith : 0 ≤ X)
    (scaledTypeIIPrefixCell_supported zbag mbag _ leftCell)
    (factorListDyadicCell_supported _ suffixCell) hnonzero
  have hN : (1 : ℝ) ≤ ((2 ^ (leftCell : ℕ) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_pow (leftCell : ℕ) 2 (by omega))
  have hM : (1 : ℝ) ≤ ((2 ^ (suffixCell : ℕ) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_pow (suffixCell : ℕ) 2 (by omega))
  apply typeIICell_energy_product_le_fixedOrder_logPow hX hk logIndex zbag mbag
  · intro f hf
    exact List.mem_of_mem_take hf
  · intro f hf
    exact List.mem_of_mem_drop hf
  · have hlen := sortedComponentFactorList_length_le logIndex zbag mbag
    simp only [typeIIPrefixFactorList, typeIISuffixFactorList,
      List.length_take, List.length_drop]
    omega
  · nlinarith [hprod.2]
  · nlinarith [hprod.2]

/-- The normalized Perron remainder loses no stationary-width factor. -/
theorem normalized_perron_remainder_le
    {D C L q N M X T theta U H eta Q : ℝ}
    (hD : 0 ≤ D) (hL : 0 ≤ L) (hq : 0 < q)
    (hNM : 0 ≤ N * M) (hX : 0 ≤ X)
    (hprod : N * M ≤ 2 * X) (htheta : 0 ≤ theta)
    (hLbound : L ≤ U * X / (eta * H))
    (heta : 0 < eta) (hH : 0 < H) (hQ : 0 < Q)
    (hqu : q * U ≤ H / Q) :
    8 * canonicalPerronKFour ^ 2 * D * L / q * q ^ 2 *
        C ^ 2 * Real.rpow (4 * N * M) theta ^ 2 *
        (N * M) * (Real.log (2 + T) / T) ^ 2 ≤
      16 * canonicalPerronKFour ^ 2 * D * C ^ 2 *
        Real.rpow (8 * X) theta ^ 2 * X ^ 2 / (eta * Q) *
        (Real.log (2 + T) / T) ^ 2 := by
  have hLq : L * q ≤ X / (eta * Q) := by
    calc
      L * q ≤ (U * X / (eta * H)) * q :=
        mul_le_mul_of_nonneg_right hLbound hq.le
      _ = (q * U) * X / (eta * H) := by ring
      _ ≤ (H / Q) * X / (eta * H) := by gcongr
      _ = X / (eta * Q) := by field_simp <;> ring
  have hpow : Real.rpow (4 * N * M) theta ^ 2 ≤
      Real.rpow (8 * X) theta ^ 2 := by
    apply pow_le_pow_left₀ (Real.rpow_nonneg (by nlinarith) _) 
    exact Real.rpow_le_rpow (by nlinarith) (by nlinarith) htheta
  calc
    _ = 8 * canonicalPerronKFour ^ 2 * D * C ^ 2 *
        Real.rpow (4 * N * M) theta ^ 2 * (L * q) *
        (N * M) * (Real.log (2 + T) / T) ^ 2 := by field_simp <;> ring
    _ ≤ 8 * canonicalPerronKFour ^ 2 * D * C ^ 2 *
        Real.rpow (8 * X) theta ^ 2 * (X / (eta * Q)) *
        (2 * X) * (Real.log (2 + T) / T) ^ 2 := by
      gcongr
    _ = _ := by ring

theorem dirichletCharacter_card_le (q : ℕ) (hq : 0 < q) :
    (Fintype.card (DirichletCharacter ℂ q) : ℝ) ≤ q := by
  letI : NeZero q := ⟨by omega⟩
  have hc := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  rw [Nat.card_eq_fintype_card] at hc
  exact_mod_cast (hc.le.trans (Nat.totient_le q))

/-- Exact polynomial saving in the normalized Perron error at the selected height. -/
theorem perron_power_saving_eq {X : ℝ} (hX : 0 < X) :
    Real.rpow (8 * X) (1 / 24 : ℝ) ^ 2 * X ^ 2 /
      Real.rpow X (2 / 3 : ℝ) ^ 2 =
      Real.rpow 8 (1 / 12 : ℝ) * Real.rpow X (3 / 4 : ℝ) := by
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ 8 * X),
    ← Real.rpow_mul_natCast hX.le]
  norm_num
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) hX.le,
    ← Real.rpow_natCast X 2]
  rw [mul_assoc, ← Real.rpow_add hX, mul_div_assoc,
    ← Real.rpow_sub hX]
  norm_num

/-- A cell-independent endpoint envelope, retaining the literal parameters. -/
def endpointEnvelope (p : Corollary53Input) (K : ℕ) (T delta H₀ : ℝ) : ℝ :=
  let U := stationaryWidth p.beta p.H
  let G := (2 : ℝ) ^ (2 * K)
  2 * p.q * U / (p.eta * p.H) + 4 * p.q * T / p.X + 4 * p.q * U / p.X +
    64 * Real.pi / Real.rpow p.X delta +
    16 * Real.pi * G * H₀ / (p.eta * p.H) +
    32 * Real.pi * G * H₀ * T / (U * p.X) +
    32 * Real.pi * G * H₀ / p.X + 128 * Real.pi ^ 2 / U

/-- Every literal nonzero Type-II cell obeys a uniform explicit budget.
All coefficient and dyadic-scale premises are derived from the actual split. -/
theorem normalized_activeTypeIICellAnalyticRHS_le_uniform
    (p : Corollary53Input) (T theta C delta H₀ Q : ℝ) {K k : ℕ}
    (hX : 1 ≤ p.X) (hk : k < K)
    (hH : 0 < p.H) (heta : 0 < p.eta) (hetaOne : p.eta ≤ 1)
    (hq : 1 ≤ (p.q : ℝ)) (hU : 0 < stationaryWidth p.beta p.H)
    (hT : 0 ≤ T) (hH₀ : 0 ≤ H₀) (htheta : 0 ≤ theta)
    (hQ : 0 < Q) (hqu : p.q * stationaryWidth p.beta p.H ≤ p.H / Q)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff p.X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff p.X K⌋₊))) (k + 1))
    (houtcome : dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag =
      .typeII)
    (leftCell : Fin (sourceDyadicCount (factorUpperProduct
      (typeIIPrefixFactorList
        (sortedComponentFactorList logIndex zbag mbag)
        (largestSmallPrefix
          (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
          (Real.rpow p.X delta))))))
    (suffixCell : Fin (sourceDyadicCount (factorUpperProduct
      (typeIISuffixFactorList
        (sortedComponentFactorList logIndex zbag mbag)
        (largestSmallPrefix
          (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
          (Real.rpow p.X delta))))))
    (hnonzero : intervalCutoff (openSourceLeft p.X) (2 * p.X)
      (literalDirichletConvolution
        (scaledTypeIIPrefixCell zbag mbag
          (typeIIPrefixFactorList
            (sortedComponentFactorList logIndex zbag mbag)
            (largestSmallPrefix
              (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
              (Real.rpow p.X delta))) leftCell)
        (factorListDyadicCell
          (typeIISuffixFactorList
            (sortedComponentFactorList logIndex zbag mbag)
            (largestSmallPrefix
              (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
              (Real.rpow p.X delta))) suffixCell)) ≠ 0)
    (component : OuterComponent) :
    let left := typeIIPrefixFactorList (sortedComponentFactorList logIndex zbag mbag)
      (largestSmallPrefix (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
        (Real.rpow p.X delta))
    let suffix := typeIISuffixFactorList (sortedComponentFactorList logIndex zbag mbag)
      (largestSmallPrefix (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
        (Real.rpow p.X delta))
    let U := stationaryWidth p.beta p.H
    (divisorCount p.q : ℝ) ^ 4 / (p.q * U ^ 2) *
      activeTypeIICellAnalyticRHSV3 p T theta C logIndex zbag mbag
        left suffix leftCell suffixCell component ≤
      16 * canonicalPerronKFour ^ 2 * (divisorCount p.q : ℝ) ^ 4 *
        Real.log (1 + T) ^ 2 * p.X * endpointEnvelope p K T delta H₀ *
        (((K ^ K * Nat.factorial K * Nat.factorial K : ℕ) : ℝ)) ^ 2 *
        (1 + Real.log (8 * p.X)) ^ (8 * K + 4 * K * K) +
      16 * canonicalPerronKFour ^ 2 * (divisorCount p.q : ℝ) ^ 4 * C ^ 2 *
        Real.rpow (8 * p.X) theta ^ 2 * p.X ^ 2 / (p.eta * Q) *
        (Real.log (2 + T) / T) ^ 2 := by
  dsimp only
  let s := largestSmallPrefix (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
    (Real.rpow p.X delta)
  let left := typeIIPrefixFactorList (sortedComponentFactorList logIndex zbag mbag) s
  let suffix := typeIISuffixFactorList (sortedComponentFactorList logIndex zbag mbag) s
  let N : ℝ := (2 ^ (leftCell : ℕ) : ℕ)
  let M : ℝ := (2 ^ (suffixCell : ℕ) : ℕ)
  let U := stationaryWidth p.beta p.H
  let L := (componentEndpoints p.X p.beta p.eta component).2 -
    (componentEndpoints p.X p.beta p.eta component).1
  have hX0 : 0 < p.X := by linarith
  have hq0 : 0 < (p.q : ℝ) := by linarith
  have hL : L ≤ U * p.X / (p.eta * p.H) :=
    MRTProposition61TypeIIEndpointWidthV3.componentEndpoints_sub_le_stationaryWidth_mul
      hX0.le heta.le hH component
  have hL0 : 0 ≤ L := by
    dsimp [L]
    rw [MRTProposition61TypeIIEndpointWidthV3.componentEndpoints_sub_eq_outerUpper_sub_outerLower]
    unfold outerUpper outerLower
    have hbase : p.eta * |p.beta| * p.X ≤ |p.beta| * p.X / p.eta := by
      apply (le_div_iff₀ heta).2
      have hsq : p.eta ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hsq
        (mul_nonneg (abs_nonneg p.beta) hX0.le)]
    linarith
  have hprod := nonzero_intervalCutoff_literalConvolution_product_bounds hX0.le
    (scaledTypeIIPrefixCell_supported zbag mbag left leftCell)
    (factorListDyadicCell_supported suffix suffixCell) hnonzero
  have he := actualTypeIICell_energy_product_le_fixedOrder_logPow hX hk
    logIndex zbag mbag s leftCell suffixCell hnonzero
  have hG : (2 : ℝ) ^ left.length ≤ (2 : ℝ) ^ (2 * K) := by
    exact_mod_cast typeIIPrefix_pow_length_le_branchEnvelope ⟨k, hk⟩
      logIndex zbag mbag s
  have hep := MRTProposition61TypeIIActualEndpointLedgerV3.actualTypeIICell_normalized_product_le_endpoint_terms
    hX0 hH heta hetaOne hq hU hT hH₀ logIndex zbag mbag houtcome
    leftCell suffixCell hnonzero component
  have hep' : ((p.q * (2 * U) + 8 * Real.pi * N) *
      (p.q * (L + 2 * T + 2 * U) + 8 * Real.pi * M)) /
      (p.q * U * p.X) ≤ endpointEnvelope p K T delta H₀ := by
    apply hep.trans
    unfold endpointEnvelope
    dsimp only
    gcongr
  have hep0 : 0 ≤ endpointEnvelope p K T delta H₀ := by
    apply le_trans _ hep'
    have hU0 : 0 < U := hU
    have hN0 : 0 ≤ N := by dsimp [N]; positivity
    have hM0 : 0 ≤ M := by dsimp [M]; positivity
    positivity
  have hc := dirichletCharacter_card_le p.q (by exact_mod_cast hq0)
  have herr := normalized_perron_remainder_le
    (D := (divisorCount p.q : ℝ) ^ 4) (C := C) (T := T)
    (N := N) (M := M) (theta := theta)
    (by positivity) hL0 hq0 (by dsimp [N, M]; positivity) hX0.le
    hprod.2 htheta hL heta hH hQ hqu
  rw [MRTProposition61TypeIINormalizedAnalyticV3.normalized_activeTypeIICellAnalyticRHS_eq
    p T theta C hX0 hq0 hU hT]
  try dsimp only
  apply add_le_add
  · have hlead := mul_le_mul_of_nonneg_left he
      (show 0 ≤ 16 * canonicalPerronKFour ^ 2 * (divisorCount p.q : ℝ) ^ 4 *
        Real.log (1 + T) ^ 2 * p.X * endpointEnvelope p K T delta H₀ by positivity)
    calc
      _ ≤ 16 * canonicalPerronKFour ^ 2 * (divisorCount p.q : ℝ) ^ 4 *
        Real.log (1 + T) ^ 2 * p.X * endpointEnvelope p K T delta H₀ *
        coefficientEnergy (criticalDyadicCoefficient (scaledTypeIIPrefixCell zbag mbag left leftCell))
          (2 ^ (leftCell : ℕ)) *
        coefficientEnergy (criticalDyadicCoefficient (factorListDyadicCell suffix suffixCell))
          (2 ^ (suffixCell : ℕ)) := by
        gcongr
        · unfold coefficientEnergy; positivity
        · unfold coefficientEnergy; positivity
      _ ≤ _ := by convert hlead using 1 <;> ring
  · apply le_trans _ herr
    change 8 * canonicalPerronKFour ^ 2 * (divisorCount p.q : ℝ) ^ 4 *
      L / p.q * (Fintype.card (DirichletCharacter ℂ p.q) : ℝ) ^ 2 * C ^ 2 *
      Real.rpow (4 * N * M) theta ^ 2 * (N * M) * (Real.log (2 + T) / T) ^ 2 ≤ _
    gcongr

theorem endpointEnvelope_le_three_losses
    (p : Corollary53Input) (K : ℕ) {delta reserve Q : ℝ}
    (hX : 1 ≤ p.X) (hQ : 1 ≤ Q) (hqQ : (p.q : ℝ) ≤ Q)
    (hH : p.H = (1 / 2 : ℝ) * Real.rpow p.X (2 / 15 + reserve))
    (heta : p.eta = 1 / Real.sqrt Q)
    (hU : 1 ≤ stationaryWidth p.beta p.H)
    (hqu : p.q * stationaryWidth p.beta p.H ≤ p.H / Q)
    (hdelta : delta ≤ 1 / 240) (hr0 : 0 ≤ reserve) (hr : reserve ≤ 1 / 1200) :
    endpointEnvelope p K (Real.rpow p.X (2 / 3 : ℝ)) delta
      (Real.rpow p.X (delta + 1 / 8)) ≤
      1000 * (1 + Real.pi ^ 2) * (2 : ℝ) ^ (2 * K) *
        (Q * Real.rpow p.X (-delta) + 1 / Real.sqrt Q +
          1 / stationaryWidth p.beta p.H) := by
  have hX0 : 0 < p.X := by linarith
  have hH0 : 0 < p.H := by
    rw [hH]
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hX0 _)
  have hp := MRTProposition61TypeIIParameterAbsorptionV3.typeII_parameter_power_ratios
    hX hdelta hr0 hr
  dsimp only at hp
  rw [← hH] at hp
  have hb := MRTProposition61TypeIIParameterAbsorptionV3.endpoint_terms_le_three_losses
    hX0 hQ (Nat.cast_nonneg p.q) hqQ hH0
    (Real.rpow_nonneg hX0.le (delta + 1 / 8)) hU
    (Real.rpow_nonneg hX0.le (2 / 3 : ℝ))
    (show 1 ≤ (2 : ℝ) ^ (2 * K) by exact one_le_pow₀ (by norm_num))
    (Real.rpow_nonneg hX0.le (-delta)) hqu hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
  unfold endpointEnvelope
  dsimp only
  rw [heta]
  simpa only [Real.rpow_eq_pow, Real.rpow_neg hX0.le, div_eq_mul_inv] using hb

theorem selected_log_bounds {X : ℝ} (hX : 1 ≤ X) (hlog : 1 ≤ Real.log X) :
    Real.log (1 + Real.rpow X (2 / 3 : ℝ)) ^ 2 ≤ 9 * Real.log X ^ 2 ∧
    Real.log (2 + Real.rpow X (2 / 3 : ℝ)) ^ 2 ≤ 9 * Real.log X ^ 2 ∧
    0 ≤ 1 + Real.log (8 * X) ∧
    1 + Real.log (8 * X) ≤ (2 + Real.log 8) * Real.log X := by
  have hX0 : 0 < X := by linarith
  have hT0 : 0 ≤ Real.rpow X (2 / 3 : ℝ) := Real.rpow_nonneg hX0.le (2 / 3 : ℝ)
  have hT : Real.rpow X (2 / 3 : ℝ) ≤ X := by
    simpa using Real.rpow_le_rpow_of_exponent_le hX (show (2 / 3 : ℝ) ≤ 1 by norm_num)
  have hbound (a : ℝ) (ha : 1 ≤ a) (ha3 : a ≤ 3) :
      Real.log (a + Real.rpow X (2 / 3 : ℝ)) ^ 2 ≤ 9 * Real.log X ^ 2 := by
    have hn : 0 ≤ Real.log (a + Real.rpow X (2 / 3 : ℝ)) :=
      Real.log_nonneg (by linarith)
    have hm : Real.log (a + Real.rpow X (2 / 3 : ℝ)) ≤ 3 * Real.log X := by
      have hm := Real.log_le_log (by linarith : 0 < a + Real.rpow X (2 / 3 : ℝ))
        (show a + Real.rpow X (2 / 3 : ℝ) ≤ 4 * X by nlinarith)
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hX0.ne'] at hm
      have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      nlinarith
    nlinarith [sq_nonneg (3 * Real.log X - Real.log (a + Real.rpow X (2 / 3 : ℝ)))]
  refine ⟨hbound 1 (by norm_num) (by norm_num), hbound 2 (by norm_num) (by norm_num), ?_, ?_⟩
  · have := Real.log_nonneg (show 1 ≤ 8 * X by linarith)
    linarith
  · rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hX0.ne']
    have h8 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)
    nlinarith

def cellBudgetConstant (K : ℕ) (C : ℝ) : ℝ :=
  16 * canonicalPerronKFour ^ 2 *
    (1000 * (1 + Real.pi ^ 2) * (2 : ℝ) ^ (2 * K) *
      (((K ^ K * Nat.factorial K * Nat.factorial K : ℕ) : ℝ)) ^ 2 *
      (2 + Real.log 8) ^ (8 * K + 4 * K * K) +
      C ^ 2 * Real.rpow 8 (1 / 12 : ℝ)) * 9

theorem cellBudgetConstant_nonneg (K : ℕ) (C : ℝ) :
    0 ≤ cellBudgetConstant K C := by
  have h8 : 0 ≤ Real.log (8 : ℝ) := Real.log_nonneg (by norm_num)
  unfold cellBudgetConstant
  simp only [Real.rpow_eq_pow]
  positivity

theorem normalized_activeTypeIICellAnalyticRHS_le_polylog
    (p : Corollary53Input) (C delta reserve Q : ℝ) {K k : ℕ}
    (hX : 1 ≤ p.X) (hlog : 1 ≤ Real.log p.X) (hk : k < K)
    (hq : 1 ≤ (p.q : ℝ)) (hQ : 1 ≤ Q) (hqQ : (p.q : ℝ) ≤ Q)
    (hH : p.H = (1 / 2 : ℝ) * Real.rpow p.X (2 / 15 + reserve))
    (heta : p.eta = 1 / Real.sqrt Q)
    (hU : 1 ≤ stationaryWidth p.beta p.H)
    (hqu : p.q * stationaryWidth p.beta p.H ≤ p.H / Q)
    (hdelta : delta ≤ 1 / 240) (hr0 : 0 ≤ reserve) (hr : reserve ≤ 1 / 1200)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff p.X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff p.X K⌋₊))) (k + 1))
    (houtcome : dynamicComponentOutcome 8 delta (Real.rpow p.X (delta + 1 / 8)) logIndex zbag mbag =
      .typeII)
    (leftCell : Fin (sourceDyadicCount (factorUpperProduct
      (typeIIPrefixFactorList
        (sortedComponentFactorList logIndex zbag mbag)
        (largestSmallPrefix
          (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
          (Real.rpow p.X delta))))))
    (suffixCell : Fin (sourceDyadicCount (factorUpperProduct
      (typeIISuffixFactorList
        (sortedComponentFactorList logIndex zbag mbag)
        (largestSmallPrefix
          (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
          (Real.rpow p.X delta))))))
    (hnonzero : intervalCutoff (openSourceLeft p.X) (2 * p.X)
      (literalDirichletConvolution
        (scaledTypeIIPrefixCell zbag mbag
          (typeIIPrefixFactorList
            (sortedComponentFactorList logIndex zbag mbag)
            (largestSmallPrefix
              (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
              (Real.rpow p.X delta))) leftCell)
        (factorListDyadicCell
          (typeIISuffixFactorList
            (sortedComponentFactorList logIndex zbag mbag)
            (largestSmallPrefix
              (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
              (Real.rpow p.X delta))) suffixCell)) ≠ 0)
    (component : OuterComponent) :
    let left := typeIIPrefixFactorList (sortedComponentFactorList logIndex zbag mbag)
      (largestSmallPrefix (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
        (Real.rpow p.X delta))
    let suffix := typeIISuffixFactorList (sortedComponentFactorList logIndex zbag mbag)
      (largestSmallPrefix (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
        (Real.rpow p.X delta))
    let U := stationaryWidth p.beta p.H
    (divisorCount p.q : ℝ) ^ 4 / (p.q * U ^ 2) *
      activeTypeIICellAnalyticRHSV3 p (Real.rpow p.X (2 / 3 : ℝ)) (1 / 24 : ℝ) C logIndex zbag mbag
        left suffix leftCell suffixCell component ≤
      cellBudgetConstant K C * (divisorCount p.q : ℝ) ^ 4 * p.X *
        Real.log p.X ^ (8 * K + 4 * K * K + 2) *
        (Q * Real.rpow p.X (-delta) + 1 / Real.sqrt Q +
          1 / U + Real.rpow p.X (-1 / 4 : ℝ)) := by
  dsimp only
  let T := Real.rpow p.X (2 / 3 : ℝ)
  let U := stationaryWidth p.beta p.H
  let E := 8 * K + 4 * K * K
  let S : ℝ := ((K ^ K * Nat.factorial K * Nat.factorial K : ℕ) : ℝ)
  let A := 1000 * (1 + Real.pi ^ 2) * (2 : ℝ) ^ (2 * K)
  let B := A * S ^ 2 * (2 + Real.log 8) ^ E
  let D : ℝ := (divisorCount p.q : ℝ) ^ 4
  let F := 16 * canonicalPerronKFour ^ 2 * D
  let loss := Q * Real.rpow p.X (-delta) + 1 / Real.sqrt Q + 1 / U
  have hX0 : 0 < p.X := by linarith
  have hQ0 : 0 < Q := by linarith
  have hs : 1 ≤ Real.sqrt Q := (Real.one_le_sqrt).2 hQ
  have hs0 : 0 < Real.sqrt Q := by linarith
  have heta0 : 0 < p.eta := by rw [heta]; positivity
  have heta1 : p.eta ≤ 1 := by rw [heta]; exact (div_le_one hs0).2 hs
  have hH0 : 0 < p.H := by
    rw [hH]
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hX0 _)
  have hU0 : 0 < U := by dsimp [U]; linarith
  have hT0 : 0 ≤ T := Real.rpow_nonneg hX0.le _
  have hlogs := selected_log_bounds hX hlog
  have h8 : 0 ≤ Real.log (8 : ℝ) := Real.log_nonneg (by norm_num)
  have hF : 0 ≤ F := by dsimp [F, D]; positivity
  have hB : 0 ≤ B := by dsimp [B, A, S]; positivity
  have hloss : 0 ≤ loss := by dsimp [loss]; positivity
  have hep := endpointEnvelope_le_three_losses p K hX hQ hqQ hH heta hU hqu hdelta hr0 hr
  have hmain := normalized_activeTypeIICellAnalyticRHS_le_uniform p T (1 / 24 : ℝ) C
    delta (Real.rpow p.X (delta + 1 / 8)) Q hX hk hH0 heta0 heta1 hq
    hU0 hT0 (Real.rpow_nonneg hX0.le _) (by norm_num) hQ0 hqu
    logIndex zbag mbag houtcome leftCell suffixCell hnonzero component
  apply hmain.trans
  have hep0 : 0 ≤ endpointEnvelope p K T delta (Real.rpow p.X (delta + 1 / 8)) := by
    unfold endpointEnvelope
    simp only [Real.rpow_eq_pow]
    positivity
  have hpow0 := pow_nonneg hlogs.2.2.1 E
  have hR0 : 0 ≤ Real.rpow p.X (3 / 4 : ℝ) := Real.rpow_nonneg hX0.le _
  have hRsmall0 : 0 ≤ Real.rpow p.X (-1 / 4 : ℝ) := Real.rpow_nonneg hX0.le _
  have h8R0 : 0 ≤ Real.rpow 8 (1 / 12 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hpow := pow_le_pow_left₀ hlogs.2.2.1 hlogs.2.2.2 E
  have hlead :
      16 * canonicalPerronKFour ^ 2 * D * Real.log (1 + T) ^ 2 * p.X *
        endpointEnvelope p K T delta (Real.rpow p.X (delta + 1 / 8)) * S ^ 2 *
        (1 + Real.log (8 * p.X)) ^ E ≤
      F * 9 * B * p.X * Real.log p.X ^ (E + 2) * loss := by
    calc
      _ ≤ 16 * canonicalPerronKFour ^ 2 * D * (9 * Real.log p.X ^ 2) * p.X *
          (A * loss) * S ^ 2 * ((2 + Real.log 8) * Real.log p.X) ^ E := by
        gcongr
        · exact hlogs.1
      _ = _ := by dsimp [F, B]; rw [mul_pow, pow_add]; ring
  have hetaQ : 1 ≤ p.eta * Q := by
    rw [heta]
    calc
      1 ≤ Real.sqrt Q := hs
      _ = 1 / Real.sqrt Q * Q := by
        field_simp
        nlinarith [Real.sq_sqrt hQ0.le]
  have hpower := perron_power_saving_eq hX0
  have hpower' : Real.rpow p.X (3 / 4 : ℝ) = p.X * Real.rpow p.X (-1 / 4 : ℝ) := by
    simpa only [Real.rpow_eq_pow, show (1 : ℝ) + (-1 / 4) = 3 / 4 by norm_num,
      Real.rpow_one] using Real.rpow_add hX0 1 (-1 / 4)
  have hsmall : Real.log p.X ^ 2 ≤ Real.log p.X ^ (E + 2) :=
    pow_le_pow_right₀ hlog (by omega)
  have herr :
      16 * canonicalPerronKFour ^ 2 * D * C ^ 2 *
        Real.rpow (8 * p.X) (1 / 24 : ℝ) ^ 2 * p.X ^ 2 / (p.eta * Q) *
        (Real.log (2 + T) / T) ^ 2 ≤
      F * 9 * (C ^ 2 * Real.rpow 8 (1 / 12 : ℝ)) * p.X *
        Real.log p.X ^ (E + 2) * Real.rpow p.X (-1 / 4 : ℝ) := by
    calc
      _ = F * C ^ 2 *
          (Real.rpow (8 * p.X) (1 / 24 : ℝ) ^ 2 * p.X ^ 2 / T ^ 2) *
          Real.log (2 + T) ^ 2 / (p.eta * Q) := by dsimp [F]; ring
      _ = F * C ^ 2 * (Real.rpow 8 (1 / 12 : ℝ) * Real.rpow p.X (3 / 4 : ℝ)) *
          Real.log (2 + T) ^ 2 / (p.eta * Q) := by rw [hpower]
      _ ≤ F * C ^ 2 * (Real.rpow 8 (1 / 12 : ℝ) * Real.rpow p.X (3 / 4 : ℝ)) *
          Real.log (2 + T) ^ 2 := div_le_self (by positivity) hetaQ
      _ ≤ F * C ^ 2 * (Real.rpow 8 (1 / 12 : ℝ) * Real.rpow p.X (3 / 4 : ℝ)) *
          (9 * Real.log p.X ^ (E + 2)) := by
        gcongr
        exact hlogs.2.1.trans (mul_le_mul_of_nonneg_left hsmall (by norm_num))
      _ = _ := by rw [hpower']; ring
  have hsum := add_le_add hlead herr
  apply hsum.trans
  have hcross : B * loss + (C ^ 2 * Real.rpow 8 (1 / 12 : ℝ)) *
      Real.rpow p.X (-1 / 4 : ℝ) ≤
      (B + C ^ 2 * Real.rpow 8 (1 / 12 : ℝ)) *
        (loss + Real.rpow p.X (-1 / 4 : ℝ)) := by
    nlinarith [mul_nonneg hB (Real.rpow_nonneg hX0.le (-1 / 4 : ℝ)),
      mul_nonneg (show 0 ≤ C ^ 2 * Real.rpow 8 (1 / 12 : ℝ) by positivity) hloss]
  have hfinal := mul_le_mul_of_nonneg_left hcross
    (show 0 ≤ F * 9 * p.X * Real.log p.X ^ (E + 2) by positivity)
  convert hfinal using 1 <;> dsimp [cellBudgetConstant, F, D, B, A, S, E, loss] <;> ring

end
end MRTProposition61TypeIIActiveCellBudgetV3

#print axioms MRTProposition61TypeIIActiveCellBudgetV3.normalized_activeTypeIICellAnalyticRHS_le_uniform
#print axioms MRTProposition61TypeIIActiveCellBudgetV3.normalized_activeTypeIICellAnalyticRHS_le_polylog
