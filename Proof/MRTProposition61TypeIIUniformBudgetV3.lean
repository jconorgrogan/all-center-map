import MRTProposition61TypeIIActiveCellBudgetV3
import MRTProposition61TypeIIPolylogBudgetV3
import MRTLemma215DynamicTypeIIGlobalCountV3
import MRTLemma215DynamicTypeIIParameterGeometryV3

/-! # Uniform refined Type-II source budget at the actual MAP parameters -/

namespace MRTProposition61TypeIIUniformBudgetV3

open scoped BigOperators
open Filter
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPDynamicHBSourceV3 MAPFinishDynamicLowTypes MAPFinishDynamicLowTypesRefinedV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicFactorExtractionV3 MRTLemma215DynamicRegroupingV3
open MRTLemma215DynamicSupportV3 MRTLemma215ScaleClassifierV3
open MRTLemma215DynamicOutcomeWeldV3 MRTLemma215DynamicTypeIIFactorizationV3
open MRTProposition61TypeIIComponentTotalV3 MRTProposition61TypeIIActiveAggregateBoundV3
open MRTProposition61TypeIIGlobalFilteredAnalyticV3
open MRTProposition61TypeIIActiveCellBudgetV3 MRTProposition61TypeIIDivisorNormalizationV3
open MRTLemma215DynamicTypeIIGlobalCountV3 MRTLemma215DynamicTypeIIParameterGeometryV3
open MRTProposition61TypeIIPolylogBudgetV3

noncomputable section

set_option maxHeartbeats 1600000

/-- Coefficient in the literal global counting envelope. -/
def globalCountConstant (K : ℕ) : ℝ :=
  144 * (K : ℝ) ^ 2 * ((6 + K : ℕ) : ℝ) ^ (4 * K) * (18 * K) ^ 4

theorem globalCountConstant_nonneg (K : ℕ) : 0 ≤ globalCountConstant K := by
  unfold globalCountConstant
  positivity

theorem typeII_cell_constant_nonneg (K : ℕ) (C : ℝ) :
    0 ≤ cellBudgetConstant K C := by
  have hlog : 0 ≤ Real.log (8 : ℝ) := Real.log_nonneg (by norm_num)
  have hpow : 0 ≤ Real.rpow (8 : ℝ) (1 / 12 : ℝ) := Real.rpow_nonneg (by norm_num) _
  unfold cellBudgetConstant
  positivity

/-- The complete refined source, with one coefficient constant, one divisor
constant and one fixed logarithmic exponent chosen before all input data. -/
theorem exists_uniform_normalized_typeII_le_scalar_envelope
    (delta : ℝ) (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 240) :
    ∃ Ctotal : ℝ, 0 < Ctotal ∧ ∃ P : ℕ,
      ∀ (p : Corollary53Input) [NeZero p.q]
        (hp : Corollary53Admissible 1 1 p) (Q reserve : ℝ)
        (hX : 3 ≤ p.X) (hlog : 1 ≤ Real.log p.X)
        (hQ : 1 ≤ Q) (hqQ : (p.q : ℝ) ≤ Q)
        (hH : p.H = (1 / 2 : ℝ) * Real.rpow p.X (2 / 15 + reserve))
        (heta : p.eta = 1 / Real.sqrt Q)
        (hU : 1 ≤ stationaryWidth p.beta p.H)
        (hqu : p.q * stationaryWidth p.beta p.H ≤ p.H / Q)
        (hr0 : 0 ≤ reserve) (hr : reserve ≤ 1 / 1200)
        (hglobal : (2 : ℝ) ^ (2 * hbOrder delta) *
          (2 * Real.rpow p.X (delta + 1 / 8)) ≤ p.X),
        dynamicLowNormalizationV3 p *
          (∑ component : OuterComponent,
            dynamicAllTypeIIMassRefinedV3 p delta (Real.rpow p.X (delta + 1 / 8))
              (le_trans (by norm_num : (2 : ℝ) ≤ 3) hX) hdelta component) ≤
          Ctotal * p.X * Real.log p.X ^ P *
            (Real.rpow Q (1 / 8 : ℝ) *
                (Q * Real.rpow p.X (-delta) + 1 / Real.sqrt Q +
                  1 / stationaryWidth p.beta p.H) +
              Real.rpow Q (1 / 8 : ℝ) * Real.rpow p.X (-(1 / 4 : ℝ))) := by
  classical
  obtain ⟨C, hC, hsource⟩ :=
    exists_fixedOrder_sum_dynamicAllTypeIIMassRefined_le_uniformFilteredAnalyticLedger
      delta (1 / 24) hdelta (by norm_num)
  obtain ⟨Cd, hCd, hdivisor⟩ := exists_divisorCount_four_le_range_subpower
    (1 / 8) (by norm_num)
  let K := hbOrder delta
  let E := 8 * K + 4 * K * K + 2
  let F := 4 * K + 6
  let G := globalCountConstant K
  let Ccell := cellBudgetConstant K C
  let Ctotal := 1 + G * Ccell * Cd
  have hG0 : 0 ≤ G := globalCountConstant_nonneg K
  have hCc0 : 0 ≤ Ccell := typeII_cell_constant_nonneg K C
  have htotal : 0 < Ctotal := by dsimp [Ctotal]; positivity
  refine ⟨Ctotal, htotal, F + E, ?_⟩
  intro p _ hp Q reserve hX hlog hQ hqQ hH heta hU hqu hr0 hr hglobal
  have hX0 : 0 < p.X := by linarith
  have hX1 : 1 ≤ p.X := by linarith
  have hX2 : 2 ≤ p.X := by linarith
  have hqNat : 1 ≤ p.q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne p.q)
  have hq : 1 ≤ (p.q : ℝ) := by exact_mod_cast hqNat
  have hQ0 : 0 < Q := by linarith
  have hlog0 : 0 ≤ Real.log p.X := by linarith
  have hU0 : 0 < stationaryWidth p.beta p.H := by linarith
  have hXpow : 0 ≤ Real.rpow p.X (-delta) := Real.rpow_nonneg hX0.le _
  have hXquarter : 0 ≤ Real.rpow p.X (-(1 / 4 : ℝ)) := Real.rpow_nonneg hX0.le _
  have hQe : 0 ≤ Real.rpow Q (1 / 8 : ℝ) := Real.rpow_nonneg hQ0.le _
  let loss := Q * Real.rpow p.X (-delta) + 1 / Real.sqrt Q +
    1 / stationaryWidth p.beta p.H + Real.rpow p.X (-(1 / 4 : ℝ))
  have hloss : 0 ≤ loss := by dsimp [loss]; positivity
  let Bcell := Ccell * (divisorCount p.q : ℝ) ^ 4 * p.X * Real.log p.X ^ E * loss
  have hBcell : 0 ≤ Bcell := by dsimp [Bcell]; positivity
  have hnorm : 0 ≤ dynamicLowNormalizationV3 p := by
    unfold dynamicLowNormalizationV3
    positivity
  have hledger := scaled_dynamicAllTypeIIFilteredAnalyticLedger_le_polylog_of_activeCell_bound
    (delta := delta) (H₀ := Real.rpow p.X (delta + 1 / 8))
    (T := Real.rpow p.X (2 / 3 : ℝ)) (theta := (1 / 24 : ℝ)) (C := C)
    hX hBcell hnorm (by
      intro component branch logIndex zbag mbag
      dsimp only
      intro hout hsuffix leftCell suffixCell hactive
      have hn := (Finset.mem_filter.mp hactive).2
      have hc := normalized_activeTypeIICellAnalyticRHS_le_polylog p C delta reserve Q
        hX1 hlog branch.isLt hq hQ hqQ hH heta hU hqu hdeltaUpper hr0 hr
        logIndex zbag mbag hout leftCell suffixCell hn component
      simpa only [dynamicLowNormalizationV3, Bcell, Ccell, E, K, loss, neg_div] using hc)
  have hsrc := hsource p hp (Real.rpow p.X (delta + 1 / 8))
    (Real.rpow p.X (2 / 3 : ℝ)) hX2
    (Real.rpow_nonneg hX0.le _) hglobal
    (Real.one_le_rpow hX1 (by norm_num))
  have hd := hdivisor p.q Q hqNat hqQ
  calc
    _ ≤ G * Real.log p.X ^ F * Bcell := by
      exact (mul_le_mul_of_nonneg_left hsrc hnorm).trans hledger
    _ = (G * Ccell * (divisorCount p.q : ℝ) ^ 4) * p.X *
        Real.log p.X ^ (F + E) * loss := by dsimp [Bcell]; rw [pow_add]; ring
    _ ≤ (G * Ccell * (Cd * Real.rpow Q (1 / 8 : ℝ))) * p.X *
        Real.log p.X ^ (F + E) * loss := by gcongr
    _ = (G * Ccell * Cd) * p.X * Real.log p.X ^ (F + E) *
        (Real.rpow Q (1 / 8 : ℝ) *
            (Q * Real.rpow p.X (-delta) + 1 / Real.sqrt Q +
              1 / stationaryWidth p.beta p.H) +
          Real.rpow Q (1 / 8 : ℝ) * Real.rpow p.X (-(1 / 4 : ℝ))) := by
      dsimp [loss]
      ring
    _ ≤ _ := by
      have hc : G * Ccell * Cd ≤ Ctotal := by dsimp [Ctotal]; linarith
      gcongr

/-- Uniform `/30` producer for the literal refined Type-II low-type field.
Both logarithmic parameter exponents may subsequently be increased. -/
theorem eventually_refined_typeII_budget_thirtieth
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
              (∑ component : OuterComponent,
                dynamicAllTypeIIMassRefinedV3 p delta (Real.rpow p.X (delta + 1 / 8))
                  hXp hdelta component) ≤ p.X * Real.rpow (Real.log p.X) (-A) / 30 := by
  obtain ⟨C, hC, P, hsource⟩ :=
    exists_uniform_normalized_typeII_le_scalar_envelope delta hdelta hdeltaUpper
  obtain ⟨B₀, hB₀⟩ := eventually_typeII_scalar_envelope_le_thirtieth
    C (P : ℝ) A delta hC.le hdelta
  refine ⟨B₀, ?_⟩
  intro B hB
  obtain ⟨Cc₀, hCc₀⟩ := hB₀ B hB
  refine ⟨Cc₀, ?_⟩
  intro Cc hCc
  have hlogEvent : ∀ᶠ X : ℝ in atTop, 1 ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  filter_upwards [hCc₀ Cc hCc,
    eventually_actual_typeII_parameter_geometry delta hdelta hdeltaUpper,
    hlogEvent] with X hscalar hgeometry hlog
  intro p _ hp hpX reserve hr0 hr hH heta hqQ hbeta hfar hXp
  have hX3 : 3 ≤ p.X := by simpa only [hpX] using hgeometry.1
  have hX0 : 0 < p.X := by linarith
  have hlogp : 1 ≤ Real.log p.X := by simpa only [hpX] using hlog
  have hQ : 1 ≤ (Real.log p.X) ^ B := one_le_pow₀ hlogp
  have hQ0 : 0 < (Real.log p.X) ^ B := by linarith
  have hCcPow : 1 ≤ (Real.log p.X) ^ Cc := one_le_pow₀ hlogp
  have hU : 1 ≤ stationaryWidth p.beta p.H := by linarith
  have hUpow : (Real.log p.X) ^ Cc ≤ stationaryWidth p.beta p.H := by linarith
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
  have hglobal : (2 : ℝ) ^ (2 * hbOrder delta) *
      (2 * Real.rpow p.X (delta + 1 / 8)) ≤ p.X := by
    simpa only [hpX] using hgeometry.2.2.2.2.1
  have hs := hsource p hp ((Real.log p.X) ^ B) reserve hX3 hlogp
    hQ hqQ hH heta hU hqu hr0 hr hglobal
  have hscalarp := hscalar (stationaryWidth p.beta p.H)
    (by simpa only [← hpX] using hUpow)
  have hmul := mul_le_mul_of_nonneg_left hscalarp hX0.le
  calc
    _ ≤ _ := hs
    _ ≤ p.X * Real.rpow (Real.log p.X) (-A) / 30 := by
      convert hmul using 1 <;>
        simp only [← hpX, Real.rpow_eq_pow, Real.rpow_natCast] <;> ring

/-- Threshold form with all input data quantified after `X₀`. -/
theorem exists_refined_typeII_budget_threshold
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
              (∑ component : OuterComponent,
                dynamicAllTypeIIMassRefinedV3 p delta (Real.rpow p.X (delta + 1 / 8))
                  hXp hdelta component) ≤ p.X * Real.rpow (Real.log p.X) (-A) / 30 := by
  obtain ⟨B₀, hB₀⟩ := eventually_refined_typeII_budget_thirtieth delta A hdelta hdeltaUpper
  refine ⟨B₀, ?_⟩
  intro B hB
  obtain ⟨Cc₀, hCc₀⟩ := hB₀ B hB
  refine ⟨Cc₀, ?_⟩
  intro Cc hCc
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp (hCc₀ Cc hCc)
  refine ⟨max 3 X₀, le_max_left _ _, ?_⟩
  intro X hX
  exact hX₀ X ((le_max_right _ _).trans hX)

end
end MRTProposition61TypeIIUniformBudgetV3

#print axioms MRTProposition61TypeIIUniformBudgetV3.exists_uniform_normalized_typeII_le_scalar_envelope

#print axioms MRTProposition61TypeIIUniformBudgetV3.eventually_refined_typeII_budget_thirtieth

#print axioms MRTProposition61TypeIIUniformBudgetV3.exists_refined_typeII_budget_threshold
