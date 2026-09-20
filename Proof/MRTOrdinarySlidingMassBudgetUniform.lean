import MRTOrdinarySlidingMassBudget
import MRTProposition61TypeIIPolylogBudgetV3

namespace MAPMRTOrdinarySlidingMassBudgetUniform
open Filter
open MAPMRTCorollary53Source MAPMRTOrdinarySlidingMassBudget
open MRTProposition61TypeIIPolylogBudgetV3
noncomputable section
set_option maxHeartbeats 800000

/-- The literal ordinary error admits a uniform scalar envelope. -/
theorem ordinaryError_map_le_scalar {X H beta eta : ℝ}
    (hX : 2 ≤ X) (hH : 1 ≤ H) (hHX : H ≤ X)
    (heta : 0 ≤ eta) (hetaOne : eta ≤ 1)
    (hU : 1 ≤ stationaryWidth beta H) :
    ordinaryError X H (mapMangoldtCoeff X) beta eta ≤
      64 * X * Real.log X ^ 2 * (eta + 1 / stationaryWidth beta H) := by
  have hH0 : 0 < H := by linarith
  have hX0 : 0 < X := by linarith
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hlog2 : Real.log (2 * X) ≤ 2 * Real.log X := by
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hX0.ne']
    have := Real.log_le_log (by norm_num : (0:ℝ) < 2) hX
    linarith
  have hlog20 : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
  have hi0 : 0 ≤ 1 / stationaryWidth beta H := by positivity
  have hi1 : 1 / stationaryWidth beta H ≤ 1 := by
    exact (div_le_one (by linarith : 0 < stationaryWidth beta H)).mpr hU
  have hs : (eta + 1 / stationaryWidth beta H)^2 ≤
      2 * (eta + 1 / stationaryWidth beta H) := by nlinarith
  have hl : Real.log (2 * X)^2 ≤ 4 * Real.log X^2 := by nlinarith
  have hm := ordinarySlidingMass_map_le hX hH hHX
  rw [ordinaryError_eq_U (by rfl : stationaryWidth beta H = stationaryWidth beta H)]
  calc
    _ ≤ (eta + 1 / stationaryWidth beta H)^2 / H^2 *
        (8 * X * H^2 * Real.log (2 * X)^2) := by
      exact mul_le_mul_of_nonneg_left hm (by positivity)
    _ = 8 * X * (eta + 1 / stationaryWidth beta H)^2 * Real.log (2 * X)^2 := by
      field_simp
    _ ≤ 8 * X * (2 * (eta + 1 / stationaryWidth beta H)) *
        (4 * Real.log X^2) := by gcongr
    _ = _ := by ring

/-- Constants precede X and all source parameters. Both B and Cc can be
increased. The conclusion concerns the literal Mangoldt ordinary error and
requires only the source H-range, eta normalization, and far U-inequality. -/
theorem exists_ordinary_error_budget_threshold (A : ℝ) :
    ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∃ Cc₀ : ℕ, ∀ Cc : ℕ, Cc₀ ≤ Cc →
        ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
          ∀ (p : Corollary53Input)
            (hp : Corollary53Admissible 1 1 p) (hpX : p.X = X)
            (heta : p.eta = 1 / Real.sqrt ((Real.log p.X) ^ B))
            (hfar : 2 * (Real.log p.X) ^ Cc < stationaryWidth p.beta p.H),
            ordinaryError p.X p.H (mapMangoldtCoeff p.X) p.beta p.eta ≤
              p.X * Real.rpow (Real.log p.X) (-A) / 5 := by
  obtain ⟨B₀, hB₀⟩ := eventually_typeII_scalar_envelope_le_thirtieth
    64 2 A 1 (by norm_num) (by norm_num)
  refine ⟨B₀, ?_⟩
  intro B hB
  obtain ⟨Cc₀, hCc₀⟩ := hB₀ B hB
  refine ⟨Cc₀, ?_⟩
  intro Cc hCc
  have hlogs : ∀ᶠ X : ℝ in atTop, 1 ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hall : ∀ᶠ X : ℝ in atTop,
      3 ≤ X ∧ 1 ≤ Real.log X ∧
      ∀ U : ℝ, (Real.log X)^Cc ≤ U →
        let Q := (Real.log X)^B
        64 * Real.rpow (Real.log X) 2 *
          (Real.rpow Q (1/8:ℝ) * (Q * Real.rpow X (-1) + 1 / Real.sqrt Q + 1/U) +
            Real.rpow Q (1/8:ℝ) * Real.rpow X (-(1/4:ℝ))) ≤
          Real.rpow (Real.log X) (-A) / 30 := by
    filter_upwards [hCc₀ Cc hCc, hlogs, eventually_ge_atTop 3] with X hs hl hx
    exact ⟨hx, hl, hs⟩
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp hall
  refine ⟨max 3 X₀, le_max_left _ _, ?_⟩
  intro X hX p hp hpX heta hfar
  obtain ⟨hX3, hlog, hs⟩ := hX₀ X ((le_max_right _ _).trans hX)
  subst X
  have hQ : 1 ≤ (Real.log p.X)^B := one_le_pow₀ hlog
  have hQ0 : 0 < (Real.log p.X)^B := by linarith
  have hCcPow : 1 ≤ (Real.log p.X)^Cc := one_le_pow₀ hlog
  have hU : 1 ≤ stationaryWidth p.beta p.H := by linarith
  have hUpow : (Real.log p.X)^Cc ≤ stationaryWidth p.beta p.H := by linarith
  have hX0 : 0 ≤ p.X := by linarith
  have hs' := hs (stationaryWidth p.beta p.H) hUpow
  dsimp only at hs'
  have hQpow : 1 ≤ Real.rpow ((Real.log p.X)^B) (1/8:ℝ) :=
    Real.one_le_rpow hQ (by norm_num)
  have hrem : 0 ≤ (Real.log p.X)^B * Real.rpow p.X (-1) :=
    mul_nonneg hQ0.le (Real.rpow_nonneg hX0 _)
  have hrem2 : 0 ≤ Real.rpow ((Real.log p.X)^B) (1/8:ℝ) *
      Real.rpow p.X (-(1/4:ℝ)) :=
    mul_nonneg (Real.rpow_nonneg hQ0.le _) (Real.rpow_nonneg hX0 _)
  have hin : p.eta + 1 / stationaryWidth p.beta p.H ≤
      Real.rpow ((Real.log p.X)^B) (1/8:ℝ) *
        ((Real.log p.X)^B * Real.rpow p.X (-1) +
          1 / Real.sqrt ((Real.log p.X)^B) + 1 / stationaryWidth p.beta p.H) +
      Real.rpow ((Real.log p.X)^B) (1/8:ℝ) * Real.rpow p.X (-(1/4:ℝ)) := by
    rw [heta]
    have hi : 0 ≤ 1 / Real.sqrt ((Real.log p.X)^B) + 1 / stationaryWidth p.beta p.H := by positivity
    nlinarith
  have hscalar : 64 * Real.log p.X^2 * (p.eta + 1 / stationaryWidth p.beta p.H) ≤
      Real.rpow (Real.log p.X) (-A) / 30 := by
    have h := mul_le_mul_of_nonneg_left hin (show 0 ≤ 64 * Real.log p.X^2 by positivity)
    exact h.trans (by simpa only [Real.rpow_eq_pow, Real.rpow_two] using hs')
  have hm := ordinaryError_map_le_scalar (by linarith : 2 ≤ p.X)
    hp.1 hp.2.1 hp.2.2.2.2.1.le hp.2.2.2.2.2.1 hU
  calc
    _ ≤ 64 * p.X * Real.log p.X^2 * (p.eta + 1 / stationaryWidth p.beta p.H) := hm
    _ ≤ p.X * Real.rpow (Real.log p.X) (-A) / 30 := by
      have h := mul_le_mul_of_nonneg_left hscalar hX0
      nlinarith
    _ ≤ _ := by
      have hr : 0 ≤ Real.rpow (Real.log p.X) (-A) :=
        Real.rpow_nonneg (by linarith) _
      have hm := mul_nonneg hX0 hr
      linarith
end
end MAPMRTOrdinarySlidingMassBudgetUniform
#print axioms MAPMRTOrdinarySlidingMassBudgetUniform.exists_ordinary_error_budget_threshold
