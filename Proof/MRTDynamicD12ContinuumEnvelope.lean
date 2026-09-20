import MRTDynamicD12ContinuumBand

namespace MRTDynamicD12ContinuumSampling
noncomputable section
open scoped BigOperators
open MRTDynamicD12MomentSource MRTDynamicD12SmoothSampled

theorem smoothBandBudgetShape_le_five {T rho : ℝ} {q L U : ℕ}
    (hT : 0 < T) (hrho : 0 < rho) (hq : (q : ℝ) ≤ T)
    (hL : 1 ≤ L) (hUT : (U : ℝ) ≤ T^2) (hUrho : (U : ℝ) ≤ rho^2) :
    smoothBandBudgetShape T rho q L U ≤ 5 * ((q : ℝ)*T) := by
  have hqerr : (q : ℝ)^2/T^2 ≤ 1 :=
    (div_le_one (pow_pos hT 2)).mpr (pow_le_pow_left₀ (Nat.cast_nonneg _) hq 2)
  have hUerr : (U : ℝ)^2/T^4 ≤ 1 := by
    apply (div_le_one (pow_pos hT 4)).mpr
    have h := pow_le_pow_left₀ (Nat.cast_nonneg _) hUT 2
    nlinarith
  have hLerr : 1/(L : ℝ)^2 ≤ 1 := by
    have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
    apply (div_le_one (by positivity : 0 < (L : ℝ)^2)).mpr
    nlinarith
  have hres : (U : ℝ)^2/rho^4 ≤ 1 := by
    apply (div_le_one (pow_pos hrho 4)).mpr
    have h := pow_le_pow_left₀ (Nat.cast_nonneg _) hUrho 2
    nlinarith
  have hbase : 0 ≤ (q : ℝ)*T := mul_nonneg (Nat.cast_nonneg _) hT.le
  have hmain := mul_le_mul_of_nonneg_left
    (show (q : ℝ)^2/T^2+(U : ℝ)^2/T^4+1/(L : ℝ)^2 ≤ 3 by linarith) hbase
  have htail := mul_le_mul_of_nonneg_right hres hbase
  unfold smoothBandBudgetShape
  have heq : (U : ℝ)^2*(((q : ℝ)*T)/rho^4) = ((U : ℝ)^2/rho^4)*((q : ℝ)*T) := by ring
  rw [heq]
  linarith

/-- The geometric `rho² ≥ 2X` threshold kills all cutoff sectors uniformly. -/
theorem smoothBandBudgetShape_le_five_of_rho {X T rho : ℝ} {q L U : ℕ}
    (hrho : 0 < rho) (hrhoT : rho ≤ T) (hq : (q : ℝ) ≤ T)
    (hL : 1 ≤ L) (hUX : (U : ℝ) ≤ 2*X) (hXrho : 2*X ≤ rho^2) :
    smoothBandBudgetShape T rho q L U ≤ 5*((q : ℝ)*T) := by
  exact smoothBandBudgetShape_le_five (hrho.trans_le hrhoT) hrho hq hL
    ((hUX.trans hXrho).trans (pow_le_pow_left₀ hrho.le hrhoT 2)) (hUX.trans hXrho)

/-- A single uniform polylog budget for both literal smooth coefficient systems. -/
theorem dynamicD12SmoothContinuumPowerBudget_proved :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ, 4 ≤ B ∧
      ∀ {X T K a b rho : ℝ} {q L U : ℕ} [NeZero q],
        DynamicD12MomentRange X T K q U → 2 ≤ L → L < U →
        a ≤ b → b-a+1 ≤ T → 0 < rho → rho ≤ T → (U : ℝ) ≤ rho^2 →
        (∀ t ∈ Set.Icc a b, rho ≤ |t| ∧ |t| ≤ T) →
        continuumMass (smoothIntervalPolynomial q L U) a b ≤
          C*((q : ℝ)*T)*(1+Real.log X)^B ∧
        continuumMass (smoothLogIntervalPolynomial q L U) a b ≤
          C*((q : ℝ)*T)*(1+Real.log X)^B := by
  obtain ⟨C,hC,B,hB,hsource⟩ := dynamicD12SmoothContinuumBandBudget_proved
  refine ⟨5*C, by positivity, B+4, by omega, ?_⟩
  intro X T K a b rho q L U _ hrange hL hLU hab hlen hrho hrhoT hUrho hann
  have hT : 0 ≤ T := by linarith [hrange.T_ge_two]
  have h := hsource hrange hL hLU hab hlen hrho hann
  have hshape := smoothBandBudgetShape_le_five (L := L) (by linarith [hrange.T_ge_two]) hrho hrange.q_le_T
    (by omega) (hUrho.trans (pow_le_pow_left₀ hrho.le hrhoT 2)) hUrho
  have hlog : 1 ≤ 1+Real.log X := by
    have := Real.log_nonneg (show 1 ≤ X by linarith [hrange.X_large])
    linarith
  have hUpos : 0 < (U : ℝ) := by exact_mod_cast (show 0 < U by omega)
  have hlogU : Real.log (U : ℝ) ≤ 1+Real.log X := by
    have := Real.log_le_log hUpos hrange.cutoff_le_X
    linarith
  have hlogU0 : 0 ≤ Real.log (U : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ U by omega))
  have hp : (1+Real.log X)^B ≤ (1+Real.log X)^(B+4) :=
    pow_le_pow_right₀ hlog (by omega)
  have hbase : 0 ≤ (q : ℝ)*T := by positivity
  have hmain := mul_le_mul_of_nonneg_left hshape
    (by positivity : 0 ≤ C*(1+Real.log X)^B)
  constructor
  · have hh := h.1.trans hmain
    have he : C*(1+Real.log X)^B*(5*((q : ℝ)*T)) =
        (5*C)*((q : ℝ)*T)*(1+Real.log X)^B := by ring
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hp (by positivity))
  · have hh := h.2.trans (mul_le_mul_of_nonneg_right hmain (pow_nonneg hlogU0 4))
    have hpow := pow_le_pow_left₀ hlogU0 hlogU 4
    have hh' := hh.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
    convert hh' using 1 <;> rw [pow_add] <;> ring

end
end MRTDynamicD12ContinuumSampling

#print axioms MRTDynamicD12ContinuumSampling.dynamicD12SmoothContinuumPowerBudget_proved
