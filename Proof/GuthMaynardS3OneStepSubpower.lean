import GuthMaynardFiniteSqrtBootstrap

open scoped Real
noncomputable section
namespace GuthMaynardS3OneStepSubpower

/-- Scalar coefficient absorption used after the shifted finite square-root
bound.  The coefficient and `K` are selected before `T`; no sign assumption
on `Y` is needed because `Real.sqrt` vanishes on the negative half-line. -/
theorem one_step_subpower
    {C K T eta delta epsilon X Y : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hT : 1 ≤ T)
    (heta : 0 < eta) (hdelta : 0 < delta)
    (hexp : 8 * eta + 2 * delta ≤ epsilon)
    (hY : Y ≤ K * T ^ epsilon)
    (hX : X ≤ C * (16 : ℝ)^6 * T ^ (3 * eta) + C +
      C * (16 : ℝ)^2 * T ^ (4 * eta + delta) * Real.sqrt Y) :
    X ≤ (C * (16 : ℝ)^6 + C + C * (16 : ℝ)^2 * Real.sqrt K) * T ^ epsilon := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hT0 : 0 ≤ T := hTpos.le
  have hE0 : 0 ≤ epsilon := by
    have hq : 0 ≤ 8 * eta + 2 * delta := by positivity
    linarith
  have hKpow : 0 ≤ K * T ^ epsilon := by positivity
  have hsqrtY : Real.sqrt Y ≤ Real.sqrt K * T ^ (epsilon / 2) := by
    by_cases hY0 : 0 ≤ Y
    · have hs := Real.sqrt_le_sqrt (show Y ≤ K * T ^ epsilon from hY)
      calc
        Real.sqrt Y ≤ Real.sqrt (K * T ^ epsilon) := hs
        _ = Real.sqrt K * T ^ (epsilon / 2) := by
          rw [Real.sqrt_mul hK]
          have hp : Real.sqrt (T ^ epsilon) = T ^ (epsilon / 2) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT0]
            congr 1 <;> ring
          rw [hp]
    · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hY0)]
      positivity
  have h3 : 3 * eta ≤ epsilon := by
    nlinarith
  have hmid : 4 * eta + delta + epsilon / 2 ≤ epsilon := by
    nlinarith
  have hpow3 : T ^ (3 * eta) ≤ T ^ epsilon :=
    Real.rpow_le_rpow_of_exponent_le hT h3
  have hpowmid : T ^ (4 * eta + delta) * T ^ (epsilon / 2) ≤ T ^ epsilon := by
    rw [← Real.rpow_add hTpos]
    exact Real.rpow_le_rpow_of_exponent_le hT hmid
  have hsqrtY' :
      C * (16 : ℝ)^2 * T ^ (4 * eta + delta) * Real.sqrt Y ≤
      C * (16 : ℝ)^2 * Real.sqrt K * T ^ epsilon := by
    have hc : 0 ≤ C * (16 : ℝ)^2 * T ^ (4 * eta + delta) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hsqrtY hc
    calc
      C * (16 : ℝ)^2 * T ^ (4 * eta + delta) * Real.sqrt Y ≤
          C * (16 : ℝ)^2 * T ^ (4 * eta + delta) *
            (Real.sqrt K * T ^ (epsilon / 2)) := hmul
      _ = C * (16 : ℝ)^2 * Real.sqrt K *
            (T ^ (4 * eta + delta) * T ^ (epsilon / 2)) := by ring
      _ ≤ C * (16 : ℝ)^2 * Real.sqrt K * T ^ epsilon := by
        gcongr
  calc
    X ≤ C * (16 : ℝ)^6 * T ^ (3 * eta) + C +
        C * (16 : ℝ)^2 * T ^ (4 * eta + delta) * Real.sqrt Y := hX
    _ ≤ C * (16 : ℝ)^6 * T ^ epsilon + C +
        C * (16 : ℝ)^2 * Real.sqrt K * T ^ epsilon := by
      gcongr
    _ ≤ C * (16 : ℝ)^6 * T ^ epsilon + C * T ^ epsilon +
        C * (16 : ℝ)^2 * Real.sqrt K * T ^ epsilon := by
      have hTe : 1 ≤ T ^ epsilon := Real.one_le_rpow hT hE0
      have hCt : C ≤ C * T ^ epsilon :=
        le_mul_of_one_le_right hC hTe
      linarith
    _ = (C * (16 : ℝ)^6 + C + C * (16 : ℝ)^2 * Real.sqrt K) * T ^ epsilon := by ring

end GuthMaynardS3OneStepSubpower

#print axioms GuthMaynardS3OneStepSubpower.one_step_subpower
