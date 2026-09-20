import FordFiniteGrowthBound

open scoped BigOperators
noncomputable section
namespace FordGrowthWidth

open FordAllLambdaOffsetBound FordFiniteGrowthBound

def widthEta (T : ℝ) : ℝ :=
  savingCoeff * T ^ (-(9 / 10 : ℝ))

theorem width_properties {T : ℝ} (hT : 1 ≤ T) :
    0 < widthEta T ∧
    widthEta T ≤ (1 : ℝ) / 2 ∧
    1000 * widthEta T * T ^ ((4 : ℝ) / 5) ≤ 1 ∧
    widthEta T * Real.sqrt (widthEta T / savingCoeff) * T ≤ 1 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hc : 0 < savingCoeff := savingCoeff_pos
  have hcsmall : savingCoeff ≤ (1 / 10000000000 : ℝ) := by
    dsimp [savingCoeff]
    exact min_le_right _ _
  have hc1 : savingCoeff ≤ (1 : ℝ) := by
    linarith
  have hneg : T ^ (-(9 / 10 : ℝ)) ≤ 1 := by
    have := Real.rpow_le_rpow_of_exponent_le hT (by norm_num : -(9 / 10 : ℝ) ≤ 0)
    simpa using this
  have hpos : 0 < widthEta T := by
    dsimp [widthEta]
    positivity
  have hhalf : widthEta T ≤ (1 : ℝ) / 2 := by
    dsimp [widthEta]
    have : savingCoeff * T ^ (-(9 / 10 : ℝ)) ≤ savingCoeff := by
      simpa [mul_comm] using (mul_le_of_le_one_left hc.le hneg)
    linarith
  have hfirst_id :
      1000 * widthEta T * T ^ ((4 : ℝ) / 5) =
        1000 * savingCoeff * T ^ (-(1 / 10 : ℝ)) := by
    dsimp [widthEta]
    calc
      1000 * (savingCoeff * T ^ (-(9 / 10 : ℝ))) * T ^ ((4 : ℝ) / 5) =
          1000 * savingCoeff *
            (T ^ (-(9 / 10 : ℝ)) * T ^ ((4 : ℝ) / 5)) := by ring
      _ = 1000 * savingCoeff * T ^ (-(1 / 10 : ℝ)) := by
        rw [← Real.rpow_add hTpos]
        congr 2
        ring
  have hfirst : 1000 * widthEta T * T ^ ((4 : ℝ) / 5) ≤ 1 := by
    rw [hfirst_id]
    have hpow : T ^ (-(1 / 10 : ℝ)) ≤ 1 := by
      simpa using (Real.rpow_le_rpow_of_exponent_le hT
        (by norm_num : -(1 / 10 : ℝ) ≤ 0))
    have hcoef : 1000 * savingCoeff ≤ 1 := by nlinarith [hcsmall]
    calc
      1000 * savingCoeff * T ^ (-(1 / 10 : ℝ)) ≤
          1 * T ^ (-(1 / 10 : ℝ)) :=
        mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (by positivity) _)
      _ ≤ 1 := by simpa using hpow
  have hratio : widthEta T / savingCoeff = T ^ (-(9 / 10 : ℝ)) := by
    dsimp [widthEta]
    field_simp [ne_of_gt hc]
  have hsqrt : Real.sqrt (widthEta T / savingCoeff) =
      T ^ (-(9 / 20 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, hratio]
    rw [← Real.rpow_mul hTpos.le]
    congr 1
    ring
  have hsecond_id :
      widthEta T * Real.sqrt (widthEta T / savingCoeff) * T =
        savingCoeff * T ^ (-(7 / 20 : ℝ)) := by
    rw [hsqrt]
    dsimp [widthEta]
    calc
      (savingCoeff * T ^ (-(9 / 10 : ℝ))) * T ^ (-(9 / 20 : ℝ)) * T =
          savingCoeff *
            (T ^ (-(9 / 10 : ℝ)) * T ^ (-(9 / 20 : ℝ))) * T := by ring
      _ = savingCoeff * T ^ (-(9 / 10 : ℝ) + -(9 / 20 : ℝ)) * T := by
        rw [← Real.rpow_add hTpos]
      _ = savingCoeff * T ^ (-(9 / 10 : ℝ) + -(9 / 20 : ℝ)) *
          T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = savingCoeff * T ^ (-(9 / 10 : ℝ) + -(9 / 20 : ℝ) + 1) := by
        calc
          _ = savingCoeff *
              (T ^ (-(9 / 10 : ℝ) + -(9 / 20 : ℝ)) * T ^ (1 : ℝ)) := by ring
          _ = _ := by rw [← Real.rpow_add hTpos]
      _ = savingCoeff * T ^ (-(7 / 20 : ℝ)) := by
        congr 2
        ring
  have hsecond :
      widthEta T * Real.sqrt (widthEta T / savingCoeff) * T ≤ 1 := by
    rw [hsecond_id]
    have hpow : T ^ (-(7 / 20 : ℝ)) ≤ 1 :=
      by simpa using (Real.rpow_le_rpow_of_exponent_le hT
        (by norm_num : -(7 / 20 : ℝ) ≤ 0))
    calc
      savingCoeff * T ^ (-(7 / 20 : ℝ)) ≤
          1 * T ^ (-(7 / 20 : ℝ)) :=
        mul_le_mul_of_nonneg_right hc1 (Real.rpow_nonneg (by positivity) _)
      _ ≤ 1 := by simpa using hpow
  exact ⟨hpos, hhalf, hfirst, hsecond⟩

theorem commonEnvelope_width_le {R T : ℝ} (hR : 0 ≤ R) (hT : 1 ≤ T) :
    commonEnvelope R (Real.exp T) (widthEta T) ≤
      R + 273 * Real.exp 1 + 12 * Real.pi := by
  obtain ⟨hpos, hhalf, hfirst, hsecond⟩ := width_properties hT
  have hlog : Real.log (Real.exp T) = T := Real.log_exp T
  have hexp1 : Real.exp (1000 * widthEta T *
      (Real.log (Real.exp T)) ^ ((4 : ℝ) / 5)) ≤ Real.exp 1 := by
    rw [hlog]
    exact Real.exp_le_exp.mpr hfirst
  have hexp2 : Real.exp (widthEta T *
      Real.sqrt (widthEta T / savingCoeff) * Real.log (Real.exp T)) ≤
      Real.exp 1 := by
    rw [hlog]
    exact Real.exp_le_exp.mpr hsecond
  dsimp [commonEnvelope]
  calc
    R + Real.exp (1000 * widthEta T *
        (Real.log (Real.exp T)) ^ ((4 : ℝ) / 5)) +
        272 * Real.exp (widthEta T * Real.sqrt
          (widthEta T / savingCoeff) * Real.log (Real.exp T)) +
        12 * Real.pi ≤ R + Real.exp 1 + 272 * Real.exp 1 + 12 * Real.pi := by
      gcongr
    _ = R + 273 * Real.exp 1 + 12 * Real.pi := by ring

end FordGrowthWidth

#print axioms FordGrowthWidth.width_properties
#print axioms FordGrowthWidth.commonEnvelope_width_le
