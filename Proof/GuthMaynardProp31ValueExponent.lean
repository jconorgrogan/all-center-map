import GuthMaynardS3Assembly

set_option maxHeartbeats 400000

namespace GuthMaynardProp31ValueExponent
noncomputable section

/-- Canonical logarithmic exponent for a value in the Prop. 3.1 window. -/
def valueExponent (N V : ℝ) : ℝ := Real.log V / Real.log N

/-- Every legal value `V` in the Prop. 3.1 window has an exact power
representation with exponent in `[7/10,4/5]`. -/
theorem valueExponent_spec
    {N V : ℝ} (hN : 1 < N) (hV : 0 < V)
    (hlo : Real.rpow N (7 / 10 : ℝ) ≤ V)
    (hhi : V ≤ Real.rpow N (4 / 5 : ℝ)) :
    (7 / 10 : ℝ) ≤ valueExponent N V ∧
      valueExponent N V ≤ (4 / 5 : ℝ) ∧
      V = Real.rpow N (valueExponent N V) := by
  have hNpos : 0 < N := lt_trans zero_lt_one hN
  have hlogN : 0 < Real.log N := Real.log_pos hN
  have hloglo : Real.log (Real.rpow N (7 / 10 : ℝ)) ≤ Real.log V :=
    Real.log_le_log (Real.rpow_pos_of_pos hNpos _) hlo
  have hloghi : Real.log V ≤ Real.log (Real.rpow N (4 / 5 : ℝ)) :=
    Real.log_le_log hV hhi
  have hloglo' : Real.log (Real.rpow N (7 / 10 : ℝ)) =
      (7 / 10 : ℝ) * Real.log N :=
    Real.log_rpow hNpos _
  have hloghi' : Real.log (Real.rpow N (4 / 5 : ℝ)) =
      (4 / 5 : ℝ) * Real.log N :=
    Real.log_rpow hNpos _
  have hloσ : (7 / 10 : ℝ) ≤ valueExponent N V := by
    apply (le_div_iff₀ hlogN).2
    rw [hloglo'] at hloglo
    exact hloglo
  have hhiσ : valueExponent N V ≤ (4 / 5 : ℝ) := by
    apply (div_le_iff₀ hlogN).2
    rw [hloghi'] at hloghi
    exact hloghi
  have hrepr : V = Real.rpow N (valueExponent N V) := by
    calc
      V = Real.exp (Real.log V) := (Real.exp_log hV).symm
      _ = Real.exp (valueExponent N V * Real.log N) := by
        congr 1
        dsimp [valueExponent]
        field_simp
      _ = Real.rpow N (valueExponent N V) := by
        convert (Real.rpow_def_of_pos hNpos (valueExponent N V)).symm using 1 <;> ring
  exact ⟨hloσ, hhiσ, hrepr⟩

end
end GuthMaynardProp31ValueExponent

#print axioms GuthMaynardProp31ValueExponent.valueExponent_spec
