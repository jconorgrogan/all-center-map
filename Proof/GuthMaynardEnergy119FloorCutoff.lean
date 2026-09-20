import GuthMaynardEnergy119GCDWeights

noncomputable section
namespace GuthMaynardEnergy119FloorCutoff

/-- The natural floor cutoff loses at most a factor two in the reciprocal
tail budget, including the interval 1 ≤ N²/T < 2. -/
theorem floor_cutoff_bounds {N T : ℝ} (hT : 0 < T) (hscale : T ≤ N^2) :
    let D := Nat.floor (N^2/T)
    1 ≤ D ∧ (D : ℝ)⁻¹ ≤ 2*T/N^2 := by
  dsimp
  let x : ℝ := N^2/T
  have hx : 1 ≤ x := by
    dsimp [x]
    exact (le_div_iff₀ hT).mpr (by simpa using hscale)
  have hx0 : 0 ≤ x := by linarith
  have hD : 1 ≤ Nat.floor x := (Nat.le_floor_iff hx0).mpr (by simpa using hx)
  have hDreal : (1 : ℝ) ≤ Nat.floor x := by exact_mod_cast hD
  have hxlt : x < (Nat.floor x : ℝ)+1 := Nat.lt_floor_add_one x
  have hhalf : x ≤ 2*(Nat.floor x : ℝ) := by linarith
  have hDpos : (0 : ℝ) < Nat.floor x := by linarith
  have hxpos : 0 < x := by linarith
  refine ⟨hD,?_⟩
  have hinv : (Nat.floor x : ℝ)⁻¹ ≤ 2/x := by
    apply (le_div_iff₀ hxpos).mpr
    apply (inv_mul_le_iff₀ hDpos).mpr
    simpa only [mul_comm] using hhalf
  calc
    (Nat.floor (N^2/T) : ℝ)⁻¹ ≤ 2/x := hinv
    _ = 2*T/N^2 := by dsimp [x]; field_simp

theorem square_scale_of_three_quarters {N T : ℝ}
    (hT : 1 ≤ T) (hN : Real.rpow T (3/4 : ℝ) ≤ N) : T ≤ N^2 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hpow0 : 0 ≤ Real.rpow T (3/4 : ℝ) := Real.rpow_nonneg hTpos.le _
  have hN0 : 0 ≤ N := hpow0.trans hN
  have hsq := (sq_le_sq₀ hpow0 hN0).mpr hN
  have hid : (Real.rpow T (3/4 : ℝ))^2 = Real.rpow T (3/2 : ℝ) := by
    calc
      _ = Real.rpow T ((3/4 : ℝ)*(2 : ℕ)) :=
        (Real.rpow_mul_natCast hTpos.le (3/4 : ℝ) 2).symm
      _ = _ := by norm_num
  rw [hid] at hsq
  have hh := Real.rpow_le_rpow_of_exponent_le hT (by norm_num : (1 : ℝ) ≤ 3/2)
  rw [Real.rpow_one] at hh
  exact hh.trans hsq

end GuthMaynardEnergy119FloorCutoff
#print axioms GuthMaynardEnergy119FloorCutoff.floor_cutoff_bounds
#print axioms GuthMaynardEnergy119FloorCutoff.square_scale_of_three_quarters
