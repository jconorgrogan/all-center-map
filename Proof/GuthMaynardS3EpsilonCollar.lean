import GuthMaynardAffineSmoothingNorms

open scoped BigOperators Real FourierTransform
open MeasureTheory Filter

noncomputable section
namespace GuthMaynardS3EpsilonCollar

/-- Once `0 ≤ δ < 1` is fixed, a finite smoothing depth has a uniformly
small collar at sufficiently large time.  The depth is fixed before `T`. -/
theorem eventually_fixed_collar
    {delta : ℝ} (hdelta : 0 ≤ delta) (hdelta1 : delta < 1)
    (N : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      (7 : ℝ) ≤ T ∧ Real.rpow T delta ≤ T ∧
        (N : ℝ) * (2 * Real.rpow T delta / T) ≤ (1 : ℝ) / 4 := by
  have hgap : 0 < 1 - delta := by linarith
  have hpow := (tendsto_rpow_atTop hgap).eventually
    (eventually_ge_atTop (8 * (N : ℝ)))
  filter_upwards [hpow, eventually_ge_atTop (7 : ℝ)] with T hpow hT7
  have hT1 : 1 ≤ T := by linarith
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hTdelta : Real.rpow T delta ≤ T := by
    have h := Real.rpow_le_rpow_of_exponent_le hT1
      (show delta ≤ (1 : ℝ) by linarith)
    simpa only [Real.rpow_one] using h
  have hpow_nonneg : 0 ≤ Real.rpow T (1 - delta) :=
    Real.rpow_nonneg hTpos.le _
  have hdelta_nonneg : 0 ≤ Real.rpow T delta :=
    Real.rpow_nonneg hTpos.le _
  have hmul :
      8 * (N : ℝ) * Real.rpow T delta ≤
        Real.rpow T (1 - delta) * Real.rpow T delta := by
    exact mul_le_mul_of_nonneg_right hpow hdelta_nonneg
  have hpow_add :
      Real.rpow T (1 - delta) * Real.rpow T delta = T := by
    calc
      Real.rpow T (1 - delta) * Real.rpow T delta =
          Real.rpow T ((1 - delta) + delta) := by
        symm
        exact Real.rpow_add hTpos (1 - delta) delta
      _ = T := by ring_nf; simp
  have hmul' : 8 * (N : ℝ) * Real.rpow T delta ≤ T := by
    rw [hpow_add] at hmul
    exact hmul
  have hcollar :
      (N : ℝ) * (2 * Real.rpow T delta / T) ≤ (1 : ℝ) / 4 := by
    have hrewrite :
        (N : ℝ) * (2 * Real.rpow T delta / T) =
          (2 * (N : ℝ) * Real.rpow T delta) / T := by ring
    rw [hrewrite]
    apply (div_le_iff₀ hTpos).2
    nlinarith
  exact ⟨hT7, hTdelta, hcollar⟩

/-- A single epsilon chooses positive exponents and a finite depth before the
large-time limit.  The resulting collar and exponent budget are then uniform
for all sufficiently large `T`. -/
theorem exists_epsilon_collar_parameters
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ eta delta : ℝ, ∃ N : ℕ,
      0 < eta ∧ eta ≤ 1 ∧ 0 < delta ∧ delta < 1 ∧
      8 * eta + 2 * delta + 2 / (2 : ℝ) ^ N < epsilon ∧
      ∀ᶠ T : ℝ in atTop,
        (7 : ℝ) ≤ T ∧ Real.rpow T delta ≤ T ∧
          (N : ℝ) * (2 * Real.rpow T delta / T) ≤ (1 : ℝ) / 4 := by
  let a : ℝ := epsilon / (100 + epsilon)
  have hden : 0 < 100 + epsilon := by linarith
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    apply (div_le_iff₀ hden).2
    linarith
  obtain ⟨N, hN⟩ :=
    pow_unbounded_of_one_lt (4 / epsilon)
      (by norm_num : (1 : ℝ) < 2)
  have hpow : 4 / epsilon < (2 : ℝ) ^ N := hN
  have hpowpos : 0 < (2 : ℝ) ^ N := by positivity
  have hterm : 2 / (2 : ℝ) ^ N < epsilon / 2 := by
    apply (div_lt_iff₀ hpowpos).2
    have hmul : 4 < epsilon * (2 : ℝ) ^ N := by
      have h := (div_lt_iff₀ hepsilon).mp hpow
      simpa [mul_comm] using h
    nlinarith
  have haeps : 10 * a < epsilon / 2 := by
    dsimp [a]
    rw [show 10 * (epsilon / (100 + epsilon)) =
      (10 * epsilon) / (100 + epsilon) by ring]
    apply (div_lt_iff₀ hden).2
    nlinarith
  refine ⟨a, a, N, ha, ha1, ha, ?_, ?_, ?_⟩
  · dsimp [a]
    apply (div_lt_iff₀ hden).2
    nlinarith
  · nlinarith
  · exact eventually_fixed_collar (le_of_lt ha) (by
      dsimp [a]
      apply (div_lt_iff₀ hden).2
      nlinarith) N

end GuthMaynardS3EpsilonCollar

#print axioms GuthMaynardS3EpsilonCollar.eventually_fixed_collar
#print axioms GuthMaynardS3EpsilonCollar.exists_epsilon_collar_parameters
