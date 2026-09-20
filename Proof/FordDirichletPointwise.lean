import Mathlib

open scoped BigOperators

namespace FordDirichletPointwise

noncomputable section

private def phase (x : ℝ) : ℂ := Complex.exp (Complex.I * (2 * Real.pi * x))

def dirichletSum (L : ℕ) (x : ℝ) : ℂ :=
  ∑ c ∈ Finset.range L,
    Complex.exp (Complex.I * (2 * Real.pi * ((c + 1 : ℕ) : ℝ) * x))

lemma norm_phase (x : ℝ) : ‖phase x‖ = 1 := by
  simp [phase, Complex.norm_exp]

lemma dirichletSum_norm_le (L : ℕ) (x : ℝ) :
    ‖dirichletSum L x‖ ≤ L := by
  unfold dirichletSum
  calc
    ‖∑ c ∈ Finset.range L,
        Complex.exp (Complex.I * (2 * Real.pi * ((c + 1 : ℕ) : ℝ) * x))‖ ≤
        ∑ c ∈ Finset.range L,
          ‖Complex.exp (Complex.I * (2 * Real.pi * ((c + 1 : ℕ) : ℝ) * x))‖ :=
      norm_sum_le _ _
    _ = L := by
      simp [Complex.norm_exp, Finset.card_range]

lemma dirichletSum_eq_phase_mul_geom (L : ℕ) (x : ℝ) :
    dirichletSum L x = phase x * ∑ c ∈ Finset.range L, (phase x) ^ c := by
  unfold dirichletSum phase
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma phase_ne_one_of_sub_round_ne_zero {x : ℝ}
    (h : x - (round x : ℝ) ≠ 0) : phase x ≠ 1 := by
  intro hp
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hp
  have him := congrArg Complex.im hn
  simp at him
  have hx : x = (n : ℝ) := by nlinarith [Real.pi_pos]
  have hd := abs_sub_round (n : ℝ)
  have hzero : (n : ℝ) - (round (n : ℝ) : ℝ) = 0 := by
    by_contra hne
    have hcast : n - round (n : ℝ) ≠ 0 := by exact_mod_cast hne
    have hz : (1 : ℝ) ≤ |((n - round (n : ℝ) : ℤ) : ℝ)| := by
      exact_mod_cast (Int.one_le_abs hcast)
    have hz' : (1 : ℝ) ≤ |(n : ℝ) - (round (n : ℝ) : ℝ)| := by
      simpa [Int.cast_sub] using hz
    linarith
  exact h (by simpa [hx] using hzero)

private lemma abs_sin_pi_mul_eq_round_distance {x : ℝ} :
    |Real.sin (Real.pi * x)| =
      |Real.sin (Real.pi * (x - (round x : ℝ)))| := by
  have heq : Real.pi * x =
      Real.pi * (x - (round x : ℝ)) + (round x : ℤ) * Real.pi := by ring
  rw [heq, Real.sin_add_int_mul_pi]
  simp [abs_mul]

private lemma abs_sin_pi_mul_ge_round_distance {x : ℝ} :
    2 * |x - (round x : ℝ)| ≤ |Real.sin (Real.pi * x)| := by
  rw [abs_sin_pi_mul_eq_round_distance]
  have hd := abs_sub_round x
  have hpi : 0 < Real.pi := Real.pi_pos
  have harg : |Real.pi * (x - (round x : ℝ))| ≤ Real.pi / 2 := by
    rw [abs_mul]
    rw [abs_of_pos hpi]
    nlinarith [hd]
  have hs := Real.mul_abs_le_abs_sin harg
  have harg' : (2 / Real.pi) *
      |Real.pi * (x - (round x : ℝ))| = 2 *
        |x - (round x : ℝ)| := by
    rw [abs_mul]
    rw [abs_of_pos hpi]
    field_simp [ne_of_gt hpi]
  rw [harg'] at hs
  exact hs

theorem dirichletSum_norm_le_reciprocal
    {L : ℕ} {x : ℝ} (h : x - (round x : ℝ) ≠ 0) :
    ‖dirichletSum L x‖ ≤ 1 / (2 * |x - (round x : ℝ)|) := by
  have hphase : phase x ≠ 1 := phase_ne_one_of_sub_round_ne_zero h
  have hdist : 0 < |x - (round x : ℝ)| := abs_pos.mpr h
  have hden : 4 * |x - (round x : ℝ)| ≤ ‖phase x - 1‖ := by
    have he := Complex.norm_exp_I_mul_ofReal_sub_one (2 * Real.pi * x)
    rw [show 2 * Real.pi * x / 2 = Real.pi * x by ring] at he
    have he' : ‖phase x - 1‖ = |2 * Real.sin (Real.pi * x)| := by
      simpa [phase, mul_assoc, mul_left_comm, mul_comm] using he
    rw [he']
    have hs := abs_sin_pi_mul_ge_round_distance (x := x)
    have hs' : 4 * |x - (round x : ℝ)| ≤
        2 * |Real.sin (Real.pi * x)| := by nlinarith [hs]
    simpa [abs_mul] using hs'
  have hnum : ‖phase x ^ L - 1‖ ≤ 2 := by
    calc
      ‖phase x ^ L - 1‖ ≤ ‖phase x ^ L‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp [norm_phase]; norm_num
  rw [dirichletSum_eq_phase_mul_geom, geom_sum_eq hphase]
  rw [norm_mul, norm_div]
  have hdenpos : 0 < ‖phase x - 1‖ := lt_of_lt_of_le (by positivity) hden
  have hfrac : ‖phase x ^ L - 1‖ / ‖phase x - 1‖ ≤
      2 / (4 * |x - (round x : ℝ)|) := by
    gcongr
  calc
    ‖phase x‖ * (‖phase x ^ L - 1‖ / ‖phase x - 1‖) ≤
        1 * (2 / (4 * |x - (round x : ℝ)|)) := by
          gcongr
          exact (norm_phase x).le
    _ = 1 / (2 * |x - (round x : ℝ)|) := by ring

#print axioms FordDirichletPointwise.dirichletSum_norm_le
#print axioms FordDirichletPointwise.dirichletSum_norm_le_reciprocal

end
end FordDirichletPointwise
