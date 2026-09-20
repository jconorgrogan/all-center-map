import Mathlib

open Filter
noncomputable section
namespace FordEulerBoundaryDecay

/-- The finite Euler-cell boundary term decays on the half-plane `Re s > 1`. -/
theorem tendsto_cpow_one_sub_atTop_zero
    {a : ℝ} {s : ℂ} (ha : 0 < a) (hs : 1 < s.re) :
    Tendsto
      (fun K : ℕ =>
        ((a + (K : ℝ) : ℝ) : ℂ) ^ (1 - s))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hdelta : 0 < s.re - 1 := by linarith
  have hbase :
      Tendsto (fun K : ℕ => a + (K : ℝ)) atTop atTop := by
    simpa [add_comm] using
      (tendsto_atTop_add_const_right atTop a
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hpow :
      Tendsto (fun K : ℕ => (a + (K : ℝ)) ^ (-(s.re - 1)))
        atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hdelta).comp hbase
  refine hpow.congr' (Eventually.of_forall (fun K => ?_))
  have hpos : 0 < a + (K : ℝ) := by positivity
  change (a + (K : ℝ)) ^ (-(s.re - 1)) =
    ‖((a + (K : ℝ) : ℝ) : ℂ) ^ (1 - s)‖
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  congr 1
  simp only [Complex.sub_re, Complex.one_re]
  ring

end FordEulerBoundaryDecay

#print axioms FordEulerBoundaryDecay.tendsto_cpow_one_sub_atTop_zero
