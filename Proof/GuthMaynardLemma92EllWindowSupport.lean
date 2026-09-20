import GuthMaynardJIterationBumpWeld

open scoped Real ContDiff

noncomputable section
namespace GuthMaynardJIteration

/-- A literal finite `ell` window containing every nonzero sample
`sourceBump R hR ((M : ℝ) * ell / T)`.  The outer radius of `sourceBump` is
exactly `2 * R`, hence the coefficient `2` in this definition. -/
def sourceBumpEllRange (M : ℕ) (T R : ℝ) : Finset ℤ :=
  sourceIntegerWindow 0 (2 * R * T / (M : ℝ))

/-- The concrete source bump vanishes outside its exact support-driven finite
`ell` window.  This discharges the `hsupport` premise in the canonical
Lemma 9.2 producer without replacing compact support by a hypothesis. -/
theorem sourceBump_eq_zero_outside_sourceBumpEllRange
    {M : ℕ} (hM : 0 < M) {T R : ℝ} (hT : 0 < T) (hR : 0 < R)
    {ell : ℤ} (hell : ell ∉ sourceBumpEllRange M T R) :
    sourceBump R hR ((M : ℝ) * (ell : ℝ) / T) = 0 := by
  apply sourceBump_eq_zero_of_two_mul_le_abs
  have hMreal : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hellAbs : 2 * R * T / (M : ℝ) < |(ell : ℝ)| := by
    apply lt_of_not_ge
    intro hle
    exact hell (mem_sourceIntegerWindow_zero_of_abs_le hle)
  have hmul : 2 * R * T < |(ell : ℝ)| * (M : ℝ) :=
    (div_lt_iff₀ hMreal).mp hellAbs
  have hscaled : 2 * R < (M : ℝ) * |(ell : ℝ)| / T := by
    apply (lt_div_iff₀ hT).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have habs :
      |(M : ℝ) * (ell : ℝ) / T| = (M : ℝ) * |(ell : ℝ)| / T := by
    rw [abs_div, abs_mul, abs_of_pos hMreal, abs_of_pos hT]
  rw [habs]
  exact hscaled.le

/-- Function-valued form matching the exact `hsupport` binder of
`GuthMaynardJIteration.sigmaIIFinite_sourcePositiveDyadic_le_canonicalAffineJ_sqrt_add_time_neg100`. -/
theorem sourceBump_support_on_sourceBumpEllRange
    {M : ℕ} (hM : 0 < M) {T R : ℝ} (hT : 0 < T) (hR : 0 < R) :
    ∀ ell : ℤ, ell ∉ sourceBumpEllRange M T R →
      sourceBump R hR ((M : ℝ) * (ell : ℝ) / T) = 0 := by
  intro ell hell
  exact sourceBump_eq_zero_outside_sourceBumpEllRange hM hT hR hell

#print axioms GuthMaynardJIteration.sourceBump_eq_zero_outside_sourceBumpEllRange
#print axioms GuthMaynardJIteration.sourceBump_support_on_sourceBumpEllRange

end GuthMaynardJIteration
