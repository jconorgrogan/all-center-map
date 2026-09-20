import GuthMaynardJIterationDeterministic

open scoped Real
noncomputable section
namespace GuthMaynardS3EnergyNormalization

/-- Exact normalization of the degree-six / square-root energy step. The
normalizer dominates both initial norm terms; the additive remainder is kept
explicit rather than silently discarded. -/
theorem normalized_energy_step
    {m D L Q E E' a b c r : ℝ}
    (hm : 0 < m) (hD : 0 < D) (hQ : 0 ≤ Q) (hE' : 0 ≤ E')
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hL : m^2*L^2 ≤ D) (hQD : Q ≤ D)
    (hr : r ≤ c*(m^4*D))
    (hstep : E ≤ a*m^6*L^2 + b*m^2*Real.sqrt (Q*E') + r) :
    E/(m^4*D) ≤ a+c+b*Real.sqrt (E'/(m^4*D)) := by
  have hm4 : 0 < m^4 := by positivity
  have hn : 0 < m^4*D := mul_pos hm4 hD
  have hX : 0 ≤ E'/(m^4*D) := div_nonneg hE' hn.le
  have hroot : m^2*Real.sqrt (Q*E') ≤
      (m^4*D)*Real.sqrt (E'/(m^4*D)) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).1
    rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hQ hE'), Real.sq_sqrt hX]
    have hmul := mul_le_mul_of_nonneg_right hQD hE'
    have hn0 : m^4*D ≠ 0 := hn.ne'
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hmul hm4.le]
  have hlead : a*m^6*L^2 ≤ a*(m^4*D) := by
    have hh := mul_le_mul_of_nonneg_left hL (mul_nonneg ha hm4.le)
    nlinarith
  have hmid := mul_le_mul_of_nonneg_left hroot hb
  apply (div_le_iff₀ hn).2
  calc
    E ≤ a*m^6*L^2 + b*m^2*Real.sqrt (Q*E') + r := hstep
    _ ≤ a*(m^4*D) + b*((m^4*D)*Real.sqrt (E'/(m^4*D))) +
        c*(m^4*D) := by nlinarith
    _ = (a+c+b*Real.sqrt (E'/(m^4*D)))*(m^4*D) := by ring

end GuthMaynardS3EnergyNormalization
#print axioms GuthMaynardS3EnergyNormalization.normalized_energy_step
