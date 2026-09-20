import FordLogTaylor
import FordUnitPhaseLipschitz
import FordSourceWeakBilinear

open scoped BigOperators
noncomputable section

namespace FordLogPhaseTaylor

open FordLogTaylor FordUnitPhaseLipschitz FordPolynomialPhase
open FordSourceWeakBilinear

/-- The logarithmic Taylor correction written in the `e(·)` frequency convention. -/
def phaseTaylor (k : ℕ) (t z h : ℝ) : ℝ :=
  ∑ j ∈ Finset.range k,
    ((-1 : ℝ) ^ (j + 1) * t /
      (2 * Real.pi * (j + 1) * z ^ (j + 1))) * h ^ (j + 1)

lemma phaseTaylor_fin (k : ℕ) (t z h : ℝ) :
    phaseTaylor k t z h =
      ∑ j : Fin k, sourceGamma t z j.val * h ^ (j.val + 1) := by
  unfold phaseTaylor
  simpa [sourceGamma] using
    (Fin.sum_univ_eq_sum_range
      (fun j : ℕ => sourceGamma t z j * h ^ (j + 1)) k).symm

lemma phaseTaylor_eq (k : ℕ) (t z h : ℝ) :
    phaseTaylor k t z h =
      (-t / (2 * Real.pi)) * FordLogTaylor.logTaylor k (h / z) := by
  unfold phaseTaylor FordLogTaylor.logTaylor
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring_nf
  field_simp
  ring

/-- A Taylor approximation for the shifted logarithmic phase, valid at every
nonnegative increment `h` (there is no restriction `h/z ≤ 1`). -/
theorem shifted_log_phase_bound {k : ℕ} {t z h : ℝ}
    (ht : 0 ≤ t) (hz : 0 < z) (hh : 0 ≤ h) :
    ‖unitPhase (-t * Real.log (z + h)) -
        unitPhase (-t * Real.log z) *
          FordPolynomialPhase.e (phaseTaylor k t z h)‖ ≤
      t * (h / z) ^ (k + 1) / (k + 1) := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hratio : 0 ≤ h / z := div_nonneg hh (le_of_lt hz)
  have hfac : z + h = z * (1 + h / z) := by
    field_simp
  have hlogadd : Real.log (z + h) = Real.log z + Real.log (1 + h / z) := by
    rw [hfac, Real.log_mul hz.ne' (by positivity)]
  have hrem := FordLogTaylor.log_taylor_remainder hratio (k := k)
  have hphase :
      unitPhase (-t * Real.log z) * FordPolynomialPhase.e (phaseTaylor k t z h) =
        unitPhase (-t * Real.log (z + h) -
          (-t * Real.log (1 + h / z) + t * FordLogTaylor.logTaylor k (h / z))) := by
    rw [hlogadd]
    rw [phaseTaylor_eq]
    unfold unitPhase FordPolynomialPhase.e
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
    field_simp [Real.pi_ne_zero]
  rw [hphase]
  have hunit := FordUnitPhaseLipschitz.unitPhase_sub_norm_le
    (-t * Real.log (z + h))
    (-t * Real.log (z + h) -
      (-t * Real.log (1 + h / z) + t * FordLogTaylor.logTaylor k (h / z)))
  calc
    _ ≤ |(-t * Real.log (z + h)) -
        (-t * Real.log (z + h) -
          (-t * Real.log (1 + h / z) + t * FordLogTaylor.logTaylor k (h / z)))| := hunit
    _ = t * |Real.log (1 + h / z) - FordLogTaylor.logTaylor k (h / z)| := by
      rw [show -t * Real.log (z + h) -
          (-t * Real.log (z + h) - (-t * Real.log (1 + h / z) +
            t * FordLogTaylor.logTaylor k (h / z))) =
          (-t) * (Real.log (1 + h / z) - FordLogTaylor.logTaylor k (h / z)) by ring]
      rw [abs_mul]
      simp [abs_of_nonneg ht]
    _ ≤ t * ((h / z) ^ (k + 1) / (k + 1)) := by
      exact mul_le_mul_of_nonneg_left hrem ht
    _ = t * (h / z) ^ (k + 1) / (k + 1) := by ring

end FordLogPhaseTaylor

#print axioms FordLogPhaseTaylor.shifted_log_phase_bound

namespace FordLogPhaseTaylor

open FordUnitPhaseLipschitz FordSourceWeakBilinear

/-- The same bound with the source coefficient convention used by the Ford
moment interfaces. -/
theorem shifted_log_phase_bound_source {k : ℕ} {t z h : ℝ}
    (ht : 0 ≤ t) (hz : 0 < z) (hh : 0 ≤ h) :
    ‖unitPhase (-t * Real.log (z + h)) -
        unitPhase (-t * Real.log z) *
          FordPolynomialPhase.e
            (∑ j : Fin k, sourceGamma t z j.val * h ^ (j.val + 1))‖ ≤
      t * (h / z) ^ (k + 1) / (k + 1) := by
  rw [← phaseTaylor_fin]
  exact shifted_log_phase_bound ht hz hh

end FordLogPhaseTaylor

#print axioms FordLogPhaseTaylor.shifted_log_phase_bound_source
