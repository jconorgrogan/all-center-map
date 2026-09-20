import FordUnitPhaseLipschitz
import FordMixedReciprocalIntegral

open scoped ComplexConjugate
noncomputable section

namespace FordPhaseDifferencing

open FordUnitPhaseLipschitz
open FordMixedReciprocalIntegral

/-- Recursive multiplicative differencing of a unit-modulus phase sequence. -/
def phaseDiff : List ℝ → (ℝ → ℝ) → ℝ → ℂ
  | [], f, x => unitPhase (f x)
  | h :: hs, f, x => phaseDiff hs f (x + h) * conj (phaseDiff hs f x)

lemma unitPhase_sub (u v : ℝ) :
    unitPhase u * conj (unitPhase v) = unitPhase (u - v) := by
  unfold unitPhase
  rw [← Complex.exp_conj]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- Multiplicative phase differencing is exactly the unit phase of the
corresponding recursive additive mixed difference. -/
theorem phaseDiff_eq_unitPhase
    (hs : List ℝ) (f : ℝ → ℝ) (x : ℝ) :
    phaseDiff hs f x = unitPhase (mixedDiff hs f x) := by
  induction hs generalizing f x with
  | nil => rfl
  | cons h hs ih =>
      rw [phaseDiff, mixedDiff]
      rw [ih, ih]
      exact unitPhase_sub _ _

/-- Every recursively differenced unit phase still has norm one. -/
theorem phaseDiff_norm
    (hs : List ℝ) (f : ℝ → ℝ) (x : ℝ) :
    ‖phaseDiff hs f x‖ = 1 := by
  rw [phaseDiff_eq_unitPhase]
  exact unitPhase_norm _

end FordPhaseDifferencing

#print axioms FordPhaseDifferencing.phaseDiff_eq_unitPhase
#print axioms FordPhaseDifferencing.phaseDiff_norm
