import JutilaRightEdgeLogBoundComplete
import JutilaGammaZeroShift

/-!
# Exact primitive zero-line boundary for Rademacher convexity

The functional equation is paired with the now-certified logarithmic bound
on `Re s = 1`.  This is the left boundary for a Gaussian-damped three-lines
argument; no epsilon-dependent constant appears here.
-/

namespace MAPBHPRademacherZeroBoundary

open Complex
open MAPJutilaRightEdgeLogBound
open MAPJutilaRightEdgeLogBoundComplete
open MAPJutilaGammaZeroShift

noncomputable section

/-- Inversion preserves nonprincipality. -/
theorem inv_ne_one {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) : chi⁻¹ ≠ 1 := by
  intro h
  apply hchi
  have := congrArg (fun z : DirichletCharacter ℂ q => z⁻¹) h
  simpa using this

/-- Exact primitive left boundary at `Re s = 0`, with the logarithm and
cutoff exposed rather than hidden in `q^epsilon`. -/
theorem norm_LFunction_imaginary_le_logarithmic
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1) (t : ℝ) :
    let K := q * Nat.ceil (1 + |t|)
    ‖DirichletCharacter.LFunction chi ((t : ℂ) * I)‖ ≤
      (4 + Real.log (K : ℝ)) *
        Real.rpow (q : ℝ) (1 / 2) *
          Real.rpow (1 + |t|) (1 / 2) := by
  dsimp only
  let K : ℕ := q * Nat.ceil (1 + |t|)
  let B : ℝ := 4 + Real.log (K : ℝ)
  have hK : 1 ≤ K := by
    dsimp [K]
    have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hc : 1 ≤ Nat.ceil (1 + |t|) := by
      apply Nat.one_le_iff_ne_zero.mpr
      exact ne_of_gt (Nat.ceil_pos.mpr (by positivity))
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (NeZero.ne q) (Nat.ne_of_gt hc))
  have hB0 : 0 ≤ B := by
    dsimp [B]
    have : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg (by exact_mod_cast hK)
    linarith
  have hright := norm_LFunction_rightBoundary_le chi⁻¹
    (inv_ne_one chi hchi) t
  change ‖DirichletCharacter.LFunction chi⁻¹
      (rightBoundaryPoint t)‖ ≤ B at hright
  exact norm_LFunction_imaginary_le_of_rightEdge chi hprim hchi t B hB0 hright

/-- Cleaner zero-line form obtained from the complete-block right boundary.
Unlike the cutoff form above, this matches the conductor-height scale used by
the Gaussian interpolation without a ceiling conversion. -/
theorem norm_LFunction_imaginary_le_clean
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1) (t : ℝ) :
    ‖DirichletCharacter.LFunction chi ((t : ℂ) * I)‖ ≤
      3 * (1 + Real.log (2 * (q : ℝ) * (3 + |t|))) *
        Real.rpow (q : ℝ) (1 / 2) *
          Real.rpow (1 + |t|) (1 / 2) := by
  let B : ℝ := 3 * (1 + Real.log (2 * (q : ℝ) * (3 + |t|)))
  have hqnat : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast hqnat
  have hscale : 1 ≤ 2 * (q : ℝ) * (3 + |t|) := by
    nlinarith [abs_nonneg t]
  have hB0 : 0 ≤ B := by
    dsimp [B]
    have hlog : 0 ≤ Real.log (2 * (q : ℝ) * (3 + |t|)) :=
      Real.log_nonneg hscale
    positivity
  have hright := nonprincipal_norm_LFunction_rightBoundary_le chi⁻¹
    (inv_ne_one chi hchi) t
  change ‖DirichletCharacter.LFunction chi⁻¹
      (rightBoundaryPoint t)‖ ≤ B at hright
  exact norm_LFunction_imaginary_le_of_rightEdge chi hprim hchi t B hB0 hright

end
end MAPBHPRademacherZeroBoundary

#print axioms MAPBHPRademacherZeroBoundary.norm_LFunction_imaginary_le_logarithmic
#print axioms MAPBHPRademacherZeroBoundary.norm_LFunction_imaginary_le_clean
