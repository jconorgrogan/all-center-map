import GuthMaynardLemma295CutoffAnalytic
import JutilaMultiplierBaseStrip

/-!
# The archimedean multiplier on the deep-left line in Lemma 29.5

This file specializes the already-certified two-step `Gammaℝ` recurrence and
base-strip estimate to the Riemann-zeta multiplier `sourceZetaTheta`.  It is the
finite algebraic content behind the source's appeal to Stirling on
`Re z = 5/2-j`.
-/

namespace GuthMaynardLemma295ThetaBounds

open Complex
open GuthMaynardLemma295CutoffAnalytic
open JutilaMultiplierRecurrence

noncomputable section

/-- Exact two-step recurrence for the source multiplier. -/
theorem sourceZetaTheta_shift_two (z : ℂ) (hz : z.im ≠ 0) :
    sourceZetaTheta z =
      ((-1 - z) * z / ((2 : ℂ) * Real.pi) ^ 2) *
        sourceZetaTheta (z + 2) := by
  exact even_gammaQuotient_shift_two z hz

/-- Exact finite iteration of the two-step recurrence. -/
theorem norm_sourceZetaTheta_eq_evenStepProduct
    (z : ℂ) (hz : z.im ≠ 0) (n : ℕ) :
    ‖sourceZetaTheta z‖ =
      evenStepProduct 1 z n * ‖sourceZetaTheta (shiftTwo z n)‖ := by
  induction n with
  | zero => simp [evenStepProduct, shiftTwo]
  | succ n ih =>
      have hzim : (shiftTwo z n).im ≠ 0 := by
        rw [shiftTwo_im]
        exact hz
      have hstep := sourceZetaTheta_shift_two (shiftTwo z n) hzim
      rw [ih, hstep, norm_mul]
      simp only [evenStepProduct, Finset.prod_range_succ, evenStep,
        shiftTwo_succ, one_pow, Nat.cast_one, one_mul]
      ring

/-- On the terminal strip the source multiplier has a uniform polynomial
bound.  This is the conductor-one even case of the certified Gamma quotient
estimate, stated without a character wrapper. -/
theorem norm_sourceZetaTheta_baseStrip_le
    {z : ℂ} (hzlo : -2 ≤ z.re) (hzhi : z.re ≤ 0)
    (hzim : 2 ≤ |z.im|) :
    ‖sourceZetaTheta z‖ ≤ 1152 * (1 + |z.im|) ^ 5 := by
  have h := JutilaMultiplierBaseStrip.gammaFactor_quotient_baseStrip_le
    (1 : DirichletCharacter ℂ 1) hzlo hzhi hzim
  have heven : (1 : DirichletCharacter ℂ 1).Even := by
    rw [DirichletCharacter.Even]
    have hm : (-1 : ZMod 1) = 1 := Subsingleton.elim _ _
    rw [hm, map_one]
  have hinv : ((1 : DirichletCharacter ℂ 1)⁻¹).Even := by
    rw [DirichletCharacter.Even]
    have hm : (-1 : ZMod 1) = 1 := Subsingleton.elim _ _
    rw [hm, map_one]
  simpa [sourceZetaTheta, hinv.gammaFactor_def, heven.gammaFactor_def] using h

/-- The functional-equation multiplier has exactly unit norm on the
critical line, as used when the truncated dual polynomial is moved back to
`Re s = 1/2`. -/
theorem norm_sourceZetaTheta_criticalLine_eq_one (u : ℝ) :
    ‖sourceZetaTheta (((1 / 2 : ℝ) : ℂ) + u * Complex.I)‖ = 1 := by
  have h :=
    JutilaCriticalPartialTruncation.norm_gammaFactor_quotient_criticalPoint_eq_one
      (1 : DirichletCharacter ℂ 1) u
  have heven : (1 : DirichletCharacter ℂ 1).Even := by
    rw [DirichletCharacter.Even]
    have hm : (-1 : ZMod 1) = 1 := Subsingleton.elim _ _
    rw [hm, map_one]
  have hinv : ((1 : DirichletCharacter ℂ 1)⁻¹).Even := by
    rw [DirichletCharacter.Even]
    have hm : (-1 : ZMod 1) = 1 := Subsingleton.elim _ _
    rw [hm, map_one]
  simpa [sourceZetaTheta, JutilaCriticalPartialTruncation.criticalPoint,
    hinv.gammaFactor_def, heven.gammaFactor_def] using h

/-- Quantitative deep-left bound after any finite number of two-step shifts,
provided the terminal point lies in the certified base strip. -/
theorem norm_sourceZetaTheta_deepLeft_le
    {z : ℂ} (hz : z.im ≠ 0) (hzim : 2 ≤ |z.im|) (n : ℕ)
    (hlo : -2 ≤ (shiftTwo z n).re) (hhi : (shiftTwo z n).re ≤ 0) :
    ‖sourceZetaTheta z‖ ≤
      ((1 + ‖z‖ + 2 * n) ^ 2) ^ n *
        (1152 * (1 + |z.im|) ^ 5) := by
  rw [norm_sourceZetaTheta_eq_evenStepProduct z hz n]
  have hp := evenStepProduct_le 1 z n
  simp only [Nat.cast_one, one_pow, one_mul] at hp
  have hzim' : 2 ≤ |(shiftTwo z n).im| := by simpa [shiftTwo_im] using hzim
  have hb := norm_sourceZetaTheta_baseStrip_le hlo hhi hzim'
  rw [shiftTwo_im] at hb
  exact mul_le_mul hp hb (norm_nonneg _) (by positivity)

end
end GuthMaynardLemma295ThetaBounds

#print axioms GuthMaynardLemma295ThetaBounds.sourceZetaTheta_shift_two
#print axioms GuthMaynardLemma295ThetaBounds.norm_sourceZetaTheta_baseStrip_le
#print axioms GuthMaynardLemma295ThetaBounds.norm_sourceZetaTheta_criticalLine_eq_one
#print axioms GuthMaynardLemma295ThetaBounds.norm_sourceZetaTheta_deepLeft_le
