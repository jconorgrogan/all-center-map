import GuthMaynardLemma295DualTail
import GuthMaynardLemma295MellinPolynomialDecay

/-!
# Arbitrary-order deep-left tail envelope for Lemma 29.5

This strengthens the fixed quadratic Mellin envelope in the initial tail
module to an arbitrary natural decay order, as required to integrate against
the polynomial growth of the functional-equation multiplier.
-/

namespace GuthMaynardLemma295DeepLeftTailPolynomial

open Complex Real
open GuthMaynardLemma295CutoffAnalytic
open GuthMaynardLemma295ThetaBounds
open GuthMaynardLemma295DualTail
open GuthMaynardLemma295MellinPolynomialDecay

noncomputable section

theorem norm_lemma295DeepLeftTailIntegrand_le_polynomial
    {N : ℝ} (hN : 0 < N) (g : ℝ) (K n k : ℕ) {t : ℝ}
    (htg : t ≠ g) (him : 2 ≤ |t - g|) :
    ‖lemma295DeepLeftTailIntegrand N g K n t‖ ≤
      (((1 + ‖((deepLeftSigma n : ℂ) + (t - g) * I)‖ + 2 * n) ^ 2) ^ n *
        (1152 * (1 + |t - g|) ^ 5)) *
      ((K + 1 : ℝ) ^ (deepLeftSigma n - 1) +
        (K + 1 : ℝ) ^ deepLeftSigma n / (-deepLeftSigma n)) *
      (Real.rpow N (deepLeftSigma n) *
        (sourceMellinDecayConstantAt (deepLeftSigma n) k /
          (1 + |t| ^ k))) := by
  let s : ℂ := (deepLeftSigma n : ℝ) + t * I
  let z : ℂ := s - g * I
  have hzform : z = (deepLeftSigma n : ℂ) + (t - g) * I := by
    dsimp [z, s]
    ring
  have hzre : z.re = deepLeftSigma n := by simp [z, s]
  have hzim : z.im = t - g := by simp [z, s]
  have hzneg : z.re < 0 := by
    rw [hzre]
    unfold deepLeftSigma
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hzne : z.im ≠ 0 := by
    rw [hzim]
    exact sub_ne_zero.mpr htg
  have hshiftLo : -2 ≤ (JutilaMultiplierRecurrence.shiftTwo z n).re := by
    simp [JutilaMultiplierRecurrence.shiftTwo, hzre, deepLeftSigma]
    norm_num
  have hshiftHi : (JutilaMultiplierRecurrence.shiftTwo z n).re ≤ 0 := by
    simp [JutilaMultiplierRecurrence.shiftTwo, hzre, deepLeftSigma]
  have htheta := norm_sourceZetaTheta_deepLeft_le hzne
    (by simpa [hzim] using him) n hshiftLo hshiftHi
  rw [hzform] at htheta
  have htheta' :
      ‖sourceZetaTheta z‖ ≤
        ((1 + ‖((deepLeftSigma n : ℂ) + (t - g) * I)‖ + 2 * n) ^ 2) ^ n *
          (1152 * (1 + |t - g|) ^ 5) := by
    simpa [hzform] using htheta
  have htail := norm_sourceDualTailNat_le hzneg K
  rw [hzre] at htail
  have hscale : ‖(N : ℂ) ^ (s - g * I)‖ =
      Real.rpow N (deepLeftSigma n) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN]
    simp [s, deepLeftSigma]
  have hmellin :=
    norm_mellin_sourceHZero_vertical_le_inv_one_add_abs_pow
      (deepLeftSigma n) k t
  have htailNonneg : 0 ≤
      (K + 1 : ℝ) ^ (deepLeftSigma n - 1) +
        (K + 1 : ℝ) ^ deepLeftSigma n / (-deepLeftSigma n) :=
    (norm_nonneg _).trans htail
  have hthetaNonneg : 0 ≤
      ((1 + ‖((deepLeftSigma n : ℂ) + (t - g) * I)‖ + 2 * n) ^ 2) ^ n *
        (1152 * (1 + |t - g|) ^ 5) :=
    (norm_nonneg _).trans htheta'
  have hscaleNonneg : 0 ≤ Real.rpow N (deepLeftSigma n) :=
    Real.rpow_nonneg hN.le _
  unfold lemma295DeepLeftTailIntegrand
  dsimp only
  repeat' rw [norm_mul]
  rw [hscale]
  calc
    ‖sourceZetaTheta z‖ * ‖sourceDualTailNat K z‖ *
        Real.rpow N (deepLeftSigma n) * ‖mellin sourceHZero s‖ ≤
      (((1 + ‖((deepLeftSigma n : ℂ) + (t - g) * I)‖ + 2 * n) ^ 2) ^ n *
        (1152 * (1 + |t - g|) ^ 5)) *
      ((K + 1 : ℝ) ^ (deepLeftSigma n - 1) +
        (K + 1 : ℝ) ^ deepLeftSigma n / (-deepLeftSigma n)) *
      Real.rpow N (deepLeftSigma n) * ‖mellin sourceHZero s‖ := by
        gcongr
    _ ≤ (((1 + ‖((deepLeftSigma n : ℂ) + (t - g) * I)‖ + 2 * n) ^ 2) ^ n *
        (1152 * (1 + |t - g|) ^ 5)) *
      ((K + 1 : ℝ) ^ (deepLeftSigma n - 1) +
        (K + 1 : ℝ) ^ deepLeftSigma n / (-deepLeftSigma n)) *
      (Real.rpow N (deepLeftSigma n) *
        (sourceMellinDecayConstantAt (deepLeftSigma n) k /
          (1 + |t| ^ k))) := by
      rw [mul_assoc]
      gcongr

end

end GuthMaynardLemma295DeepLeftTailPolynomial

#print axioms GuthMaynardLemma295DeepLeftTailPolynomial.norm_lemma295DeepLeftTailIntegrand_le_polynomial
