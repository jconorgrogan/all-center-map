import GuthMaynardLemma295ThetaHorizontal
import GuthMaynardLemma295MellinPolynomialDecay
import GuthMaynardLemma295ReflectedFiniteContour

/-!
# Pointwise horizontal decay for the finite reflected integrand

This file records the elementary finite-prefix and positive-base power bounds
needed on the horizontal sides of the second Lemma 29.5 rectangle.  It also
isolates the remaining compact-strip uniformity issue from the already proved
fixed-line Mellin decay.
-/

namespace GuthMaynardLemma295HorizontalPointwise

open Complex Real Set Filter Topology
open GuthMaynardLemma295CutoffAnalytic
open GuthMaynardLemma295DualTail
open GuthMaynardLemma295ThetaHorizontal
open GuthMaynardLemma295MellinPolynomialDecay
open GuthMaynardLemma295ReflectedFiniteContour

noncomputable section

/-- Every term of the finite reflected zeta prefix has norm at most one to the
left of the critical line. -/
theorem norm_sourceDualPartialNat_le_card
    (K : ℕ) {z : ℂ} (hz : z.re ≤ 1 / 2) :
    ‖sourceDualPartialNat K z‖ ≤ K := by
  unfold sourceDualPartialNat
  calc
    ‖∑ m ∈ Finset.range K,
        1 / ((m + 1 : ℕ) : ℂ) ^ (1 - z)‖ ≤
      ∑ m ∈ Finset.range K,
        ‖1 / ((m + 1 : ℕ) : ℂ) ^ (1 - z)‖ :=
          norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.range K, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      have hmpos : 0 < m + 1 := by omega
      rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hmpos]
      have hbase : (1 : ℝ) ≤ m + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
      have hexp : 0 ≤ 1 - z.re := by linarith
      have hpow : 1 ≤ Real.rpow (m + 1 : ℝ) (1 - z.re) :=
        Real.one_le_rpow hbase hexp
      simp only [sub_re, one_re]
      norm_cast
      rw [show ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 by norm_num]
      have hpos : 0 < Real.rpow ((m : ℝ) + 1) (1 - z.re) :=
        Real.rpow_pos_of_pos (by positivity) _
      exact (div_le_one hpos).2 hpow
    _ = K := by simp

/-- The positive-base scale factor is bounded by its endpoint powers on a
closed horizontal segment. -/
theorem norm_positiveScale_horizontal_le_max
    {N a b x t : ℝ} (hN : 0 < N) (hax : a ≤ x) (hxb : x ≤ b) :
    ‖(N : ℂ) ^ ((x : ℂ) + t * I)‖ ≤
      max (Real.rpow N a) (Real.rpow N b) := by
  exact RamachandraShiftedGammaPoleContour.norm_posReal_cpow_horizontal_le_max
    hN hax hxb

/-- The Mellin order used on a depth-`n` horizontal side.  It exceeds the
archimedean degree by two. -/
def horizontalMellinOrder (n : ℕ) : ℕ := 2 * n + 7

/-- Literal pointwise product bound on the upper horizontal side.  Its only
`x`-dependent coefficient is the fixed-line Schwartz seminorm displayed on
the right; making that coefficient uniform on the compact real interval is
the final leaf needed before interval integration. -/
theorem norm_lemma295ReflectedFiniteIntegrand_horizontal_le
    {N : ℝ} (hN : 0 < N) (g : ℝ) (K n : ℕ) {x B : ℝ}
    (hx : x ∈ Set.Icc (deepLeftSigma n) (1 / 2))
    (hheight : 2 ≤ |B - g|) :
    ‖lemma295ReflectedFiniteIntegrand N g K
        ((x : ℂ) + B * I)‖ ≤
      (1152 * horizontalThetaRadius n (B - g) ^ (2 * n + 5)) * K *
        max (Real.rpow N (deepLeftSigma n)) (Real.rpow N (1 / 2)) *
          (sourceMellinDecayConstantAt x (horizontalMellinOrder n) /
            (1 + |B| ^ horizontalMellinOrder n)) := by
  let s : ℂ := (x : ℂ) + B * I
  let z : ℂ := s - g * I
  have hzform : z = (x : ℂ) + (((B - g : ℝ) : ℂ)) * I := by
    dsimp [z, s]
    apply Complex.ext <;> simp
  have hzre : z.re = x := by simp [z, s]
  have htheta := norm_sourceZetaTheta_horizontal_le n hx hheight
  rw [← hzform] at htheta
  have hprefix := norm_sourceDualPartialNat_le_card K (z := z) (by
    rw [hzre]
    exact hx.2)
  have hscale := norm_positiveScale_horizontal_le_max hN hx.1 hx.2
    (t := B - g)
  rw [← hzform] at hscale
  have hmellin := norm_mellin_sourceHZero_vertical_le_inv_one_add_abs_pow
    x (horizontalMellinOrder n) B
  change ‖mellin sourceHZero s‖ ≤ _ at hmellin
  unfold lemma295ReflectedFiniteIntegrand
  dsimp only
  repeat' rw [norm_mul]
  have hthetaUpper : 0 ≤
      1152 * horizontalThetaRadius n (B - g) ^ (2 * n + 5) :=
    (norm_nonneg _).trans htheta
  have hprefixUpper : 0 ≤ (K : ℝ) := by positivity
  have hscaleUpper : 0 ≤
      max (Real.rpow N (deepLeftSigma n)) (Real.rpow N (1 / 2)) :=
    (norm_nonneg _).trans hscale
  have hmellinUpper : 0 ≤
      sourceMellinDecayConstantAt x (horizontalMellinOrder n) /
        (1 + |B| ^ horizontalMellinOrder n) :=
    (norm_nonneg _).trans hmellin
  exact mul_le_mul
    (mul_le_mul
      (mul_le_mul htheta hprefix (norm_nonneg _) hthetaUpper)
      hscale (norm_nonneg _) (mul_nonneg hthetaUpper hprefixUpper))
    hmellin (norm_nonneg _)
      (mul_nonneg (mul_nonneg hthetaUpper hprefixUpper) hscaleUpper)

end
end GuthMaynardLemma295HorizontalPointwise

#print axioms GuthMaynardLemma295HorizontalPointwise.norm_sourceDualPartialNat_le_card
#print axioms GuthMaynardLemma295HorizontalPointwise.norm_positiveScale_horizontal_le_max
#print axioms GuthMaynardLemma295HorizontalPointwise.norm_lemma295ReflectedFiniteIntegrand_horizontal_le
