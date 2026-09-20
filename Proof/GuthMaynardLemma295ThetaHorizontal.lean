import GuthMaynardLemma295ThetaBounds
import GuthMaynardLemma295DualTail

/-!
# Horizontal archimedean control in Guth--Maynard Lemma 29.5

The horizontal sides of the reflected rectangle range over the whole compact
real interval from `deepLeftSigma n` to `1/2`.  This file supplies a completely
explicit polynomial envelope for the zeta functional-equation multiplier on
that interval.  The only analytic inputs are the certified compact-strip Gamma
bounds; movement to the left is by the exact two-step recurrence.
-/

namespace GuthMaynardLemma295ThetaHorizontal

open Complex Real
open GuthMaynardLemma295CutoffAnalytic
open GuthMaynardLemma295ThetaBounds
open GuthMaynardLemma295DualTail
open MAPGammaCompactStripSharp MAPGammaInverseGrowthSharp

noncomputable section

private theorem stripPoint_norm_ge_abs_im (a t : ℝ) :
    |t| ≤ ‖GammaCompactStripScratch.stripPoint a t‖ := by
  simpa [GammaCompactStripScratch.stripPoint] using
    Complex.abs_im_le_norm (GammaCompactStripScratch.stripPoint a t)

/-- The numerator Gamma factor remains under the same convenient polynomial
envelope when its real part is allowed down to `1/4`. -/
theorem norm_Gamma_quarter_threeHalves_le
    {a t : ℝ} (ha : 1 / 4 ≤ a) (ha' : a ≤ 3 / 2) (ht : 1 ≤ |t|) :
    ‖Complex.Gamma (GammaCompactStripScratch.stripPoint a t)‖ ≤
      24 * (1 + |t|) ^ 2 *
        Real.exp (-(Real.pi / 2) * |t|) := by
  by_cases hhalf : 1 / 2 ≤ a
  · exact JutilaMultiplierBaseStrip.norm_Gamma_half_two_le
      hhalf (by linarith) ht
  · let w := GammaCompactStripScratch.stripPoint a t
    have hw : w ≠ 0 := by
      intro hw
      have him := congrArg Complex.im hw
      simp [w, GammaCompactStripScratch.stripPoint] at him
      subst t
      norm_num at ht
    have hrec := Complex.Gamma_add_one w hw
    have hadd : w + 1 =
        GammaCompactStripScratch.stripPoint (a + 1) t := by
      exact GammaCompactStripScratch.stripPoint_add_one a t
    have hupper := MAPGammaCompactStripSharp.norm_Gamma_positive_strip_le_exp_pi_half
      (a := a + 1) (t := t) (by linarith) (by linarith)
    have hwnorm : 1 ≤ ‖w‖ :=
      ht.trans (stripPoint_norm_ge_abs_im a t)
    have hnorm := congrArg norm hrec
    rw [norm_mul, hadd] at hnorm
    change ‖Complex.Gamma w‖ ≤ _
    calc
      ‖Complex.Gamma w‖ ≤ ‖w‖ * ‖Complex.Gamma w‖ :=
        le_mul_of_one_le_left (norm_nonneg _) hwnorm
      _ = ‖Complex.Gamma
          (GammaCompactStripScratch.stripPoint (a + 1) t)‖ := hnorm.symm
      _ ≤ 12 * (1 + |t|) *
          Real.exp (-(Real.pi / 2) * |t|) := hupper
      _ ≤ 24 * (1 + |t|) ^ 2 *
          Real.exp (-(Real.pi / 2) * |t|) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        have hy : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
        nlinarith [sq_nonneg (1 + |t|)]

private theorem norm_sourceZetaTheta_eq_gamma_product (z : ℂ) :
    ‖sourceZetaTheta z‖ =
      Real.rpow Real.pi (z.re - 1 / 2) *
        ‖Complex.Gamma ((1 - z) / 2)‖ *
        ‖(Complex.Gamma (z / 2))⁻¹‖ := by
  rw [sourceZetaTheta_eq_printed, norm_mul, norm_div, norm_inv]
  have hpow : ‖(Real.pi : ℂ) ^ (z - 1 / 2)‖ =
      Real.rpow Real.pi (z.re - 1 / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    simp
  rw [hpow]
  ring

/-- A base strip reaching the critical line.  The slightly wider right edge is
needed because a horizontal contour contains `0 < Re z ≤ 1/2`. -/
theorem norm_sourceZetaTheta_wideBaseStrip_le
    {z : ℂ} (hzlo : -2 ≤ z.re) (hzhi : z.re ≤ 1 / 2)
    (hzim : 2 ≤ |z.im|) :
    ‖sourceZetaTheta z‖ ≤ 1152 * (1 + |z.im|) ^ 5 := by
  have ht : 1 ≤ |z.im / 2| := by
    rw [abs_div]
    norm_num
    linarith
  have hpi : Real.rpow Real.pi (z.re - 1 / 2) ≤ 1 := by
    calc
      Real.rpow Real.pi (z.re - 1 / 2) ≤ Real.rpow Real.pi 0 :=
        Real.rpow_le_rpow_of_exponent_le
          (by linarith [Real.pi_gt_three]) (by linarith)
      _ = 1 := by simp
  have hnum := norm_Gamma_quarter_threeHalves_le
    (a := (1 - z.re) / 2) (t := -z.im / 2)
    (by linarith) (by linarith) (by
      simpa only [show -z.im / 2 = -(z.im / 2) by ring, abs_neg] using ht)
  have hden := JutilaMultiplierBaseStrip.norm_inv_Gamma_neg_one_half_le
    (a := z.re / 2) (t := z.im / 2)
    (by linarith) (by linarith) ht
  have hgeom1 : (1 - z) / 2 =
      GammaCompactStripScratch.stripPoint ((1 - z.re) / 2) (-z.im / 2) := by
    apply Complex.ext <;> simp [GammaCompactStripScratch.stripPoint] <;> ring_nf
  have hgeom2 : z / 2 =
      GammaCompactStripScratch.stripPoint (z.re / 2) (z.im / 2) := by
    apply Complex.ext <;> simp [GammaCompactStripScratch.stripPoint]
  rw [← hgeom1] at hnum
  rw [← hgeom2] at hden
  have hnum' : ‖Complex.Gamma ((1 - z) / 2)‖ ≤
      24 * (1 + |z.im / 2|) ^ 2 *
        Real.exp (-(Real.pi / 2) * |z.im / 2|) := by
    simpa only [show -z.im / 2 = -(z.im / 2) by ring, abs_neg] using hnum
  rw [norm_sourceZetaTheta_eq_gamma_product]
  have habs : |z.im / 2| ≤ |z.im| := by
    rw [abs_div]
    norm_num
  calc
    Real.rpow Real.pi (z.re - 1 / 2) *
        ‖Complex.Gamma ((1 - z) / 2)‖ *
        ‖(Complex.Gamma (z / 2))⁻¹‖ ≤
      1 * (24 * (1 + |z.im / 2|) ^ 2 *
        Real.exp (-(Real.pi / 2) * |z.im / 2|)) *
        (48 * (1 + |z.im / 2|) ^ 3 *
          Real.exp ((Real.pi / 2) * |z.im / 2|)) := by
        gcongr
    _ ≤ 1152 * (1 + |z.im|) ^ 5 := by
      have hexp : Real.exp (-(Real.pi / 2) * |z.im / 2|) *
          Real.exp ((Real.pi / 2) * |z.im / 2|) = 1 := by
        rw [← Real.exp_add]
        convert Real.exp_zero using 1 <;> ring_nf
      rw [show 1 * (24 * (1 + |z.im / 2|) ^ 2 *
            Real.exp (-(Real.pi / 2) * |z.im / 2|)) *
            (48 * (1 + |z.im / 2|) ^ 3 *
              Real.exp ((Real.pi / 2) * |z.im / 2|)) =
          1152 * (1 + |z.im / 2|) ^ 5 *
            (Real.exp (-(Real.pi / 2) * |z.im / 2|) *
              Real.exp ((Real.pi / 2) * |z.im / 2|)) by ring,
        hexp, mul_one]
      exact mul_le_mul_of_nonneg_left (by gcongr) (by norm_num)

/-- A convenient radius for the horizontal polynomial envelope. -/
def horizontalThetaRadius (n : ℕ) (u : ℝ) : ℝ :=
  4 + 4 * n + |u|

private theorem one_add_norm_horizontal_le_radius_succ
    {n : ℕ} {x u : ℝ}
    (hxlo : deepLeftSigma (n + 1) ≤ x) (hxhi : x < -2) :
    1 + ‖(x : ℂ) + ((u : ℝ) : ℂ) * I‖ ≤ horizontalThetaRadius (n + 1) u := by
  have hxnonpos : x ≤ 0 := by linarith
  have hnorm : ‖(x : ℂ) + ((u : ℝ) : ℂ) * I‖ ≤ |x| + |u| := by
    simpa using Complex.norm_le_abs_re_add_abs_im
      ((x : ℂ) + ((u : ℝ) : ℂ) * I)
  have hxabs : |x| ≤ (5 / 2 : ℝ) + 2 * n := by
    rw [abs_of_nonpos hxnonpos]
    unfold deepLeftSigma at hxlo
    push_cast at hxlo ⊢
    linarith
  unfold horizontalThetaRadius
  push_cast
  linarith

private theorem horizontalThetaRadius_mono (n : ℕ) (u : ℝ) :
    horizontalThetaRadius n u ≤ horizontalThetaRadius (n + 1) u := by
  unfold horizontalThetaRadius
  push_cast
  linarith

private theorem horizontalThetaRadius_one_le (n : ℕ) (u : ℝ) :
    1 ≤ horizontalThetaRadius n u := by
  unfold horizontalThetaRadius
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith [abs_nonneg u, hn]

/-- **Horizontal archimedean leaf for Lemma 29.5.**  Uniformly across the
entire horizontal segment from the deep-left line to the critical line, the
functional-equation multiplier has polynomial growth in the ordinate.  Both
the constant and the degree are explicit (and may depend on the chosen
deep-left depth `n`). -/
theorem norm_sourceZetaTheta_horizontal_le
    (n : ℕ) {x B g : ℝ}
    (hx : x ∈ Set.Icc (deepLeftSigma n) (1 / 2))
    (hheight : 2 ≤ |B - g|) :
    ‖sourceZetaTheta ((x : ℂ) + (((B - g : ℝ) : ℂ)) * I)‖ ≤
      1152 * (horizontalThetaRadius n (B - g)) ^ (2 * n + 5) := by
  induction n generalizing x with
  | zero =>
      have hbase := norm_sourceZetaTheta_wideBaseStrip_le
        (z := (x : ℂ) + (((B - g : ℝ) : ℂ)) * I)
        (by
          have hxlo : (-(1 / 2 : ℝ)) ≤ x := by
            simpa [deepLeftSigma] using hx.1
          simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
            mul_zero, mul_one, sub_zero, add_zero]
          linarith)
        (by simpa using hx.2) (by simpa using hheight)
      have him : (((x : ℂ) + (((B - g : ℝ) : ℂ)) * I).im) = B - g := by simp
      rw [him] at hbase
      have hr := horizontalThetaRadius_one_le 0 (B - g)
      have hpow : (1 + |B - g|) ^ 5 ≤
          horizontalThetaRadius 0 (B - g) ^ 5 := by
        apply pow_le_pow_left₀ (by positivity)
        unfold horizontalThetaRadius
        norm_num
      simpa using hbase.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))
  | succ n ih =>
      by_cases hbaseRange : -2 ≤ x
      · have hbase := norm_sourceZetaTheta_wideBaseStrip_le
          (z := (x : ℂ) + (((B - g : ℝ) : ℂ)) * I)
          (by simpa using hbaseRange) (by simpa using hx.2)
          (by simpa using hheight)
        have him : (((x : ℂ) + (((B - g : ℝ) : ℂ)) * I).im) = B - g := by simp
        rw [him] at hbase
        have hr := horizontalThetaRadius_one_le (n + 1) (B - g)
        have hlow : 1 + |B - g| ≤
            horizontalThetaRadius (n + 1) (B - g) := by
          unfold horizontalThetaRadius
          push_cast
          linarith
        have hexp : 5 ≤ 2 * (n + 1) + 5 := by omega
        have hpow : (1 + |B - g|) ^ 5 ≤
            horizontalThetaRadius (n + 1) (B - g) ^ (2 * (n + 1) + 5) := by
          exact (pow_le_pow_left₀ (by positivity) hlow 5).trans
            (pow_le_pow_right₀ hr hexp)
        exact hbase.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))
      · have hxlt : x < -2 := lt_of_not_ge hbaseRange
        let z : ℂ := (x : ℂ) + (((B - g : ℝ) : ℂ)) * I
        have hzim : z.im ≠ 0 := by
          have : B - g ≠ 0 := by
            intro hzero
            rw [hzero, abs_zero] at hheight
            norm_num at hheight
          simpa [z] using this
        have hshiftMem : x + 2 ∈ Set.Icc (deepLeftSigma n) (1 / 2) := by
          constructor
          · unfold deepLeftSigma at hx ⊢
            push_cast at hx ⊢
            linarith [hx.1]
          · linarith
        have hih := ih (x := x + 2) hshiftMem
        have hshift : z + 2 = ((x + 2 : ℝ) : ℂ) +
            (((B - g : ℝ) : ℂ)) * I := by
          apply Complex.ext <;> simp [z]
        rw [← hshift] at hih
        have hrec := sourceZetaTheta_shift_two z hzim
        have hstep :
            ‖((-1 - z) * z / ((2 : ℂ) * Real.pi) ^ 2)‖ ≤
              (1 + ‖z‖) ^ 2 := by
          simpa [JutilaMultiplierRecurrence.evenStep] using
            JutilaMultiplierRecurrence.norm_evenStep_le 1 z
        have hradStep : 1 + ‖z‖ ≤
            horizontalThetaRadius (n + 1) (B - g) := by
          dsimp [z]
          exact one_add_norm_horizontal_le_radius_succ
            (u := B - g) hx.1 hxlt
        have hradIH := horizontalThetaRadius_mono n (B - g)
        have hRnnonneg : 0 ≤ horizontalThetaRadius n (B - g) :=
          zero_le_one.trans (horizontalThetaRadius_one_le _ _)
        have hRnonneg : 0 ≤ horizontalThetaRadius (n + 1) (B - g) :=
          zero_le_one.trans (horizontalThetaRadius_one_le _ _)
        rw [hrec, norm_mul]
        calc
          ‖(-1 - z) * z / ((2 : ℂ) * Real.pi) ^ 2‖ *
              ‖sourceZetaTheta (z + 2)‖ ≤
            (1 + ‖z‖) ^ 2 *
              (1152 * horizontalThetaRadius n (B - g) ^ (2 * n + 5)) :=
                mul_le_mul hstep hih
                  (norm_nonneg _)
                  (sq_nonneg _)
          _ ≤ horizontalThetaRadius (n + 1) (B - g) ^ 2 *
              (1152 * horizontalThetaRadius (n + 1) (B - g) ^ (2 * n + 5)) := by
                apply mul_le_mul
                · exact pow_le_pow_left₀ (by positivity) hradStep 2
                · apply mul_le_mul_of_nonneg_left
                  exact pow_le_pow_left₀
                    hRnnonneg hradIH _
                  norm_num
                · exact mul_nonneg (by norm_num) (pow_nonneg hRnnonneg _)
                · exact pow_nonneg hRnonneg _
          _ = 1152 * horizontalThetaRadius (n + 1) (B - g) ^
              (2 * (n + 1) + 5) := by
                rw [show 2 * (n + 1) + 5 = 2 + (2 * n + 5) by omega,
                  pow_add]
                ring

end
end GuthMaynardLemma295ThetaHorizontal

#print axioms GuthMaynardLemma295ThetaHorizontal.norm_Gamma_quarter_threeHalves_le
#print axioms GuthMaynardLemma295ThetaHorizontal.norm_sourceZetaTheta_wideBaseStrip_le
#print axioms GuthMaynardLemma295ThetaHorizontal.norm_sourceZetaTheta_horizontal_le
