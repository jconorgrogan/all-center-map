import GammaMellinInversion

/-!
# Gamma kernel on Jutila's Lemma-6 contour

Jutila shifts the Mellin line to `Gamma(-beta+iu)`.  On MAP's regular
branch `4/5 ≤ beta ≤ 1-omega`, so the distance from the pole at `-1` is
visible.  One Gamma recurrence and the certified positive-line Cauchy
envelope give an integrable bound with an explicit `omega⁻¹` constant.
-/

namespace MAPJutilaLemma6GammaKernel

open Complex Real
open MAPGammaMellinInversion

noncomputable section

def lemmaSixGammaConstant (omega : ℝ) : ℝ :=
  (5 / 2) * (omega⁻¹ + 1)

def lemmaSixGammaSqConstant (omega : ℝ) : ℝ :=
  8 * (1 + (4 * omega / 5)⁻¹)

theorem lemmaSixGammaConstant_pos {omega : ℝ} (homega : 0 < omega) :
    0 < lemmaSixGammaConstant omega := by
  unfold lemmaSixGammaConstant
  positivity

theorem lemmaSixGammaSqConstant_pos {omega : ℝ} (homega : 0 < omega) :
    0 < lemmaSixGammaSqConstant omega := by
  unfold lemmaSixGammaSqConstant
  positivity

/-- The fourth-order Cauchy envelope extends to the whole strip
`-1 < Re z < 0`.  The explicit inverse factor records the distance to the
two neighboring Gamma poles. -/
theorem norm_Gamma_minus_one_zero_vertical_le_inv_sq
    {a t : ℝ} (halo : -1 < a) (hahi : a < 0) :
    ‖Complex.Gamma ((a : ℂ) + t * I)‖ ≤
      ((1 + ((-a) * (a + 1))⁻¹) *
        (Real.Gamma (a + 2) + Real.Gamma (a + 4))) *
        (1 + t ^ 2)⁻¹ ^ 2 := by
  let z : ℂ := (a : ℂ) + t * I
  let c : ℝ := (-a) * (a + 1)
  let P : ℝ := ‖z + 1‖ * ‖z‖
  let D : ℝ := 1 + t ^ 2
  let C : ℝ := Real.Gamma (a + 2) + Real.Gamma (a + 4)
  have ha1 : 0 < a + 1 := by linarith
  have hnega : 0 < -a := by linarith
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos hnega ha1
  have hz : z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [z] at hre
    linarith
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [z] at hre
    linarith
  have hrec : Complex.Gamma (z + 2) =
      (z + 1) * z * Complex.Gamma z := by
    calc
      Complex.Gamma (z + 2) = Complex.Gamma ((z + 1) + 1) := by ring_nf
      _ = (z + 1) * Complex.Gamma (z + 1) :=
        Complex.Gamma_add_one (z + 1) hz1
      _ = (z + 1) * z * Complex.Gamma z := by
        rw [Complex.Gamma_add_one z hz]
        ring
  have hnormrec : ‖Complex.Gamma (z + 2)‖ =
      P * ‖Complex.Gamma z‖ := by
    rw [hrec, norm_mul, norm_mul]
  have hzre : -a ≤ ‖z‖ := by
    have h := Complex.abs_re_le_norm z
    simpa [z, abs_of_nonpos hahi.le] using h
  have hz1re : a + 1 ≤ ‖z + 1‖ := by
    have h := Complex.abs_re_le_norm (z + 1)
    simpa [z, abs_of_pos ha1] using h
  have hcP : c ≤ P := by
    dsimp [c, P]
    calc
      (-a) * (a + 1) ≤ ‖z‖ * ‖z + 1‖ :=
        mul_le_mul hzre hz1re (by positivity) (norm_nonneg _)
      _ = ‖z + 1‖ * ‖z‖ := by ring
  have hzt : |t| ≤ ‖z‖ := by
    simpa [z] using Complex.abs_im_le_norm z
  have hz1t : |t| ≤ ‖z + 1‖ := by
    simpa [z] using Complex.abs_im_le_norm (z + 1)
  have htP : t ^ 2 ≤ P := by
    dsimp [P]
    rw [← sq_abs, pow_two]
    exact mul_le_mul hz1t hzt (abs_nonneg t) (norm_nonneg (z + 1))
  have hDP : D ≤ (c⁻¹ + 1) * P := by
    calc
      D = 1 + t ^ 2 := rfl
      _ ≤ c⁻¹ * P + P :=
        add_le_add ((one_le_inv_mul₀ hc).2 hcP) htP
      _ = (c⁻¹ + 1) * P := by ring
  have hD : 0 < D := by dsimp [D]; positivity
  have hE : 0 ≤ c⁻¹ + 1 := by positivity
  have hshift0 := MAPGammaMellinInversion.norm_Gamma_vertical_le_inv_one_add_sq
    (sigma := a + 2) (t := t) (by linarith)
  have hshift : ‖Complex.Gamma (z + 2)‖ ≤ C * D⁻¹ := by
    have hzshift : z + 2 = ((a + 2 : ℝ) : ℂ) + t * I := by
      dsimp [z]
      push_cast
      ring
    rw [hzshift]
    simpa [C, D, show a + 2 + 2 = a + 4 by ring] using hshift0
  have hDG : D * ‖Complex.Gamma z‖ ≤
      (c⁻¹ + 1) * ‖Complex.Gamma (z + 2)‖ := by
    calc
      D * ‖Complex.Gamma z‖ ≤
          ((c⁻¹ + 1) * P) * ‖Complex.Gamma z‖ :=
        mul_le_mul_of_nonneg_right hDP (norm_nonneg _)
      _ = (c⁻¹ + 1) * ‖Complex.Gamma (z + 2)‖ := by
        rw [hnormrec]
        ring
  have hshiftD : ‖Complex.Gamma (z + 2)‖ * D ≤ C := by
    have := mul_le_mul_of_nonneg_right hshift hD.le
    simpa [hD.ne', C, D] using this
  have hfinal : ‖Complex.Gamma z‖ * (D * D) ≤
      (c⁻¹ + 1) * C := by
    calc
      ‖Complex.Gamma z‖ * (D * D) =
          (D * ‖Complex.Gamma z‖) * D := by ring
      _ ≤ ((c⁻¹ + 1) * ‖Complex.Gamma (z + 2)‖) * D :=
        mul_le_mul_of_nonneg_right hDG hD.le
      _ = (c⁻¹ + 1) * (‖Complex.Gamma (z + 2)‖ * D) := by ring
      _ ≤ (c⁻¹ + 1) * C := mul_le_mul_of_nonneg_left hshiftD hE
  change ‖Complex.Gamma z‖ ≤ (1 + c⁻¹) * C * D⁻¹ ^ 2
  rw [show D⁻¹ ^ 2 = (D * D)⁻¹ by rw [mul_inv, pow_two]]
  rw [← div_eq_mul_inv]
  exact (le_div_iff₀ (mul_pos hD hD)).2 (by
    simpa [add_comm] using hfinal)


/-- Pointwise integrable envelope for the exact Gamma factor in (2.11). -/
theorem norm_Gamma_neg_beta_vertical_le
    {beta omega t : ℝ} (homega : 0 < omega)
    (hbetaLow : 4 / 5 ≤ beta) (hbetaHigh : beta ≤ 1 - omega) :
    ‖Complex.Gamma ((-beta : ℝ) + (t : ℂ) * I)‖ ≤
      lemmaSixGammaConstant omega * (1 + t ^ 2)⁻¹ := by
  let a : ℝ := -beta
  let z : ℂ := (a : ℂ) + (t : ℂ) * I
  have haNeg : a < 0 := by dsimp [a]; linarith
  have haOne : 0 < a + 1 := by dsimp [a]; linarith
  have haTwoOne : 1 ≤ a + 2 := by dsimp [a]; linarith
  have haThreeTwo : 2 ≤ a + 3 := by dsimp [a]; linarith
  have haThreeLe : a + 3 ≤ 3 := by dsimp [a]; linarith
  have hz : z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [z] at hre
    linarith
  have hrec : Complex.Gamma (z + 1) = z * Complex.Gamma z := by
    exact Complex.Gamma_add_one z hz
  have hnormrec : ‖Complex.Gamma (z + 1)‖ =
      ‖z‖ * ‖Complex.Gamma z‖ := by rw [hrec, norm_mul]
  have hzLower : -a ≤ ‖z‖ := by
    have h := Complex.abs_re_le_norm z
    simpa [z, abs_of_nonpos haNeg.le] using h
  have hGa3 : Real.Gamma (a + 3) ≤ Real.Gamma 3 :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn
      (by simpa only [Set.mem_Ici] using haThreeTwo)
      (by norm_num : (3 : ℝ) ∈ Set.Ici 2) haThreeLe
  have hGa3Two : Real.Gamma (a + 3) ≤ 2 := by
    simpa [Real.Gamma_ofNat_eq_factorial] using hGa3
  have hGa2 : Real.Gamma (a + 2) ≤ 2 := by
    have hGa2pos : 0 < Real.Gamma (a + 2) :=
      Real.Gamma_pos_of_pos (by linarith)
    calc
      Real.Gamma (a + 2) ≤ (a + 2) * Real.Gamma (a + 2) :=
        (le_mul_iff_one_le_left hGa2pos).2 haTwoOne
      _ = Real.Gamma (a + 3) := by
        rw [show a + 3 = (a + 2) + 1 by ring,
          Real.Gamma_add_one (by linarith : a + 2 ≠ 0)]
      _ ≤ 2 := hGa3Two
  have hGa1 : Real.Gamma (a + 1) ≤ 2 / omega := by
    have hrecReal : Real.Gamma (a + 2) =
        (a + 1) * Real.Gamma (a + 1) := by
      rw [show a + 2 = (a + 1) + 1 by ring,
        Real.Gamma_add_one (ne_of_gt haOne)]
    have hGa1pos : 0 < Real.Gamma (a + 1) :=
      Real.Gamma_pos_of_pos haOne
    have homegaLe : omega ≤ a + 1 := by dsimp [a]; linarith
    apply (le_div_iff₀ homega).2
    calc
      Real.Gamma (a + 1) * omega =
          omega * Real.Gamma (a + 1) := by ring
      _ ≤
          (a + 1) * Real.Gamma (a + 1) :=
        mul_le_mul_of_nonneg_right homegaLe hGa1pos.le
      _ = Real.Gamma (a + 2) := hrecReal.symm
      _ ≤ 2 := hGa2
  have hsum : Real.Gamma (a + 1) + Real.Gamma (a + 3) ≤
      2 / omega + 2 := add_le_add hGa1 hGa3Two
  have hshiftRaw := norm_Gamma_vertical_le_inv_one_add_sq
    (sigma := a + 1) (t := t) haOne
  have hzshift : z + 1 = ((a + 1 : ℝ) : ℂ) + (t : ℂ) * I := by
    dsimp [z]
    push_cast
    ring
  have hshift : ‖Complex.Gamma (z + 1)‖ ≤
      (2 / omega + 2) * (1 + t ^ 2)⁻¹ := by
    rw [hzshift]
    exact hshiftRaw.trans (by
      simpa only [show a + 1 + 2 = a + 3 by ring] using
        (mul_le_mul_of_nonneg_right hsum (by positivity)))
  have hminusALow : 4 / 5 ≤ -a := by dsimp [a]; linarith
  have hGamma0 : 0 ≤ ‖Complex.Gamma z‖ := norm_nonneg _
  have hprod : (4 / 5 : ℝ) * ‖Complex.Gamma z‖ ≤
      (2 / omega + 2) * (1 + t ^ 2)⁻¹ := by
    calc
      (4 / 5 : ℝ) * ‖Complex.Gamma z‖ ≤
          (-a) * ‖Complex.Gamma z‖ :=
        mul_le_mul_of_nonneg_right hminusALow hGamma0
      _ ≤ ‖z‖ * ‖Complex.Gamma z‖ :=
        mul_le_mul_of_nonneg_right hzLower hGamma0
      _ = ‖Complex.Gamma (z + 1)‖ := hnormrec.symm
      _ ≤ (2 / omega + 2) * (1 + t ^ 2)⁻¹ := hshift
  have hscaled : ‖Complex.Gamma z‖ ≤
      (5 / 4 : ℝ) * ((2 / omega + 2) * (1 + t ^ 2)⁻¹) := by
    nlinarith
  change ‖Complex.Gamma z‖ ≤
    lemmaSixGammaConstant omega * (1 + t ^ 2)⁻¹
  calc
    ‖Complex.Gamma z‖ ≤
        (5 / 4 : ℝ) * ((2 / omega + 2) * (1 + t ^ 2)⁻¹) := hscaled
    _ = lemmaSixGammaConstant omega * (1 + t ^ 2)⁻¹ := by
      unfold lemmaSixGammaConstant
      field_simp [homega.ne']
      ring

/-- Stronger fourth-order envelope.  This is the useful form for the
Lemma-6 integral, since it allows the p.48 L-function factor to be bounded by
a linear height without losing integrability. -/
theorem norm_Gamma_neg_beta_vertical_le_inv_sq
    {beta omega t : ℝ} (homega : 0 < omega)
    (hbetaLow : 4 / 5 ≤ beta) (hbetaHigh : beta ≤ 1 - omega) :
    ‖Complex.Gamma ((-beta : ℝ) + (t : ℂ) * I)‖ ≤
      lemmaSixGammaSqConstant omega * (1 + t ^ 2)⁻¹ ^ 2 := by
  let a : ℝ := -beta
  have haLow : -1 < a := by dsimp [a]; linarith
  have haHigh : a < 0 := by dsimp [a]; linarith
  have hraw := norm_Gamma_minus_one_zero_vertical_le_inv_sq
    (a := a) (t := t) haLow haHigh
  have hbetaOne : omega ≤ 1 - beta := by linarith
  have hcLower : 4 * omega / 5 ≤ beta * (1 - beta) := by
    calc
      4 * omega / 5 = (4 / 5 : ℝ) * omega := by ring
      _ ≤ beta * (1 - beta) :=
        mul_le_mul hbetaLow hbetaOne homega.le (by linarith)
  have hcPos : 0 < beta * (1 - beta) := by
    exact mul_pos (by linarith) (homega.trans_le hbetaOne)
  have hbasePos : 0 < 4 * omega / 5 := by positivity
  have hcinv : (beta * (1 - beta))⁻¹ ≤ (4 * omega / 5)⁻¹ :=
    (inv_le_inv₀ hcPos hbasePos).2 hcLower
  have hfac : 1 + (beta * (1 - beta))⁻¹ ≤
      1 + (4 * omega / 5)⁻¹ := by linarith
  have haTwoPos : 0 < a + 2 := by dsimp [a]; linarith
  have haTwoOne : 1 ≤ a + 2 := by dsimp [a]; linarith
  have haThreeTwo : 2 ≤ a + 3 := by dsimp [a]; linarith
  have haThreeLe : a + 3 ≤ 3 := by dsimp [a]; linarith
  have hGa3 : Real.Gamma (a + 3) ≤ Real.Gamma 3 :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn
      (by simpa only [Set.mem_Ici] using haThreeTwo)
      (by norm_num : (3 : ℝ) ∈ Set.Ici 2) haThreeLe
  have hGa2 : Real.Gamma (a + 2) ≤ 2 := by
    have hGa2pos := Real.Gamma_pos_of_pos haTwoPos
    calc
      Real.Gamma (a + 2) ≤ (a + 2) * Real.Gamma (a + 2) :=
        (le_mul_iff_one_le_left hGa2pos).2 haTwoOne
      _ = Real.Gamma (a + 3) := by
        rw [show a + 3 = (a + 2) + 1 by ring,
          Real.Gamma_add_one (ne_of_gt haTwoPos)]
      _ ≤ Real.Gamma 3 := hGa3
      _ = 2 := by norm_num [Real.Gamma_ofNat_eq_factorial]
  have haFourTwo : 2 ≤ a + 4 := by dsimp [a]; linarith
  have haFourLe : a + 4 ≤ 4 := by dsimp [a]; linarith
  have hGa4 : Real.Gamma (a + 4) ≤ 6 := by
    calc
      Real.Gamma (a + 4) ≤ Real.Gamma 4 :=
        Real.Gamma_strictMonoOn_Ici.monotoneOn
          (by simpa only [Set.mem_Ici] using haFourTwo)
          (by norm_num : (4 : ℝ) ∈ Set.Ici 2) haFourLe
      _ = 6 := by norm_num [Real.Gamma_ofNat_eq_factorial]
  have hsum : Real.Gamma (a + 2) + Real.Gamma (a + 4) ≤ 8 := by
    linarith
  have hsum0 : 0 ≤ Real.Gamma (a + 2) + Real.Gamma (a + 4) :=
    add_nonneg (Real.Gamma_pos_of_pos haTwoPos).le
      (Real.Gamma_pos_of_pos (by linarith)).le
  have hfactor0 : 0 ≤ 1 + (4 * omega / 5)⁻¹ := by positivity
  have hcoeff :
      (1 + ((-a) * (a + 1))⁻¹) *
          (Real.Gamma (a + 2) + Real.Gamma (a + 4)) ≤
        lemmaSixGammaSqConstant omega := by
    have hca : (-a) * (a + 1) = beta * (1 - beta) := by
      dsimp [a]
      ring
    rw [hca]
    calc
      (1 + (beta * (1 - beta))⁻¹) *
          (Real.Gamma (a + 2) + Real.Gamma (a + 4)) ≤
        (1 + (4 * omega / 5)⁻¹) * 8 :=
          mul_le_mul hfac hsum hsum0 hfactor0
      _ = lemmaSixGammaSqConstant omega := by
        unfold lemmaSixGammaSqConstant
        ring
  have hinvSq0 : 0 ≤ (1 + t ^ 2)⁻¹ ^ 2 := sq_nonneg _
  change ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖ ≤
    lemmaSixGammaSqConstant omega * (1 + t ^ 2)⁻¹ ^ 2
  exact hraw.trans (mul_le_mul_of_nonneg_right hcoeff hinvSq0)

end

end MAPJutilaLemma6GammaKernel

#print axioms MAPJutilaLemma6GammaKernel.norm_Gamma_neg_beta_vertical_le
#print axioms MAPJutilaLemma6GammaKernel.norm_Gamma_neg_beta_vertical_le_inv_sq
