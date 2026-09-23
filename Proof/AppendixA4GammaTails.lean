import AppendixA4FullContourLimit
import Mathlib.Analysis.SpecialFunctions.PolynomialExp

namespace MAPAppendixA4GammaTails

open Set MeasureTheory Complex Filter
open scoped Topology ArithmeticFunction LSeries.notation BigOperators
open MAPMollifierCoefficientIdentity MAPAppendixA4FullContourLimit
  MAPAppendixA4GammaEndpoint

noncomputable section

variable {q : ℕ} [NeZero q]

/-- Elementary uniform bound for the finite mollifier on every nonnegative
real-part line. -/
theorem norm_mollifier_le_card
    (chi : DirichletCharacter ℂ q) (U : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖mollifier chi U s‖ ≤ U + 1 := by
  rw [MAPAppendixA4Detector.mollifier_eq_sum_range]
  calc
    ‖∑ n ∈ Finset.range (U + 1),
        LSeries.term (((chi ·) : ℕ → ℂ) * truncatedMoebius U) s n‖
        ≤ ∑ n ∈ Finset.range (U + 1),
          ‖LSeries.term (((chi ·) : ℕ → ℂ) * truncatedMoebius U) s n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range (U + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [LSeries.norm_term_eq]
      split_ifs with hn0
      · norm_num
      · have hn1 : 1 ≤ (n : ℝ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
        have hden : 1 ≤ (n : ℝ) ^ s.re :=
          Real.one_le_rpow hn1 hs
        have hchi : ‖chi (n : ZMod q)‖ ≤ 1 := chi.norm_le_one _
        have hmu : ‖truncatedMoebius U n‖ ≤ 1 :=
          norm_truncatedMoebius_le_one U n
        have hnum : ‖chi (n : ZMod q) * truncatedMoebius U n‖ ≤ 1 := by
          rw [norm_mul]
          nlinarith [norm_nonneg (chi (n : ZMod q)),
            norm_nonneg (truncatedMoebius U n)]
        simp only [Pi.mul_apply]
        exact (div_le_one (by positivity)).2 (hnum.trans hden)
    _ = U + 1 := by simp


/-- Explicit common envelope for both horizontal sides. -/
def horizontalEnvelope (q U : ℕ) (rho : ℂ) (Y B : ℝ) : ℝ :=
  (12 * (1 + B) * Real.exp (-B)) *
    Y ^ (1 / 2 : ℝ) *
    (200 * (q : ℝ) ^ 2 * (5 + |rho.im| + B) ^ 2) *
    (U + 1)

/-- Pointwise envelope on the upper horizontal side of the literal A.4
rectangle. -/
theorem norm_regularized_upper_le_envelope
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {rho : ℂ} (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    (U : ℕ) {Y B x : ℝ} (hY : 1 ≤ Y) (hB : 1 ≤ B)
    (hx : x ∈ Set.uIoc (1 / 2 - rho.re) (1 / 2)) :
    ‖MAPAppendixA4Detector.regularizedDetectorIntegrand chi rho U Y
        (x + B * I)‖ ≤ horizontalEnvelope q U rho Y B := by
  have hac : 1 / 2 - rho.re ≤ (1 / 2 : ℝ) := by linarith
  have hx' : 1 / 2 - rho.re < x ∧ x ≤ 1 / 2 := by
    rw [Set.uIoc_of_le hac] at hx
    exact hx
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hz : (x : ℂ) + (B : ℂ) * I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  rw [MAPAppendixA4Detector.regularizedDetectorIntegrand_eq_raw chi hrho hz]
  unfold MAPMellinDetectorLeaf.gammaMellinWeight horizontalEnvelope
  rw [norm_mul, norm_mul, norm_mul]
  have hgamma :
      ‖Complex.Gamma ((x : ℂ) + B * I)‖ ≤
        12 * (1 + B) * Real.exp (-B) := by
    have hg := GammaCompactStripScratch.norm_Gamma_compactStrip_le_exp
      (a := x) (t := B) (by linarith [hx'.1, hbetaHigh]) hx'.2
      (by simpa [abs_of_nonneg (le_trans zero_le_one hB)] using hB)
    simpa [GammaCompactStripScratch.stripPoint,
      abs_of_nonneg (le_trans zero_le_one hB)] using hg
  have hYpow : ‖(Y : ℂ) ^ ((x : ℂ) + B * I)‖ ≤ Y ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hYpos]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul,
      sub_zero, add_zero]
    exact Real.rpow_le_rpow_of_exponent_le hY hx'.2
  have hslo : -1 ≤ (rho + ((x : ℂ) + B * I)).re := by
    simp
    linarith [hx'.1]
  have hshi : (rho + ((x : ℂ) + B * I)).re ≤ 2 := by
    simp
    linarith [hx'.2, hbetaHigh]
  have hL0 := PLInteriorGrowth.norm_LFunction_fixedStrip_le chi hchi hslo hshi
  have him : |(rho + ((x : ℂ) + B * I) + 3).im| ≤ |rho.im| + B := by
    simp
    exact (abs_add_le rho.im B).trans_eq (by
      rw [abs_of_nonneg (le_trans zero_le_one hB)])
  have hre : |(rho + ((x : ℂ) + B * I) + 3).re| ≤ 5 := by
    simp
    rw [abs_of_nonneg]
    · linarith [hx'.2, hbetaHigh]
    · linarith [hx'.1]
  have hnormshift : ‖rho + ((x : ℂ) + B * I) + 3‖ ≤
      5 + |rho.im| + B := by
    calc
      ‖rho + ((x : ℂ) + B * I) + 3‖ ≤
          |(rho + ((x : ℂ) + B * I) + 3).re| +
            |(rho + ((x : ℂ) + B * I) + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 5 + (|rho.im| + B) := add_le_add hre him
      _ = 5 + |rho.im| + B := by ring
  have hL : ‖DirichletCharacter.LFunction chi
      (rho + ((x : ℂ) + B * I))‖ ≤
      200 * (q : ℝ) ^ 2 * (5 + |rho.im| + B) ^ 2 := by
    exact hL0.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hnormshift 2) (by positivity))
  have hsnonneg : 0 ≤ (rho + ((x : ℂ) + B * I)).re := by
    simp
    linarith [hx'.1]
  have hM := norm_mollifier_le_card chi U hsnonneg
  gcongr


/-- Pointwise envelope on the lower horizontal side of the literal A.4
rectangle. -/
theorem norm_regularized_lower_le_envelope
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {rho : ℂ} (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    (U : ℕ) {Y B x : ℝ} (hY : 1 ≤ Y) (hB : 1 ≤ B)
    (hx : x ∈ Set.uIoc (1 / 2 - rho.re) (1 / 2)) :
    ‖MAPAppendixA4Detector.regularizedDetectorIntegrand chi rho U Y
        (x - B * I)‖ ≤ horizontalEnvelope q U rho Y B := by
  have hac : 1 / 2 - rho.re ≤ (1 / 2 : ℝ) := by linarith
  have hx' : 1 / 2 - rho.re < x ∧ x ≤ 1 / 2 := by
    rw [Set.uIoc_of_le hac] at hx
    exact hx
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hz : (x : ℂ) - (B : ℂ) * I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  rw [MAPAppendixA4Detector.regularizedDetectorIntegrand_eq_raw chi hrho hz]
  unfold MAPMellinDetectorLeaf.gammaMellinWeight horizontalEnvelope
  rw [norm_mul, norm_mul, norm_mul]
  have hgamma :
      ‖Complex.Gamma ((x : ℂ) - B * I)‖ ≤
        12 * (1 + B) * Real.exp (-B) := by
    have hg := GammaCompactStripScratch.norm_Gamma_compactStrip_le_exp
      (a := x) (t := -B) (by linarith [hx'.1, hbetaHigh]) hx'.2
      (by simpa [abs_of_nonneg (le_trans zero_le_one hB)] using hB)
    simpa [GammaCompactStripScratch.stripPoint, sub_eq_add_neg,
      abs_of_nonneg (le_trans zero_le_one hB)] using hg
  have hYpow : ‖(Y : ℂ) ^ ((x : ℂ) - B * I)‖ ≤ Y ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hYpos]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul,
      sub_zero]
    exact Real.rpow_le_rpow_of_exponent_le hY hx'.2
  have hslo : -1 ≤ (rho + ((x : ℂ) - B * I)).re := by
    simp
    linarith [hx'.1]
  have hshi : (rho + ((x : ℂ) - B * I)).re ≤ 2 := by
    simp
    linarith [hx'.2, hbetaHigh]
  have hL0 := PLInteriorGrowth.norm_LFunction_fixedStrip_le chi hchi hslo hshi
  have him : |(rho + ((x : ℂ) - B * I) + 3).im| ≤ |rho.im| + B := by
    simp
    have habs := abs_sub rho.im B
    exact habs.trans_eq (by
      rw [abs_of_nonneg (le_trans zero_le_one hB)])
  have hre : |(rho + ((x : ℂ) - B * I) + 3).re| ≤ 5 := by
    simp
    rw [abs_of_nonneg]
    · linarith [hx'.2, hbetaHigh]
    · linarith [hx'.1]
  have hnormshift : ‖rho + ((x : ℂ) - B * I) + 3‖ ≤
      5 + |rho.im| + B := by
    calc
      ‖rho + ((x : ℂ) - B * I) + 3‖ ≤
          |(rho + ((x : ℂ) - B * I) + 3).re| +
            |(rho + ((x : ℂ) - B * I) + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 5 + (|rho.im| + B) := add_le_add hre him
      _ = 5 + |rho.im| + B := by ring
  have hL : ‖DirichletCharacter.LFunction chi
      (rho + ((x : ℂ) - B * I))‖ ≤
      200 * (q : ℝ) ^ 2 * (5 + |rho.im| + B) ^ 2 := by
    exact hL0.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hnormshift 2) (by positivity))
  have hsnonneg : 0 ≤ (rho + ((x : ℂ) - B * I)).re := by
    simp
    linarith [hx'.1]
  have hM := norm_mollifier_le_card chi U hsnonneg
  gcongr


/-- The explicit horizontal envelope tends to zero.  This spends only the
standard theorem that an exponential dominates a fixed polynomial. -/
theorem tendsto_horizontalEnvelope_zero
    (q U : ℕ) (rho : ℂ) {Y : ℝ} (hY : 1 ≤ Y) :
    Tendsto (horizontalEnvelope q U rho Y) atTop (𝓝 0) := by
  let C : ℝ := 5 + |rho.im|
  let K : ℝ := 12 * Y ^ (1 / 2 : ℝ) *
    (200 * (q : ℝ) ^ 2) * (U + 1)
  let G : ℝ → ℝ := fun B =>
    K * Real.exp C * ((B + C) ^ 3 * Real.exp (-(B + C)))
  have hshift : Tendsto (fun B : ℝ => B + C) atTop atTop :=
    tendsto_atTop_add_const_right atTop C tendsto_id
  have hpoly : Tendsto (fun B : ℝ =>
      (B + C) ^ 3 * Real.exp (-(B + C))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).comp hshift
  have hG : Tendsto G atTop (𝓝 0) := by
    have := (hpoly.const_mul (K * Real.exp C))
    simpa [G] using this
  apply squeeze_zero' (g := G)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
    unfold horizontalEnvelope
    positivity
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
    have hC : 1 ≤ C := by dsimp [C]; nlinarith [abs_nonneg rho.im]
    have hbase : 0 ≤ C + B := by linarith
    have hone : 1 + B ≤ C + B := by linarith
    have hpow : (1 + B) * (C + B) ^ 2 ≤ (C + B) ^ 3 := by
      calc
        (1 + B) * (C + B) ^ 2 ≤ (C + B) * (C + B) ^ 2 :=
          mul_le_mul_of_nonneg_right hone (sq_nonneg (C + B))
        _ = (C + B) ^ 3 := by ring
    have hK : 0 ≤ K := by dsimp [K]; positivity
    have hexp : 0 ≤ Real.exp (-B) := Real.exp_pos _ |>.le
    have hrewrite : Real.exp C * Real.exp (-(B + C)) = Real.exp (-B) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      horizontalEnvelope q U rho Y B =
          K * ((1 + B) * (C + B) ^ 2 * Real.exp (-B)) := by
        dsimp [horizontalEnvelope, C, K]
        ring
      _ ≤ K * ((C + B) ^ 3 * Real.exp (-B)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpow hexp) hK
      _ = G B := by
        rw [← hrewrite]
        dsimp [G]
        ring
  · exact hG


/-- Upper horizontal side tends to zero for the literal detector rectangle. -/
theorem tendsto_upper_horizontal_zero
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {rho : ℂ} (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    (U : ℕ) {Y : ℝ} (hY : 1 ≤ Y) :
    Tendsto (fun B : ℝ =>
      ∫ x : ℝ in (1 / 2 - rho.re)..(1 / 2),
        MAPAppendixA4Detector.regularizedDetectorIntegrand chi rho U Y
          (x + B * I)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let W : ℝ := |(1 / 2 : ℝ) - (1 / 2 - rho.re)|
  have henv := (tendsto_horizontalEnvelope_zero q U rho hY).mul_const W
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun B => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with B hB
    exact MAPAppendixA4Detector.horizontal_segment_norm_le
      (MAPAppendixA4Detector.regularizedDetectorIntegrand chi rho U Y)
      (B := B) (M := horizontalEnvelope q U rho Y B)
      (fun x hx => norm_regularized_upper_le_envelope chi hchi hrho
        hbetaLow hbetaHigh U hY hB hx)
  · simpa [W] using henv

/-- Lower horizontal side tends to zero for the literal detector rectangle. -/
theorem tendsto_lower_horizontal_zero
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {rho : ℂ} (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    (U : ℕ) {Y : ℝ} (hY : 1 ≤ Y) :
    Tendsto (fun B : ℝ =>
      ∫ x : ℝ in (1 / 2 - rho.re)..(1 / 2),
        MAPAppendixA4Detector.regularizedDetectorIntegrand chi rho U Y
          (x - B * I)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let W : ℝ := |(1 / 2 : ℝ) - (1 / 2 - rho.re)|
  have henv := (tendsto_horizontalEnvelope_zero q U rho hY).mul_const W
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun B => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with B hB
    simpa [sub_eq_add_neg] using
      (MAPAppendixA4Detector.horizontal_segment_norm_le
        (MAPAppendixA4Detector.regularizedDetectorIntegrand chi rho U Y)
        (B := -B) (M := horizontalEnvelope q U rho Y B)
        (fun x hx => by
          have hx' : x ∈ Set.uIoc (1 / 2 - rho.re) (1 / 2) := by
            simpa only [one_div, sub_eq_add_neg] using hx
          have hbound := norm_regularized_lower_le_envelope chi hchi hrho
            hbetaLow hbetaHigh U hY hB hx'
          simpa [sub_eq_add_neg] using hbound))
  · simpa [W] using henv

/-- Two Gamma recurrences give an integrable fourth-order Cauchy envelope on
the shifted line `-1/2 ≤ Re z < 0`.  This is the global (including `t = 0`)
version needed for the left side of the literal A.4 contour. -/
theorem norm_Gamma_left_vertical_le_inv_sq
    {a t : ℝ} (halo : -(1 / 2 : ℝ) ≤ a) (hahi : a < 0) :
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

/-- The literal Gamma--L--mollifier integrand on the shifted line
`Re z = 1/2-beta` is integrable.  No tail premise is used: two Gamma
recurrences supply `(1+t²)⁻²`, while the certified fixed-strip L-bound costs
only one factor `(1+t²)`. -/
theorem integrable_gammaLeftIntegrand
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {rho : ℂ} (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    (U : ℕ) {Y : ℝ} (hY : 1 ≤ Y) :
    Integrable (gammaLeftIntegrand chi U rho Y) := by
  let a : ℝ := 1 / 2 - rho.re
  let D : ℝ → ℝ := fun t => 1 + t ^ 2
  let Cγ : ℝ :=
    (1 + ((-a) * (a + 1))⁻¹) *
      (Real.Gamma (a + 2) + Real.Gamma (a + 4))
  let C₀ : ℝ := 5 + |rho.im|
  let K : ℝ := Cγ * (400 * (q : ℝ) ^ 2 * C₀ ^ 2) * (U + 1)
  have haLow : -(1 / 2 : ℝ) ≤ a := by dsimp [a]; linarith
  have haHigh : a < 0 := by dsimp [a]; linarith
  have ha1 : 0 < a + 1 := by linarith
  have hc : 0 < (-a) * (a + 1) := mul_pos (neg_pos.mpr haHigh) ha1
  have hCγ : 0 ≤ Cγ := by
    dsimp [Cγ]
    exact mul_nonneg (by positivity) (add_nonneg
      (Real.Gamma_pos_of_pos (by linarith)).le
      (Real.Gamma_pos_of_pos (by linarith)).le)
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hmajor : Integrable (fun t : ℝ => K * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul K
  have hcontinuous : Continuous (gammaLeftIntegrand chi U rho Y) := by
    have hreg : Continuous (fun t : ℝ =>
        MAPAppendixA4Detector.regularizedDetectorIntegrand chi rho U Y
          (a + t * I)) := by
      rw [continuous_iff_continuousAt]
      intro t
      have hstrip : ((a : ℂ) + t * I) ∈
          MAPAppendixA4Detector.contourStrip := by
        change -1 < (((a : ℂ) + t * I).re)
        simp [a]
        linarith
      exact (MAPAppendixA4Detector.analyticAt_regularizedDetectorIntegrand
        chi hchi hYpos hstrip).continuousAt.comp_of_eq (by fun_prop) rfl
    apply hreg.congr
    intro t
    simpa [a] using regularized_eq_gammaLeft chi hrho hbetaLow U Y t
  apply hmajor.mono' hcontinuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => by
    have hD : 0 < D t := by dsimp [D]; positivity
    have hgamma : ‖Complex.Gamma ((a : ℂ) + t * I)‖ ≤
        Cγ * (D t)⁻¹ ^ 2 := by
      exact norm_Gamma_left_vertical_le_inv_sq haLow haHigh
    have hYpow : ‖(Y : ℂ) ^ ((a : ℂ) + t * I)‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hYpos]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul,
        sub_zero, add_zero]
      exact Real.rpow_le_one_of_one_le_of_nonpos hY haHigh.le
    have hslo : -1 ≤ (rho + ((a : ℂ) + t * I)).re := by
      simp [a]
      norm_num
    have hshi : (rho + ((a : ℂ) + t * I)).re ≤ 2 := by
      simp [a]
      norm_num
    have hL0 := PLInteriorGrowth.norm_LFunction_fixedStrip_le chi hchi hslo hshi
    have him : |(rho + ((a : ℂ) + t * I) + 3).im| ≤
        |rho.im| + |t| := by
      simp
      exact abs_add_le rho.im t
    have hre : |(rho + ((a : ℂ) + t * I) + 3).re| ≤ 5 := by
      simp [a]
      norm_num
    have hnormshift : ‖rho + ((a : ℂ) + t * I) + 3‖ ≤
        C₀ * (1 + |t|) := by
      calc
        ‖rho + ((a : ℂ) + t * I) + 3‖ ≤
            |(rho + ((a : ℂ) + t * I) + 3).re| +
              |(rho + ((a : ℂ) + t * I) + 3).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        _ ≤ 5 + (|rho.im| + |t|) := add_le_add hre him
        _ ≤ C₀ * (1 + |t|) := by
          dsimp [C₀]
          nlinarith [abs_nonneg rho.im, abs_nonneg t]
    have habspoly : (1 + |t|) ^ 2 ≤ 2 * D t := by
      dsimp [D]
      have habssq : |t| ^ 2 = t ^ 2 := sq_abs t
      nlinarith [sq_nonneg (|t| - 1)]
    have hL : ‖DirichletCharacter.LFunction chi
        (rho + ((a : ℂ) + t * I))‖ ≤
        (400 * (q : ℝ) ^ 2 * C₀ ^ 2) * D t := by
      calc
        ‖DirichletCharacter.LFunction chi
            (rho + ((a : ℂ) + t * I))‖ ≤
            200 * (q : ℝ) ^ 2 *
              ‖rho + ((a : ℂ) + t * I) + 3‖ ^ 2 := hL0
        _ ≤ 200 * (q : ℝ) ^ 2 * (C₀ * (1 + |t|)) ^ 2 := by
          gcongr
        _ = (200 * (q : ℝ) ^ 2 * C₀ ^ 2) * (1 + |t|) ^ 2 := by ring
        _ ≤ (200 * (q : ℝ) ^ 2 * C₀ ^ 2) * (2 * D t) := by
          gcongr
        _ = (400 * (q : ℝ) ^ 2 * C₀ ^ 2) * D t := by ring
    have hsnonneg : 0 ≤ (rho + ((a : ℂ) + t * I)).re := by
      simp [a]
    have hM := norm_mollifier_le_card chi U hsnonneg
    unfold gammaLeftIntegrand MAPMellinDetectorLeaf.gammaMellinWeight
    dsimp only
    rw [norm_mul, norm_mul, norm_mul]
    calc
      ‖Complex.Gamma ((a : ℂ) + t * I)‖ *
          ‖(Y : ℂ) ^ ((a : ℂ) + t * I)‖ *
          ‖DirichletCharacter.LFunction chi
            (rho + ((a : ℂ) + t * I))‖ *
          ‖mollifier chi U (rho + ((a : ℂ) + t * I))‖
          ≤ (Cγ * (D t)⁻¹ ^ 2) * 1 *
              ((400 * (q : ℝ) ^ 2 * C₀ ^ 2) * D t) * (U + 1) := by
            gcongr
      _ = K * (1 + t ^ 2)⁻¹ := by
        dsimp [K, D]
        field_simp

/-- Literal Appendix (A.4), with every contour and tail obligation discharged.
The right side is exactly the shifted line `Re z = 1/2-beta`, in the
`(2π)⁻¹ dt = (2πi)⁻¹ dz` normalization of the manuscript. -/
theorem literal_A4_full_identity
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {U : ℕ} (hU : 1 ≤ U) {rho : ℂ}
    (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y : ℝ} (hY : 1 ≤ Y) :
    (Real.exp (-(1 / Y)) : ℂ) +
        ∑' n : {n // n ∉ Finset.range (U + 1)},
          arithmeticDetectorTerm chi U rho Y n =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, gammaLeftIntegrand chi U rho Y t) := by
  exact literal_A4_full_identity_of_left_integrable_horizontal_decay
    chi hchi hU hrho hbetaLow hbetaHigh
    (lt_of_lt_of_le zero_lt_one hY)
    (integrable_gammaLeftIntegrand chi hchi hrho hbetaLow hbetaHigh U hY)
    (tendsto_lower_horizontal_zero chi hchi hrho hbetaLow hbetaHigh U hY)
    (tendsto_upper_horizontal_zero chi hchi hrho hbetaLow hbetaHigh U hY)

end
end MAPAppendixA4GammaTails

#print axioms MAPAppendixA4GammaTails.norm_mollifier_le_card
#print axioms MAPAppendixA4GammaTails.norm_Gamma_left_vertical_le_inv_sq
#print axioms MAPAppendixA4GammaTails.integrable_gammaLeftIntegrand
#print axioms MAPAppendixA4GammaTails.tendsto_upper_horizontal_zero
#print axioms MAPAppendixA4GammaTails.tendsto_lower_horizontal_zero
#print axioms MAPAppendixA4GammaTails.literal_A4_full_identity
