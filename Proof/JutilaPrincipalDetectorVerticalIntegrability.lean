import JutilaPrincipalDetectorInfiniteShift
import JutilaLemma6SieveCoefficientBridge
import JutilaPseudocharacterHarmonicLower
import GammaCompactStrip
import GammaCompactStripSharp
import JutilaPolynomialExponentialIntegral

/-!
# Vertical integrability of the conductor-one Lemma 6 detector

The infinite-height one-pole identity in
`JutilaPrincipalDetectorInfiniteShift` takes integrability of both vertical
sides as hypotheses.  This module discharges those hypotheses for an
arbitrary finite mollifier, and therefore for the canonical sieve.

The L-factor is zeta.  Polynomial growth of `(s-1)ζ(s)` on the fixed strip,
together with the exponential Gamma envelope, is enough for integrability.
Nonprincipal convexity theorems are not applied to `χ = 1`.
-/

namespace MAPJutilaPrincipalDetectorVerticalIntegrability

open Complex Real MeasureTheory Set Filter Topology
open MAPJutilaPrincipalDetectorInfiniteShift
open MAPJutilaPrincipalDetectorFinitePole
open MAPJutilaLemma6FiniteContour
open MAPJutilaLemma6SieveCoefficientBridge
open MAPJutilaPseudocharacterHarmonicLower
open MAPJutilaMEntire
open MAPJutilaMNonnegativeHalfPlaneBound
open MAPPrincipalZetaFixedStrip
open MAPGammaCompactStripSharp
open JutilaPolynomialExponentialIntegral

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)
local notation "principalF" => MAPPrincipalZetaFixedStrip.principalRegularized

/-- Undo the entire regularization at a definite distance from the pole. -/
theorem norm_riemannZeta_of_dist
    {s : ℂ} (hslo : -1 ≤ s.re) (hshi : s.re ≤ 2)
    {δ : ℝ} (hδ : 0 < δ) (hs1 : δ ≤ ‖s - 1‖) :
    ‖riemannZeta s‖ ≤ (1600 / δ) * ‖s + 3‖ ^ 6 := by
  have hsne : s ≠ 1 := by
    intro h
    subst s
    simp at hs1
    linarith
  have hreg :=
    MAPPrincipalZetaFixedStrip.norm_principalRegularized_fixedStrip_le hslo hshi
  have heq :=
    MAPPrincipalZetaFixedStrip.principalRegularized_apply_of_ne_one hsne
  rw [heq, norm_mul] at hreg
  have hden : 0 < ‖s - 1‖ := lt_of_lt_of_le hδ hs1
  have hinv : (‖s - 1‖)⁻¹ ≤ δ⁻¹ :=
    (inv_le_inv₀ hden hδ).2 hs1
  calc
    ‖riemannZeta s‖ =
        (‖s - 1‖)⁻¹ * (‖s - 1‖ * ‖riemannZeta s‖) := by
      field_simp [hden.ne']
    _ ≤ δ⁻¹ * (1600 * ‖s + 3‖ ^ 6) := by
      gcongr
    _ = (1600 * δ⁻¹) * ‖s + 3‖ ^ 6 := by ring
    _ = (1600 / δ) * ‖s + 3‖ ^ 6 := by rw [div_eq_mul_inv]

/-- Two recurrences place `Re = -β` inside the certified positive Gamma strip. -/
theorem norm_Gamma_principal_leftLine_le
    {beta u : ℝ} (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1) :
    ‖Complex.Gamma (((-beta : ℝ) : ℂ) + u * I)‖ ≤
      (15 / (1 - beta)) * (1 + |u|) *
        Real.exp (-(Real.pi / 2) * |u|) := by
  let z : ℂ := ((-beta : ℝ) : ℂ) + u * I
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
    have h1 := Complex.Gamma_add_one z hz
    have h2 := Complex.Gamma_add_one (z + 1) hz1
    calc
      Complex.Gamma (z + 2) = Complex.Gamma ((z + 1) + 1) := by ring_nf
      _ = (z + 1) * Complex.Gamma (z + 1) := h2
      _ = (z + 1) * (z * Complex.Gamma z) := by rw [h1]
      _ = (z + 1) * z * Complex.Gamma z := by ring
  have hnorm : ‖Complex.Gamma (z + 2)‖ =
      ‖z + 1‖ * ‖z‖ * ‖Complex.Gamma z‖ := by
    rw [hrec, norm_mul, norm_mul]
  have hshift : ‖Complex.Gamma (z + 2)‖ ≤
      12 * (1 + |u|) * Real.exp (-(Real.pi / 2) * |u|) := by
    have hp := norm_Gamma_positive_strip_le_exp_pi_half
      (a := 2 - beta) (t := u)
      (by linarith : (1 / 2 : ℝ) ≤ 2 - beta)
      (by linarith : 2 - beta ≤ 3 / 2)
    have heq : z + 2 =
        GammaCompactStripScratch.stripPoint (2 - beta) u := by
      apply Complex.ext <;> simp [z, GammaCompactStripScratch.stripPoint]
      ring
    simpa [heq] using hp
  have hzre : (4 / 5 : ℝ) ≤ ‖z‖ := by
    have h := Complex.abs_re_le_norm z
    have hre : z.re = -beta := by simp [z]
    have habs : |z.re| = beta := by
      rw [hre, abs_of_nonpos (by linarith)]
      ring
    rw [habs] at h
    linarith
  have hz1re : 1 - beta ≤ ‖z + 1‖ := by
    have h := Complex.abs_re_le_norm (z + 1)
    have hre : (z + 1).re = 1 - beta := by simp [z]; ring
    rw [hre, abs_of_nonneg (by linarith)] at h
    exact h
  have hden : 0 < ‖z‖ * ‖z + 1‖ :=
    mul_pos (norm_pos_iff.mpr hz) (norm_pos_iff.mpr hz1)
  have hdiv : ‖Complex.Gamma z‖ =
      ‖Complex.Gamma (z + 2)‖ / (‖z‖ * ‖z + 1‖) := by
    apply eq_div_of_mul_eq hden.ne'
    calc
      ‖Complex.Gamma z‖ * (‖z‖ * ‖z + 1‖) =
          ‖z + 1‖ * ‖z‖ * ‖Complex.Gamma z‖ := by ring
      _ = ‖Complex.Gamma (z + 2)‖ := hnorm.symm
  have hdenLo : (4 / 5 : ℝ) * (1 - beta) ≤ ‖z‖ * ‖z + 1‖ :=
    mul_le_mul hzre hz1re (by linarith) (norm_nonneg _)
  have hconst :
      (12 : ℝ) / ((4 / 5) * (1 - beta)) = 15 / (1 - beta) := by
    rw [← div_div, show (12 : ℝ) / (4 / 5) = 15 by norm_num]
  have hgap : 0 < 1 - beta := by linarith
  calc
    ‖Complex.Gamma z‖ =
        ‖Complex.Gamma (z + 2)‖ / (‖z‖ * ‖z + 1‖) := hdiv
    _ ≤ (12 * (1 + |u|) * Real.exp (-(Real.pi / 2) * |u|)) /
          (‖z‖ * ‖z + 1‖) := by gcongr
    _ ≤ (12 * (1 + |u|) * Real.exp (-(Real.pi / 2) * |u|)) /
          ((4 / 5) * (1 - beta)) := by
      apply div_le_div_of_nonneg_left
      · positivity
      · positivity
      · exact hdenLo
    _ = ((12 : ℝ) / ((4 / 5) * (1 - beta))) *
          ((1 + |u|) * Real.exp (-(Real.pi / 2) * |u|)) := by ring
    _ = (15 / (1 - beta)) * (1 + |u|) *
          Real.exp (-(Real.pi / 2) * |u|) := by
      rw [hconst]
      ring

theorem norm_Gamma_principal_rightLine_le (u : ℝ) :
    ‖Complex.Gamma ((1 : ℂ) + u * I)‖ ≤
      12 * (1 + |u|) * Real.exp (-(Real.pi / 2) * |u|) := by
  have hp := norm_Gamma_positive_strip_le_exp_pi_half
    (a := 1) (t := u) (by norm_num) (by norm_num)
  have heq : (1 : ℂ) + u * I =
      GammaCompactStripScratch.stripPoint 1 u := by
    apply Complex.ext <;> simp [GammaCompactStripScratch.stripPoint]
  simpa [heq] using hp

private theorem exp_pi_half_le_exp_neg (u : ℝ) :
    Real.exp (-(Real.pi / 2) * |u|) ≤ Real.exp (-|u|) := by
  apply Real.exp_le_exp.mpr
  nlinarith [Real.pi_gt_three, abs_nonneg u]

private theorem one_add_height_factor (t u : ℝ) :
    5 + |t| + |u| ≤ (5 + |t|) * (1 + |u|) := by
  nlinarith [abs_nonneg t, abs_nonneg u]

/-- Pointwise left-line envelope.  The factor `(1-β)⁻¹` records the distance
from `Re = -β` to the Gamma pole at `-1`. -/
theorem norm_principal_detector_left_le
    {beta t : ℝ} (xi : ℕ → ℂ) {D : Finset ℕ}
    (hDpos : ∀ d ∈ D, 0 < d) (S : Finset ℕ)
    {X C u : ℝ} (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hM : ∀ s : ℂ, 0 ≤ s.re →
      ‖jutilaMWeightedSumComplex chiOne xi D S s‖ ≤ C)
    (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0) :
    ‖jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        xi D S X (((-beta : ℝ) : ℂ) + u * I)‖ ≤
      (24000 / (1 - beta)) * (5 + |t|) ^ 6 *
        Real.rpow X (-beta) * C *
        ((1 + |u|) ^ 7 * Real.exp (-|u|)) := by
  let rho : ℂ := lemmaSixZeroPoint beta t
  let z : ℂ := ((-beta : ℝ) : ℂ) + u * I
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hrho1 : rho ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [rho, lemmaSixZeroPoint] at hre
    linarith
  have hz : z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [z] at hre
    linarith
  have hLrho :
      DirichletCharacter.LFunction chiOne rho = 0 :=
    LFunction_chiOne_eq_zero_of_principalRegularized hrho hrho1
  rw [jutilaDetectorExtension_eq_raw chiOne xi D S X hLrho hz]
  have hG := norm_Gamma_principal_leftLine_le (u := u) hbetaLo hbetaHi
  have hPow : ‖(X : ℂ) ^ z‖ = Real.rpow X (-beta) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hXpos]
    simp [z]
  let s : ℂ := rho + z
  have hslo : -1 ≤ s.re := by simp [s, rho, z, lemmaSixZeroPoint]
  have hshi : s.re ≤ 2 := by simp [s, rho, z, lemmaSixZeroPoint]
  have hs1 : (1 : ℝ) ≤ ‖s - 1‖ := by
    have hre : (s - 1).re = -1 := by
      simp [s, rho, z, lemmaSixZeroPoint]
    have h := Complex.abs_re_le_norm (s - 1)
    rw [hre, abs_of_nonpos (by norm_num)] at h
    norm_num at h
    exact h
  have hzBound :=
    norm_riemannZeta_of_dist hslo hshi (δ := 1) (by norm_num) hs1
  have hznorm : ‖s + 3‖ ≤ 5 + |t| + |u| := by
    have hre : (s + 3).re = 3 := by
      simp [s, rho, z, lemmaSixZeroPoint]
    have him : (s + 3).im = t + u := by
      simp [s, rho, z, lemmaSixZeroPoint]
    calc
      ‖s + 3‖ ≤ |(s + 3).re| + |(s + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |3| + |t + u| := by rw [hre, him]
      _ ≤ 5 + |t| + |u| := by
        simp only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
        linarith [abs_add_le t u]
  have hL : ‖DirichletCharacter.LFunction chiOne s‖ ≤
      1600 * (5 + |t| + |u|) ^ 6 := by
    rw [DirichletCharacter.LFunction_modOne_eq]
    have hdiv : (1600 / (1 : ℝ)) = 1600 := by norm_num
    rw [hdiv] at hzBound
    exact hzBound.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hznorm 6) (by positivity))
  have hsRe : 0 ≤ s.re := by simp [s, rho, z, lemmaSixZeroPoint]
  have hm := hM s hsRe
  have hfac := one_add_height_factor t u
  have hXpow : 0 ≤ Real.rpow X (-beta) := Real.rpow_nonneg hXpos.le _
  have hpow6 : (5 + |t| + |u|) ^ 6 ≤
      (5 + |t|) ^ 6 * (1 + |u|) ^ 6 := by
    calc
      (5 + |t| + |u|) ^ 6 ≤ ((5 + |t|) * (1 + |u|)) ^ 6 :=
        pow_le_pow_left₀ (by positivity) hfac 6
      _ = _ := by ring
  have hexp := exp_pi_half_le_exp_neg u
  have hgap : 0 < 1 - beta := by linarith
  simp only [norm_mul, hPow]
  calc
    _ ≤ ((15 / (1 - beta)) * (1 + |u|) *
          Real.exp (-(Real.pi / 2) * |u|)) *
        (1600 * (5 + |t| + |u|) ^ 6) *
        Real.rpow X (-beta) * C := by gcongr
    _ ≤ ((15 / (1 - beta)) * (1 + |u|) * Real.exp (-|u|)) *
        (1600 * ((5 + |t|) ^ 6 * (1 + |u|) ^ 6)) *
        Real.rpow X (-beta) * C := by gcongr
    _ = (24000 / (1 - beta)) * (5 + |t|) ^ 6 *
          Real.rpow X (-beta) * C *
          ((1 + |u|) ^ 7 * Real.exp (-|u|)) := by ring

/-- Pointwise right-line envelope.  The line `Re = 1` stays a definite
margin `β ≥ 4/5` from the zeta pole. -/
theorem norm_principal_detector_right_le
    {beta t : ℝ} (xi : ℕ → ℂ) {D : Finset ℕ}
    (hDpos : ∀ d ∈ D, 0 < d) (S : Finset ℕ)
    {X C u : ℝ} (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hM : ∀ s : ℂ, 0 ≤ s.re →
      ‖jutilaMWeightedSumComplex chiOne xi D S s‖ ≤ C)
    (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0) :
    ‖jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        xi D S X ((1 : ℂ) + u * I)‖ ≤
      24000 * (5 + |t|) ^ 6 * X * C *
        ((1 + |u|) ^ 7 * Real.exp (-|u|)) := by
  let rho : ℂ := lemmaSixZeroPoint beta t
  let z : ℂ := (1 : ℂ) + u * I
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hrho1 : rho ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [rho, lemmaSixZeroPoint] at hre
    linarith
  have hz : z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [z] at hre
  have hLrho :
      DirichletCharacter.LFunction chiOne rho = 0 :=
    LFunction_chiOne_eq_zero_of_principalRegularized hrho hrho1
  rw [jutilaDetectorExtension_eq_raw chiOne xi D S X hLrho hz]
  have hG := norm_Gamma_principal_rightLine_le u
  have hPow : ‖(X : ℂ) ^ z‖ = X := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hXpos]
    simp [z]
  let s : ℂ := rho + z
  have hslo : -1 ≤ s.re := by simp [s, rho, z, lemmaSixZeroPoint]; linarith
  have hshi : s.re ≤ 2 := by simp [s, rho, z, lemmaSixZeroPoint]; linarith
  have hs1 : (4 / 5 : ℝ) ≤ ‖s - 1‖ := by
    have hre : (s - 1).re = beta := by
      simp [s, rho, z, lemmaSixZeroPoint]
    have h := Complex.abs_re_le_norm (s - 1)
    rw [hre, abs_of_nonneg (by linarith)] at h
    exact h.trans' hbetaLo
  have hzBound :=
    norm_riemannZeta_of_dist hslo hshi (δ := 4 / 5) (by norm_num) hs1
  have hznorm : ‖s + 3‖ ≤ 5 + |t| + |u| := by
    have hre : (s + 3).re = beta + 4 := by
      simp [s, rho, z, lemmaSixZeroPoint]
      ring
    have him : (s + 3).im = t + u := by
      simp [s, rho, z, lemmaSixZeroPoint]
    calc
      ‖s + 3‖ ≤ |(s + 3).re| + |(s + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |beta + 4| + |t + u| := by rw [hre, him]
      _ ≤ 5 + |t| + |u| := by
        rw [abs_of_nonneg (by linarith : 0 ≤ beta + 4)]
        linarith [abs_add_le t u]
  have hL : ‖DirichletCharacter.LFunction chiOne s‖ ≤
      2000 * (5 + |t| + |u|) ^ 6 := by
    rw [DirichletCharacter.LFunction_modOne_eq]
    have hdiv : 1600 / (4 / 5 : ℝ) = 2000 := by norm_num
    rw [hdiv] at hzBound
    exact hzBound.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hznorm 6) (by positivity))
  have hsRe : 0 ≤ s.re := by simp [s, rho, z, lemmaSixZeroPoint]; linarith
  have hm := hM s hsRe
  have hfac := one_add_height_factor t u
  have hpow6 : (5 + |t| + |u|) ^ 6 ≤
      (5 + |t|) ^ 6 * (1 + |u|) ^ 6 := by
    calc
      (5 + |t| + |u|) ^ 6 ≤ ((5 + |t|) * (1 + |u|)) ^ 6 :=
        pow_le_pow_left₀ (by positivity) hfac 6
      _ = _ := by ring
  have hexp := exp_pi_half_le_exp_neg u
  simp only [norm_mul, hPow]
  calc
    _ ≤ (12 * (1 + |u|) * Real.exp (-(Real.pi / 2) * |u|)) *
        (2000 * (5 + |t| + |u|) ^ 6) * X * C := by gcongr
    _ ≤ (12 * (1 + |u|) * Real.exp (-|u|)) *
        (2000 * ((5 + |t|) ^ 6 * (1 + |u|) ^ 6)) * X * C := by gcongr
    _ = 24000 * (5 + |t|) ^ 6 * X * C *
          ((1 + |u|) ^ 7 * Real.exp (-|u|)) := by ring

theorem continuous_principal_detector_left
    {beta t : ℝ} (xi : ℕ → ℂ) {D : Finset ℕ}
    (hDpos : ∀ d ∈ D, 0 < d) (S : Finset ℕ)
    {X : ℝ} (hX : 0 < X)
    (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0) :
    Continuous (fun u : ℝ =>
      jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        xi D S X (((-beta : ℝ) : ℂ) + u * I)) := by
  let rho : ℂ := lemmaSixZeroPoint beta t
  have hrho1 : rho ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [rho, lemmaSixZeroPoint] at hre
    linarith
  have hLrho :
      DirichletCharacter.LFunction chiOne rho = 0 :=
    LFunction_chiOne_eq_zero_of_principalRegularized hrho hrho1
  have hG : Continuous (fun u : ℝ =>
      Complex.Gamma (((-beta : ℝ) : ℂ) + u * I)) := by
    rw [continuous_iff_continuousAt]
    intro u
    have hnp : ∀ n : ℕ,
        (((-beta : ℝ) : ℂ) + (u : ℂ) * I) ≠ -(n : ℂ) := by
      intro n hn
      have hre := congrArg Complex.re hn
      simp [Complex.neg_re] at hre
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rcases n with _ | n
      · norm_num at hre
        linarith
      · have : (1 : ℝ) ≤ Nat.succ n := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        linarith
    have hadd : ContinuousAt (fun z : ℂ =>
        (((-beta : ℝ) : ℂ) + z)) ((u : ℂ) * I) := by fun_prop
    have hgamma : ContinuousAt (fun z : ℂ =>
        Complex.Gamma (((-beta : ℝ) : ℂ) + z)) ((u : ℂ) * I) :=
      (Complex.continuousAt_Gamma _ hnp).comp' hadd
    have hpath : ContinuousAt (fun v : ℝ => (v : ℂ) * I) u := by fun_prop
    have htmp := hgamma.comp_of_eq hpath (by rfl)
    simpa [Function.comp_def] using htmp
  have hL : Continuous (fun u : ℝ =>
      DirichletCharacter.LFunction chiOne
        (rho + (((-beta : ℝ) : ℂ) + u * I))) := by
    rw [continuous_iff_continuousAt]
    intro u
    have hz1 : rho + (((-beta : ℝ) : ℂ) + (u : ℂ) * I) ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      simp [rho, lemmaSixZeroPoint] at hre
    have hinner : ContinuousAt (fun v : ℝ =>
        rho + (((-beta : ℝ) : ℂ) + v * I)) u := by fun_prop
    exact ContinuousAt.comp
      (f := fun v : ℝ => rho + (((-beta : ℝ) : ℂ) + v * I))
      (g := DirichletCharacter.LFunction chiOne) (x := u)
      (DirichletCharacter.differentiableAt_LFunction
        chiOne _ (Or.inl hz1)).continuousAt hinner
  have hpow : Continuous (fun u : ℝ =>
      (X : ℂ) ^ (((-beta : ℝ) : ℂ) + u * I)) :=
    (differentiable_id.const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).continuous.comp
      (by fun_prop)
  have hMc : Continuous (fun u : ℝ =>
      jutilaMWeightedSumComplex chiOne xi D S
        (rho + (((-beta : ℝ) : ℂ) + u * I))) :=
    (differentiable_jutilaMWeightedSumComplex chiOne xi hDpos S).continuous.comp
      (by fun_prop)
  have hfun : (fun u : ℝ =>
      jutilaDetectorExtension chiOne rho xi D S X
        (((-beta : ℝ) : ℂ) + u * I)) =
      fun u : ℝ =>
        Complex.Gamma (((-beta : ℝ) : ℂ) + u * I) *
          DirichletCharacter.LFunction chiOne
            (rho + (((-beta : ℝ) : ℂ) + u * I)) *
          (X : ℂ) ^ (((-beta : ℝ) : ℂ) + u * I) *
          jutilaMWeightedSumComplex chiOne xi D S
            (rho + (((-beta : ℝ) : ℂ) + u * I)) := by
    funext u
    have hz : (((-beta : ℝ) : ℂ) + u * I) ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    exact jutilaDetectorExtension_eq_raw chiOne xi D S X hLrho hz
  rw [hfun]
  exact ((hG.mul hL).mul hpow).mul hMc

theorem continuous_principal_detector_right
    {beta t : ℝ} (xi : ℕ → ℂ) {D : Finset ℕ}
    (hDpos : ∀ d ∈ D, 0 < d) (S : Finset ℕ)
    {X : ℝ} (hX : 0 < X)
    (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0) :
    Continuous (fun u : ℝ =>
      jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        xi D S X ((1 : ℂ) + u * I)) := by
  let rho : ℂ := lemmaSixZeroPoint beta t
  have hrho1 : rho ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [rho, lemmaSixZeroPoint] at hre
    linarith
  have hLrho :
      DirichletCharacter.LFunction chiOne rho = 0 :=
    LFunction_chiOne_eq_zero_of_principalRegularized hrho hrho1
  have hG : Continuous (fun u : ℝ => Complex.Gamma ((1 : ℂ) + u * I)) := by
    rw [continuous_iff_continuousAt]
    intro u
    have hnp : ∀ n : ℕ, (1 : ℂ) + (u : ℂ) * I ≠ -(n : ℂ) := by
      intro n hn
      have hre := congrArg Complex.re hn
      simp [Complex.neg_re] at hre
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hadd : ContinuousAt (fun z : ℂ => (1 : ℂ) + z) ((u : ℂ) * I) := by
      fun_prop
    have hgamma : ContinuousAt (fun z : ℂ =>
        Complex.Gamma ((1 : ℂ) + z)) ((u : ℂ) * I) :=
      (Complex.continuousAt_Gamma _ hnp).comp' hadd
    have hpath : ContinuousAt (fun v : ℝ => (v : ℂ) * I) u := by fun_prop
    have htmp := hgamma.comp_of_eq hpath (by rfl)
    simpa [Function.comp_def] using htmp
  have hL : Continuous (fun u : ℝ =>
      DirichletCharacter.LFunction chiOne (rho + ((1 : ℂ) + u * I))) := by
    rw [continuous_iff_continuousAt]
    intro u
    have hz1 : rho + ((1 : ℂ) + (u : ℂ) * I) ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      simp [rho, lemmaSixZeroPoint] at hre
      linarith
    have hinner : ContinuousAt (fun v : ℝ =>
        rho + ((1 : ℂ) + v * I)) u := by fun_prop
    exact ContinuousAt.comp
      (f := fun v : ℝ => rho + ((1 : ℂ) + v * I))
      (g := DirichletCharacter.LFunction chiOne) (x := u)
      (DirichletCharacter.differentiableAt_LFunction
        chiOne _ (Or.inl hz1)).continuousAt hinner
  have hpow : Continuous (fun u : ℝ => (X : ℂ) ^ ((1 : ℂ) + u * I)) :=
    (differentiable_id.const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).continuous.comp
      (by fun_prop)
  have hMc : Continuous (fun u : ℝ =>
      jutilaMWeightedSumComplex chiOne xi D S (rho + ((1 : ℂ) + u * I))) :=
    (differentiable_jutilaMWeightedSumComplex chiOne xi hDpos S).continuous.comp
      (by fun_prop)
  have hfun : (fun u : ℝ =>
      jutilaDetectorExtension chiOne rho xi D S X ((1 : ℂ) + u * I)) =
      fun u : ℝ =>
        Complex.Gamma ((1 : ℂ) + u * I) *
          DirichletCharacter.LFunction chiOne (rho + ((1 : ℂ) + u * I)) *
          (X : ℂ) ^ ((1 : ℂ) + u * I) *
          jutilaMWeightedSumComplex chiOne xi D S
            (rho + ((1 : ℂ) + u * I)) := by
    funext u
    have hz : (1 : ℂ) + u * I ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
    exact jutilaDetectorExtension_eq_raw chiOne xi D S X hLrho hz
  simpa [hfun, rho] using! ((hG.mul hL).mul hpow).mul hMc

theorem integrable_principal_detector_left
    {beta t : ℝ} (xi : ℕ → ℂ) {D : Finset ℕ}
    (hDpos : ∀ d ∈ D, 0 < d) (S : Finset ℕ)
    {X : ℝ} (hX : 1 ≤ X)
    (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0) :
    Integrable (fun u : ℝ =>
      jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        xi D S X (((-beta : ℝ) : ℂ) + u * I)) := by
  obtain ⟨C, hC, hM⟩ :=
    exists_jutilaMWeightedSumComplex_bound chiOne xi hDpos S
  let K : ℝ := (24000 / (1 - beta)) * (5 + |t|) ^ 6 *
    Real.rpow X (-beta) * C
  have hgap : 0 < 1 - beta := by linarith
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hEbase : Integrable (fun u : ℝ =>
      (1 + |u|) ^ 7 * Real.exp (-|u|)) := by
    have h := integrable_shiftedAbsPowExp
      (A := 1) (k := 7) (c := 1) (by norm_num) (by norm_num)
    convert h using 1
    ext u
    simp [shiftedAbsPowExp]
  have hE : Integrable (fun u : ℝ => K * ((1 + |u|) ^ 7 * Real.exp (-|u|))) :=
    hEbase.const_mul K
  apply hE.mono'
  · exact (continuous_principal_detector_left xi hDpos S
      (zero_lt_one.trans_le hX) hbetaLo hbetaHi hrho).aestronglyMeasurable
  · filter_upwards with u
    simpa [K] using
      norm_principal_detector_left_le xi hDpos S hX hC hM
        hbetaLo hbetaHi hrho (u := u)

theorem integrable_principal_detector_right
    {beta t : ℝ} (xi : ℕ → ℂ) {D : Finset ℕ}
    (hDpos : ∀ d ∈ D, 0 < d) (S : Finset ℕ)
    {X : ℝ} (hX : 1 ≤ X)
    (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0) :
    Integrable (fun u : ℝ =>
      jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        xi D S X ((1 : ℂ) + u * I)) := by
  obtain ⟨C, hC, hM⟩ :=
    exists_jutilaMWeightedSumComplex_bound chiOne xi hDpos S
  let K : ℝ := 24000 * (5 + |t|) ^ 6 * X * C
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hEbase : Integrable (fun u : ℝ =>
      (1 + |u|) ^ 7 * Real.exp (-|u|)) := by
    have h := integrable_shiftedAbsPowExp
      (A := 1) (k := 7) (c := 1) (by norm_num) (by norm_num)
    convert h using 1
    ext u
    simp [shiftedAbsPowExp]
  have hE : Integrable (fun u : ℝ => K * ((1 + |u|) ^ 7 * Real.exp (-|u|))) :=
    hEbase.const_mul K
  apply hE.mono'
  · exact (continuous_principal_detector_right xi hDpos S
      (zero_lt_one.trans_le hX) hbetaLo hbetaHi hrho).aestronglyMeasurable
  · filter_upwards with u
    simpa [K] using
      norm_principal_detector_right_le xi hDpos S hX hC hM
        hbetaLo hbetaHi hrho (u := u)

/-- Canonical-mollifier left vertical line. -/
theorem integrable_principal_canonical_left
    {beta t z1 z2 : ℝ} {R : ℕ} {X : ℝ}
    (hX : 1 ≤ X) (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0) :
    Integrable (fun u : ℝ =>
      jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        (jutilaLambdaComplex z1 z2) (jutilaLambdaSupport z2)
        (jutilaPrimedRSet 1 R) X (((-beta : ℝ) : ℂ) + u * I)) :=
  integrable_principal_detector_left
    (jutilaLambdaComplex z1 z2)
    (fun d hd => (Finset.mem_Icc.mp hd).1)
    (jutilaPrimedRSet 1 R) hX hbetaLo hbetaHi hrho

/-- Canonical-mollifier right vertical line. -/
theorem integrable_principal_canonical_right
    {beta t z1 z2 : ℝ} {R : ℕ} {X : ℝ}
    (hX : 1 ≤ X) (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0) :
    Integrable (fun u : ℝ =>
      jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        (jutilaLambdaComplex z1 z2) (jutilaLambdaSupport z2)
        (jutilaPrimedRSet 1 R) X ((1 : ℂ) + u * I)) :=
  integrable_principal_detector_right
    (jutilaLambdaComplex z1 z2)
    (fun d hd => (Finset.mem_Icc.mp hd).1)
    (jutilaPrimedRSet 1 R) hX hbetaLo hbetaHi hrho

end

end MAPJutilaPrincipalDetectorVerticalIntegrability

#print axioms MAPJutilaPrincipalDetectorVerticalIntegrability.integrable_principal_detector_left
#print axioms MAPJutilaPrincipalDetectorVerticalIntegrability.integrable_principal_detector_right
#print axioms MAPJutilaPrincipalDetectorVerticalIntegrability.integrable_principal_canonical_left
#print axioms MAPJutilaPrincipalDetectorVerticalIntegrability.integrable_principal_canonical_right
