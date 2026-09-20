import JutilaPrincipalDetectorVerticalIntegrability
import JutilaPrincipalDetectorFinitePole
import JutilaPrincipalShiftedErrorBound
import JutilaLemma6SieveCoefficientBridge
import JutilaLemma6DirectTail
import JutilaPseudocharacterHarmonicLower

/-!
# One-pole identity with left line at `Re z = -β + ε`

Square-root convexity for zeta is certified only on `ε ≤ Re s ≤ 3ε`.
The classical Lemma 6 left line `Re z = -β` places `ρ+z` on `Re = 0`,
outside that strip.  Shifting the left abscissa to `-β+ε` places the
L-factor at `Re = ε` while remaining strictly left of the crossed pole
`z = 1-ρ` and of the removable point `z = 0`.

The shift parameter is the fixed positive number `1/500`, small enough
that the Mellin factor `X^ε` is absorbed by the collar power saving at
`δ = 1/280` (see `JutilaPrincipalEpsilonRemainder`).
-/

namespace MAPJutilaPrincipalEpsilonShiftedContour

open Complex Real MeasureTheory Set Filter Topology
open MAPJutilaPrincipalDetectorVerticalIntegrability
open MAPJutilaPrincipalDetectorInfiniteShift
open MAPJutilaPrincipalDetectorFinitePole
open MAPJutilaPrincipalDetectorPole
open MAPJutilaLemma6FiniteContour
open MAPJutilaLemma6SieveCoefficientBridge
open MAPJutilaMEntire
open MAPJutilaMNonnegativeHalfPlaneBound
open MAPJutilaPseudocharacterHarmonicLower
open MAPPrincipalZetaFixedStrip
open MAPPrincipalZetaDetectorPoleRemoval
open MAPGammaCompactStripSharp
open JutilaPolynomialExponentialIntegral
open MAPJutilaLemma6DirectTail

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)
local notation "principalF" => MAPPrincipalZetaFixedStrip.principalRegularized

/-- Fixed positive shift placing `ρ+z` on the square-root convexity strip. -/
def principalSqrtShift : ℝ := 1 / 500

theorem principalSqrtShift_pos : 0 < principalSqrtShift := by
  norm_num [principalSqrtShift]

theorem principalSqrtShift_le_one_eight : principalSqrtShift ≤ 1 / 8 := by
  norm_num [principalSqrtShift]

theorem principalSqrtShift_lt_four_fifths : principalSqrtShift < 4 / 5 := by
  norm_num [principalSqrtShift]

theorem principalSqrtShift_add_one_eight_lt_one :
    principalSqrtShift + (1 / 8 : ℝ) < 1 := by
  norm_num [principalSqrtShift]

def principalEpsilonLeft (beta u : ℝ) : ℂ :=
  ((-beta + principalSqrtShift : ℝ) : ℂ) + u * I

theorem principalEpsilonLeft_re (beta u : ℝ) :
    (principalEpsilonLeft beta u).re = -beta + principalSqrtShift := by
  simp [principalEpsilonLeft]

theorem principalEpsilonLeft_ne_zero
    {beta : ℝ} (hbetaLo : 4 / 5 ≤ beta) (u : ℝ) :
    principalEpsilonLeft beta u ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp [principalEpsilonLeft] at hre
  have : principalSqrtShift < 4 / 5 := principalSqrtShift_lt_four_fifths
  linarith

/-- Two recurrences place `Re = -β+ε` inside the certified positive Gamma strip. -/
theorem norm_Gamma_principal_epsilonLeft_le
    {beta u : ℝ} (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1) :
    ‖Complex.Gamma (principalEpsilonLeft beta u)‖ ≤
      (12 / ((4 / 5 - principalSqrtShift) * principalSqrtShift)) * (1 + |u|) *
        Real.exp (-(Real.pi / 2) * |u|) := by
  let z : ℂ := principalEpsilonLeft beta u
  have hz : z ≠ 0 := principalEpsilonLeft_ne_zero hbetaLo u
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [z, principalEpsilonLeft] at hre
    linarith [principalSqrtShift_pos]
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
      (a := 2 - beta + principalSqrtShift) (t := u)
      (by linarith [principalSqrtShift_pos] : (1 / 2 : ℝ) ≤
        2 - beta + principalSqrtShift)
      (by linarith [principalSqrtShift_le_one_eight] :
        2 - beta + principalSqrtShift ≤ 3 / 2)
    have heq : z + 2 =
        GammaCompactStripScratch.stripPoint
          (2 - beta + principalSqrtShift) u := by
      apply Complex.ext <;> simp [z, principalEpsilonLeft,
        GammaCompactStripScratch.stripPoint]
      ring
    simpa [heq] using hp
  have hzre : (4 / 5 - principalSqrtShift : ℝ) ≤ ‖z‖ := by
    have h := Complex.abs_re_le_norm z
    have hre : z.re = -beta + principalSqrtShift := by
      simp [z, principalEpsilonLeft]
    have habs : |z.re| = beta - principalSqrtShift := by
      rw [hre, abs_of_nonpos]
      · ring
      · linarith [principalSqrtShift_lt_four_fifths]
    rw [habs] at h
    linarith
  have hz1re : principalSqrtShift ≤ ‖z + 1‖ := by
    have h := Complex.abs_re_le_norm (z + 1)
    have hre : (z + 1).re = 1 - beta + principalSqrtShift := by
      simp [z, principalEpsilonLeft]; ring
    have habs : |(z + 1).re| = 1 - beta + principalSqrtShift := by
      rw [hre, abs_of_nonneg]
      linarith [principalSqrtShift_pos]
    rw [habs] at h
    exact (le_add_of_nonneg_left (by linarith : (0 : ℝ) ≤ 1 - beta)).trans h
  have hden : 0 < ‖z‖ * ‖z + 1‖ :=
    mul_pos (norm_pos_iff.mpr hz) (norm_pos_iff.mpr hz1)
  have hdiv : ‖Complex.Gamma z‖ =
      ‖Complex.Gamma (z + 2)‖ / (‖z‖ * ‖z + 1‖) := by
    apply eq_div_of_mul_eq hden.ne'
    calc
      ‖Complex.Gamma z‖ * (‖z‖ * ‖z + 1‖) =
          ‖z + 1‖ * ‖z‖ * ‖Complex.Gamma z‖ := by ring
      _ = ‖Complex.Gamma (z + 2)‖ := hnorm.symm
  have hdenLo : (4 / 5 - principalSqrtShift) * principalSqrtShift ≤
      ‖z‖ * ‖z + 1‖ :=
    mul_le_mul hzre hz1re principalSqrtShift_pos.le (norm_nonneg _)
  have hgap : 0 < (4 / 5 - principalSqrtShift) * principalSqrtShift := by
    apply mul_pos _ principalSqrtShift_pos
    linarith [principalSqrtShift_lt_four_fifths]
  calc
    ‖Complex.Gamma z‖ =
        ‖Complex.Gamma (z + 2)‖ / (‖z‖ * ‖z + 1‖) := hdiv
    _ ≤ (12 * (1 + |u|) * Real.exp (-(Real.pi / 2) * |u|)) /
          (‖z‖ * ‖z + 1‖) := by gcongr
    _ ≤ (12 * (1 + |u|) * Real.exp (-(Real.pi / 2) * |u|)) /
          ((4 / 5 - principalSqrtShift) * principalSqrtShift) := by
      apply div_le_div_of_nonneg_left
      · positivity
      · exact hgap
      · exact hdenLo
    _ = (12 / ((4 / 5 - principalSqrtShift) * principalSqrtShift)) *
          ((1 + |u|) * Real.exp (-(Real.pi / 2) * |u|)) := by ring
    _ = _ := by ring

private theorem exp_pi_half_le_exp_neg (u : ℝ) :
    Real.exp (-(Real.pi / 2) * |u|) ≤ Real.exp (-|u|) := by
  apply Real.exp_le_exp.mpr
  nlinarith [Real.pi_gt_three, abs_nonneg u]

private theorem one_add_height_factor (t u : ℝ) :
    5 + |t| + |u| ≤ (5 + |t|) * (1 + |u|) := by
  nlinarith [abs_nonneg t, abs_nonneg u]

/-- Polynomial envelope on the shifted left line, used only for integrability.
The square-root remainder is proved separately. -/
theorem norm_principal_detector_epsilonLeft_poly_le
    {beta t : ℝ} (xi : ℕ → ℂ) {D : Finset ℕ}
    (hDpos : ∀ d ∈ D, 0 < d) (S : Finset ℕ)
    {X C u : ℝ} (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hM : ∀ s : ℂ, 0 ≤ s.re →
      ‖jutilaMWeightedSumComplex chiOne xi D S s‖ ≤ C)
    (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0) :
    ‖jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        xi D S X (principalEpsilonLeft beta u)‖ ≤
      (12 / ((4 / 5 - principalSqrtShift) * principalSqrtShift)) *
        (1600 / (1 - principalSqrtShift)) * (5 + |t|) ^ 6 *
        Real.rpow X (-beta + principalSqrtShift) * C *
        ((1 + |u|) ^ 7 * Real.exp (-|u|)) := by
  let rho : ℂ := lemmaSixZeroPoint beta t
  let z : ℂ := principalEpsilonLeft beta u
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hrho1 : rho ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [rho, lemmaSixZeroPoint] at hre
    linarith
  have hz : z ≠ 0 := principalEpsilonLeft_ne_zero hbetaLo u
  have hLrho :
      DirichletCharacter.LFunction chiOne rho = 0 :=
    LFunction_chiOne_eq_zero_of_principalRegularized hrho hrho1
  rw [jutilaDetectorExtension_eq_raw chiOne xi D S X hLrho hz]
  have hG := norm_Gamma_principal_epsilonLeft_le (u := u) hbetaLo hbetaHi
  have hPow : ‖(X : ℂ) ^ z‖ = Real.rpow X (-beta + principalSqrtShift) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hXpos]
    simp [z, principalEpsilonLeft]
  let s : ℂ := rho + z
  have hslo : -1 ≤ s.re := by
    simp [s, rho, z, lemmaSixZeroPoint, principalEpsilonLeft]
    linarith [principalSqrtShift_pos]
  have hshi : s.re ≤ 2 := by
    simp [s, rho, z, lemmaSixZeroPoint, principalEpsilonLeft]
    linarith [principalSqrtShift_le_one_eight]
  have hs1 : (1 - principalSqrtShift : ℝ) ≤ ‖s - 1‖ := by
    have hre : (s - 1).re = principalSqrtShift - 1 := by
      simp [s, rho, z, lemmaSixZeroPoint, principalEpsilonLeft]
    have h := Complex.abs_re_le_norm (s - 1)
    have habs : |(s - 1).re| = 1 - principalSqrtShift := by
      rw [hre, abs_of_nonpos]
      · ring
      · linarith [principalSqrtShift_le_one_eight]
    rw [habs] at h
    exact h
  have hzBound :=
    norm_riemannZeta_of_dist hslo hshi
      (δ := 1 - principalSqrtShift)
      (by linarith [principalSqrtShift_le_one_eight]) hs1
  have hznorm : ‖s + 3‖ ≤ 5 + |t| + |u| := by
    have hre : (s + 3).re = 3 + principalSqrtShift := by
      simp [s, rho, z, lemmaSixZeroPoint, principalEpsilonLeft]
      ring
    have him : (s + 3).im = t + u := by
      simp [s, rho, z, lemmaSixZeroPoint, principalEpsilonLeft]
    calc
      ‖s + 3‖ ≤ |(s + 3).re| + |(s + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |3 + principalSqrtShift| + |t + u| := by rw [hre, him]
      _ ≤ 5 + |t| + |u| := by
        rw [abs_of_nonneg (by linarith [principalSqrtShift_pos])]
        linarith [abs_add_le t u, principalSqrtShift_le_one_eight]
  have hL : ‖DirichletCharacter.LFunction chiOne s‖ ≤
      (1600 / (1 - principalSqrtShift)) * (5 + |t| + |u|) ^ 6 := by
    rw [DirichletCharacter.LFunction_modOne_eq]
    have hcoef : 0 ≤ (1600 / (1 - principalSqrtShift) : ℝ) := by
      norm_num [principalSqrtShift]
    exact hzBound.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hznorm 6) hcoef)
  have hsRe : 0 ≤ s.re := by
    simp [s, rho, z, lemmaSixZeroPoint, principalEpsilonLeft]
    exact principalSqrtShift_pos.le
  have hm := hM s hsRe
  have hfac := one_add_height_factor t u
  have hpow6 : (5 + |t| + |u|) ^ 6 ≤
      (5 + |t|) ^ 6 * (1 + |u|) ^ 6 := by
    calc
      (5 + |t| + |u|) ^ 6 ≤ ((5 + |t|) * (1 + |u|)) ^ 6 :=
        pow_le_pow_left₀ (by positivity) hfac 6
      _ = _ := by ring
  have hexp := exp_pi_half_le_exp_neg u
  have hGconst :
      0 ≤ 12 / ((4 / 5 - principalSqrtShift) * principalSqrtShift) := by
    apply div_nonneg (by norm_num)
    apply mul_nonneg
    · linarith [principalSqrtShift_lt_four_fifths]
    · exact principalSqrtShift_pos.le
  have hxp : 0 ≤ Real.rpow X (-beta + principalSqrtShift) :=
    Real.rpow_nonneg (le_of_lt hXpos) _
  have hcoef : 0 ≤ (1600 / (1 - principalSqrtShift) : ℝ) := by
    norm_num [principalSqrtShift]
  simp only [norm_mul, hPow]
  calc
    _ ≤ ((12 / ((4 / 5 - principalSqrtShift) * principalSqrtShift)) *
          (1 + |u|) * Real.exp (-(Real.pi / 2) * |u|)) *
        ((1600 / (1 - principalSqrtShift)) * (5 + |t| + |u|) ^ 6) *
        Real.rpow X (-beta + principalSqrtShift) * C := by
      gcongr
    _ ≤ ((12 / ((4 / 5 - principalSqrtShift) * principalSqrtShift)) *
          (1 + |u|) * Real.exp (-|u|)) *
        ((1600 / (1 - principalSqrtShift)) *
          ((5 + |t|) ^ 6 * (1 + |u|) ^ 6)) *
        Real.rpow X (-beta + principalSqrtShift) * C := by
      gcongr
    _ = (12 / ((4 / 5 - principalSqrtShift) * principalSqrtShift)) *
          (1600 / (1 - principalSqrtShift)) * (5 + |t|) ^ 6 *
          Real.rpow X (-beta + principalSqrtShift) * C *
          ((1 + |u|) ^ 7 * Real.exp (-|u|)) := by ring

theorem continuous_principal_detector_epsilonLeft
    {beta t : ℝ} (xi : ℕ → ℂ) {D : Finset ℕ}
    (hDpos : ∀ d ∈ D, 0 < d) (S : Finset ℕ)
    {X : ℝ} (hX : 0 < X)
    (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0) :
    Continuous (fun u : ℝ =>
      jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        xi D S X (principalEpsilonLeft beta u)) := by
  let rho : ℂ := lemmaSixZeroPoint beta t
  have hrho1 : rho ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [rho, lemmaSixZeroPoint] at hre
    linarith
  have hLrho :
      DirichletCharacter.LFunction chiOne rho = 0 :=
    LFunction_chiOne_eq_zero_of_principalRegularized hrho hrho1
  have hEps : Continuous (fun v : ℝ => principalEpsilonLeft beta v) := by
    unfold principalEpsilonLeft
    fun_prop
  have hG : Continuous (fun u : ℝ =>
      Complex.Gamma (principalEpsilonLeft beta u)) := by
    rw [continuous_iff_continuousAt]
    intro u
    have hnp : ∀ n : ℕ,
        principalEpsilonLeft beta (u : ℝ) ≠ -(n : ℂ) := by
      intro n hn
      have hre := congrArg Complex.re hn
      simp [principalEpsilonLeft, Complex.neg_re] at hre
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rcases n with _ | n
      · simp at hre
        linarith [principalSqrtShift_lt_four_fifths]
      · have : (1 : ℝ) ≤ Nat.succ n := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        linarith [principalSqrtShift_pos]
    exact (Complex.continuousAt_Gamma _ hnp).comp hEps.continuousAt
  have hL : Continuous (fun u : ℝ =>
      DirichletCharacter.LFunction chiOne
        (rho + principalEpsilonLeft beta u)) := by
    rw [continuous_iff_continuousAt]
    intro u
    have hz1 : rho + principalEpsilonLeft beta (u : ℝ) ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      simp [rho, lemmaSixZeroPoint, principalEpsilonLeft] at hre
      linarith [principalSqrtShift_le_one_eight]
    have hinner : ContinuousAt (fun v : ℝ =>
        rho + principalEpsilonLeft beta v) u :=
      continuous_const.continuousAt.add hEps.continuousAt
    exact ContinuousAt.comp
      (f := fun v : ℝ => rho + principalEpsilonLeft beta v)
      (g := DirichletCharacter.LFunction chiOne) (x := u)
      (DirichletCharacter.differentiableAt_LFunction
        chiOne _ (Or.inl hz1)).continuousAt hinner
  have hpow : Continuous (fun u : ℝ =>
      (X : ℂ) ^ principalEpsilonLeft beta u) :=
    (differentiable_id.const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).continuous.comp
      hEps
  have hMc : Continuous (fun u : ℝ =>
      jutilaMWeightedSumComplex chiOne xi D S
        (rho + principalEpsilonLeft beta u)) :=
    (differentiable_jutilaMWeightedSumComplex chiOne xi hDpos S).continuous.comp
      (continuous_const.add hEps)
  have hfun : (fun u : ℝ =>
      jutilaDetectorExtension chiOne rho xi D S X
        (principalEpsilonLeft beta u)) =
      fun u : ℝ =>
        Complex.Gamma (principalEpsilonLeft beta u) *
          DirichletCharacter.LFunction chiOne
            (rho + principalEpsilonLeft beta u) *
          (X : ℂ) ^ principalEpsilonLeft beta u *
          jutilaMWeightedSumComplex chiOne xi D S
            (rho + principalEpsilonLeft beta u) := by
    funext u
    exact jutilaDetectorExtension_eq_raw chiOne xi D S X hLrho
      (principalEpsilonLeft_ne_zero hbetaLo u)
  simpa [hfun, rho] using ((hG.mul hL).mul hpow).mul hMc

theorem integrable_principal_detector_epsilonLeft
    {beta t : ℝ} (xi : ℕ → ℂ) {D : Finset ℕ}
    (hDpos : ∀ d ∈ D, 0 < d) (S : Finset ℕ)
    {X : ℝ} (hX : 1 ≤ X)
    (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0) :
    Integrable (fun u : ℝ =>
      jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        xi D S X (principalEpsilonLeft beta u)) := by
  obtain ⟨C, hC, hM⟩ :=
    exists_jutilaMWeightedSumComplex_bound chiOne xi hDpos S
  let K : ℝ :=
    (12 / ((4 / 5 - principalSqrtShift) * principalSqrtShift)) *
      (1600 / (1 - principalSqrtShift)) * (5 + |t|) ^ 6 *
      Real.rpow X (-beta + principalSqrtShift) * C
  have hK : 0 ≤ K := by
    dsimp [K]
    have h1 : 0 < 4 / 5 - principalSqrtShift := by
      linarith [principalSqrtShift_lt_four_fifths]
    have h2 : 0 < 1 - principalSqrtShift := by
      linarith [principalSqrtShift_le_one_eight]
    have hxp : 0 ≤ Real.rpow X (-beta + principalSqrtShift) :=
      Real.rpow_nonneg (by linarith : 0 ≤ X) _
    have hA : 0 ≤ (12 / ((4 / 5 - principalSqrtShift) * principalSqrtShift) : ℝ) := by
      norm_num [principalSqrtShift]
    have hB : 0 ≤ (1600 / (1 - principalSqrtShift) : ℝ) := by
      norm_num [principalSqrtShift]
    have hpow : 0 ≤ (5 + |t|) ^ 6 := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hA hB) hpow) hxp) hC
  have hEbase : Integrable (fun u : ℝ =>
      (1 + |u|) ^ 7 * Real.exp (-|u|)) := by
    have h := integrable_shiftedAbsPowExp
      (A := 1) (k := 7) (c := 1) (by norm_num) (by norm_num)
    convert h using 1
    ext u
    simp [shiftedAbsPowExp]
  have hE : Integrable (fun u : ℝ =>
      K * ((1 + |u|) ^ 7 * Real.exp (-|u|))) :=
    hEbase.const_mul K
  apply hE.mono'
  · exact (continuous_principal_detector_epsilonLeft xi hDpos S
      (zero_lt_one.trans_le hX) hbetaLo hbetaHi hrho).aestronglyMeasurable
  · filter_upwards with u
    simpa [K] using
      norm_principal_detector_epsilonLeft_poly_le xi hDpos S hX hC hM
        hbetaLo hbetaHi hrho (u := u)

/-- Finite rectangle with left line at `Re = -β+ε`. -/
theorem principalLemmaSix_epsilonRectangle_eq_residue
    {beta t : ℝ} (xi : ℕ → ℂ) {D : Finset ℕ}
    (hDpos : ∀ d ∈ D, 0 < d) (S : Finset ℕ)
    {X B : ℝ} (hX : 0 < X)
    (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0)
    (hB : |t| + 1 ≤ B) :
    (∫ y : ℝ in -B..B,
        jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
          xi D S X ((1 : ℂ) + y * I)) =
      (∫ y : ℝ in -B..B,
        jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
          xi D S X (principalEpsilonLeft beta y)) +
      I * ((∫ x : ℝ in (-beta + principalSqrtShift)..1,
        jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
          xi D S X (x + (-B) * I)) -
        (∫ x : ℝ in (-beta + principalSqrtShift)..1,
          jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
            xi D S X (x + B * I))) +
      (2 * Real.pi : ℂ) *
        principalLemmaSixResidue (lemmaSixZeroPoint beta t) xi D S X := by
  let rho : ℂ := lemmaSixZeroPoint beta t
  have hrho1 : rho ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [rho, lemmaSixZeroPoint] at hre
    linarith
  have hre : rho.re = beta := by simp [rho, lemmaSixZeroPoint]
  have him : rho.im = t := by simp [rho, lemmaSixZeroPoint]
  have hpRe : (principalPoleLocation rho).re = 1 - beta := by
    simp [principalPoleLocation, hre]
  have hpIm : (principalPoleLocation rho).im = -t := by
    simp [principalPoleLocation, him]
  have hr : (0 : ℝ) < (1 / 8 : ℝ) := by norm_num
  have ha : (-beta + principalSqrtShift : ℝ) = -beta + principalSqrtShift := rfl
  have haStrip : -1 < (-beta + principalSqrtShift : ℝ) := by
    linarith [principalSqrtShift_pos]
  have hleft : (-beta + principalSqrtShift : ℝ) <
      (principalPoleLocation rho).re - (1 / 8 : ℝ) := by
    rw [hpRe]
    linarith [principalSqrtShift_add_one_eight_lt_one]
  have hright : (principalPoleLocation rho).re + (1 / 8 : ℝ) < (1 : ℝ) := by
    rw [hpRe]
    linarith
  have hbottom : -B < (principalPoleLocation rho).im - (1 / 8 : ℝ) := by
    rw [hpIm]
    have := le_abs_self t
    linarith
  have htop : (principalPoleLocation rho).im + (1 / 8 : ℝ) < B := by
    rw [hpIm]
    have := neg_le_abs t
    linarith
  have hbetaHigh : rho.re ≤ 1 := by rw [hre]; linarith
  have ha0 : (-beta + principalSqrtShift : ℝ) ≠ 0 := by
    linarith [principalSqrtShift_lt_four_fifths]
  have hb0 : (1 : ℝ) ≠ 0 := by norm_num
  have hu0 : (-B : ℝ) ≠ 0 := by linarith
  have hv0 : (B : ℝ) ≠ 0 := by linarith
  have h :=
    principalLemmaSix_right_eq_left_add_horizontals_add_residue
      (rho := rho) xi hDpos S hX hrho hrho1 hbetaHigh hr haStrip
      hleft hright hbottom htop ha0 hb0 hu0 hv0
  simpa [rho, principalEpsilonLeft, Complex.ofReal_add, Complex.ofReal_neg]
    using h

private theorem tendsto_shifted_pow_exp_neg
    (k : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun B : ℝ => (c + B) ^ k * Real.exp (-B)) atTop (𝓝 0) := by
  have hbase := tendsto_pow_mul_exp_neg_atTop_nhds_zero k
  have hshift : Tendsto (fun B : ℝ => c + B) atTop atTop :=
    tendsto_atTop_mono (fun B => le_add_of_nonneg_left hc) tendsto_id
  have hcomp := hbase.comp hshift
  have hmul : Tendsto (fun B : ℝ =>
      ((c + B) ^ k * Real.exp (-(c + B))) * Real.exp c) atTop (𝓝 0) := by
    simpa [mul_comm] using hcomp.mul_const (Real.exp c)
  have hfun : (fun B : ℝ =>
      ((c + B) ^ k * Real.exp (-(c + B))) * Real.exp c) =
      fun B : ℝ => (c + B) ^ k * Real.exp (-B) := by
    funext B
    have : Real.exp (-(c + B)) * Real.exp c = Real.exp (-B) := by
      rw [← Real.exp_add]
      ring_nf
    calc
      ((c + B) ^ k * Real.exp (-(c + B))) * Real.exp c =
          (c + B) ^ k * (Real.exp (-(c + B)) * Real.exp c) := by ring
      _ = (c + B) ^ k * Real.exp (-B) := by rw [this]
  rw [hfun] at hmul
  exact hmul

theorem tendsto_principal_detector_epsilonHorizontal_zero
    {rho : ℂ} (hrho : principalF rho = 0) (hrho1 : rho ≠ 1)
    (xi : ℕ → ℂ) {D : Finset ℕ} (hDpos : ∀ d ∈ D, 0 < d)
    (S : Finset ℕ) {X a ε : ℝ} (hX : 1 ≤ X)
    (hrlo : 0 ≤ rho.re) (hrhi : rho.re ≤ 1)
    (haLo : -rho.re ≤ a) (haHi : a ≤ 1) (hε : |ε| = 1) :
    Tendsto (fun B : ℝ => ∫ x : ℝ in a..1,
      jutilaDetectorExtension chiOne rho xi D S X
        ((x : ℂ) + (ε * B) * I))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hM⟩ :=
    exists_jutilaMWeightedSumComplex_bound chiOne xi hDpos S
  let K : ℝ := 6 + |rho.im|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hlen : |1 - a| ≤ 2 := by
    have : -1 ≤ a := by linarith
    have : a ≤ 1 := haHi
    rw [abs_of_nonneg (by linarith)]
    linarith
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
    (g := fun B : ℝ =>
      12 * 1600 * X * C * (2 : ℝ) *
        (K + B) ^ 7 * Real.exp (-B))
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (|rho.im| + 1)] with B hB
    have hB0 : 0 ≤ B := by linarith [abs_nonneg rho.im]
    have hB1 : 1 ≤ B := by linarith [abs_nonneg rho.im]
    have habs : |ε * B| = B := by
      rw [abs_mul, hε, one_mul, abs_of_nonneg hB0]
    have hsep : 1 ≤ |rho.im + ε * B| := by
      have : B ≤ |rho.im + ε * B| + |rho.im| := by
        calc
          B = |ε * B| := by
            rw [abs_mul, hε, one_mul, abs_of_nonneg hB0]
          _ = |(rho.im + ε * B) - rho.im| := by ring_nf
          _ ≤ |rho.im + ε * B| + |rho.im| := abs_sub _ _
      linarith
    have h1 : 1 + B ≤ K + B := by dsimp [K]; linarith [abs_nonneg rho.im]
    have h2 : 5 + |rho.im| + B ≤ K + B := by dsimp [K]; linarith
    have hpoly :
        (12 * (1 + B) * Real.exp (-B)) *
          (1600 * (5 + |rho.im| + B) ^ 6) * X * C ≤
        12 * 1600 * X * C * (K + B) ^ 7 * Real.exp (-B) := by
      calc
        _ ≤ (12 * (K + B) * Real.exp (-B)) *
            (1600 * (K + B) ^ 6) * X * C := by gcongr
        _ = 12 * 1600 * X * C * (K + B) ^ 7 * Real.exp (-B) := by ring
    have hinter := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := 1)
      (C := 12 * (1 + B) * Real.exp (-B) *
        (1600 * (5 + |rho.im| + B) ^ 6) * X * C) (f := fun x : ℝ =>
          jutilaDetectorExtension chiOne rho xi D S X
            ((x : ℂ) + (ε * B) * I)) (by
      intro x hx
      have hx' : x ∈ Set.Icc (-rho.re) 1 := by
        have hh := Set.uIoc_subset_uIcc hx
        have hab : a ≤ 1 := haHi
        have hxI : x ∈ Set.Icc a 1 := by
          rw [Set.uIcc_of_le hab] at hh
          exact hh
        exact ⟨haLo.trans hxI.1, hxI.2⟩
      have hh := norm_principal_detector_horizontal_le hrho hrho1 xi D S
        hX hC hM hrlo hrhi hx'.1 hx'.2 (t := ε * B)
        (by rw [habs]; exact hB1) (by simpa [habs] using hsep)
      rw [habs] at hh
      simpa only [Complex.ofReal_mul] using hh
    )
    have hbound : ‖∫ (x : ℝ) in a..1,
          jutilaDetectorExtension chiOne rho xi D S X
            ((x : ℂ) + (ε * B) * I)‖ ≤
          (12 * (1 + B) * Real.exp (-B) *
            (1600 * (5 + |rho.im| + B) ^ 6) * X * C) * |1 - a| := by
      simpa only [id] using hinter
    calc
      ‖∫ (x : ℝ) in a..1,
          jutilaDetectorExtension chiOne rho xi D S X
            ((x : ℂ) + (ε * B) * I)‖ ≤
          (12 * (1 + B) * Real.exp (-B) *
            (1600 * (5 + |rho.im| + B) ^ 6) * X * C) * |1 - a| := hbound
      _ ≤ (12 * (1 + B) * Real.exp (-B) *
            (1600 * (5 + |rho.im| + B) ^ 6) * X * C) * 2 := by
        gcongr
      _ ≤ 12 * 1600 * X * C * (2 : ℝ) *
          (K + B) ^ 7 * Real.exp (-B) := by
        linarith [hpoly]
  · have hpoly := tendsto_shifted_pow_exp_neg 7 K hK
    have hpoly' : Tendsto (fun B : ℝ =>
        (K + B) ^ 7 * Real.exp (-B)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using hpoly
    have hconst :
        Tendsto (fun B : ℝ =>
          (12 * 1600 * X * C * (2 : ℝ)) *
            ((K + B) ^ 7 * Real.exp (-B))) atTop (𝓝 0) :=
      by
        simpa [mul_assoc] using
          (hpoly'.const_mul (12 * 1600 * X * C * (2 : ℝ)))
    simpa [mul_assoc] using hconst

theorem principal_detector_right_eq_epsilonLeft_add_residue
    {beta t : ℝ} (xi : ℕ → ℂ) {D : Finset ℕ}
    (hDpos : ∀ d ∈ D, 0 < d) (S : Finset ℕ)
    {X : ℝ} (hX : 1 ≤ X)
    (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0) :
    (∫ u : ℝ, jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        xi D S X ((1 : ℂ) + u * I)) =
      (∫ u : ℝ, jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        xi D S X (principalEpsilonLeft beta u)) +
      (2 * Real.pi : ℂ) *
        principalLemmaSixResidue (lemmaSixZeroPoint beta t) xi D S X := by
  let rho : ℂ := lemmaSixZeroPoint beta t
  let F := jutilaDetectorExtension chiOne rho xi D S X
  let a : ℝ := -beta + principalSqrtShift
  let Rv : ℝ → ℂ := fun B => ∫ u : ℝ in -B..B, F ((1 : ℂ) + u * I)
  let Lv : ℝ → ℂ := fun B => ∫ u : ℝ in -B..B, F (principalEpsilonLeft beta u)
  let Hm : ℝ → ℂ := fun B => ∫ x : ℝ in a..1, F ((x : ℂ) - B * I)
  let Hp : ℝ → ℂ := fun B => ∫ x : ℝ in a..1, F ((x : ℂ) + B * I)
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hrlo : 0 ≤ rho.re := by simp [rho, lemmaSixZeroPoint]; linarith
  have hrhi : rho.re ≤ 1 := by simp [rho, lemmaSixZeroPoint]; linarith
  have hrho1 : rho ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [rho, lemmaSixZeroPoint] at hre
    linarith
  have hre : rho.re = beta := by simp [rho, lemmaSixZeroPoint]
  have haLo : -rho.re ≤ a := by
    dsimp [a]
    rw [hre]
    linarith [principalSqrtShift_pos]
  have haHi : a ≤ 1 := by
    dsimp [a]
    linarith [principalSqrtShift_le_one_eight]
  have hrightInt := integrable_principal_detector_right xi hDpos S hX
    hbetaLo hbetaHi hrho
  have hleftInt := integrable_principal_detector_epsilonLeft xi hDpos S hX
    hbetaLo hbetaHi hrho
  have hR : Tendsto Rv atTop (𝓝 (∫ u : ℝ, F ((1 : ℂ) + u * I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral hrightInt
      Filter.tendsto_neg_atTop_atBot tendsto_id
  have hL : Tendsto Lv atTop
      (𝓝 (∫ u : ℝ, F (principalEpsilonLeft beta u))) :=
    MeasureTheory.intervalIntegral_tendsto_integral hleftInt
      Filter.tendsto_neg_atTop_atBot tendsto_id
  have hm : Tendsto Hm atTop (𝓝 0) := by
    have h := tendsto_principal_detector_epsilonHorizontal_zero
      hrho hrho1 xi hDpos S hX hrlo hrhi haLo haHi
      (ε := (-1 : ℝ)) (by norm_num)
    simpa [Hm, F, a, sub_eq_add_neg, neg_mul] using h
  have hp : Tendsto Hp atTop (𝓝 0) := by
    have h := tendsto_principal_detector_epsilonHorizontal_zero
      hrho hrho1 xi hDpos S hX hrlo hrhi haLo haHi
      (ε := (1 : ℝ)) (by norm_num)
    simpa [Hp, F, a] using h
  let Z : ℂ := (2 * Real.pi : ℂ) *
    principalLemmaSixResidue rho xi D S X
  have hcombo : Tendsto (fun B => Lv B + I * (Hm B - Hp B) + Z) atTop
      (𝓝 ((∫ u : ℝ, F (principalEpsilonLeft beta u)) + I * (0 - 0) + Z)) :=
    (hL.add (tendsto_const_nhds.mul (hm.sub hp))).add tendsto_const_nhds
  have heq : ∀ᶠ B : ℝ in atTop, Rv B = Lv B + I * (Hm B - Hp B) + Z := by
    filter_upwards [eventually_ge_atTop (|t| + 1)] with B hB
    have hf := principalLemmaSix_epsilonRectangle_eq_residue
      (beta := beta) (t := t) xi hDpos S hXpos hbetaLo hbetaHi hrho hB
    simpa [Rv, Lv, Hm, Hp, F, Z, rho, a, principalEpsilonLeft,
      sub_eq_add_neg] using hf
  have hR' := hcombo.congr' (Filter.EventuallyEq.symm heq)
  have hunique := tendsto_nhds_unique hR hR'
  simpa [F, rho, Z] using hunique

theorem principal_canonical_right_eq_epsilonLeft_add_pole
    {beta t z1 z2 : ℝ} {R : ℕ} {X : ℝ}
    (hX : 1 ≤ X) (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0) :
    (∫ u : ℝ, jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        (jutilaLambdaComplex z1 z2) (jutilaLambdaSupport z2)
        (jutilaPrimedRSet 1 R) X ((1 : ℂ) + u * I)) =
      (∫ u : ℝ, jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        (jutilaLambdaComplex z1 z2) (jutilaLambdaSupport z2)
        (jutilaPrimedRSet 1 R) X (principalEpsilonLeft beta u)) +
      (2 * Real.pi : ℂ) *
        principalDetectorPole (lemmaSixZeroPoint beta t) X z1 z2 R := by
  have hrho1 : lemmaSixZeroPoint beta t ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [lemmaSixZeroPoint] at hre
    linarith
  have h := principal_detector_right_eq_epsilonLeft_add_residue
    (jutilaLambdaComplex z1 z2)
    (D := jutilaLambdaSupport z2)
    (fun d hd => (Finset.mem_Icc.mp hd).1)
    (jutilaPrimedRSet 1 R) hX hbetaLo hbetaHi hrho
  rw [h, principalLemmaSixResidue_eq_principalDetectorPole
    (X := X) (z1 := z1) (z2 := z2) R hrho hrho1]

private theorem one_div_two_pi_mul_two_pi :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) * (2 * Real.pi : ℂ)) = 1 := by
  have htwo : (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by
    simp [Complex.ofReal_mul]
  rw [htwo, ← Complex.ofReal_mul]
  have : (1 / (2 * Real.pi) : ℝ) * (2 * Real.pi) = 1 := by
    field_simp [Real.pi_ne_zero]
  rw [this, Complex.ofReal_one]

/-- Canonical Mellin series after the epsilon-shifted one-pole identity. -/
theorem principal_canonical_directSeries_eq_epsilonLeft_add_pole
    {beta t z1 z2 : ℝ} {R : ℕ} {X : ℝ}
    (hz1 : 1 < z1) (hz12 : z1 < z2)
    (hX : 1 ≤ X) (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0) :
    (∑' n : ℕ, jutilaLemmaSixDirectTerm chiOne z1 z2
        (jutilaPrimedRSet 1 R) (lemmaSixZeroPoint beta t) X n) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ u : ℝ, jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
          (jutilaLambdaComplex z1 z2) (jutilaLambdaSupport z2)
          (jutilaPrimedRSet 1 R) X (principalEpsilonLeft beta u)) +
      principalDetectorPole (lemmaSixZeroPoint beta t) X z1 z2 R := by
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hS : jutilaPrimedRSet 1 R ⊆ Finset.Icc 1 R :=
    jutilaPrimedRSet_subset_Icc 1 R
  have hrightRe : 1 < (lemmaSixZeroPoint beta t + (1 : ℂ)).re := by
    simp [lemmaSixZeroPoint]
    linarith
  have hmellin :=
    jutilaSelectedDirectSeries_eq_gamma_rightLine (q := 1) (R := R) chiOne
      hS (fun r hr => squarefree_of_mem_jutilaPrimedRSet hr)
      (fun r hr => coprime_of_mem_jutilaPrimedRSet hr)
      hz1 hz12 (c := 1) (by norm_num) hXpos
      (lemmaSixZeroPoint beta t) hrightRe
  have hrho1 : lemmaSixZeroPoint beta t ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [lemmaSixZeroPoint] at hre
    linarith
  have hLrho :
      DirichletCharacter.LFunction chiOne (lemmaSixZeroPoint beta t) = 0 :=
    LFunction_chiOne_eq_zero_of_principalRegularized hrho hrho1
  have hpoint :
      (∫ v : ℝ,
        DirichletCharacter.LFunction chiOne
            (lemmaSixZeroPoint beta t + ((1 : ℂ) + v * I)) *
          jutilaMWeightedSumComplex chiOne
            (jutilaLambdaComplex z1 z2) (jutilaLambdaSupport z2)
            (jutilaPrimedRSet 1 R)
            (lemmaSixZeroPoint beta t + ((1 : ℂ) + v * I)) *
          Complex.Gamma ((1 : ℂ) + v * I) *
          (X : ℂ) ^ ((1 : ℂ) + v * I)) =
        ∫ v : ℝ, jutilaDetectorExtension chiOne
          (lemmaSixZeroPoint beta t)
          (jutilaLambdaComplex z1 z2) (jutilaLambdaSupport z2)
          (jutilaPrimedRSet 1 R) X ((1 : ℂ) + v * I) := by
    apply integral_congr_ae
    filter_upwards with v
    have hz : (1 : ℂ) + v * I ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
    rw [jutilaDetectorExtension_eq_raw chiOne
      (jutilaLambdaComplex z1 z2) (jutilaLambdaSupport z2)
      (jutilaPrimedRSet 1 R) X hLrho hz]
    ring
  have hshift :=
    principal_canonical_right_eq_epsilonLeft_add_pole
      hX hbetaLo hbetaHi hrho (z1 := z1) (z2 := z2) (R := R)
  simp only [Complex.ofReal_one] at hmellin
  rw [hmellin, hpoint, hshift, mul_add]
  have hpole :
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((2 * Real.pi : ℂ) *
          principalDetectorPole (lemmaSixZeroPoint beta t) X z1 z2 R)) =
        principalDetectorPole (lemmaSixZeroPoint beta t) X z1 z2 R := by
    rw [← mul_assoc, one_div_two_pi_mul_two_pi, one_mul]
  rw [hpole]

theorem principal_canonical_directSeries_sub_pole_eq_epsilonLeft
    {beta t z1 z2 : ℝ} {R : ℕ} {X : ℝ}
    (hz1 : 1 < z1) (hz12 : z1 < z2)
    (hX : 1 ≤ X) (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0) :
    (∑' n : ℕ, jutilaLemmaSixDirectTerm chiOne z1 z2
        (jutilaPrimedRSet 1 R) (lemmaSixZeroPoint beta t) X n) -
      principalDetectorPole (lemmaSixZeroPoint beta t) X z1 z2 R =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ u : ℝ, jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
          (jutilaLambdaComplex z1 z2) (jutilaLambdaSupport z2)
          (jutilaPrimedRSet 1 R) X (principalEpsilonLeft beta u)) := by
  rw [principal_canonical_directSeries_eq_epsilonLeft_add_pole
    hz1 hz12 hX hbetaLo hbetaHi hrho]
  ring

end

end MAPJutilaPrincipalEpsilonShiftedContour

#print axioms MAPJutilaPrincipalEpsilonShiftedContour.principal_detector_right_eq_epsilonLeft_add_residue
#print axioms MAPJutilaPrincipalEpsilonShiftedContour.principal_canonical_directSeries_eq_epsilonLeft_add_pole
#print axioms MAPJutilaPrincipalEpsilonShiftedContour.principal_canonical_directSeries_sub_pole_eq_epsilonLeft
