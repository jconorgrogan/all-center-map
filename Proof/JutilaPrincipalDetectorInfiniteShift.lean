import JutilaPrincipalDetectorFinitePole
import JutilaLemma6HorizontalDecay
import JutilaLemma6SieveCoefficientBridge
import JutilaMNonnegativeHalfPlaneBound
import PrincipalZetaFixedStrip
import JutilaLemma6SelectedRightLine

/-!
# Infinite-height one-pole displacement for the conductor-one Lemma 6 detector

The finite rectangle identity is passed to infinite height.  Horizontal edges
vanish by the Gamma exponential and the polynomial fixed-strip zeta bound.
The crossed residue is retained exactly; for the canonical mollifier it is
`principalDetectorPole`.

Nonprincipal contour theorems are not applied to `χ = 1`.
-/

namespace MAPJutilaPrincipalDetectorInfiniteShift

open Complex Real MeasureTheory Set Filter Topology
open MAPJutilaPrincipalDetectorFinitePole
open MAPJutilaPrincipalDetectorPole
open MAPJutilaLemma6FiniteContour
open MAPJutilaLemma6HorizontalDecay
open MAPJutilaLemma6ErrorBound
open MAPJutilaMEntire
open MAPJutilaMNonnegativeHalfPlaneBound
open MAPJutilaLemma6SieveCoefficientBridge
open MAPJutilaPseudocharacterHarmonicLower
open MAPPrincipalZetaDetectorPoleRemoval
open MAPPrincipalZetaFixedStrip
open MAPJutilaLemma6SelectedRightLine

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)
local notation "principalF" => MAPPrincipalZetaFixedStrip.principalRegularized

theorem norm_riemannZeta_fixedStrip_of_separated
    {s : ℂ} (hslo : -1 ≤ s.re) (hshi : s.re ≤ 2)
    (hs1 : 1 ≤ ‖s - 1‖) :
    ‖riemannZeta s‖ ≤ 1600 * ‖s + 3‖ ^ 6 := by
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
  have hz : ‖riemannZeta s‖ ≤ ‖s - 1‖ * ‖riemannZeta s‖ := by
    nlinarith [norm_nonneg (riemannZeta s)]
  exact hz.trans hreg

theorem norm_principal_detector_horizontal_le
    {rho : ℂ} (hrho : principalF rho = 0) (hrho1 : rho ≠ 1)
    (xi : ℕ → ℂ) (D S : Finset ℕ)
    {X C x t : ℝ} (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hM : ∀ s : ℂ, 0 ≤ s.re →
      ‖jutilaMWeightedSumComplex chiOne xi D S s‖ ≤ C)
    (hrlo : 0 ≤ rho.re) (hrhi : rho.re ≤ 1)
    (hxlo : -rho.re ≤ x) (hxhi : x ≤ 1)
    (ht : 1 ≤ |t|) (hsep : 1 ≤ |rho.im + t|) :
    ‖jutilaDetectorExtension chiOne rho xi D S X ((x : ℂ) + t * I)‖ ≤
      (12 * (1 + |t|) * Real.exp (-|t|)) *
        (1600 * (5 + |rho.im| + |t|) ^ 6) * X * C := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hz : (x : ℂ) + t * I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    rw [him] at ht
    simp at ht
    linarith
  have hLrho :
      DirichletCharacter.LFunction chiOne rho = 0 :=
    LFunction_chiOne_eq_zero_of_principalRegularized hrho hrho1
  rw [jutilaDetectorExtension_eq_raw chiOne xi D S X hLrho hz]
  have hG := norm_Gamma_detectorStrip_le (by linarith) hxhi ht
  have hxp : ‖(X : ℂ) ^ ((x : ℂ) + t * I)‖ ≤ X := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hXpos]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero]
    simpa using Real.rpow_le_rpow_of_exponent_le hX hxhi
  let s : ℂ := rho + ((x : ℂ) + t * I)
  have hslo : -1 ≤ s.re := by simp [s]; linarith
  have hshi : s.re ≤ 2 := by simp [s]; linarith
  have hs1 : 1 ≤ ‖s - 1‖ := by
    have him' : |(s - 1).im| = |rho.im + t| := by simp [s]
    have := Complex.abs_im_le_norm (s - 1)
    rw [him'] at this
    exact hsep.trans this
  have hL : DirichletCharacter.LFunction chiOne s = riemannZeta s := by
    simp [DirichletCharacter.LFunction_modOne_eq]
  have hzBound := norm_riemannZeta_fixedStrip_of_separated hslo hshi hs1
  have hznorm : ‖s + 3‖ ≤ 5 + |rho.im| + |t| := by
    calc
      ‖s + 3‖ ≤ |(s + 3).re| + |(s + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |rho.re + x + 3| + |rho.im + t| := by simp [s]
      _ ≤ 5 + |rho.im| + |t| := by
        rw [abs_of_nonneg (by linarith : 0 ≤ rho.re + x + 3)]
        linarith [abs_add_le rho.im t]
  have hzeta : ‖DirichletCharacter.LFunction chiOne s‖ ≤
      1600 * (5 + |rho.im| + |t|) ^ 6 := by
    rw [hL]
    exact hzBound.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hznorm 6) (by positivity))
  have hsRe : 0 ≤ s.re := by simp [s]; linarith
  have hm := hM s hsRe
  simp only [norm_mul]
  calc
    _ ≤ (12 * (1 + |t|) * Real.exp (-|t|)) *
        (1600 * (5 + |rho.im| + |t|) ^ 6) * X * C := by
      gcongr

private theorem tendsto_shifted_pow_exp_neg
    (k : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun B : ℝ => (c + B) ^ k * Real.exp (-B)) atTop (𝓝 0) := by
  have hbase := tendsto_pow_mul_exp_neg_atTop_nhds_zero k
  have hshift : Tendsto (fun B : ℝ => c + B) atTop atTop :=
    tendsto_atTop_mono (fun B => le_add_of_nonneg_left hc) tendsto_id
  have hcomp := hbase.comp hshift
  have hcomp' : Tendsto (fun B : ℝ =>
      (c + B) ^ k * Real.exp (-(c + B))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using hcomp
  have hmul := hcomp'.mul_const (Real.exp c)
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
  simpa only [zero_mul] using hmul

theorem tendsto_principal_detector_horizontal_zero
    {rho : ℂ} (hrho : principalF rho = 0) (hrho1 : rho ≠ 1)
    (xi : ℕ → ℂ) {D : Finset ℕ} (hDpos : ∀ d ∈ D, 0 < d)
    (S : Finset ℕ) {X ε : ℝ} (hX : 1 ≤ X)
    (hrlo : 0 ≤ rho.re) (hrhi : rho.re ≤ 1) (hε : |ε| = 1) :
    Tendsto (fun B : ℝ => ∫ x : ℝ in (-rho.re)..1,
      jutilaDetectorExtension chiOne rho xi D S X
        ((x : ℂ) + (ε * B) * I))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hM⟩ :=
    exists_jutilaMWeightedSumComplex_bound chiOne xi hDpos S
  let K : ℝ := 6 + |rho.im|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
    (g := fun B : ℝ =>
      12 * 1600 * X * C * |1 - (-rho.re)| *
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
    calc
      ‖∫ x : ℝ in -rho.re..1,
          jutilaDetectorExtension chiOne rho xi D S X
            ((x : ℂ) + (ε * B) * I)‖ ≤
        (12 * 1600 * X * C * (K + B) ^ 7 * Real.exp (-B)) *
          |1 - (-rho.re)| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro x hx
        have hx' : x ∈ Set.Icc (-rho.re) 1 := by
          have hh := Set.uIoc_subset_uIcc hx
          simpa [Set.uIcc_of_le (show -rho.re ≤ 1 by linarith)] using hh
        have hh := norm_principal_detector_horizontal_le hrho hrho1 xi D S
          hX hC hM hrlo hrhi hx'.1 hx'.2 (t := ε * B)
          (by rw [habs]; exact hB1) (by simpa [habs] using hsep)
        have h1 : 1 + B ≤ K + B := by
          dsimp [K]
          linarith [abs_nonneg rho.im]
        have h2 : 5 + |rho.im| + B ≤ K + B := by
          dsimp [K]
          linarith
        have hpoly :
            (12 * (1 + B) * Real.exp (-B)) *
              (1600 * (5 + |rho.im| + B) ^ 6) * X * C ≤
            12 * 1600 * X * C * (K + B) ^ 7 * Real.exp (-B) := by
          calc
            _ ≤ (12 * (K + B) * Real.exp (-B)) *
                (1600 * (K + B) ^ 6) * X * C := by gcongr
            _ = 12 * 1600 * X * C * (K + B) ^ 7 * Real.exp (-B) := by ring
        rw [habs] at hh
        simpa only [Complex.ofReal_mul] using hh.trans hpoly
      _ = 12 * 1600 * X * C * |1 - (-rho.re)| *
          (K + B) ^ 7 * Real.exp (-B) := by ring
  · have hpoly := tendsto_shifted_pow_exp_neg 7 K hK
    have hpoly' : Tendsto (fun B : ℝ =>
        (K + B) ^ 7 * Real.exp (-B)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using hpoly
    have hconst :
        Tendsto (fun B : ℝ =>
          (12 * 1600 * X * C * |1 - (-rho.re)|) *
            ((K + B) ^ 7 * Real.exp (-B))) atTop (𝓝 0) :=
      by
        simpa [mul_assoc] using
          (hpoly'.const_mul (12 * 1600 * X * C * |1 - (-rho.re)|))
    convert hconst using 1
    funext B
    ring

/-- Infinite-height displacement, given integrability of both vertical
sides.  The residue is the exact one-pole term. -/
theorem principal_detector_right_eq_left_add_residue_of_integrable
    {beta t : ℝ} (xi : ℕ → ℂ) {D : Finset ℕ}
    (hDpos : ∀ d ∈ D, 0 < d) (S : Finset ℕ)
    {X : ℝ} (hX : 1 ≤ X)
    (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0)
    (hrightInt : Integrable (fun u : ℝ =>
      jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        xi D S X ((1 : ℂ) + u * I)))
    (hleftInt : Integrable (fun u : ℝ =>
      jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        xi D S X (((-beta : ℝ) : ℂ) + u * I))) :
    (∫ u : ℝ, jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        xi D S X ((1 : ℂ) + u * I)) =
      (∫ u : ℝ, jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        xi D S X (((-beta : ℝ) : ℂ) + u * I)) +
      (2 * Real.pi : ℂ) *
        principalLemmaSixResidue (lemmaSixZeroPoint beta t) xi D S X := by
  let rho : ℂ := lemmaSixZeroPoint beta t
  let F := jutilaDetectorExtension chiOne rho xi D S X
  let Rv : ℝ → ℂ := fun B => ∫ u : ℝ in -B..B, F ((1 : ℂ) + u * I)
  let Lv : ℝ → ℂ := fun B => ∫ u : ℝ in -B..B, F (((-beta : ℝ) : ℂ) + u * I)
  let Hm : ℝ → ℂ := fun B => ∫ x : ℝ in -beta..1, F ((x : ℂ) - B * I)
  let Hp : ℝ → ℂ := fun B => ∫ x : ℝ in -beta..1, F ((x : ℂ) + B * I)
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hrlo : 0 ≤ rho.re := by simp [rho, lemmaSixZeroPoint]; linarith
  have hrhi : rho.re ≤ 1 := by simp [rho, lemmaSixZeroPoint]; linarith
  have hrho1 : rho ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [rho, lemmaSixZeroPoint] at hre
    linarith
  have hR : Tendsto Rv atTop (𝓝 (∫ u : ℝ, F ((1 : ℂ) + u * I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral hrightInt
      Filter.tendsto_neg_atTop_atBot tendsto_id
  have hL : Tendsto Lv atTop
      (𝓝 (∫ u : ℝ, F (((-beta : ℝ) : ℂ) + u * I))) :=
    MeasureTheory.intervalIntegral_tendsto_integral hleftInt
      Filter.tendsto_neg_atTop_atBot tendsto_id
  have hm : Tendsto Hm atTop (𝓝 0) := by
    have h := tendsto_principal_detector_horizontal_zero
      hrho hrho1 xi hDpos S hX hrlo hrhi (ε := (-1 : ℝ)) (by norm_num)
    have hre : rho.re = beta := by simp [rho, lemmaSixZeroPoint]
    simpa [Hm, F, rho, hre, sub_eq_add_neg, neg_mul] using h
  have hp : Tendsto Hp atTop (𝓝 0) := by
    have h := tendsto_principal_detector_horizontal_zero
      hrho hrho1 xi hDpos S hX hrlo hrhi (ε := (1 : ℝ)) (by norm_num)
    have hre : rho.re = beta := by simp [rho, lemmaSixZeroPoint]
    simpa [Hp, F, rho, hre] using h
  let Z : ℂ := (2 * Real.pi : ℂ) *
    principalLemmaSixResidue rho xi D S X
  have hcombo : Tendsto (fun B => Lv B + I * (Hm B - Hp B) + Z) atTop
      (𝓝 ((∫ u : ℝ, F (((-beta : ℝ) : ℂ) + u * I)) + I * (0 - 0) + Z)) :=
    (hL.add (tendsto_const_nhds.mul (hm.sub hp))).add tendsto_const_nhds
  have heq : ∀ᶠ B : ℝ in atTop, Rv B = Lv B + I * (Hm B - Hp B) + Z := by
    filter_upwards [eventually_ge_atTop (|t| + 1)] with B hB
    have hf := principalLemmaSix_sourceRectangle_eq_residue
      (beta := beta) (t := t) xi hDpos S hXpos hbetaLo hbetaHi hrho hB
    simpa [Rv, Lv, Hm, Hp, F, Z, rho, sub_eq_add_neg] using hf
  have hR' := hcombo.congr' (Filter.EventuallyEq.symm heq)
  have hunique := tendsto_nhds_unique hR hR'
  simpa [F, rho, Z] using hunique

/-- Canonical-mollifier form of the infinite displacement. -/
theorem principal_canonical_right_eq_left_add_principalDetectorPole_of_integrable
    {beta t z1 z2 : ℝ} {R : ℕ} {X : ℝ}
    (hX : 1 ≤ X) (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta < 1)
    (hrho : principalF (lemmaSixZeroPoint beta t) = 0)
    (hDpos : ∀ d ∈ jutilaLambdaSupport z2, 0 < d)
    (hrightInt : Integrable (fun u : ℝ =>
      jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        (jutilaLambdaComplex z1 z2) (jutilaLambdaSupport z2)
        (jutilaPrimedRSet 1 R) X ((1 : ℂ) + u * I)))
    (hleftInt : Integrable (fun u : ℝ =>
      jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        (jutilaLambdaComplex z1 z2) (jutilaLambdaSupport z2)
        (jutilaPrimedRSet 1 R) X (((-beta : ℝ) : ℂ) + u * I))) :
    (∫ u : ℝ, jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        (jutilaLambdaComplex z1 z2) (jutilaLambdaSupport z2)
        (jutilaPrimedRSet 1 R) X ((1 : ℂ) + u * I)) =
      (∫ u : ℝ, jutilaDetectorExtension chiOne (lemmaSixZeroPoint beta t)
        (jutilaLambdaComplex z1 z2) (jutilaLambdaSupport z2)
        (jutilaPrimedRSet 1 R) X (((-beta : ℝ) : ℂ) + u * I)) +
      (2 * Real.pi : ℂ) *
        principalDetectorPole (lemmaSixZeroPoint beta t) X z1 z2 R := by
  have hrho1 : lemmaSixZeroPoint beta t ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [lemmaSixZeroPoint] at hre
    linarith
  have h := principal_detector_right_eq_left_add_residue_of_integrable
    (jutilaLambdaComplex z1 z2) hDpos (jutilaPrimedRSet 1 R)
    hX hbetaLo hbetaHi hrho hrightInt hleftInt
  rw [h, principalLemmaSixResidue_eq_principalDetectorPole
    (X := X) (z1 := z1) (z2 := z2) R hrho hrho1]

end

end MAPJutilaPrincipalDetectorInfiniteShift

#print axioms MAPJutilaPrincipalDetectorInfiniteShift.norm_principal_detector_horizontal_le
#print axioms MAPJutilaPrincipalDetectorInfiniteShift.tendsto_principal_detector_horizontal_zero
#print axioms MAPJutilaPrincipalDetectorInfiniteShift.principal_detector_right_eq_left_add_residue_of_integrable
#print axioms MAPJutilaPrincipalDetectorInfiniteShift.principal_canonical_right_eq_left_add_principalDetectorPole_of_integrable
