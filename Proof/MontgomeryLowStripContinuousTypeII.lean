import LowStripGammaKernel
import BHPShiftedHolderReduction
import PostA5TypeIIFourthMoment
import RamachandraTheorem6Unconditional

/-!
# Continuous all-character Type-II route for the Montgomery low strip

The detector's central Gamma integral is compared directly with the Perron
convolution already used by the certified all-character Holder/packing layer.
This deliberately retains the integral alternative: no point is extracted
and no discrete fourth moment is assumed.
-/

namespace MAPMontgomeryLowStripContinuousTypeII

open scoped BigOperators
open Complex MeasureTheory
open CGLProofDAG
open MAPAppendixA4DetectorDichotomy
open MAPAppendixA4GammaEndpoint
open MAPAppendixA4FullContourLimit
open MAPMontgomeryLowStripGamma
open MAPMRTCorollary25Minkowski
open MAPMRTLemma211AllCharacterSource
open PostA5TypeIIFourthMoment

noncomputable section

/-- The inverse-quadratic Gamma envelope is dominated by twice the Perron
weight used by the existing all-character Holder packing theorem. -/
theorem inv_one_add_sq_le_two_perronWeight (u : ℝ) :
    (1 + u ^ 2)⁻¹ ≤ 2 * perronWeight u := by
  have hleft : 0 < 1 + u ^ 2 := by positivity
  have hright : 0 < 1 + |u| := by positivity
  rw [perronWeight, one_div, ← div_eq_mul_inv]
  rw [inv_eq_one_div]
  exact (div_le_div_iff₀ hleft hright).2 (by
    nlinarith [sq_nonneg (|u| - 1 / 2), sq_abs u])

/-- Pointwise comparison of the literal Gamma--L--mollifier integrand with
the common Perron convolution integrand. -/
theorem norm_gammaLeftIntegrand_le_perron
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q)
    {delta : ℝ} (hdelta : 0 < delta)
    {U : ℕ} {rho : ℂ}
    (hbetaLow : 1 / 2 + delta ≤ rho.re)
    (hbetaHigh : rho.re ≤ 7 / 10)
    {Y : ℝ} (hY : 1 ≤ Y) (u : ℝ) :
    ‖gammaLeftIntegrand chi U rho Y u‖ ≤
      (2 * lowStripGammaConstant delta *
          Real.rpow Y (1 / 2 - rho.re) *
          (2 * Real.sqrt U)) *
        (perronWeight u * criticalLineLNorm chi (rho.im + u)) := by
  have hk := gammaLeftKernelNorm_le_lowStrip
    hdelta hbetaLow hbetaHigh hY u
  have hp := inv_one_add_sq_le_two_perronWeight u
  have hkernel : gammaLeftKernelNorm rho Y u ≤
      2 * lowStripGammaConstant delta *
        Real.rpow Y (1 / 2 - rho.re) * perronWeight u := by
    calc
      gammaLeftKernelNorm rho Y u ≤
          lowStripGammaConstant delta *
            Real.rpow Y (1 / 2 - rho.re) * (1 + u ^ 2)⁻¹ := hk
      _ ≤ lowStripGammaConstant delta *
            Real.rpow Y (1 / 2 - rho.re) *
              (2 * perronWeight u) := by
        exact mul_le_mul_of_nonneg_left hp
          (mul_nonneg (lowStripGammaConstant_pos hdelta).le
            (Real.rpow_nonneg (by linarith) _))
      _ = 2 * lowStripGammaConstant delta *
            Real.rpow Y (1 / 2 - rho.re) * perronWeight u := by ring
  let s : ℂ := (((1 / 2 : ℝ) : ℂ) + (rho.im + u) * I)
  have hs : s.re = 1 / 2 := by dsimp [s]; simp
  have hmoll := norm_mollifier_criticalLine_le_two_sqrt chi U hs
  have hproduct : criticalLineProductNorm chi U rho u ≤
      criticalLineLNorm chi (rho.im + u) * (2 * Real.sqrt U) := by
    rw [criticalLineProductNorm_eq, norm_mul]
    simpa [criticalLineLNorm, s] using
      mul_le_mul_of_nonneg_left hmoll
        (norm_nonneg (DirichletCharacter.LFunction chi s))
  rw [norm_gammaLeftIntegrand_eq_kernel_mul_criticalLineProductNorm]
  calc
    gammaLeftKernelNorm rho Y u * criticalLineProductNorm chi U rho u ≤
        (2 * lowStripGammaConstant delta *
          Real.rpow Y (1 / 2 - rho.re) * perronWeight u) *
            (criticalLineLNorm chi (rho.im + u) *
              (2 * Real.sqrt U)) :=
      mul_le_mul hkernel hproduct (norm_nonneg _)
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by positivity) (lowStripGammaConstant_pos hdelta).le)
            (Real.rpow_nonneg (by linarith) _))
          (perronWeight_pos u).le)
    _ = (2 * lowStripGammaConstant delta *
          Real.rpow Y (1 / 2 - rho.re) *
          (2 * Real.sqrt U)) *
        (perronWeight u * criticalLineLNorm chi (rho.im + u)) := by ring

/-- Direct upper bound for the normalized central detector integral by the
critical-line Perron convolution. -/
theorem norm_normalizedCentralGammaIntegral_le_perronConvolution
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {delta : ℝ} (hdelta : 0 < delta)
    {U : ℕ} {rho : ℂ}
    (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 1 / 2 + delta ≤ rho.re)
    (hbetaHigh : rho.re ≤ 7 / 10)
    {Y B : ℝ} (hY : 1 ≤ Y) (hB : 0 ≤ B) :
    ‖normalizedCentralGammaIntegral chi U rho Y B‖ ≤
      ((lowStripGammaConstant delta / Real.pi) *
          Real.rpow Y (1 / 2 - rho.re) *
          (2 * Real.sqrt U)) *
        perronConvolution (criticalLineLNorm chi) B rho.im := by
  let A : ℝ := 2 * lowStripGammaConstant delta *
    Real.rpow Y (1 / 2 - rho.re) * (2 * Real.sqrt U)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) (lowStripGammaConstant_pos hdelta).le)
        (Real.rpow_nonneg (by linarith) _))
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
  have hmajorCont : Continuous (fun u : ℝ =>
      A * (perronWeight u * criticalLineLNorm chi (rho.im + u))) := by
    apply continuous_const.mul
    exact continuous_perronWeight.mul
      ((continuous_criticalLineLNorm chi).comp
        (continuous_const.add continuous_id))
  have hint :
      ‖∫ u : ℝ in (-B)..B, gammaLeftIntegrand chi U rho Y u‖ ≤
        ∫ u : ℝ in (-B)..B,
          A * (perronWeight u * criticalLineLNorm chi (rho.im + u)) := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
    · exact Filter.Eventually.of_forall fun u _ => by
        simpa [A] using norm_gammaLeftIntegrand_le_perron
          chi hdelta hbetaLow hbetaHigh hY u
    · exact hmajorCont.intervalIntegrable _ _
  have hconstNorm :
      ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    positivity
  rw [normalizedCentralGammaIntegral, norm_mul, hconstNorm]
  calc
    (1 / (2 * Real.pi)) *
        ‖∫ u : ℝ in (-B)..B, gammaLeftIntegrand chi U rho Y u‖ ≤
      (1 / (2 * Real.pi)) *
        ∫ u : ℝ in (-B)..B,
          A * (perronWeight u * criticalLineLNorm chi (rho.im + u)) := by
      exact mul_le_mul_of_nonneg_left hint (by positivity)
    _ = (1 / (2 * Real.pi)) * A *
        perronConvolution (criticalLineLNorm chi) B rho.im := by
      rw [intervalIntegral.integral_const_mul]
      unfold perronConvolution
      ring
    _ = ((lowStripGammaConstant delta / Real.pi) *
          Real.rpow Y (1 / 2 - rho.re) *
          (2 * Real.sqrt U)) *
        perronConvolution (criticalLineLNorm chi) B rho.im := by
      dsimp [A]
      field_simp [ne_of_gt Real.pi_pos]
      <;> ring

/-- The Perron-weighted local fourth moment is bounded by the unweighted
fourth moment on the recentered ordinate window. -/
theorem perronConvolution_criticalLineFourth_le_localIntegral
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {B t : ℝ} (hB : 0 ≤ B) :
    perronConvolution (criticalLineLFourth chi) B t ≤
      ∫ s in (t - B)..(t + B), criticalLineLFourth chi s := by
  rw [perronConvolution_eq_translatedIntegral]
  have hcont : Continuous (criticalLineLFourth chi) :=
    continuous_criticalLineLFourth chi
  have hmono :
      (∫ s in (-B + t)..(B + t),
        perronWeight (s - t) * criticalLineLFourth chi s) ≤
      ∫ s in (-B + t)..(B + t), criticalLineLFourth chi s := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact ((continuous_perronWeight.comp
        (continuous_id.sub continuous_const)).mul hcont).intervalIntegrable _ _
    · exact hcont.intervalIntegrable _ _
    · intro s hs
      have hw : perronWeight (s - t) ≤ 1 := by
        unfold perronWeight
        have hd : 1 ≤ 1 + |s - t| := by linarith [abs_nonneg (s - t)]
        exact (div_le_one (by positivity : 0 < 1 + |s - t|)).2 hd
      exact mul_le_of_le_one_left (by unfold criticalLineLFourth; positivity) hw
  simpa [sub_eq_add_neg, add_comm] using hmono

/-- Literal continuous Type-II estimate for one selected zero.  It retains
the central integral, applies Holder before any point extraction, and ends
with an unweighted local critical-line fourth moment. -/
theorem centralGammaIntegral_fourth_le_localFourth
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {delta : ℝ} (hdelta : 0 < delta)
    {U : ℕ} {rho : ℂ}
    (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 1 / 2 + delta ≤ rho.re)
    (hbetaHigh : rho.re ≤ 7 / 10)
    {Y B : ℝ} (hY : 1 ≤ Y) (hB : 0 < B) :
    ‖normalizedCentralGammaIntegral chi U rho Y B‖ ^ 4 ≤
      ((lowStripGammaConstant delta / Real.pi) *
          Real.rpow Y (1 / 2 - rho.re) *
          (2 * Real.sqrt U)) ^ 4 *
        (∫ u in (-B)..B, perronWeight u) ^ 3 *
        (∫ s in (rho.im - B)..(rho.im + B),
          criticalLineLFourth chi s) := by
  let A := (lowStripGammaConstant delta / Real.pi) *
    Real.rpow Y (1 / 2 - rho.re) * (2 * Real.sqrt U)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg
        (div_nonneg (lowStripGammaConstant_pos hdelta).le Real.pi_pos.le)
        (Real.rpow_nonneg (by linarith) _))
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
  have hc := norm_normalizedCentralGammaIntegral_le_perronConvolution
    chi hchi hdelta (U := U) hrho hbetaLow hbetaHigh hY hB.le
  have hc4 : ‖normalizedCentralGammaIntegral chi U rho Y B‖ ^ 4 ≤
      (A * perronConvolution (criticalLineLNorm chi) B rho.im) ^ 4 :=
    pow_le_pow_left₀ (norm_nonneg _) (by simpa [A] using hc) 4
  have hh := perronConvolution_fourth_le_cubeWeightMass_mul
    (t := rho.im) (continuous_criticalLineLNorm chi) hB
  have hl := perronConvolution_criticalLineFourth_le_localIntegral
    chi hB.le (t := rho.im)
  calc
    ‖normalizedCentralGammaIntegral chi U rho Y B‖ ^ 4 ≤
        (A * perronConvolution (criticalLineLNorm chi) B rho.im) ^ 4 := hc4
    _ = A ^ 4 * perronConvolution (criticalLineLNorm chi) B rho.im ^ 4 := by ring
    _ ≤ A ^ 4 * ((∫ u in (-B)..B, perronWeight u) ^ 3 *
        perronConvolution (fun x => criticalLineLNorm chi x ^ 4) B rho.im) :=
      mul_le_mul_of_nonneg_left hh (pow_nonneg hA 4)
    _ ≤ A ^ 4 * ((∫ u in (-B)..B, perronWeight u) ^ 3 *
        (∫ s in (rho.im - B)..(rho.im + B), criticalLineLFourth chi s)) := by
      apply mul_le_mul_of_nonneg_left
      apply mul_le_mul_of_nonneg_left
      · simpa [criticalLineLFourth] using hl
      · exact pow_nonneg (intervalIntegral.integral_nonneg (by linarith)
          (fun u hu => (perronWeight_pos u).le)) 3
      · exact pow_nonneg hA 4
    _ = ((lowStripGammaConstant delta / Real.pi) *
          Real.rpow Y (1 / 2 - rho.re) *
          (2 * Real.sqrt U)) ^ 4 *
        (∫ u in (-B)..B, perronWeight u) ^ 3 *
        (∫ s in (rho.im - B)..(rho.im + B),
          criticalLineLFourth chi s) := by
      dsimp [A]
      ring

/-- Ordinates separated by `3B` have disjoint recentered windows of radius
`B`.  This is the geometric reason the continuous Type-II route pays no
extra character or overlap factor. -/
theorem disjoint_recenteredIoc_of_threeBSeparated
    {B t u : ℝ} (hB : 0 < B) (hsep : 3 * B ≤ |t - u|) :
    Disjoint (Set.Ioc (t - B) (t + B)) (Set.Ioc (u - B) (u + B)) := by
  rw [Set.disjoint_left]
  intro x hxt hxu
  have htuUpper : t - u < 2 * B := by linarith [hxt.1, hxu.2]
  have htuLower : -(2 * B) < t - u := by linarith [hxu.1, hxt.2]
  have habs : |t - u| < 2 * B := (abs_lt).2 ⟨htuLower, htuUpper⟩
  linarith

/-- Sum of the local fourth moments over one `3B`-separated character fiber.
The recentered windows are disjoint and lie inside the single enlarged
Ramachandra interval. -/
theorem sum_localFourth_le_enlargedFourth
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (W : Finset ℝ)
    {B T : ℝ} (hB : 0 < B) (hT : 0 ≤ T)
    (hheight : ∀ t ∈ W, |t| ≤ T)
    (hsep : ∀ t ∈ W, ∀ u ∈ W, t ≠ u → 3 * B ≤ |t - u|) :
    (∑ t ∈ W, ∫ s in (t - B)..(t + B), criticalLineLFourth chi s) ≤
      ∫ s in (-(T + B))..(T + B), criticalLineLFourth chi s := by
  classical
  let I : ℝ → Set ℝ := fun t => Set.Ioc (t - B) (t + B)
  let J : Set ℝ := Set.Ioc (-(T + B)) (T + B)
  have hpair : Set.Pairwise (↑W) (Function.onFun Disjoint I) := by
    intro t ht u hu hne
    exact disjoint_recenteredIoc_of_threeBSeparated hB
      (hsep t ht u hu hne)
  have hmeas : ∀ t ∈ W, MeasurableSet (I t) := by
    intro t ht
    exact measurableSet_Ioc
  have hintLocal : ∀ t ∈ W,
      IntegrableOn (criticalLineLFourth chi) (I t) := by
    intro t ht
    exact (continuous_criticalLineLFourth chi).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hunion :
      (∫ s in ⋃ t ∈ W, I t, criticalLineLFourth chi s) =
        ∑ t ∈ W, ∫ s in I t, criticalLineLFourth chi s :=
    MeasureTheory.integral_biUnion_finset W hmeas hpair hintLocal
  have hsub : (⋃ t ∈ W, I t) ⊆ J := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨t, ht⟩ := hx
    obtain ⟨htW, hxI⟩ := ht
    have htbound := abs_le.mp (hheight t htW)
    dsimp [I, J] at hxI ⊢
    constructor <;> linarith [hxI.1, hxI.2, htbound.1, htbound.2]
  have hglobal : IntegrableOn (criticalLineLFourth chi) J :=
    (continuous_criticalLineLFourth chi).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hmono :
      (∫ s in ⋃ t ∈ W, I t, criticalLineLFourth chi s) ≤
        ∫ s in J, criticalLineLFourth chi s := by
    apply MeasureTheory.setIntegral_mono_set hglobal
    · exact Filter.Eventually.of_forall fun s => by
        unfold criticalLineLFourth
        positivity
    · exact Filter.Eventually.of_forall fun s hs => hsub hs
  calc
    (∑ t ∈ W, ∫ s in (t - B)..(t + B), criticalLineLFourth chi s) =
        ∑ t ∈ W, ∫ s in I t, criticalLineLFourth chi s := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [intervalIntegral.integral_of_le (by linarith)]
    _ = ∫ s in ⋃ t ∈ W, I t, criticalLineLFourth chi s := hunion.symm
    _ ≤ ∫ s in J, criticalLineLFourth chi s := hmono
    _ = ∫ s in (-(T + B))..(T + B), criticalLineLFourth chi s := by
      rw [intervalIntegral.integral_of_le (by linarith)]

/-- Imaginary part is injective on a `3B`-separated zero family. -/
theorem im_injOn_of_threeBSeparated
    (W : Finset ℂ) {B : ℝ} (hB : 0 < B)
    (hsep : ∀ rho ∈ W, ∀ rho' ∈ W, rho ≠ rho' →
      3 * B ≤ |rho.im - rho'.im|) :
    Set.InjOn Complex.im (↑W : Set ℂ) := by
  intro rho hrho rho' hrho' him
  by_contra hne
  have hs := hsep rho hrho rho' hrho' hne
  rw [him, sub_self, abs_zero] at hs
  linarith

/-- Deterministic all-character continuous Type-II budget.  The only inputs
are the selected zeros and their retained central-integral lower bounds; the
right side is one all-character continuous fourth moment, with no factor of
`q` from separate character estimates. -/
theorem continuous_typeII_family_budget
    {q : ℕ} [NeZero q]
    (W : DirichletCharacter ℂ q → Finset ℂ)
    {delta sigma Y B T b : ℝ}
    (hdelta : 0 < delta) (hY : 1 ≤ Y) (hB : 0 < B)
    (hT : 0 ≤ T) (hb : 0 ≤ b)
    {U : ℕ}
    (hchi : ∀ chi rho, rho ∈ W chi → chi ≠ 1)
    (hrho : ∀ chi rho, rho ∈ W chi →
      DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : ∀ chi rho, rho ∈ W chi →
      1 / 2 + delta ≤ rho.re)
    (hbetaHigh : ∀ chi rho, rho ∈ W chi → rho.re ≤ 7 / 10)
    (hsigma : ∀ chi rho, rho ∈ W chi → sigma ≤ rho.re)
    (hheight : ∀ chi rho, rho ∈ W chi → |rho.im| ≤ T)
    (hsep : ∀ chi rho, rho ∈ W chi → ∀ rho', rho' ∈ W chi →
      rho ≠ rho' → 3 * B ≤ |rho.im - rho'.im|)
    (hcentral : ∀ chi rho, rho ∈ W chi →
      b ≤ ‖normalizedCentralGammaIntegral chi U rho Y B‖) :
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * b ^ 4 ≤
      ((lowStripGammaConstant delta / Real.pi) *
          Real.rpow Y (1 / 2 - sigma) * (2 * Real.sqrt U)) ^ 4 *
        (∫ u in (-B)..B, perronWeight u) ^ 3 *
        allCharacterCriticalLineFourthIntegral q (T + B) := by
  classical
  let A : ℝ := (lowStripGammaConstant delta / Real.pi) *
    Real.rpow Y (1 / 2 - sigma) * (2 * Real.sqrt U)
  let K : ℝ := (∫ u in (-B)..B, perronWeight u) ^ 3
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg
        (div_nonneg (lowStripGammaConstant_pos hdelta).le Real.pi_pos.le)
        (Real.rpow_nonneg (by linarith) _))
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
  have hK : 0 ≤ K := by
    dsimp [K]
    exact pow_nonneg (intervalIntegral.integral_nonneg (by linarith)
      (fun u hu => (perronWeight_pos u).le)) 3
  have hrow : ∀ chi rho, rho ∈ W chi →
      b ^ 4 ≤ A ^ 4 * K *
        (∫ s in (rho.im - B)..(rho.im + B), criticalLineLFourth chi s) := by
    intro chi rho hrhoW
    have hlower4 : b ^ 4 ≤
        ‖normalizedCentralGammaIntegral chi U rho Y B‖ ^ 4 :=
      pow_le_pow_left₀ hb (hcentral chi rho hrhoW) 4
    have hlocal := centralGammaIntegral_fourth_le_localFourth
      chi (hchi chi rho hrhoW) hdelta (U := U)
      (hrho chi rho hrhoW) (hbetaLow chi rho hrhoW)
      (hbetaHigh chi rho hrhoW) hY hB
    have hrpow : Real.rpow Y (1 / 2 - rho.re) ≤
        Real.rpow Y (1 / 2 - sigma) :=
      Real.rpow_le_rpow_of_exponent_le hY
        (by linarith [hsigma chi rho hrhoW])
    let Arho : ℝ := (lowStripGammaConstant delta / Real.pi) *
      Real.rpow Y (1 / 2 - rho.re) * (2 * Real.sqrt U)
    have hArho0 : 0 ≤ Arho := by
      dsimp [Arho]
      exact mul_nonneg
        (mul_nonneg
          (div_nonneg (lowStripGammaConstant_pos hdelta).le Real.pi_pos.le)
          (Real.rpow_nonneg (by linarith) _))
        (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
    have hArho : Arho ≤ A := by
      dsimp [Arho, A]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrpow
          (div_nonneg (lowStripGammaConstant_pos hdelta).le Real.pi_pos.le))
        (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
    have hArho4 : Arho ^ 4 ≤ A ^ 4 :=
      pow_le_pow_left₀ hArho0 hArho 4
    have hlocal0 : 0 ≤
        ∫ s in (rho.im - B)..(rho.im + B), criticalLineLFourth chi s :=
      intervalIntegral.integral_nonneg (by linarith) (fun s hs => by
        unfold criticalLineLFourth
        positivity)
    calc
      b ^ 4 ≤ ‖normalizedCentralGammaIntegral chi U rho Y B‖ ^ 4 := hlower4
      _ ≤ Arho ^ 4 * K *
          (∫ s in (rho.im - B)..(rho.im + B),
            criticalLineLFourth chi s) := by simpa [Arho, K] using hlocal
      _ ≤ A ^ 4 * K *
          (∫ s in (rho.im - B)..(rho.im + B),
            criticalLineLFourth chi s) := by
        gcongr
  calc
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * b ^ 4 =
        ∑ chi : DirichletCharacter ℂ q,
          ∑ rho ∈ W chi, b ^ 4 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro chi hchimem
      simp
    _ ≤ ∑ chi : DirichletCharacter ℂ q,
        ∑ rho ∈ W chi, A ^ 4 * K *
          (∫ s in (rho.im - B)..(rho.im + B),
            criticalLineLFourth chi s) := by
      gcongr with chi hchimem rho hrhoW
      exact hrow chi rho hrhoW
    _ = A ^ 4 * K *
        (∑ chi : DirichletCharacter ℂ q,
          ∑ rho ∈ W chi,
            ∫ s in (rho.im - B)..(rho.im + B),
              criticalLineLFourth chi s) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro chi hchimem
      rw [Finset.mul_sum]
    _ ≤ A ^ 4 * K * allCharacterCriticalLineFourthIntegral q (T + B) := by
      apply mul_le_mul_of_nonneg_left
      unfold allCharacterCriticalLineFourthIntegral
      apply Finset.sum_le_sum
      intro chi hchimem
      let WI : Finset ℝ := (W chi).image Complex.im
      have himinj := im_injOn_of_threeBSeparated (W chi) hB
        (fun rho hrhoW rho' hrhoW' hne =>
          hsep chi rho hrhoW rho' hrhoW' hne)
      have hsumImage :
          (∑ rho ∈ W chi,
            ∫ s in (rho.im - B)..(rho.im + B), criticalLineLFourth chi s) =
          ∑ t ∈ WI,
            ∫ s in (t - B)..(t + B), criticalLineLFourth chi s := by
        dsimp [WI]
        rw [Finset.sum_image]
        intro rho hrhoW rho' hrhoW' him
        exact himinj hrhoW hrhoW' him
      rw [hsumImage]
      apply sum_localFourth_le_enlargedFourth chi WI hB hT
      · intro t ht
        rcases Finset.mem_image.mp ht with ⟨rho, hrhoW, rfl⟩
        exact hheight chi rho hrhoW
      · intro t ht u hu hne
        rcases Finset.mem_image.mp ht with ⟨rho, hrhoW, rfl⟩
        rcases Finset.mem_image.mp hu with ⟨rho', hrhoW', hrhoeq⟩
        subst u
        have hnerho : rho ≠ rho' := by
          intro heq
          subst rho'
          exact hne rfl
        exact hsep chi rho hrhoW rho' hrhoW' hnerho
      · exact mul_nonneg (pow_nonneg hA 4) hK
    _ = ((lowStripGammaConstant delta / Real.pi) *
          Real.rpow Y (1 / 2 - sigma) * (2 * Real.sqrt U)) ^ 4 *
        (∫ u in (-B)..B, perronWeight u) ^ 3 *
        allCharacterCriticalLineFourthIntegral q (T + B) := by
      rfl

/-- Premise-free analytic closure of the continuous Type-II budget by
Ramachandra's certified all-character Theorem 6 at `sigma = 1/2`. -/
theorem continuous_typeII_family_budget_ramachandra
    {q : ℕ} [NeZero q]
    (W : DirichletCharacter ℂ q → Finset ℂ)
    {delta sigma Y B T b : ℝ}
    (hdelta : 0 < delta) (hY : 1 ≤ Y) (hB : 0 < B)
    (hT : 0 ≤ T) (hTB : 3 ≤ T + B) (hb : 0 ≤ b)
    {U : ℕ}
    (hchi : ∀ chi rho, rho ∈ W chi → chi ≠ 1)
    (hrho : ∀ chi rho, rho ∈ W chi →
      DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : ∀ chi rho, rho ∈ W chi →
      1 / 2 + delta ≤ rho.re)
    (hbetaHigh : ∀ chi rho, rho ∈ W chi → rho.re ≤ 7 / 10)
    (hsigma : ∀ chi rho, rho ∈ W chi → sigma ≤ rho.re)
    (hheight : ∀ chi rho, rho ∈ W chi → |rho.im| ≤ T)
    (hsep : ∀ chi rho, rho ∈ W chi → ∀ rho', rho' ∈ W chi →
      rho ≠ rho' → 3 * B ≤ |rho.im - rho'.im|)
    (hcentral : ∀ chi rho, rho ∈ W chi →
      b ≤ ‖normalizedCentralGammaIntegral chi U rho Y B‖) :
    ∃ C₆ : ℝ, 0 < C₆ ∧
      (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * b ^ 4 ≤
        ((lowStripGammaConstant delta / Real.pi) *
            Real.rpow Y (1 / 2 - sigma) * (2 * Real.sqrt U)) ^ 4 *
          (∫ u in (-B)..B, perronWeight u) ^ 3 *
          (C₆ * RamachandraTheorem6ShiftedStripSource.ramachandraTheorem6K2Scale
            q (T + B)) := by
  obtain ⟨C₆, hC₆, hram⟩ :=
    RamachandraTheorem6Unconditional.ramachandraTheorem6K2Source_proved
  refine ⟨C₆, hC₆, ?_⟩
  have hq : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hprod : 1 < (q : ℝ) * (T + B) := by
    have hthree : (3 : ℝ) ≤ (q : ℝ) * (T + B) := by
      nlinarith [mul_le_mul hq hTB (by norm_num : (0 : ℝ) ≤ 3)
        (by positivity : (0 : ℝ) ≤ q)]
    linarith
  have hstrip : |(1 / 2 : ℝ) - 1 / 2| ≤
      (100 * Real.log ((q : ℝ) * (T + B)))⁻¹ := by
    rw [sub_self, abs_zero]
    exact inv_nonneg.mpr (mul_nonneg (by norm_num)
      (Real.log_pos hprod).le)
  have hram' := hram q (T + B) (1 / 2 : ℝ) hTB hstrip
  have heq :
      RamachandraTheorem6ShiftedStripSource.allCharacterShiftedStripFourthIntegral
          q (T + B) (1 / 2) =
        allCharacterCriticalLineFourthIntegral q (T + B) := by
    rfl
  rw [heq] at hram'
  have hdet := continuous_typeII_family_budget W hdelta hY hB hT hb
    hchi hrho hbetaLow hbetaHigh hsigma hheight hsep hcentral
  calc
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * b ^ 4 ≤
        ((lowStripGammaConstant delta / Real.pi) *
            Real.rpow Y (1 / 2 - sigma) * (2 * Real.sqrt U)) ^ 4 *
          (∫ u in (-B)..B, perronWeight u) ^ 3 *
          allCharacterCriticalLineFourthIntegral q (T + B) := hdet
    _ ≤ ((lowStripGammaConstant delta / Real.pi) *
            Real.rpow Y (1 / 2 - sigma) * (2 * Real.sqrt U)) ^ 4 *
          (∫ u in (-B)..B, perronWeight u) ^ 3 *
          (C₆ * RamachandraTheorem6ShiftedStripSource.ramachandraTheorem6K2Scale
            q (T + B)) := by
      have hcoef : 0 ≤
          ((lowStripGammaConstant delta / Real.pi) *
            Real.rpow Y (1 / 2 - sigma) * (2 * Real.sqrt U)) ^ 4 *
          (∫ u in (-B)..B, perronWeight u) ^ 3 :=
        mul_nonneg (by positivity)
          (pow_nonneg (intervalIntegral.integral_nonneg (by linarith)
            (fun u hu => (perronWeight_pos u).le)) 3)
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hram' hcoef

end
end MAPMontgomeryLowStripContinuousTypeII

#print axioms MAPMontgomeryLowStripContinuousTypeII.inv_one_add_sq_le_two_perronWeight
#print axioms MAPMontgomeryLowStripContinuousTypeII.norm_gammaLeftIntegrand_le_perron
#print axioms MAPMontgomeryLowStripContinuousTypeII.norm_normalizedCentralGammaIntegral_le_perronConvolution
#print axioms MAPMontgomeryLowStripContinuousTypeII.perronConvolution_criticalLineFourth_le_localIntegral
#print axioms MAPMontgomeryLowStripContinuousTypeII.centralGammaIntegral_fourth_le_localFourth
#print axioms MAPMontgomeryLowStripContinuousTypeII.disjoint_recenteredIoc_of_threeBSeparated
#print axioms MAPMontgomeryLowStripContinuousTypeII.sum_localFourth_le_enlargedFourth
#print axioms MAPMontgomeryLowStripContinuousTypeII.im_injOn_of_threeBSeparated
#print axioms MAPMontgomeryLowStripContinuousTypeII.continuous_typeII_family_budget
#print axioms MAPMontgomeryLowStripContinuousTypeII.continuous_typeII_family_budget_ramachandra
