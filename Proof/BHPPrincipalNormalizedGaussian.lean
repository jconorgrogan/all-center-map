import BHPPrincipalNegativeEulerBound
import RamachandraPrincipalHighSourceIdentity
import RamachandraFunctionalFactorSharpStrip
import PrincipalZetaFixedStrip
import RightEdgePSeriesExplicitBound
import BHPRademacherGaussianEnvelope
import Mathlib.Analysis.Complex.Hadamard

/-!
# Pole-safe Gaussian interpolation for the principal BHP horizontal edges

The principal `L`-function cannot itself be sent through Hadamard's strip,
because the strip crosses its pole at one.  The correct analytic object is

`LFunctionTrivChar₁(q,s) / (s+1)`.

Away from the pole this is `((s-1)/(s+1)) L(s,1_q)`.  The normalization has
two useful features: it cancels the pole, and the quotient has bounded norm
on both boundary lines and at the high horizontal ordinates.  Thus it does
not introduce the fatal extra power of the height that appears if one
interpolates `(s-1)L(s)` directly.
-/

namespace MAPBHPPrincipalNormalizedGaussian

open Complex Set
open Complex.HadamardThreeLines
open PrimitiveEulerZeroTransport
open MAPBHPPrincipalNegativeEulerBound
open MAPPrincipalZetaFixedStrip
open MAPZeroFreeSiegelSpine
open MAPRightEdgePSeriesExplicitBound
open MAPBHPRademacherGaussianEnvelope
open RamachandraPrincipalHighSourceIdentity
open RamachandraFunctionalFactorSharpStrip

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)

def principalNormalized (q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  DirichletCharacter.LFunctionTrivChar₁ q s / (s + 1)

def principalAux (q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  principalNormalized 1 s * trivialEulerCorrection q s

def principalNormalizedGaussian (q : ℕ) [NeZero q]
    (u : ℝ) (s : ℂ) : ℂ :=
  principalAux q s *
    Complex.exp (3 * (s - (u : ℂ) * I) ^ 2)

theorem principalNormalized_eq_ratio_mul_LFunction
    {q : ℕ} [NeZero q] {s : ℂ} (hs1 : s ≠ 1) :
    principalNormalized q s =
      ((s - 1) / (s + 1)) *
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s := by
  unfold principalNormalized DirichletCharacter.LFunctionTrivChar₁
  rw [Function.update_of_ne hs1]
  ring

theorem principalNormalized_eq_conductorOne_mul_euler
    {q : ℕ} [NeZero q] {s : ℂ} (hs1 : s ≠ 1) :
    principalNormalized q s =
      principalNormalized 1 s *
        trivialEulerCorrection q s := by
  unfold principalNormalized DirichletCharacter.LFunctionTrivChar₁
  rw [Function.update_of_ne hs1, Function.update_of_ne hs1,
    DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs1,
    DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs1]
  simp only [Nat.primeFactors_one, Finset.notMem_empty, Finset.prod_empty,
    one_mul]
  unfold trivialEulerCorrection
  ring

theorem principalAux_eq_principalNormalized_of_ne_one
    {q : ℕ} [NeZero q] {s : ℂ} (hs1 : s ≠ 1) :
    principalAux q s = principalNormalized q s := by
  rw [principalNormalized_eq_conductorOne_mul_euler hs1]
  rfl

theorem norm_principalNormalizedGaussian_exp
    (q : ℕ) [NeZero q] (u : ℝ) (s : ℂ) :
    ‖principalNormalizedGaussian q u s‖ =
      ‖principalAux q s‖ *
        Real.exp (3 * (s.re ^ 2 - (s.im - u) ^ 2)) := by
  unfold principalNormalizedGaussian
  rw [norm_mul, Complex.norm_exp]
  congr 2
  norm_num [Complex.mul_re, Complex.sub_re, Complex.sub_im, pow_two]

private theorem principalNormalizedGaussian_diffContOnCl
    {q : ℕ} [NeZero q] (u l r : ℝ) (hl : -1 < l) (hlr : l < r) :
    DiffContOnCl ℂ (principalNormalizedGaussian q u) (verticalStrip l r) := by
  have hden : ∀ z ∈ closure (verticalStrip l r), z + 1 ≠ 0 := by
    intro z hz hzero
    have hre := congrArg Complex.re hzero
    have hzmem : z.re ∈ Set.Icc l r := by
      unfold verticalStrip at hz
      rw [Complex.closure_preimage_re, closure_Ioo (ne_of_lt hlr)] at hz
      exact hz
    simp at hre
    linarith [hzmem.1]
  have hF : DiffContOnCl ℂ (DirichletCharacter.LFunctionTrivChar₁ q)
      (verticalStrip l r) :=
    (DirichletCharacter.differentiable_LFunctionTrivChar₁ q).diffContOnCl
  have hD : Differentiable ℂ (fun z : ℂ => z + 1) :=
    differentiable_id.add_const 1
  have hN : DiffContOnCl ℂ (principalNormalized 1) (verticalStrip l r) := by
    have hF1 : DiffContOnCl ℂ (DirichletCharacter.LFunctionTrivChar₁ 1)
        (verticalStrip l r) :=
      (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).diffContOnCl
    have hInv := hD.diffContOnCl.inv hden
    change DiffContOnCl ℂ
      (fun z => DirichletCharacter.LFunctionTrivChar₁ 1 z / (z + 1))
      (verticalStrip l r)
    simpa only [div_eq_mul_inv, smul_eq_mul] using hF1.smul hInv
  have hE : Differentiable ℂ (trivialEulerCorrection q) := by
    intro z
    apply AnalyticAt.differentiableAt
    unfold trivialEulerCorrection
    apply Finset.analyticAt_fun_prod
    intro p hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpow : AnalyticAt ℂ (fun w : ℂ => (p : ℂ) ^ (-w)) z := by
      have hdiff : Differentiable ℂ
          (fun w : ℂ => (p : ℂ) ^ (-w)) := by
        intro w
        apply DifferentiableAt.const_cpow differentiableAt_id.neg
        left
        exact_mod_cast hpPrime.ne_zero
      exact hdiff.analyticAt z
    exact analyticAt_const.sub hpow
  have hAux : DiffContOnCl ℂ (principalAux q) (verticalStrip l r) := by
    simpa [principalAux, smul_eq_mul] using hN.smul hE.diffContOnCl
  have hG : Differentiable ℂ
      (fun z : ℂ => Complex.exp (3 * (z - (u : ℂ) * I) ^ 2)) := by
    fun_prop
  simpa [principalNormalizedGaussian, smul_eq_mul] using
    hAux.smul hG.diffContOnCl

theorem norm_ratio_sub_add_le_four
    {s : ℂ} (hre : -(1 / 4 : ℝ) ≤ s.re) :
    ‖(s - 1) / (s + 1)‖ ≤ 4 := by
  have hden : (3 / 4 : ℝ) ≤ ‖s + 1‖ := by
    calc
      (3 / 4 : ℝ) ≤ |(s + 1).re| := by
        rw [abs_of_nonneg (by simp; linarith)]
        simp
        linarith
      _ ≤ ‖s + 1‖ := Complex.abs_re_le_norm _
  have hnum : ‖s - 1‖ ≤ ‖s + 1‖ + 2 := by
    have hid : s - 1 = (s + 1) - 2 := by ring
    rw [hid]
    calc
      ‖s + 1 - 2‖ ≤ ‖s + 1‖ + ‖(2 : ℂ)‖ := norm_sub_le _ _
      _ = ‖s + 1‖ + 2 := by norm_num
  have hdenPos : 0 < ‖s + 1‖ := lt_of_lt_of_le (by norm_num) hden
  rw [norm_div]
  apply (div_le_iff₀ hdenPos).2
  nlinarith

theorem norm_ratio_sub_add_right_le_one
    {s : ℂ} (hre : 0 ≤ s.re) :
    ‖(s - 1) / (s + 1)‖ ≤ 1 := by
  have hsquares : ‖s - 1‖ ^ 2 ≤ ‖s + 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [Complex.sub_re, one_re, Complex.sub_im, one_im, sub_zero,
      Complex.add_re, Complex.add_im, add_zero]
    nlinarith
  have hnorm : ‖s - 1‖ ≤ ‖s + 1‖ := by nlinarith [norm_nonneg (s - 1), norm_nonneg (s + 1)]
  have hden : 0 < ‖s + 1‖ := by
    apply norm_pos_iff.mpr
    intro h
    have hre' := congrArg Complex.re h
    simp at hre'
    linarith
  rw [norm_div]
  exact (div_le_one hden).2 hnorm

theorem norm_add_div_sub_le_four_of_high
    {s : ℂ} (hreLo : 0 ≤ s.re) (hreHi : s.re ≤ 2)
    (him : 1 ≤ |s.im|) :
    ‖(s + 1) / (s - 1)‖ ≤ 4 := by
  have hden : 1 ≤ ‖s - 1‖ :=
    him.trans (by simpa using Complex.abs_im_le_norm (s - 1))
  have hnum : ‖s + 1‖ ≤ ‖s - 1‖ + 2 := by
    have hid : s + 1 = (s - 1) + 2 := by ring
    rw [hid]
    calc
      ‖s - 1 + 2‖ ≤ ‖s - 1‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
      _ = ‖s - 1‖ + 2 := by norm_num
  have hdenPos : 0 < ‖s - 1‖ := zero_lt_one.trans_le hden
  rw [norm_div]
  apply (div_le_iff₀ hdenPos).2
  nlinarith

def trivialEulerQuarterBound (q : ℕ) : ℝ :=
  ∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (1 / 4 : ℝ))

theorem trivialEulerQuarterBound_nonneg (q : ℕ) :
    0 ≤ trivialEulerQuarterBound q := by
  unfold trivialEulerQuarterBound
  positivity

theorem norm_trivialEulerCorrection_le_quarterBound
    {q : ℕ} {s : ℂ} (hre : -(1 / 4 : ℝ) ≤ s.re) :
    ‖trivialEulerCorrection q s‖ ≤ trivialEulerQuarterBound q := by
  unfold trivialEulerCorrection trivialEulerQuarterBound
  rw [norm_prod]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro p hp
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpPos : 0 < (p : ℝ) := by exact_mod_cast hpPrime.pos
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hpPrime.one_le
  have hpow : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    change ‖((p : ℝ) : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpPos]
    congr 1
  have hexp : -s.re ≤ (1 / 4 : ℝ) := by linarith
  calc
    ‖1 - (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ :=
      norm_sub_le _ _
    _ = 1 + (p : ℝ) ^ (-s.re) := by rw [norm_one, hpow]
    _ ≤ 1 + (p : ℝ) ^ (1 / 4 : ℝ) := by
      gcongr

private theorem one_add_abs_mul_exp_cube_le_sixtyfour (r : ℝ) (hr : 0 ≤ r) :
    (1 + r) ^ 6 * Real.exp (-3 * r ^ 2) ≤ 64 := by
  have h := one_add_sq_mul_exp_neg_sq_le_four r hr
  have h0 : 0 ≤ (1 + r) ^ 2 * Real.exp (-(r ^ 2)) := by positivity
  have hcub := pow_le_pow_left₀ h0 h 3
  calc
    (1 + r) ^ 6 * Real.exp (-3 * r ^ 2) =
        ((1 + r) ^ 2 * Real.exp (-(r ^ 2))) ^ 3 := by
      rw [mul_pow, ← Real.exp_nat_mul]
      ring_nf
    _ ≤ 4 ^ 3 := hcub
    _ = 64 := by norm_num

private theorem principalNormalizedGaussian_bddAbove
    {q : ℕ} [NeZero q] {u l r : ℝ}
    (hlLo : -(1 / 4 : ℝ) ≤ l) (hlr : l < r) (hrHi : r ≤ 2) :
    BddAbove ((norm ∘ principalNormalizedGaussian q u) ''
      verticalClosedStrip l r) := by
  let E := trivialEulerQuarterBound q
  let M := 2200 * E * (5 + |u|) ^ 6 * 64 * Real.exp 12
  have hE0 : 0 ≤ E := by
    dsimp [E]
    exact trivialEulerQuarterBound_nonneg q
  refine ⟨M, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  have hzlo : -(1 / 4 : ℝ) ≤ z.re := hlLo.trans hz.1
  have hzloOne : -1 ≤ z.re := by linarith
  have hzhiTwo : z.re ≤ 2 := hz.2.trans hrHi
  have hF := norm_principalRegularized_fixedStrip_le hzloOne hzhiTwo
  have hden : (3 / 4 : ℝ) ≤ ‖z + 1‖ := by
    calc
      (3 / 4 : ℝ) ≤ |(z + 1).re| := by
        rw [abs_of_nonneg (by simp; linarith)]
        simp
        linarith
      _ ≤ ‖z + 1‖ := Complex.abs_re_le_norm _
  have hdenPos : 0 < ‖z + 1‖ := lt_of_lt_of_le (by norm_num) hden
  have hN : ‖principalNormalized 1 z‖ ≤ 2200 * ‖z + 3‖ ^ 6 := by
    unfold principalNormalized
    rw [norm_div]
    apply (div_le_iff₀ hdenPos).2
    calc
      ‖DirichletCharacter.LFunctionTrivChar₁ 1 z‖ ≤
          1600 * ‖z + 3‖ ^ 6 := hF
      _ ≤ (2200 * ‖z + 3‖ ^ 6) * ‖z + 1‖ := by
        have hp0 : 0 ≤ ‖z + 3‖ ^ 6 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hden hp0]
  have hEuler := norm_trivialEulerCorrection_le_quarterBound (q := q) hzlo
  have hAux : ‖principalAux q z‖ ≤ 2200 * E * ‖z + 3‖ ^ 6 := by
    unfold principalAux
    rw [norm_mul]
    exact (mul_le_mul hN hEuler (norm_nonneg _) (by positivity)).trans_eq (by
      dsimp [E]
      ring)
  let d := |z.im - u|
  have hd : 0 ≤ d := abs_nonneg _
  have hnormBasic : ‖z + 3‖ ≤ 5 + |z.im| := by
    calc
      ‖z + 3‖ ≤ |(z + 3).re| + |(z + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |z.re + 3| + |z.im| := by simp
      _ ≤ 5 + |z.im| := by
        rw [abs_of_nonneg (by linarith)]
        linarith
  have him : |z.im| ≤ |u| + d := by
    dsimp [d]
    have h := abs_add_le u (z.im - u)
    rw [show u + (z.im - u) = z.im by ring] at h
    exact h
  have hnormCenter : ‖z + 3‖ ≤ (5 + |u|) * (1 + d) := by
    calc
      ‖z + 3‖ ≤ 5 + |z.im| := hnormBasic
      _ ≤ 5 + |u| + d := by linarith
      _ ≤ (5 + |u|) * (1 + d) := by
        nlinarith [abs_nonneg u]
  have hpowNorm : ‖z + 3‖ ^ 6 ≤ ((5 + |u|) * (1 + d)) ^ 6 :=
    pow_le_pow_left₀ (norm_nonneg _) hnormCenter 6
  have hreSq : z.re ^ 2 ≤ 4 := by nlinarith [hzlo, hzhiTwo]
  have hExpRe : Real.exp (3 * z.re ^ 2) ≤ Real.exp 12 := by
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hcube := one_add_abs_mul_exp_cube_le_sixtyfour d hd
  have hdSq : d ^ 2 = (z.im - u) ^ 2 := sq_abs _
  have hExpSplit :
      Real.exp (3 * (z.re ^ 2 - (z.im - u) ^ 2)) =
        Real.exp (3 * z.re ^ 2) * Real.exp (-3 * d ^ 2) := by
    rw [hdSq]
    rw [← Real.exp_add]
    congr 1
    ring
  change ‖principalNormalizedGaussian q u z‖ ≤ M
  rw [norm_principalNormalizedGaussian_exp, hExpSplit]
  calc
    ‖principalAux q z‖ *
        (Real.exp (3 * z.re ^ 2) * Real.exp (-3 * d ^ 2)) ≤
      (2200 * E * ((5 + |u|) * (1 + d)) ^ 6) *
        (Real.exp 12 * Real.exp (-3 * d ^ 2)) := by
      have hAux' : ‖principalAux q z‖ ≤
          2200 * E * ((5 + |u|) * (1 + d)) ^ 6 :=
        hAux.trans (mul_le_mul_of_nonneg_left hpowNorm (by positivity))
      have hExp' :
          Real.exp (3 * z.re ^ 2) * Real.exp (-3 * d ^ 2) ≤
            Real.exp 12 * Real.exp (-3 * d ^ 2) :=
        mul_le_mul_of_nonneg_right hExpRe (Real.exp_pos _).le
      exact mul_le_mul hAux' hExp' (by positivity) (by positivity)
    _ = 2200 * E * (5 + |u|) ^ 6 *
        ((1 + d) ^ 6 * Real.exp (-3 * d ^ 2)) * Real.exp 12 := by ring
    _ ≤ 2200 * E * (5 + |u|) ^ 6 * 64 * Real.exp 12 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcube (by positivity))
        (Real.exp_pos _).le
    _ = M := by rfl

def principalLeftGaussianBound (q : ℕ) (x0 u : ℝ) : ℝ :=
  1024000000 * (1 + 400 * Real.log x0) * Real.exp 4 *
    Real.sqrt (q : ℝ) * (1 + |u|)

def principalRightGaussianBound (x0 : ℝ) : ℝ :=
  rightEdgePSeries (Real.log x0)⁻¹ *
    Real.exp (3 * (1 + (Real.log x0)⁻¹) ^ 2)

private theorem one_add_abs_mul_gaussian_le_four (u v : ℝ) :
    (1 + |v|) * Real.exp (-((v - u) ^ 2)) ≤ 4 * (1 + |u|) := by
  let d := |v - u|
  have hd : 0 ≤ d := abs_nonneg _
  have htri : |v| ≤ |u| + d := by
    have h := abs_add_le u (v - u)
    rw [show u + (v - u) = v by ring] at h
    exact h
  have hlinear : 1 + |v| ≤ (1 + |u|) * (1 + d) := by
    nlinarith [abs_nonneg u]
  have hsq := one_add_sq_mul_exp_neg_sq_le_four d hd
  have hone : 1 + d ≤ (1 + d) ^ 2 := by nlinarith
  have hlinGauss : (1 + d) * Real.exp (-(d ^ 2)) ≤ 4 := by
    calc
      (1 + d) * Real.exp (-(d ^ 2)) ≤
          (1 + d) ^ 2 * Real.exp (-(d ^ 2)) :=
        mul_le_mul_of_nonneg_right hone (Real.exp_pos _).le
      _ ≤ 4 := hsq
  have hdSq : d ^ 2 = (v - u) ^ 2 := sq_abs _
  rw [← hdSq]
  calc
    (1 + |v|) * Real.exp (-(d ^ 2)) ≤
        ((1 + |u|) * (1 + d)) * Real.exp (-(d ^ 2)) :=
      mul_le_mul_of_nonneg_right hlinear (Real.exp_pos _).le
    _ = (1 + |u|) * ((1 + d) * Real.exp (-(d ^ 2))) := by ring
    _ ≤ (1 + |u|) * 4 :=
      mul_le_mul_of_nonneg_left hlinGauss (by positivity)
    _ = 4 * (1 + |u|) := by ring

private theorem norm_functionalFactor_canonicalNegative_le
    {x0 v : ℝ} (hx0 : 8 ≤ x0) (hv : v ≠ 0) :
    ‖BHPRamachandraMeanValueFromDyadicAFE.ramachandraFunctionalFactor chiOne
        (((-RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset x0 : ℝ) : ℂ) +
          v * I)‖ ≤
      16000000 * (1 + |v|) := by
  let delta := RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset x0
  have hxOne : 1 < x0 := by linarith
  have hlog : 0 < Real.log x0 := Real.log_pos hxOne
  have hdelta0 : 0 < delta := by
    dsimp [delta, RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset]
    positivity
  have hdeltaQuarter : delta ≤ (1 / 4 : ℝ) := by
    dsimp [delta, RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset]
    have hlog8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    have hlog8le : Real.log 8 ≤ Real.log x0 :=
      Real.log_le_log (by norm_num) hx0
    rw [hlog8] at hlog8le
    have hden : (4 : ℝ) ≤ 400 * Real.log x0 := by
      nlinarith [Real.log_two_gt_d9]
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hden
    simpa [one_div] using hi
  let z : ℂ := (((-delta : ℝ) : ℂ) + v * I)
  have hzre : z.re = -delta := by simp [z]
  have hzim : z.im = v := by simp [z]
  have hsharp := norm_ramachandraFunctionalFactor_sharp_le chiOne
    DirichletCharacter.isPrimitive_one_level_one
    (z := z) (by rw [hzre]; linarith) (by rw [hzre]; linarith)
    (by rw [hzim]; exact abs_pos.mpr hv)
  have h2000 : (1 : ℝ) ≤ 2000 := by norm_num
  have hbase : 1 ≤ 2000 * (1 + |v|) := by
    nlinarith [abs_nonneg v]
  have hpow1 : Real.rpow 2000 (1 / 2 - delta) ≤ 2000 := by
    calc
      Real.rpow 2000 (1 / 2 - delta) ≤ Real.rpow 2000 1 :=
        Real.rpow_le_rpow_of_exponent_le h2000 (by linarith)
      _ = 2000 := by norm_num
  have hpow2 : Real.rpow (2000 * (1 + |v|)) (1 / 2 + delta) ≤
      2000 * (1 + |v|) := by
    calc
      Real.rpow (2000 * (1 + |v|)) (1 / 2 + delta) ≤
          Real.rpow (2000 * (1 + |v|)) 1 :=
        Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
      _ = 2000 * (1 + |v|) := by norm_num
  rw [hzre, hzim] at hsharp
  norm_num at hsharp
  calc
    ‖BHPRamachandraMeanValueFromDyadicAFE.ramachandraFunctionalFactor chiOne z‖ ≤
        4 * (Real.rpow 2000 (1 / 2 - delta) *
          Real.rpow (2000 * (1 + |v|)) (1 / 2 + delta)) := by
      simpa [z] using hsharp
    _ ≤ 4 * (2000 * (2000 * (1 + |v|))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul hpow1 hpow2
        (Real.rpow_nonneg (by positivity) _) (by norm_num)
    _ = 16000000 * (1 + |v|) := by ring

private theorem principalNormalizedGaussian_leftBoundary
    {q : ℕ} [NeZero q] {x0 u : ℝ}
    (hx0 : 8 ≤ x0) (hqx : (q : ℝ) ≤ x0) :
    ∀ z ∈ Complex.re ⁻¹'
        ({-RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset x0} : Set ℝ),
      ‖principalNormalizedGaussian q u z‖ ≤
        principalLeftGaussianBound q x0 u := by
  intro z hz
  let delta := RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset x0
  have hzre : z.re = -delta := by simpa [delta] using hz
  let v := z.im
  have hzform : z = (((-delta : ℝ) : ℂ) + v * I) := by
    apply Complex.ext <;> simp [v, hzre]
  have hxOne : 1 < x0 := by linarith
  have hlog : 0 < Real.log x0 := Real.log_pos hxOne
  have hdelta0 : 0 < delta := by
    dsimp [delta, RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset]
    positivity
  have hdeltaQuarter : delta ≤ (1 / 4 : ℝ) := by
    have hlog8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    have hlog8le : Real.log 8 ≤ Real.log x0 :=
      Real.log_le_log (by norm_num) hx0
    rw [hlog8] at hlog8le
    dsimp [delta, RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset]
    have hden : (4 : ℝ) ≤ 400 * Real.log x0 := by
      nlinarith [Real.log_two_gt_d9]
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hden
    simpa [one_div] using hi
  have hEuler := norm_trivialEulerCorrection_canonical_le_four_exp_sqrt
    (q := q) (v := v) hxOne hqx
  by_cases hv : v = 0
  · have hzreal : z = ((-delta : ℝ) : ℂ) := by
      rw [hzform, hv]
      simp
    have hF := norm_principalRegularized_fixedStrip_le
      (z := ((-delta : ℝ) : ℂ)) (by simp; linarith) (by simp; linarith)
    have hden : (3 / 4 : ℝ) ≤ ‖(((-delta : ℝ) : ℂ) + 1)‖ := by
      have heq : (((-delta : ℝ) : ℂ) + 1) = (((1 - delta : ℝ) : ℂ)) := by
        push_cast
        ring
      rw [heq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
      linarith
    have hN : ‖principalNormalized 1 (((-delta : ℝ) : ℂ))‖ ≤
        2200 * 3 ^ 6 := by
      unfold principalNormalized
      rw [norm_div]
      have hdenPos : 0 < ‖(((-delta : ℝ) : ℂ) + 1)‖ :=
        lt_of_lt_of_le (by norm_num) hden
      apply (div_le_iff₀ hdenPos).2
      have hnorm3 : ‖(((-delta : ℝ) : ℂ) + 3)‖ ≤ 3 := by
        have heq : (((-delta : ℝ) : ℂ) + 3) = (((3 - delta : ℝ) : ℂ)) := by
          push_cast
          ring
        rw [heq, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith)]
        linarith
      calc
        ‖DirichletCharacter.LFunctionTrivChar₁ 1 ((-delta : ℝ) : ℂ)‖ ≤
            1600 * ‖(((-delta : ℝ) : ℂ) + 3)‖ ^ 6 := hF
        _ ≤ 1600 * 3 ^ 6 := by gcongr
        _ ≤ (2200 * 3 ^ 6) * ‖(((-delta : ℝ) : ℂ) + 1)‖ := by
          calc
            (1600 : ℝ) * 3 ^ 6 ≤ (2200 * 3 ^ 6) * (3 / 4 : ℝ) := by
              norm_num
            _ ≤ (2200 * 3 ^ 6) * ‖(((-delta : ℝ) : ℂ) + 1)‖ :=
              mul_le_mul_of_nonneg_left hden (by norm_num)
    have hAux : ‖principalAux q (((-delta : ℝ) : ℂ))‖ ≤
        (2200 * 3 ^ 6) *
          (4 * Real.exp (1 / 400 : ℝ) * Real.sqrt (q : ℝ)) := by
      unfold principalAux
      rw [norm_mul]
      exact mul_le_mul hN (by simpa [hv, delta] using hEuler)
        (norm_nonneg _) (by positivity)
    have hExp : Real.exp (3 * delta ^ 2) ≤ Real.exp 3 := by
      exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg delta])
    rw [hzreal, norm_principalNormalizedGaussian_exp]
    simp only [ofReal_re, ofReal_im, sub_zero]
    calc
      ‖principalAux q ((-delta : ℝ) : ℂ)‖ *
          Real.exp (3 * ((-delta) ^ 2 - (0 - u) ^ 2)) ≤
        ((2200 * 3 ^ 6) *
          (4 * Real.exp (1 / 400 : ℝ) * Real.sqrt (q : ℝ))) *
          Real.exp (3 * delta ^ 2) := by
        apply mul_le_mul hAux
        · apply Real.exp_le_exp.mpr
          nlinarith [sq_nonneg u]
        · positivity
        · positivity
      _ ≤ ((2200 * 3 ^ 6) *
          (4 * Real.exp (1 / 400 : ℝ) * Real.sqrt (q : ℝ))) *
          Real.exp 3 := by gcongr
      _ ≤ principalLeftGaussianBound q x0 u := by
        unfold principalLeftGaussianBound
        have hP : 1 ≤ 1 + 400 * Real.log x0 := by linarith
        have hu : 1 ≤ 1 + |u| := by linarith [abs_nonneg u]
        have hexp : Real.exp (1 / 400 : ℝ) * Real.exp 3 ≤ Real.exp 4 := by
          rw [← Real.exp_add]
          exact Real.exp_le_exp.mpr (by norm_num)
        have hq0 := Real.sqrt_nonneg (q : ℝ)
        have hconst : (2200 : ℝ) * 3 ^ 6 * 4 ≤ 1024000000 := by norm_num
        calc
          (2200 * 3 ^ 6) * (4 * Real.exp (1 / 400) * Real.sqrt (q : ℝ)) *
              Real.exp 3 =
            (2200 * 3 ^ 6 * 4) *
              (Real.exp (1 / 400) * Real.exp 3) * Real.sqrt (q : ℝ) := by ring
          _ ≤ 1024000000 * Real.exp 4 * Real.sqrt (q : ℝ) := by
            exact mul_le_mul
              (mul_le_mul hconst hexp (by positivity) (by norm_num))
              (le_refl _) hq0 (by positivity)
          _ ≤ 1024000000 * (1 + 400 * Real.log x0) * Real.exp 4 *
              Real.sqrt (q : ℝ) * (1 + |u|) := by
            have hbase0 : 0 ≤ 1024000000 * Real.exp 4 * Real.sqrt (q : ℝ) := by
              positivity
            calc
              1024000000 * Real.exp 4 * Real.sqrt (q : ℝ) ≤
                  (1024000000 * Real.exp 4 * Real.sqrt (q : ℝ)) *
                    (1 + 400 * Real.log x0) :=
                le_mul_of_one_le_right hbase0 hP
              _ ≤ ((1024000000 * Real.exp 4 * Real.sqrt (q : ℝ)) *
                    (1 + 400 * Real.log x0)) * (1 + |u|) :=
                le_mul_of_one_le_right
                  (mul_nonneg hbase0 (zero_le_one.trans hP)) hu
              _ = 1024000000 * (1 + 400 * Real.log x0) * Real.exp 4 *
                    Real.sqrt (q : ℝ) * (1 + |u|) := by ring
  · have hz1 : z ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      rw [hzre] at hre
      norm_num at hre
      linarith
    have hratio := norm_ratio_sub_add_le_four
      (s := z) (by rw [hzre]; linarith)
    have hfe := LFunction_eq_ramachandraFunctionalFactor_mul_dual_principal
      (z := z) (by rw [hzre]; linarith) (by rw [hzre]; linarith)
    have hfactor := norm_functionalFactor_canonicalNegative_le hx0 hv
    have hreflect := norm_LFunction_rightEdge_le_pSeries chiOne
      hdelta0 (z := 1 - z) (by simp [hzre])
    have hN : ‖principalNormalized 1 z‖ ≤
        64000000 * rightEdgePSeries delta * (1 + |v|) := by
      rw [principalNormalized_eq_ratio_mul_LFunction hz1,
        hfe, norm_mul, norm_mul]
      have hreflectInv :
          ‖DirichletCharacter.LFunction chiOne⁻¹ (1 - z)‖ ≤
            rightEdgePSeries delta := by simpa using hreflect
      calc
        ‖(z - 1) / (z + 1)‖ *
            (‖BHPRamachandraMeanValueFromDyadicAFE.ramachandraFunctionalFactor chiOne z‖ *
              ‖DirichletCharacter.LFunction chiOne⁻¹ (1 - z)‖) ≤
          4 * (16000000 * (1 + |v|) * rightEdgePSeries delta) := by
            have hfactor' :
                ‖BHPRamachandraMeanValueFromDyadicAFE.ramachandraFunctionalFactor chiOne z‖ ≤
                  16000000 * (1 + |v|) := by
              simpa [hzform] using hfactor
            have hinner := mul_le_mul hfactor' hreflectInv
              (norm_nonneg _)
              (by positivity : 0 ≤ 16000000 * (1 + |v|))
            exact mul_le_mul hratio hinner
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
              (by norm_num)
        _ = 64000000 * rightEdgePSeries delta * (1 + |v|) := by ring
    have hAux : ‖principalAux q z‖ ≤
        (64000000 * rightEdgePSeries delta * (1 + |v|)) *
          (4 * Real.exp (1 / 400 : ℝ) * Real.sqrt (q : ℝ)) := by
      unfold principalAux
      rw [norm_mul]
      have hP0 : 0 ≤ rightEdgePSeries delta :=
        (zero_le_one.trans (one_le_rightEdgePSeries hdelta0))
      exact mul_le_mul hN (by simpa [hzform] using hEuler)
        (norm_nonneg _) (by positivity)
    have hdeltaSq : delta ^ 2 ≤ 1 := by nlinarith [sq_nonneg delta]
    have hGauss :
        (1 + |v|) * Real.exp (3 * (delta ^ 2 - (v - u) ^ 2)) ≤
          4 * Real.exp 3 * (1 + |u|) := by
      have hsplit : Real.exp (3 * (delta ^ 2 - (v - u) ^ 2)) ≤
          Real.exp 3 * Real.exp (-((v - u) ^ 2)) := by
        rw [show 3 * (delta ^ 2 - (v - u) ^ 2) =
          3 * delta ^ 2 + (-3 * (v - u) ^ 2) by ring, Real.exp_add]
        have h1 : Real.exp (3 * delta ^ 2) ≤ Real.exp 3 :=
          Real.exp_le_exp.mpr (by nlinarith)
        have h2 : Real.exp (-3 * (v - u) ^ 2) ≤
            Real.exp (-((v - u) ^ 2)) :=
          Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (v - u)])
        exact mul_le_mul h1 h2 (Real.exp_pos _).le (Real.exp_pos _).le
      calc
        (1 + |v|) * Real.exp (3 * (delta ^ 2 - (v - u) ^ 2)) ≤
          (1 + |v|) * (Real.exp 3 * Real.exp (-((v - u) ^ 2))) :=
            mul_le_mul_of_nonneg_left hsplit (by positivity)
        _ = Real.exp 3 *
            ((1 + |v|) * Real.exp (-((v - u) ^ 2))) := by ring
        _ ≤ Real.exp 3 * (4 * (1 + |u|)) :=
          mul_le_mul_of_nonneg_left
            (one_add_abs_mul_gaussian_le_four u v) (Real.exp_pos _).le
        _ = 4 * Real.exp 3 * (1 + |u|) := by ring
    rw [norm_principalNormalizedGaussian_exp, hzre]
    have hsqneg : (-delta) ^ 2 = delta ^ 2 := by ring
    rw [hsqneg]
    calc
      ‖principalAux q z‖ * Real.exp (3 * (delta ^ 2 - (z.im - u) ^ 2)) ≤
        ((64000000 * rightEdgePSeries delta * (1 + |v|)) *
          (4 * Real.exp (1 / 400 : ℝ) * Real.sqrt (q : ℝ))) *
          Real.exp (3 * (delta ^ 2 - (v - u) ^ 2)) := by
        rw [show z.im = v by rfl]
        exact mul_le_mul_of_nonneg_right hAux (Real.exp_pos _).le
      _ = 256000000 * rightEdgePSeries delta *
          Real.exp (1 / 400 : ℝ) * Real.sqrt (q : ℝ) *
          ((1 + |v|) * Real.exp (3 * (delta ^ 2 - (v - u) ^ 2))) := by ring
      _ ≤ 256000000 * rightEdgePSeries delta *
          Real.exp (1 / 400 : ℝ) * Real.sqrt (q : ℝ) *
          (4 * Real.exp 3 * (1 + |u|)) := by
        have hP0 : 0 ≤ rightEdgePSeries delta :=
          zero_le_one.trans (one_le_rightEdgePSeries hdelta0)
        exact mul_le_mul_of_nonneg_left hGauss (by positivity)
      _ ≤ principalLeftGaussianBound q x0 u := by
        unfold principalLeftGaussianBound
        have hP := rightEdgePSeries_le_one_add_inv hdelta0
        have hdInv : delta⁻¹ = 400 * Real.log x0 := by
          dsimp [delta, RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset]
          field_simp
        have hP' : rightEdgePSeries delta ≤ 1 + delta⁻¹ := by
          simpa [one_div] using hP
        rw [hdInv] at hP'
        have hexp : Real.exp (1 / 400 : ℝ) * Real.exp 3 ≤ Real.exp 4 := by
          rw [← Real.exp_add]
          exact Real.exp_le_exp.mpr (by norm_num)
        have hq0 := Real.sqrt_nonneg (q : ℝ)
        have hu0 : 0 ≤ 1 + |u| := by positivity
        calc
          256000000 * rightEdgePSeries delta * Real.exp (1 / 400) *
                Real.sqrt (q : ℝ) * (4 * Real.exp 3 * (1 + |u|)) =
            1024000000 * rightEdgePSeries delta *
              (Real.exp (1 / 400) * Real.exp 3) *
              Real.sqrt (q : ℝ) * (1 + |u|) := by ring
          _ ≤ 1024000000 * (1 + 400 * Real.log x0) * Real.exp 4 *
              Real.sqrt (q : ℝ) * (1 + |u|) := by
            gcongr

private theorem principalNormalizedGaussian_rightBoundary
    {q : ℕ} [NeZero q] {x0 u : ℝ} (hx0 : 8 ≤ x0) :
    ∀ z ∈ Complex.re ⁻¹'
        ({1 + (Real.log x0)⁻¹} : Set ℝ),
      ‖principalNormalizedGaussian q u z‖ ≤
        principalRightGaussianBound x0 := by
  intro z hz
  let r := (Real.log x0)⁻¹
  have hzre : z.re = 1 + r := by simpa [r] using hz
  have hxOne : 1 < x0 := by linarith
  have hlog : 0 < Real.log x0 := Real.log_pos hxOne
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hlog8le : Real.log 8 ≤ Real.log x0 :=
    Real.log_le_log (by norm_num) hx0
  rw [hlog8] at hlog8le
  have hlogTwo : 2 ≤ Real.log x0 := by
    nlinarith [Real.log_two_gt_d9]
  have hrHalf : r ≤ (1 / 2 : ℝ) := by
    dsimp [r]
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hlogTwo
    simpa [one_div] using hi
  have hz1 : z ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [hzre] at hre
    norm_num at hre
    linarith
  have hauxEq := principalAux_eq_principalNormalized_of_ne_one
    (q := q) (s := z) hz1
  have hratio := norm_ratio_sub_add_right_le_one
    (s := z) (by rw [hzre]; linarith)
  have hL := norm_LFunction_rightEdge_le_pSeries
    (1 : DirichletCharacter ℂ q) hr0 hzre
  have hAux : ‖principalAux q z‖ ≤ rightEdgePSeries r := by
    rw [hauxEq, principalNormalized_eq_ratio_mul_LFunction hz1, norm_mul]
    simpa using mul_le_mul hratio hL (norm_nonneg _) (by norm_num)
  rw [norm_principalNormalizedGaussian_exp]
  calc
    ‖principalAux q z‖ * Real.exp (3 * (z.re ^ 2 - (z.im - u) ^ 2)) ≤
        rightEdgePSeries r * Real.exp (3 * (1 + r) ^ 2) := by
      apply mul_le_mul hAux
      · apply Real.exp_le_exp.mpr
        rw [hzre]
        nlinarith [sq_nonneg (z.im - u)]
      · positivity
      · exact zero_le_one.trans (one_le_rightEdgePSeries hr0)
    _ = principalRightGaussianBound x0 := by
      rfl

/-- Hadamard interpolation for the pole-safe ambient principal function on
the literal Ramachandra-to-Titchmarsh strip. -/
theorem norm_principalAux_canonical_interp
    {q : ℕ} [NeZero q] {x0 sigma u : ℝ}
    (hx0 : 8 ≤ x0) (hqx : (q : ℝ) ≤ x0)
    (hsigmaLo :
      -RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset x0 ≤ sigma)
    (hsigmaHi : sigma ≤ 1 + (Real.log x0)⁻¹) :
    ‖principalAux q (((sigma : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
      Real.rpow (principalLeftGaussianBound q x0 u)
        (((1 + (Real.log x0)⁻¹) - sigma) /
          ((1 + (Real.log x0)⁻¹) +
            RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset x0)) *
      Real.rpow (principalRightGaussianBound x0)
        ((sigma + RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset x0) /
          ((1 + (Real.log x0)⁻¹) +
            RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset x0)) := by
  let delta := RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset x0
  let r := (Real.log x0)⁻¹
  let left := -delta
  let right := 1 + r
  have hxOne : 1 < x0 := by linarith
  have hlog : 0 < Real.log x0 := Real.log_pos hxOne
  have hdelta0 : 0 < delta := by
    dsimp [delta, RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset]
    positivity
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hlog8le : Real.log 8 ≤ Real.log x0 :=
    Real.log_le_log (by norm_num) hx0
  rw [hlog8] at hlog8le
  have hlogTwo : 2 ≤ Real.log x0 := by
    nlinarith [Real.log_two_gt_d9]
  have hrHalf : r ≤ (1 / 2 : ℝ) := by
    dsimp [r]
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hlogTwo
    simpa [one_div] using hi
  have hdeltaQuarter : delta ≤ (1 / 4 : ℝ) := by
    dsimp [delta, RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset]
    have hden : (4 : ℝ) ≤ 400 * Real.log x0 := by nlinarith
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hden
    simpa [one_div] using hi
  have hwidth : left < right := by dsimp [left, right]; linarith
  have hmem : (((sigma : ℝ) : ℂ) + (u : ℂ) * I) ∈
      verticalClosedStrip left right := by
    constructor <;> simp [left, right, delta, r] <;> assumption
  have hinterp :=
    Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
      (f := principalNormalizedGaussian q u)
      (z := (((sigma : ℝ) : ℂ) + (u : ℂ) * I))
      (l := left) (u := right)
      (a := principalLeftGaussianBound q x0 u)
      (b := principalRightGaussianBound x0)
      hwidth hmem
      (principalNormalizedGaussian_diffContOnCl u left right
        (by dsimp [left]; linarith) hwidth)
      (principalNormalizedGaussian_bddAbove
        (q := q) (u := u) (l := left) (r := right)
        (by dsimp [left]; linarith) hwidth (by dsimp [right]; linarith))
      (by
        simpa [left, delta] using
          (principalNormalizedGaussian_leftBoundary (q := q) (x0 := x0)
            (u := u) hx0 hqx))
      (by
        simpa [right, r] using
          (principalNormalizedGaussian_rightBoundary (q := q) (x0 := x0)
            (u := u) hx0))
  have hgauss := norm_principalNormalizedGaussian_exp q u
    (((sigma : ℝ) : ℂ) + (u : ℂ) * I)
  have hgauss' :
      ‖principalNormalizedGaussian q u
        (((sigma : ℝ) : ℂ) + (u : ℂ) * I)‖ =
      ‖principalAux q (((sigma : ℝ) : ℂ) + (u : ℂ) * I)‖ *
        Real.exp (3 * sigma ^ 2) := by
    simpa using hgauss
  have hone : 1 ≤ Real.exp (3 * sigma ^ 2) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  have haux0 := norm_nonneg
    (principalAux q (((sigma : ℝ) : ℂ) + (u : ℂ) * I))
  have hW : 0 < 1 + r + delta := by linarith
  have hleftExp :
      1 - (sigma + delta) / (1 + r + delta) =
        (1 + r - sigma) / (1 + r + delta) := by
    field_simp [ne_of_gt hW]
    ring
  have hinterp' :
      ‖principalNormalizedGaussian q u
          (((sigma : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
        Real.rpow (principalLeftGaussianBound q x0 u)
            (1 - (sigma + delta) / (1 + r + delta)) *
          Real.rpow (principalRightGaussianBound x0)
            ((sigma + delta) / (1 + r + delta)) := by
    simpa [left, right] using hinterp
  rw [hleftExp] at hinterp'
  calc
    ‖principalAux q (((sigma : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
        ‖principalAux q (((sigma : ℝ) : ℂ) + (u : ℂ) * I)‖ *
          Real.exp (3 * sigma ^ 2) :=
      (by simpa using mul_le_mul_of_nonneg_left hone haux0)
    _ = ‖principalNormalizedGaussian q u
        (((sigma : ℝ) : ℂ) + (u : ℂ) * I)‖ := hgauss'.symm
    _ ≤ _ := by
      simpa [delta, r] using hinterp'

end
end MAPBHPPrincipalNormalizedGaussian

#print axioms MAPBHPPrincipalNormalizedGaussian.principalNormalized_eq_conductorOne_mul_euler
#print axioms MAPBHPPrincipalNormalizedGaussian.norm_ratio_sub_add_le_four
#print axioms MAPBHPPrincipalNormalizedGaussian.norm_add_div_sub_le_four_of_high
