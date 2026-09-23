import BHPPrincipalNormalizedGaussian

/-!
# Principal zeta source bound for the Jutila shifted strip

This preserves the sharp `1/2 + delta` height exponent in the installed
functional-factor estimate, through the Gaussian boundary and Hadamard
interpolation for the pole-safe normalized principal L-function.
Choosing the fixed auxiliary parameter `x0 = exp (8/epsilon)` makes the
resulting height exponent at most `1/2` throughout `[epsilon,3*epsilon]`.
The final conversion to zeta uses a uniform ratio bound on that strip,
so the theorem includes small heights and zero as well as large heights.
All analytic inputs are proved in the imported functional equation, Gamma,
and strip-growth infrastructure; no analytic source premise is introduced.
-/

namespace MAPJutilaPrincipalSourceConvexity
open Complex Set
open Complex.HadamardThreeLines
open PrimitiveEulerZeroTransport MAPBHPPrincipalNegativeEulerBound
open MAPPrincipalZetaFixedStrip MAPZeroFreeSiegelSpine
open MAPRightEdgePSeriesExplicitBound MAPBHPRademacherGaussianEnvelope
open RamachandraPrincipalHighSourceIdentity RamachandraFunctionalFactorSharpStrip
open MAPBHPPrincipalNormalizedGaussian
noncomputable section
local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)
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
    simpa only [div_eq_mul_inv, smul_eq_mul] using! hF1.smul hInv
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
    simpa [principalAux, smul_eq_mul] using! hN.smul hE.diffContOnCl
  have hG : Differentiable ℂ
      (fun z : ℂ => Complex.exp (3 * (z - (u : ℂ) * I) ^ 2)) := by
    fun_prop
  simpa [principalNormalizedGaussian, smul_eq_mul] using!
    hAux.smul hG.diffContOnCl
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
    Real.sqrt (q : ℝ) * Real.rpow (1 + |u|)
      (1/2 + RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset x0)
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


private theorem rpow_height_mul_gaussian_le_four (u v p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.rpow (1+|v|) p * Real.exp (-((v-u)^2)) ≤
      4 * Real.rpow (1+|u|) p := by
  have he : Real.exp (-((v-u)^2)) ≤ Real.rpow (Real.exp (-((v-u)^2))) p := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.exp_mul]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (v-u)]
  calc
    _ ≤ Real.rpow (1+|v|) p * Real.rpow (Real.exp (-((v-u)^2))) p :=
      mul_le_mul_of_nonneg_left he (Real.rpow_nonneg (by positivity) _)
    _ = Real.rpow ((1+|v|)*Real.exp (-((v-u)^2))) p :=
      (Real.mul_rpow (by positivity) (by positivity)).symm
    _ ≤ Real.rpow (4*(1+|u|)) p :=
      Real.rpow_le_rpow (by positivity) (one_add_abs_mul_gaussian_le_four u v) hp0
    _ = Real.rpow 4 p * Real.rpow (1+|u|) p :=
      Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ 4 * Real.rpow (1+|u|) p := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
      calc
        Real.rpow 4 p ≤ Real.rpow 4 1 :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hp1
        _ = 4 := by norm_num

private theorem norm_functionalFactor_canonicalNegative_le
    {x0 v : ℝ} (hx0 : 8 ≤ x0) (hv : v ≠ 0) :
    ‖BHPRamachandraMeanValueFromDyadicAFE.ramachandraFunctionalFactor chiOne
        (((-RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset x0 : ℝ) : ℂ) +
          v * I)‖ ≤
      16000000 * Real.rpow (1 + |v|) (1/2 + RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset x0) := by
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
      2000 * Real.rpow (1 + |v|) (1 / 2 + delta) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2000) (by positivity : 0≤1+|v|)]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
    calc
      Real.rpow 2000 (1/2+delta) ≤ Real.rpow 2000 1 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2000 := by norm_num
  rw [hzre, hzim] at hsharp
  norm_num at hsharp
  calc
    ‖BHPRamachandraMeanValueFromDyadicAFE.ramachandraFunctionalFactor chiOne z‖ ≤
        4 * (Real.rpow 2000 (1 / 2 - delta) *
          Real.rpow (2000 * (1 + |v|)) (1 / 2 + delta)) := by
      simpa [z, sub_eq_add_neg] using hsharp
    _ ≤ 4 * (2000 * (2000 * Real.rpow (1 + |v|) (1/2+delta))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul hpow1 hpow2
        (Real.rpow_nonneg (by positivity) _) (by norm_num)
    _ = 16000000 * Real.rpow (1 + |v|) (1/2+delta) := by ring

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
  have hvpow0 : 0 ≤ Real.rpow (1 + |v|) (1/2+delta) := Real.rpow_nonneg (by positivity) _
  have hupow0 : 0 ≤ Real.rpow (1 + |u|) (1/2+delta) := Real.rpow_nonneg (by positivity) _
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
        have hu : 1 ≤ Real.rpow (1 + |u|) (1/2+delta) :=
          Real.one_le_rpow (by linarith [abs_nonneg u]) (by linarith)
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
              Real.sqrt (q : ℝ) * (Real.rpow (1 + |u|) (1/2+delta)) := by
            have hbase0 : 0 ≤ 1024000000 * Real.exp 4 * Real.sqrt (q : ℝ) := by
              positivity
            calc
              1024000000 * Real.exp 4 * Real.sqrt (q : ℝ) ≤
                  (1024000000 * Real.exp 4 * Real.sqrt (q : ℝ)) *
                    (1 + 400 * Real.log x0) :=
                le_mul_of_one_le_right hbase0 hP
              _ ≤ ((1024000000 * Real.exp 4 * Real.sqrt (q : ℝ)) *
                    (1 + 400 * Real.log x0)) * (Real.rpow (1 + |u|) (1/2+delta)) :=
                le_mul_of_one_le_right
                  (mul_nonneg hbase0 (zero_le_one.trans hP)) hu
              _ = 1024000000 * (1 + 400 * Real.log x0) * Real.exp 4 *
                    Real.sqrt (q : ℝ) * (Real.rpow (1 + |u|) (1/2+delta)) := by ring
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
        64000000 * rightEdgePSeries delta * (Real.rpow (1 + |v|) (1/2+delta)) := by
      rw [principalNormalized_eq_ratio_mul_LFunction hz1,
        hfe, norm_mul, norm_mul]
      have hreflectInv :
          ‖DirichletCharacter.LFunction chiOne⁻¹ (1 - z)‖ ≤
            rightEdgePSeries delta := by simpa using hreflect
      calc
        ‖(z - 1) / (z + 1)‖ *
            (‖BHPRamachandraMeanValueFromDyadicAFE.ramachandraFunctionalFactor chiOne z‖ *
              ‖DirichletCharacter.LFunction chiOne⁻¹ (1 - z)‖) ≤
          4 * (16000000 * (Real.rpow (1 + |v|) (1/2+delta)) * rightEdgePSeries delta) := by
            have hfactor' :
                ‖BHPRamachandraMeanValueFromDyadicAFE.ramachandraFunctionalFactor chiOne z‖ ≤
                  16000000 * (Real.rpow (1 + |v|) (1/2+delta)) := by
              simpa [hzform] using hfactor
            have hinner := mul_le_mul hfactor' hreflectInv
              (norm_nonneg _)
              (by positivity : 0 ≤ 16000000 * (Real.rpow (1 + |v|) (1/2+delta)))
            exact mul_le_mul hratio hinner
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
              (by norm_num)
        _ = 64000000 * rightEdgePSeries delta * (Real.rpow (1 + |v|) (1/2+delta)) := by ring
    have hAux : ‖principalAux q z‖ ≤
        (64000000 * rightEdgePSeries delta * (Real.rpow (1 + |v|) (1/2+delta))) *
          (4 * Real.exp (1 / 400 : ℝ) * Real.sqrt (q : ℝ)) := by
      unfold principalAux
      rw [norm_mul]
      have hP0 : 0 ≤ rightEdgePSeries delta :=
        (zero_le_one.trans (one_le_rightEdgePSeries hdelta0))
      exact mul_le_mul hN (by simpa [hzform] using hEuler)
        (norm_nonneg _) (by positivity)
    have hdeltaSq : delta ^ 2 ≤ 1 := by nlinarith [sq_nonneg delta]
    have hGauss :
        (Real.rpow (1 + |v|) (1/2+delta)) * Real.exp (3 * (delta ^ 2 - (v - u) ^ 2)) ≤
          4 * Real.exp 3 * (Real.rpow (1 + |u|) (1/2+delta)) := by
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
        (Real.rpow (1 + |v|) (1/2+delta)) * Real.exp (3 * (delta ^ 2 - (v - u) ^ 2)) ≤
          (Real.rpow (1 + |v|) (1/2+delta)) * (Real.exp 3 * Real.exp (-((v - u) ^ 2))) :=
            mul_le_mul_of_nonneg_left hsplit (by positivity)
        _ = Real.exp 3 *
            ((Real.rpow (1 + |v|) (1/2+delta)) * Real.exp (-((v - u) ^ 2))) := by ring
        _ ≤ Real.exp 3 * (4 * (Real.rpow (1 + |u|) (1/2+delta))) :=
          mul_le_mul_of_nonneg_left
            (rpow_height_mul_gaussian_le_four u v (1/2+delta) (by linarith) (by linarith)) (Real.exp_pos _).le
        _ = 4 * Real.exp 3 * (Real.rpow (1 + |u|) (1/2+delta)) := by ring
    rw [norm_principalNormalizedGaussian_exp, hzre]
    have hsqneg : (-delta) ^ 2 = delta ^ 2 := by ring
    rw [hsqneg]
    calc
      ‖principalAux q z‖ * Real.exp (3 * (delta ^ 2 - (z.im - u) ^ 2)) ≤
        ((64000000 * rightEdgePSeries delta * (Real.rpow (1 + |v|) (1/2+delta))) *
          (4 * Real.exp (1 / 400 : ℝ) * Real.sqrt (q : ℝ))) *
          Real.exp (3 * (delta ^ 2 - (v - u) ^ 2)) := by
        rw [show z.im = v by rfl]
        exact mul_le_mul_of_nonneg_right hAux (Real.exp_pos _).le
      _ = 256000000 * rightEdgePSeries delta *
          Real.exp (1 / 400 : ℝ) * Real.sqrt (q : ℝ) *
          ((Real.rpow (1 + |v|) (1/2+delta)) * Real.exp (3 * (delta ^ 2 - (v - u) ^ 2))) := by ring
      _ ≤ 256000000 * rightEdgePSeries delta *
          Real.exp (1 / 400 : ℝ) * Real.sqrt (q : ℝ) *
          (4 * Real.exp 3 * (Real.rpow (1 + |u|) (1/2+delta))) := by
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
        have hu0 : 0 ≤ Real.rpow (1 + |u|) (1/2+delta) := hupow0
        calc
          256000000 * rightEdgePSeries delta * Real.exp (1 / 400) *
                Real.sqrt (q : ℝ) * (4 * Real.exp 3 * (Real.rpow (1 + |u|) (1/2+delta))) =
            1024000000 * rightEdgePSeries delta *
              (Real.exp (1 / 400) * Real.exp 3) *
              Real.sqrt (q : ℝ) * (Real.rpow (1 + |u|) (1/2+delta)) := by ring
          _ ≤ 1024000000 * (1 + 400 * Real.log x0) * Real.exp 4 *
              Real.sqrt (q : ℝ) * (Real.rpow (1 + |u|) (1/2+delta)) := by
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

private theorem rpow_le_max_one_self {a p : ℝ} (ha : 0 ≤ a)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Real.rpow a p ≤ max 1 a := by
  exact (Real.rpow_le_rpow ha (le_max_right _ _) hp0).trans
    (Real.rpow_le_self_of_one_le (le_max_left _ _) hp1)

/-- The sharpened Gaussian interpolation gives a uniform square-root bound
on the complete compact real-part strip needed in Jutila's principal term. -/
theorem exists_principalAux_sqrt_bound {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilonHi : epsilon ≤ 1/8) :
    ∃ C : ℝ, 0 < C ∧ ∀ sigma t : ℝ,
      epsilon ≤ sigma → sigma ≤ 3*epsilon →
      ‖principalAux 1 ((sigma : ℂ) + t*I)‖ ≤ C * Real.sqrt (1+|t|) := by
  let x0 := Real.exp (8/epsilon)
  have hx0 : 8 ≤ x0 := by
    have h8 : 8 ≤ 8/epsilon := (le_div_iff₀ hepsilon).mpr (by linarith)
    have h := Real.add_one_le_exp (8/epsilon)
    dsimp [x0]; linarith
  have hlog : Real.log x0 = 8/epsilon := Real.log_exp _
  have hlogpos : 0 < Real.log x0 := by rw [hlog]; positivity
  have hr : (Real.log x0)⁻¹ = epsilon/8 := by rw [hlog]; field_simp <;> ring
  have hd : RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset x0 =
      epsilon/3200 := by
    unfold RamachandraTheorem6ShiftedStripSource.canonicalRamachandraOffset
    rw [hlog]; field_simp <;> ring
  let A := 1024000000 * (1+400*Real.log x0) * Real.exp 4
  let B := principalRightGaussianBound x0
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hB0 : 0 ≤ B := by
    have hP := one_le_rightEdgePSeries (show 0 < (Real.log x0)⁻¹ by positivity)
    dsimp [B, principalRightGaussianBound]
    exact mul_nonneg (by linarith) (Real.exp_pos _).le
  refine ⟨max 1 A * max 1 B, mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)), ?_⟩
  intro sigma t hslo hshi
  let p := 1/2 + epsilon/3200
  let l := (1+epsilon/8-sigma)/(1+epsilon/8+epsilon/3200)
  let r := (sigma+epsilon/3200)/(1+epsilon/8+epsilon/3200)
  have hden : 0 < 1+epsilon/8+epsilon/3200 := by positivity
  have hl0 : 0 ≤ l := by dsimp [l]; apply div_nonneg _ hden.le; linarith
  have hl1 : l ≤ 1 := by dsimp [l]; apply (div_le_one hden).mpr; linarith
  have hr0 : 0 ≤ r := by dsimp [r]; apply div_nonneg _ hden.le; linarith
  have hr1 : r ≤ 1 := by dsimp [r]; apply (div_le_one hden).mpr; linarith
  have hpl : p*l ≤ 1/2 := by
    dsimp [p,l]
    rw [← mul_div_assoc, div_le_iff₀ hden]
    have hm := mul_nonneg hepsilon.le (sub_nonneg.mpr hslo)
    nlinarith
  have hh : 1 ≤ 1+|t| := by linarith [abs_nonneg t]
  have hi := norm_principalAux_canonical_interp (q := 1) (x0 := x0)
    (sigma := sigma) (u := t) hx0 (by norm_num; linarith)
    (by rw [hd]; linarith) (by rw [hr]; linarith)
  have hleft : principalLeftGaussianBound 1 x0 t = A * Real.rpow (1+|t|) p := by
    simp [principalLeftGaussianBound, A, p, hd]
  rw [hleft, hr, hd] at hi
  change ‖principalAux 1 ((sigma : ℂ)+t*I)‖ ≤
    Real.rpow (A * Real.rpow (1+|t|) p) l * Real.rpow B r at hi
  have hheight0 : 0 ≤ Real.rpow (1+|t|) p := Real.rpow_nonneg (by positivity) _
  simp only [Real.rpow_eq_pow] at hi hheight0
  rw [Real.mul_rpow hA0 hheight0, ← Real.rpow_mul (by positivity : 0 ≤ 1+|t|)] at hi
  calc
    _ ≤ Real.rpow A l * Real.rpow (1+|t|) (p*l) * Real.rpow B r := hi
    _ ≤ max 1 A * Real.rpow (1+|t|) (1/2) * max 1 B := by
      apply mul_le_mul _ (rpow_le_max_one_self hB0 hr0 hr1)
        (Real.rpow_nonneg hB0 _) (mul_nonneg (le_trans zero_le_one (le_max_left _ _))
          (Real.rpow_nonneg (by positivity) _))
      exact mul_le_mul (rpow_le_max_one_self hA0 hl0 hl1)
        (Real.rpow_le_rpow_of_exponent_le hh hpl)
        (Real.rpow_nonneg (by positivity) _) (le_trans zero_le_one (le_max_left _ _))
    _ = (max 1 A * max 1 B) * Real.sqrt (1+|t|) := by
      rw [Real.sqrt_eq_rpow]
      norm_num
      ring

private theorem norm_riemannZeta_le_five_principalAux {z : ℂ}
    (hz0 : 0 < z.re) (hzhi : z.re ≤ 3/8) :
    ‖riemannZeta z‖ ≤ 5 * ‖principalAux 1 z‖ := by
  have hz1 : z ≠ 1 := by intro h; subst z; norm_num at hzhi
  have hzm : z-1 ≠ 0 := sub_ne_zero.mpr hz1
  have hzp : z+1 ≠ 0 := by
    intro h; have h' := congrArg Complex.re h; simp at h'; linarith
  have hden : 5/8 ≤ ‖z-1‖ := by
    have h := Complex.abs_re_le_norm (z-1)
    have hre : (z-1).re = z.re-1 := by simp
    rw [hre, abs_of_nonpos (by linarith)] at h
    linarith
  have hratio : ‖(z+1)/(z-1)‖ ≤ 5 := by
    rw [norm_div]
    apply (div_le_iff₀ (norm_pos_iff.mpr hzm)).mpr
    have ht := norm_add_le (z-1) (2:ℂ)
    have he : z-1+2 = z+1 := by ring
    rw [he] at ht
    norm_num at ht
    linarith
  have hid : riemannZeta z = ((z+1)/(z-1))*principalAux 1 z := by
    rw [principalAux_eq_principalNormalized_of_ne_one hz1,
      principalNormalized_eq_ratio_mul_LFunction hz1,
      DirichletCharacter.LFunction_modOne_eq]
    field_simp
  rw [hid, norm_mul]
  exact mul_le_mul_of_nonneg_right hratio (norm_nonneg _)

/-- Unconditional principal zeta source estimate, uniform at every height.
The real-part strip excludes the pole and retains the square-root height
scale rather than the earlier sixth-power envelope. -/
theorem exists_riemannZeta_sqrt_bound {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilonHi : epsilon ≤ 1/8) :
    ∃ C : ℝ, 0 < C ∧ ∀ sigma t : ℝ,
      epsilon ≤ sigma → sigma ≤ 3*epsilon →
      ‖riemannZeta ((sigma : ℂ) + t*I)‖ ≤ C * Real.sqrt (1+|t|) := by
  obtain ⟨C,hC,h⟩ := exists_principalAux_sqrt_bound hepsilon hepsilonHi
  refine ⟨5*C, by positivity, ?_⟩
  intro sigma t hslo hshi
  have hz0 : 0 < ((sigma : ℂ)+t*I).re := by simp; linarith
  have hzhi : ((sigma : ℂ)+t*I).re ≤ 3/8 := by simp; linarith
  calc
    _ ≤ 5*‖principalAux 1 ((sigma : ℂ)+t*I)‖ :=
      norm_riemannZeta_le_five_principalAux hz0 hzhi
    _ ≤ 5*(C*Real.sqrt (1+|t|)) :=
      mul_le_mul_of_nonneg_left (h sigma t hslo hshi) (by norm_num)
    _ = (5*C)*Real.sqrt (1+|t|) := by ring

end
end MAPJutilaPrincipalSourceConvexity
#print axioms MAPJutilaPrincipalSourceConvexity.exists_riemannZeta_sqrt_bound
