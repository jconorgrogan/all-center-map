import BHPRademacherGaussianEnvelope
import PrimitiveLFixedStripGrowthCertified
import NearOneThreeLines
import Mathlib.Analysis.Complex.Hadamard

/-!
# Quantitative Gaussian Rademacher interpolation

This is the epsilon-uniform replacement for the unsafe specialization of
BHP Lemma 8.  The Gaussian is centered at the target ordinate, so the exact
zero-line functional-equation estimate and the exact logarithmic one-line
estimate become uniform boundary constants.  No hidden constant depends on
`eta`.
-/

namespace MAPBHPRademacherGaussianThreeLines

open Complex Set
open Complex.HadamardThreeLines
open MAPBHPRademacherGaussianEnvelope
open MAPBHPRademacherZeroBoundary
open MAPJutilaRightEdgeLogBound
open MAPZeroFreeSiegelSpine

noncomputable section

/-- The entire Gaussian twist centered at ordinate `u`. -/
def gaussianTwist {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (u : ℝ) (z : ℂ) : ℂ :=
  DirichletCharacter.LFunction chi z *
    Complex.exp ((z - (u : ℂ) * I) ^ 2)

/-- Exact norm of the centered Gaussian. -/
theorem norm_centeredGaussian (u : ℝ) (z : ℂ) :
    ‖Complex.exp ((z - (u : ℂ) * I) ^ 2)‖ =
      Real.exp (z.re ^ 2 - (z.im - u) ^ 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [pow_two, Complex.mul_re, Complex.sub_re, ofReal_re,
    I_re, mul_zero, sub_zero, Complex.sub_im, Complex.mul_im, ofReal_im,
    I_im, zero_mul, add_zero]
  ring

private theorem gaussianTwist_diffContOnCl
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (u : ℝ) :
    DiffContOnCl ℂ (gaussianTwist chi u) (verticalStrip 0 1) := by
  have hL : DiffContOnCl ℂ (DirichletCharacter.LFunction chi)
      (verticalStrip 0 1) :=
    (DirichletCharacter.differentiable_LFunction hchi).diffContOnCl
  have hg : Differentiable ℂ
      (fun z : ℂ => Complex.exp ((z - (u : ℂ) * I) ^ 2)) :=
    Complex.differentiable_exp.comp
      ((differentiable_id.sub_const ((u : ℂ) * I)).pow 2)
  have hmul := hL.smul hg.diffContOnCl
  simpa only [gaussianTwist, smul_eq_mul] using hmul

private theorem four_add_abs_le_center_mul (u v : ℝ) :
    4 + |v| ≤ (4 + |u|) * (1 + |v - u|) := by
  have htri : |v| ≤ |u| + |v - u| := by
    have h := abs_add_le u (v - u)
    rw [show u + (v - u) = v by ring] at h
    exact h
  nlinarith [abs_nonneg u, abs_nonneg (v - u)]

/-- The Gaussian twist is bounded on the full closed strip.  The witness may
+depend on the fixed center `u`, which is exactly what Hadamard requires. -/
private theorem gaussianTwist_bddAbove
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (u : ℝ) :
    BddAbove ((norm ∘ gaussianTwist chi u) '' verticalClosedStrip 0 1) := by
  refine ⟨2400 * (q : ℝ) ^ 2 * (4 + |u|) ^ 2, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  let r : ℝ := |z.im - u|
  have hr : 0 ≤ r := abs_nonneg _
  have hL := PLInteriorGrowth.norm_LFunction_fixedStrip_le chi hchi
    (z := z) (by linarith [hz.1]) (by linarith [hz.2])
  have hnormBasic : ‖z + 3‖ ≤ 4 + |z.im| := by
    calc
      ‖z + 3‖ ≤ |(z + 3).re| + |(z + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |z.re + 3| + |z.im| := by simp
      _ ≤ 4 + |z.im| := by
        rw [abs_of_nonneg (by linarith [hz.1])]
        linarith [hz.2]
  have hnormCenter : ‖z + 3‖ ≤ (4 + |u|) * (1 + r) := by
    exact hnormBasic.trans (by
      dsimp only [r]
      exact four_add_abs_le_center_mul u z.im)
  have hnormCenter0 : 0 ≤ (4 + |u|) * (1 + r) := by positivity
  have hsq : ‖z + 3‖ ^ 2 ≤ ((4 + |u|) * (1 + r)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnormCenter 2
  have hreSq : z.re ^ 2 ≤ 1 := by nlinarith [hz.1, hz.2]
  have hexpre : Real.exp (z.re ^ 2) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr hreSq
  have hexp : Real.exp (z.re ^ 2 - r ^ 2) ≤
      Real.exp 1 * Real.exp (-(r ^ 2)) := by
    rw [show z.re ^ 2 - r ^ 2 = z.re ^ 2 + (-(r ^ 2)) by ring,
      Real.exp_add]
    exact mul_le_mul_of_nonneg_right hexpre (Real.exp_pos _).le
  have hgauss := one_add_sq_mul_exp_neg_sq_le_four r hr
  have hq0 : 0 ≤ (q : ℝ) ^ 2 := sq_nonneg _
  have hcenter0 : 0 ≤ (4 + |u|) ^ 2 := sq_nonneg _
  have hbase0 : 0 ≤ 200 * (q : ℝ) ^ 2 := mul_nonneg (by norm_num) hq0
  have hExp0 : 0 ≤ Real.exp (z.re ^ 2 - r ^ 2) := (Real.exp_pos _).le
  have hrsq : r ^ 2 = (z.im - u) ^ 2 := by
    dsimp only [r]
    exact sq_abs (z.im - u)
  change ‖DirichletCharacter.LFunction chi z *
      Complex.exp ((z - (u : ℂ) * I) ^ 2)‖ ≤ _
  rw [norm_mul, norm_centeredGaussian, ← hrsq]
  calc
    ‖DirichletCharacter.LFunction chi z‖ *
        Real.exp (z.re ^ 2 - r ^ 2) ≤
      (200 * (q : ℝ) ^ 2 * ‖z + 3‖ ^ 2) *
        Real.exp (z.re ^ 2 - r ^ 2) :=
      mul_le_mul_of_nonneg_right hL hExp0
    _ ≤ (200 * (q : ℝ) ^ 2 *
          (((4 + |u|) * (1 + r)) ^ 2)) *
        Real.exp (z.re ^ 2 - r ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsq hbase0) hExp0
    _ ≤ (200 * (q : ℝ) ^ 2 *
          (((4 + |u|) * (1 + r)) ^ 2)) *
        (Real.exp 1 * Real.exp (-(r ^ 2))) := by
      exact mul_le_mul_of_nonneg_left hexp
        (mul_nonneg hbase0 (sq_nonneg _))
    _ = 200 * (q : ℝ) ^ 2 * (4 + |u|) ^ 2 *
          ((1 + r) ^ 2 * Real.exp (-(r ^ 2))) * Real.exp 1 := by
      ring
    _ ≤ 200 * (q : ℝ) ^ 2 * (4 + |u|) ^ 2 * 4 * Real.exp 1 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hgauss
          (mul_nonneg hbase0 hcenter0))
        (Real.exp_pos _).le
    _ ≤ 200 * (q : ℝ) ^ 2 * (4 + |u|) ^ 2 * 4 * 3 := by
      exact mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le
        (mul_nonneg (mul_nonneg hbase0 hcenter0) (by norm_num))
    _ = 2400 * (q : ℝ) ^ 2 * (4 + |u|) ^ 2 := by ring

private theorem gaussianTwist_leftBoundary
    {eta : ℝ} (heta : 0 < eta) (hetaHalf : eta ≤ 1 / 2)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1) (u : ℝ) :
    ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ),
      ‖gaussianTwist chi u z‖ ≤
        12 * (1 + eta⁻¹) *
          Real.rpow (2 * (q : ℝ) * (3 + |u|)) (eta + 1 / 2) := by
  intro z hz
  have hzre : z.re = 0 := by simpa using hz
  let v : ℝ := z.im
  have hzform : z = (v : ℂ) * I := by
    apply Complex.ext <;> simp [v, hzre]
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hL := norm_LFunction_imaginary_le_clean chi hprim hchi v
  change ‖DirichletCharacter.LFunction chi z *
      Complex.exp ((z - (u : ℂ) * I) ^ 2)‖ ≤ _
  rw [norm_mul, hzform]
  have hg :
      ‖Complex.exp ((((v : ℂ) * I) - (u : ℂ) * I) ^ 2)‖ =
        Real.exp (-((v - u) ^ 2)) := by
    have h := norm_centeredGaussian u ((v : ℂ) * I)
    simpa using h
  rw [hg]
  calc
    ‖DirichletCharacter.LFunction chi ((v : ℂ) * I)‖ *
        Real.exp (-((v - u) ^ 2)) ≤
      (3 * (1 + Real.log (2 * (q : ℝ) * (3 + |v|))) *
        Real.rpow (q : ℝ) (1 / 2) * Real.rpow (1 + |v|) (1 / 2)) *
        Real.exp (-((v - u) ^ 2)) := by
      exact mul_le_mul_of_nonneg_right hL (Real.exp_pos _).le
    _ ≤ 12 * (1 + eta⁻¹) *
          Real.rpow (2 * (q : ℝ) * (3 + |u|)) (eta + 1 / 2) :=
      logarithmic_sqrt_gaussian_envelope heta hetaHalf hq u v

private theorem gaussianTwist_rightBoundary
    {eta : ℝ} (heta : 0 < eta) (hetaHalf : eta ≤ 1 / 2)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) (u : ℝ) :
    ∀ z ∈ Complex.re ⁻¹' ({1} : Set ℝ),
      ‖gaussianTwist chi u z‖ ≤
        36 * (1 + eta⁻¹) *
          Real.rpow (2 * (q : ℝ) * (3 + |u|)) eta := by
  intro z hz
  have hzre : z.re = 1 := by simpa using hz
  let v : ℝ := z.im
  have hzform : z = rightBoundaryPoint (-v) := by
    apply Complex.ext <;> simp [v, rightBoundaryPoint, hzre]
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hL := nonprincipal_norm_LFunction_rightBoundary_le chi hchi (-v)
  change ‖DirichletCharacter.LFunction chi z *
      Complex.exp ((z - (u : ℂ) * I) ^ 2)‖ ≤ _
  rw [norm_mul, hzform]
  have hL' :
      ‖DirichletCharacter.LFunction chi (rightBoundaryPoint (-v))‖ ≤
        3 * (1 + Real.log (2 * (q : ℝ) * (3 + |v|))) := by
    simpa only [abs_neg] using hL
  have hg :
      ‖Complex.exp ((rightBoundaryPoint (-v) - (u : ℂ) * I) ^ 2)‖ =
        Real.exp (1 - (v - u) ^ 2) := by
    have h := norm_centeredGaussian u (rightBoundaryPoint (-v))
    simpa [rightBoundaryPoint] using h
  rw [hg]
  calc
    ‖DirichletCharacter.LFunction chi (rightBoundaryPoint (-v))‖ *
        Real.exp (1 - (v - u) ^ 2) ≤
      (3 * (1 + Real.log (2 * (q : ℝ) * (3 + |v|)))) *
        Real.exp (1 - (v - u) ^ 2) := by
      exact mul_le_mul_of_nonneg_right hL' (Real.exp_pos _).le
    _ ≤ 36 * (1 + eta⁻¹) *
          Real.rpow (2 * (q : ℝ) * (3 + |u|)) eta :=
      logarithmic_gaussian_envelope heta hetaHalf hq u v

/-- Epsilon-uniform quantitative Rademacher interpolation for primitive
nonprincipal characters.  Every constant and every `eta` dependence is visible.
This is the honest source replacing the manuscript's variable-epsilon use of
BHP Lemma 8. -/
theorem norm_gaussianTwist_le_interp
    {eta : ℝ} (heta : 0 < eta) (hetaHalf : eta ≤ 1 / 2)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {sigma u : ℝ} (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    ‖gaussianTwist chi u ((sigma : ℂ) + (u : ℂ) * I)‖ ≤
      Real.rpow
        (12 * (1 + eta⁻¹) *
          Real.rpow (2 * (q : ℝ) * (3 + |u|)) (eta + 1 / 2))
        (1 - sigma) *
      Real.rpow
        (36 * (1 + eta⁻¹) *
          Real.rpow (2 * (q : ℝ) * (3 + |u|)) eta)
        sigma := by
  have hinterp :=
    Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (f := gaussianTwist chi u)
    (z := ((sigma : ℂ) + (u : ℂ) * I))
    (l := (0 : ℝ)) (u := 1)
    (a := 12 * (1 + eta⁻¹) *
      Real.rpow (2 * (q : ℝ) * (3 + |u|)) (eta + 1 / 2))
    (b := 36 * (1 + eta⁻¹) *
      Real.rpow (2 * (q : ℝ) * (3 + |u|)) eta)
    (by norm_num)
    (by
      constructor
      · simpa using hsigma0
      · simpa using hsigma1)
    (gaussianTwist_diffContOnCl chi hchi u)
    (gaussianTwist_bddAbove chi hchi u)
    (gaussianTwist_leftBoundary heta hetaHalf chi hprim hchi u)
    (gaussianTwist_rightBoundary heta hetaHalf chi hchi u)
  simpa using hinterp

/-- Removing the centered Gaussian from the unit-strip interpolation. -/
theorem norm_LFunction_le_interp
    {kappa : ℝ} (hkappa : 0 < kappa) (hkappaHalf : kappa ≤ 1 / 2)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {sigma u : ℝ} (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    ‖DirichletCharacter.LFunction chi
      ((sigma : ℂ) + (u : ℂ) * I)‖ ≤
      Real.rpow
        (12 * (1 + kappa⁻¹) *
          Real.rpow (2 * (q : ℝ) * (3 + |u|)) (kappa + 1 / 2))
        (1 - sigma) *
      Real.rpow
        (36 * (1 + kappa⁻¹) *
          Real.rpow (2 * (q : ℝ) * (3 + |u|)) kappa)
        sigma := by
  have hinterp := norm_gaussianTwist_le_interp hkappa hkappaHalf
    chi hprim hchi (sigma := sigma) (u := u) hsigma0 hsigma1
  have hg := norm_centeredGaussian u
    ((sigma : ℂ) + (u : ℂ) * I)
  have hg' :
      ‖Complex.exp (((((sigma : ℂ) + (u : ℂ) * I) -
        (u : ℂ) * I)) ^ 2)‖ = Real.exp (sigma ^ 2) := by
    simpa using hg
  have hone : 1 ≤ Real.exp (sigma ^ 2) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (sq_nonneg sigma)
  have hL0 : 0 ≤ ‖DirichletCharacter.LFunction chi
      ((sigma : ℂ) + (u : ℂ) * I)‖ := norm_nonneg _
  calc
    ‖DirichletCharacter.LFunction chi
        ((sigma : ℂ) + (u : ℂ) * I)‖ ≤
      ‖DirichletCharacter.LFunction chi
        ((sigma : ℂ) + (u : ℂ) * I)‖ * Real.exp (sigma ^ 2) := by
      simpa using mul_le_mul_of_nonneg_left hone hL0
    _ = ‖gaussianTwist chi u ((sigma : ℂ) + (u : ℂ) * I)‖ := by
      rw [gaussianTwist, norm_mul, hg']
    _ ≤ _ := hinterp

/-- Classical convexity exponent with all dependence on the fixed loss
`kappa` visible.  This is the exact Jutila p.48 nonprincipal input, before the
harmless conversion from `2q(3+|u|)` to `q(1+|u|)`. -/
theorem norm_LFunction_le_explicit_convexity
    {kappa : ℝ} (hkappa : 0 < kappa) (hkappaHalf : kappa ≤ 1 / 2)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {sigma u : ℝ} (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    ‖DirichletCharacter.LFunction chi
      ((sigma : ℂ) + (u : ℂ) * I)‖ ≤
      36 * (1 + kappa⁻¹) *
        Real.rpow (2 * (q : ℝ) * (3 + |u|))
          (kappa + (1 - sigma) / 2) := by
  let Q : ℝ := 2 * (q : ℝ) * (3 + |u|)
  let C : ℝ := 36 * (1 + kappa⁻¹)
  let A : ℝ := kappa + 1 / 2
  have hq : (1 : ℝ) ≤ q := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hQ : 1 ≤ Q := by dsimp [Q]; nlinarith [abs_nonneg u]
  have hfac : 0 < 1 + kappa⁻¹ := by
    have : 0 < kappa⁻¹ := inv_pos.mpr hkappa
    linarith
  have hC : 0 < C := by dsimp [C]; positivity
  have hA0 : 0 ≤ A := by dsimp [A]; linarith
  have hleftBase :
      0 ≤ 12 * (1 + kappa⁻¹) * Real.rpow Q A :=
    mul_nonneg (mul_nonneg (by norm_num) hfac.le)
      (Real.rpow_nonneg (by linarith) _)
  have hleftBaseLe :
      12 * (1 + kappa⁻¹) * Real.rpow Q A ≤ C * Real.rpow Q A := by
    dsimp [C]
    have hpow0 := Real.rpow_nonneg (by linarith : 0 ≤ Q) A
    nlinarith
  have honeMinus : 0 ≤ 1 - sigma := sub_nonneg.mpr hsigma1
  have hsigmaNonneg : 0 ≤ sigma := hsigma0
  have hleftRpow :
      Real.rpow (12 * (1 + kappa⁻¹) * Real.rpow Q A) (1 - sigma) ≤
        Real.rpow (C * Real.rpow Q A) (1 - sigma) :=
    Real.rpow_le_rpow hleftBase hleftBaseLe honeMinus
  have hinterp := norm_LFunction_le_interp hkappa hkappaHalf
    chi hprim hchi (sigma := sigma) (u := u) hsigma0 hsigma1
  change ‖DirichletCharacter.LFunction chi
      ((sigma : ℂ) + (u : ℂ) * I)‖ ≤
    Real.rpow (12 * (1 + kappa⁻¹) * Real.rpow Q A) (1 - sigma) *
      Real.rpow (C * Real.rpow Q kappa) sigma at hinterp
  have hmulLeft :
      Real.rpow (C * Real.rpow Q A) (1 - sigma) =
        Real.rpow C (1 - sigma) *
          Real.rpow (Real.rpow Q A) (1 - sigma) :=
    Real.mul_rpow hC.le (Real.rpow_nonneg (by linarith : 0 ≤ Q) A)
  have hmulRight :
      Real.rpow (C * Real.rpow Q kappa) sigma =
        Real.rpow C sigma * Real.rpow (Real.rpow Q kappa) sigma :=
    Real.mul_rpow hC.le (Real.rpow_nonneg (by linarith : 0 ≤ Q) kappa)
  have hpowLeft : Real.rpow (Real.rpow Q A) (1 - sigma) =
      Real.rpow Q (A * (1 - sigma)) := by
    exact (Real.rpow_mul (by linarith : 0 ≤ Q) A (1 - sigma)).symm
  have hpowRight : Real.rpow (Real.rpow Q kappa) sigma =
      Real.rpow Q (kappa * sigma) := by
    exact (Real.rpow_mul (by linarith : 0 ≤ Q) kappa sigma).symm
  have hCcombine : Real.rpow C (1 - sigma) * Real.rpow C sigma = C := by
    calc
      Real.rpow C (1 - sigma) * Real.rpow C sigma =
          Real.rpow C ((1 - sigma) + sigma) :=
        (Real.rpow_add hC (1 - sigma) sigma).symm
      _ = C := by norm_num
  have hQcombine :
      Real.rpow Q (A * (1 - sigma)) * Real.rpow Q (kappa * sigma) =
        Real.rpow Q (kappa + (1 - sigma) / 2) := by
    calc
      Real.rpow Q (A * (1 - sigma)) * Real.rpow Q (kappa * sigma) =
          Real.rpow Q (A * (1 - sigma) + kappa * sigma) :=
        (Real.rpow_add (by linarith : 0 < Q)
          (A * (1 - sigma)) (kappa * sigma)).symm
      _ = Real.rpow Q (kappa + (1 - sigma) / 2) := by
        congr 1
        dsimp [A]
        ring
  calc
    ‖DirichletCharacter.LFunction chi
        ((sigma : ℂ) + (u : ℂ) * I)‖ ≤
      Real.rpow (12 * (1 + kappa⁻¹) * Real.rpow Q A) (1 - sigma) *
        Real.rpow (C * Real.rpow Q kappa) sigma := hinterp
    _ ≤ Real.rpow (C * Real.rpow Q A) (1 - sigma) *
        Real.rpow (C * Real.rpow Q kappa) sigma :=
      mul_le_mul_of_nonneg_right hleftRpow
        (Real.rpow_nonneg
          (mul_nonneg hC.le (Real.rpow_nonneg (by linarith : 0 ≤ Q) kappa))
          sigma)
    _ = C * Real.rpow Q (kappa + (1 - sigma) / 2) := by
      rw [hmulLeft, hmulRight, hpowLeft, hpowRight]
      calc
        Real.rpow C (1 - sigma) * Real.rpow Q (A * (1 - sigma)) *
            (Real.rpow C sigma * Real.rpow Q (kappa * sigma)) =
          (Real.rpow C (1 - sigma) * Real.rpow C sigma) *
            (Real.rpow Q (A * (1 - sigma)) *
              Real.rpow Q (kappa * sigma)) := by ring
        _ = C * Real.rpow Q (kappa + (1 - sigma) / 2) := by
          rw [hCcombine, hQcombine]
    _ = 36 * (1 + kappa⁻¹) *
        Real.rpow (2 * (q : ℝ) * (3 + |u|))
          (kappa + (1 - sigma) / 2) := by rfl

/-- Jutila's conventional conductor-height normalization.  For any fixed
`0 < eta ≤ 1/2` the constant is completely explicit and independent of the
character, conductor, ordinate, and strip coordinate. -/
theorem norm_LFunction_le_jutila_convexity
    {eta : ℝ} (heta : 0 < eta) (hetaHalf : eta ≤ 1 / 2)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {sigma u : ℝ} (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    ‖DirichletCharacter.LFunction chi
      ((sigma : ℂ) + (u : ℂ) * I)‖ ≤
      (36 * (1 + eta⁻¹) * Real.rpow 6 (eta + 1 / 2)) *
        Real.rpow ((q : ℝ) * (1 + |u|))
          ((1 / 2) * (1 - sigma) + eta) := by
  have hbase := norm_LFunction_le_explicit_convexity heta hetaHalf
    chi hprim hchi (sigma := sigma) (u := u) hsigma0 hsigma1
  let P : ℝ := (q : ℝ) * (1 + |u|)
  let E : ℝ := eta + (1 - sigma) / 2
  have hq : (1 : ℝ) ≤ q := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hP : 1 ≤ P := by dsimp [P]; nlinarith [abs_nonneg u]
  have hE0 : 0 ≤ E := by dsimp [E]; nlinarith
  have hEupper : E ≤ eta + 1 / 2 := by dsimp [E]; nlinarith
  have hscale : 2 * (q : ℝ) * (3 + |u|) ≤ 6 * P := by
    dsimp [P]
    nlinarith [abs_nonneg u]
  have hpowScale :
      Real.rpow (2 * (q : ℝ) * (3 + |u|)) E ≤
        Real.rpow (6 * P) E :=
    Real.rpow_le_rpow (by positivity) hscale hE0
  have hsplit : Real.rpow (6 * P) E =
      Real.rpow 6 E * Real.rpow P E :=
    Real.mul_rpow (by norm_num) (by linarith)
  have hsix : Real.rpow 6 E ≤ Real.rpow 6 (eta + 1 / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hEupper
  have hPpow0 : 0 ≤ Real.rpow P E := Real.rpow_nonneg (by linarith) _
  calc
    ‖DirichletCharacter.LFunction chi
        ((sigma : ℂ) + (u : ℂ) * I)‖ ≤
      36 * (1 + eta⁻¹) *
        Real.rpow (2 * (q : ℝ) * (3 + |u|)) E := by
      simpa [E] using hbase
    _ ≤ 36 * (1 + eta⁻¹) * Real.rpow (6 * P) E := by
      exact mul_le_mul_of_nonneg_left hpowScale (by positivity)
    _ = 36 * (1 + eta⁻¹) * (Real.rpow 6 E * Real.rpow P E) := by
      rw [hsplit]
    _ ≤ 36 * (1 + eta⁻¹) *
        (Real.rpow 6 (eta + 1 / 2) * Real.rpow P E) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hsix hPpow0) (by positivity)
    _ = (36 * (1 + eta⁻¹) * Real.rpow 6 (eta + 1 / 2)) *
        Real.rpow ((q : ℝ) * (1 + |u|))
          ((1 / 2) * (1 - sigma) + eta) := by
      dsimp [P, E]
      rw [show eta + (1 - sigma) / 2 =
        (1 / 2) * (1 - sigma) + eta by ring]
      ring

/-! ## A fixed-width extension past `Re s = 1`

The Perron right edge lies a distance `1 / log x₀` past one.  We therefore
interpolate to the fixed line `1 + r`, where absolute convergence gives a
source-free boundary bound.  Later one chooses fixed `r` from the MAP power
reserve and imposes the explicit lower threshold `1 / log x₀ ≤ r`. -/

theorem gaussianTwist_bddAbove_wide
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (u rWidth : ℝ) (hr0 : 0 < rWidth) (hrHalf : rWidth ≤ 1 / 2) :
    BddAbove ((norm ∘ gaussianTwist chi u) ''
      verticalClosedStrip 0 (1 + rWidth)) := by
  refine ⟨800 * (q : ℝ) ^ 2 * (5 + |u|) ^ 2 *
    Real.exp ((3 / 2 : ℝ) ^ 2), ?_⟩
  rintro y ⟨z, hz, rfl⟩
  let d : ℝ := |z.im - u|
  have hd : 0 ≤ d := abs_nonneg _
  have hupper : z.re ≤ 3 / 2 := by linarith [hz.2]
  have hL := PLInteriorGrowth.norm_LFunction_fixedStrip_le chi hchi
    (z := z) (by linarith [hz.1]) (by linarith [hupper])
  have hnormBasic : ‖z + 3‖ ≤ 5 + |z.im| := by
    calc
      ‖z + 3‖ ≤ |(z + 3).re| + |(z + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |z.re + 3| + |z.im| := by simp
      _ ≤ 5 + |z.im| := by
        rw [abs_of_nonneg (by linarith [hz.1])]
        linarith
  have hnormCenter : ‖z + 3‖ ≤ (5 + |u|) * (1 + d) := by
    apply hnormBasic.trans
    have htri : |z.im| ≤ |u| + |z.im - u| := by
      have h := abs_add_le u (z.im - u)
      rw [show u + (z.im - u) = z.im by ring] at h
      exact h
    dsimp only [d]
    nlinarith [abs_nonneg u, abs_nonneg (z.im - u)]
  have hsq : ‖z + 3‖ ^ 2 ≤ ((5 + |u|) * (1 + d)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnormCenter 2
  have hreSq : z.re ^ 2 ≤ (3 / 2 : ℝ) ^ 2 := by
    nlinarith [hz.1, hupper]
  have hexpre : Real.exp (z.re ^ 2) ≤ Real.exp ((3 / 2 : ℝ) ^ 2) :=
    Real.exp_le_exp.mpr hreSq
  have hexp : Real.exp (z.re ^ 2 - d ^ 2) ≤
      Real.exp ((3 / 2 : ℝ) ^ 2) * Real.exp (-(d ^ 2)) := by
    rw [show z.re ^ 2 - d ^ 2 = z.re ^ 2 + (-(d ^ 2)) by ring,
      Real.exp_add]
    exact mul_le_mul_of_nonneg_right hexpre (Real.exp_pos _).le
  have hgauss := one_add_sq_mul_exp_neg_sq_le_four d hd
  have hbase0 : 0 ≤ 200 * (q : ℝ) ^ 2 := by positivity
  have hcenter0 : 0 ≤ (5 + |u|) ^ 2 := sq_nonneg _
  have hExp0 : 0 ≤ Real.exp (z.re ^ 2 - d ^ 2) := (Real.exp_pos _).le
  have hdsq : d ^ 2 = (z.im - u) ^ 2 := by
    dsimp only [d]
    exact sq_abs (z.im - u)
  change ‖DirichletCharacter.LFunction chi z *
      Complex.exp ((z - (u : ℂ) * I) ^ 2)‖ ≤ _
  rw [norm_mul, norm_centeredGaussian, ← hdsq]
  calc
    ‖DirichletCharacter.LFunction chi z‖ *
        Real.exp (z.re ^ 2 - d ^ 2) ≤
      (200 * (q : ℝ) ^ 2 * ‖z + 3‖ ^ 2) *
        Real.exp (z.re ^ 2 - d ^ 2) :=
      mul_le_mul_of_nonneg_right hL hExp0
    _ ≤ (200 * (q : ℝ) ^ 2 *
          (((5 + |u|) * (1 + d)) ^ 2)) *
        Real.exp (z.re ^ 2 - d ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsq hbase0) hExp0
    _ ≤ (200 * (q : ℝ) ^ 2 *
          (((5 + |u|) * (1 + d)) ^ 2)) *
        (Real.exp ((3 / 2 : ℝ) ^ 2) * Real.exp (-(d ^ 2))) := by
      exact mul_le_mul_of_nonneg_left hexp
        (mul_nonneg hbase0 (sq_nonneg _))
    _ = 200 * (q : ℝ) ^ 2 * (5 + |u|) ^ 2 *
          ((1 + d) ^ 2 * Real.exp (-(d ^ 2))) *
          Real.exp ((3 / 2 : ℝ) ^ 2) := by ring
    _ ≤ 200 * (q : ℝ) ^ 2 * (5 + |u|) ^ 2 * 4 *
          Real.exp ((3 / 2 : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hgauss
          (mul_nonneg hbase0 hcenter0))
        (Real.exp_pos _).le
    _ = 800 * (q : ℝ) ^ 2 * (5 + |u|) ^ 2 *
          Real.exp ((3 / 2 : ℝ) ^ 2) := by ring

private theorem gaussianTwist_rightBoundary_wide
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (rWidth : ℝ) (hr0 : 0 < rWidth) (u : ℝ) :
    ∀ z ∈ Complex.re ⁻¹' ({1 + rWidth} : Set ℝ),
      ‖gaussianTwist chi u z‖ ≤
        rightEdgePSeries rWidth * Real.exp ((1 + rWidth) ^ 2) := by
  intro z hz
  have hzre : z.re = 1 + rWidth := by simpa using hz
  have hL := norm_LFunction_rightEdge_le_pSeries chi hr0 hzre
  have hg := norm_centeredGaussian u z
  have hsquare : z.re ^ 2 = (1 + rWidth) ^ 2 := by rw [hzre]
  have hexpNeg : Real.exp (-((z.im - u) ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (z.im - u)])
  have hexp : Real.exp (z.re ^ 2 - (z.im - u) ^ 2) ≤
      Real.exp ((1 + rWidth) ^ 2) := by
    rw [hsquare,
      show (1 + rWidth) ^ 2 - (z.im - u) ^ 2 =
        (1 + rWidth) ^ 2 + (-((z.im - u) ^ 2)) by ring,
      Real.exp_add]
    simpa using mul_le_mul_of_nonneg_left hexpNeg (Real.exp_pos _).le
  change ‖DirichletCharacter.LFunction chi z *
      Complex.exp ((z - (u : ℂ) * I) ^ 2)‖ ≤ _
  rw [norm_mul, hg]
  exact mul_le_mul hL hexp (Real.exp_pos _).le
    (zero_le_one.trans (one_le_rightEdgePSeries hr0))

/-- Fixed-width quantitative interpolation covering the tiny Perron collar
past `Re s = 1`.  The right boundary is the exact absolutely convergent
`rightEdgePSeries`; all conductor dependence remains on the zero-line edge. -/
theorem norm_gaussianTwist_le_wide_interp
    {kappa rWidth : ℝ} (hkappa : 0 < kappa) (hkappaHalf : kappa ≤ 1 / 2)
    (hr0 : 0 < rWidth) (hrHalf : rWidth ≤ 1 / 2)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {sigma u : ℝ} (hsigma0 : 0 ≤ sigma)
    (hsigmaUpper : sigma ≤ 1 + rWidth) :
    ‖gaussianTwist chi u ((sigma : ℂ) + (u : ℂ) * I)‖ ≤
      Real.rpow
        (12 * (1 + kappa⁻¹) *
          Real.rpow (2 * (q : ℝ) * (3 + |u|)) (kappa + 1 / 2))
        (1 - sigma / (1 + rWidth)) *
      Real.rpow
        (rightEdgePSeries rWidth * Real.exp ((1 + rWidth) ^ 2))
        (sigma / (1 + rWidth)) := by
  have hwidth : (0 : ℝ) < 1 + rWidth := by linarith
  have hinterp :=
    Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (f := gaussianTwist chi u)
    (z := ((sigma : ℂ) + (u : ℂ) * I))
    (l := (0 : ℝ)) (u := 1 + rWidth)
    (a := 12 * (1 + kappa⁻¹) *
      Real.rpow (2 * (q : ℝ) * (3 + |u|)) (kappa + 1 / 2))
    (b := rightEdgePSeries rWidth * Real.exp ((1 + rWidth) ^ 2))
    hwidth
    (by
      constructor
      · simpa using hsigma0
      · simpa using hsigmaUpper)
    (by
      have hL : DiffContOnCl ℂ (DirichletCharacter.LFunction chi)
          (verticalStrip 0 (1 + rWidth)) :=
        (DirichletCharacter.differentiable_LFunction hchi).diffContOnCl
      have hg : Differentiable ℂ
          (fun z : ℂ => Complex.exp ((z - (u : ℂ) * I) ^ 2)) :=
        Complex.differentiable_exp.comp
          ((differentiable_id.sub_const ((u : ℂ) * I)).pow 2)
      have hmul := hL.smul hg.diffContOnCl
      simpa only [gaussianTwist, smul_eq_mul] using hmul)
    (gaussianTwist_bddAbove_wide chi hchi u rWidth hr0 hrHalf)
    (gaussianTwist_leftBoundary hkappa hkappaHalf chi hprim hchi u)
    (gaussianTwist_rightBoundary_wide chi rWidth hr0 u)
  simpa using hinterp

/-- Removing the Gaussian at its center costs nothing: its norm is
`exp(sigma^2) ≥ 1`. -/
theorem norm_LFunction_le_wide_interp
    {kappa rWidth : ℝ} (hkappa : 0 < kappa) (hkappaHalf : kappa ≤ 1 / 2)
    (hr0 : 0 < rWidth) (hrHalf : rWidth ≤ 1 / 2)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {sigma u : ℝ} (hsigma0 : 0 ≤ sigma)
    (hsigmaUpper : sigma ≤ 1 + rWidth) :
    ‖DirichletCharacter.LFunction chi
      ((sigma : ℂ) + (u : ℂ) * I)‖ ≤
      Real.rpow
        (12 * (1 + kappa⁻¹) *
          Real.rpow (2 * (q : ℝ) * (3 + |u|)) (kappa + 1 / 2))
        (1 - sigma / (1 + rWidth)) *
      Real.rpow
        (rightEdgePSeries rWidth * Real.exp ((1 + rWidth) ^ 2))
        (sigma / (1 + rWidth)) := by
  have hinterp := norm_gaussianTwist_le_wide_interp hkappa hkappaHalf
    hr0 hrHalf chi hprim hchi (sigma := sigma) (u := u)
      hsigma0 hsigmaUpper
  have hg := norm_centeredGaussian u
    ((sigma : ℂ) + (u : ℂ) * I)
  have hg' :
      ‖Complex.exp (((((sigma : ℂ) + (u : ℂ) * I) -
        (u : ℂ) * I)) ^ 2)‖ = Real.exp (sigma ^ 2) := by
    simpa using hg
  have hone : 1 ≤ Real.exp (sigma ^ 2) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (sq_nonneg sigma)
  have hL0 : 0 ≤ ‖DirichletCharacter.LFunction chi
      ((sigma : ℂ) + (u : ℂ) * I)‖ := norm_nonneg _
  calc
    ‖DirichletCharacter.LFunction chi
        ((sigma : ℂ) + (u : ℂ) * I)‖ ≤
      ‖DirichletCharacter.LFunction chi
        ((sigma : ℂ) + (u : ℂ) * I)‖ * Real.exp (sigma ^ 2) := by
      simpa using mul_le_mul_of_nonneg_left hone hL0
    _ = ‖gaussianTwist chi u ((sigma : ℂ) + (u : ℂ) * I)‖ := by
      rw [gaussianTwist, norm_mul, hg']
    _ ≤ _ := hinterp

end
end MAPBHPRademacherGaussianThreeLines

#print axioms MAPBHPRademacherGaussianThreeLines.norm_gaussianTwist_le_interp
#print axioms MAPBHPRademacherGaussianThreeLines.norm_LFunction_le_interp
#print axioms MAPBHPRademacherGaussianThreeLines.norm_LFunction_le_explicit_convexity
#print axioms MAPBHPRademacherGaussianThreeLines.norm_LFunction_le_jutila_convexity
#print axioms MAPBHPRademacherGaussianThreeLines.norm_gaussianTwist_le_wide_interp
#print axioms MAPBHPRademacherGaussianThreeLines.norm_LFunction_le_wide_interp
