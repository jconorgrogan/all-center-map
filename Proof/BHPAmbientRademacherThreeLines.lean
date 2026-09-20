import BHPRademacherGaussianThreeLines
import JutilaHybridConvexityEulerReduction
import PrimeFactorSquareRootBound

/-!
# Quantitative Rademacher interpolation for ambient characters

The primitive functional equation is used only on `Re s = 0`.  The elementary
`2^omega(q) <= 4 sqrt(q)` convention loss turns that boundary into a linear
conductor bound.  The `Re s = 1+r` boundary is applied directly to the ambient
character, so no Euler-factor loss contaminates the Perron right endpoint.
-/

namespace MAPBHPAmbientRademacherThreeLines

open Complex Set
open Complex.HadamardThreeLines
open MAPBHPRademacherGaussianEnvelope
open MAPBHPRademacherGaussianThreeLines
open MAPBHPRademacherZeroBoundary
open MAPJutilaHybridConvexityEulerReduction
open MAPPrimeFactorSquareRootBound
open MAPZeroFreeSiegelSpine
open PrimitiveTruncatedExplicitFormulaBridge

noncomputable section

/-- Exact ambient zero-line estimate.  The conductor-convention loss has been
absorbed with the proved square-root bound, leaving the linear ambient modulus
which BHP's Rademacher estimate permits. -/
theorem norm_ambientLFunction_imaginary_le_clean
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) (t : ℝ) :
    ‖DirichletCharacter.LFunction chi ((t : ℂ) * I)‖ ≤
      12 * (1 + Real.log (2 * (q : ℝ) * (3 + |t|))) *
        (q : ℝ) * Real.rpow (1 + |t|) (1 / 2) := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hprimNe : chi.primitiveCharacter ≠ 1 := by
    intro hp
    exact hchi ((primitiveCharacter_eq_one_iff chi).mp hp)
  have hprim := norm_LFunction_imaginary_le_clean chi.primitiveCharacter
    chi.primitiveCharacter_isPrimitive hprimNe t
  have heuler := norm_LFunction_le_primitive_mul_two_pow_card chi hchi
    (s := ((t : ℂ) * I)) (by simp)
  have hcondNat : chi.conductor ≤ q :=
    ZeroDensityInterface.conductor_le_level chi
  have hcond : (chi.conductor : ℝ) ≤ q := by exact_mod_cast hcondNat
  have hqNat : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast hqNat
  have hcondNatOne : 1 ≤ chi.conductor :=
    Nat.one_le_iff_ne_zero.mpr chi.conductor_ne_zero
  have hcondOne : (1 : ℝ) ≤ chi.conductor := by exact_mod_cast hcondNatOne
  have hcondPos : (0 : ℝ) < chi.conductor := by
    exact_mod_cast (Nat.pos_of_ne_zero chi.conductor_ne_zero)
  have hscaleCond : 0 < 2 * (chi.conductor : ℝ) * (3 + |t|) := by positivity
  have hscaleQ : 0 < 2 * (q : ℝ) * (3 + |t|) := by positivity
  have hscaleLe : 2 * (chi.conductor : ℝ) * (3 + |t|) ≤
      2 * (q : ℝ) * (3 + |t|) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcond (by norm_num)) (by positivity)
  have hlogLe :
      1 + Real.log (2 * (chi.conductor : ℝ) * (3 + |t|)) ≤
        1 + Real.log (2 * (q : ℝ) * (3 + |t|)) := by
    simpa [add_comm] using add_le_add_left
      (Real.strictMonoOn_log.monotoneOn hscaleCond hscaleQ hscaleLe) 1
  have hsqrtCond : Real.rpow (chi.conductor : ℝ) (1 / 2) ≤
      Real.sqrt (q : ℝ) := by
    have h := Real.sqrt_le_sqrt hcond
    simpa only [Real.sqrt_eq_rpow] using h
  have hheight0 : 0 ≤ Real.rpow (1 + |t|) (1 / 2) :=
    Real.rpow_nonneg (by positivity) _
  have hcondHalf0 : 0 ≤ Real.rpow (chi.conductor : ℝ) (1 / 2) :=
    Real.rpow_nonneg hcondPos.le _
  have hlogQ0 :
      0 ≤ 1 + Real.log (2 * (q : ℝ) * (3 + |t|)) := by
    have hs : 1 ≤ 2 * (q : ℝ) * (3 + |t|) := by
      nlinarith [abs_nonneg t]
    have := Real.log_nonneg hs
    linarith
  have hprimQ :
      ‖DirichletCharacter.LFunction chi.primitiveCharacter ((t : ℂ) * I)‖ ≤
        3 * (1 + Real.log (2 * (q : ℝ) * (3 + |t|))) *
          Real.sqrt (q : ℝ) * Real.rpow (1 + |t|) (1 / 2) := by
    calc
      ‖DirichletCharacter.LFunction chi.primitiveCharacter ((t : ℂ) * I)‖ ≤
        3 * (1 + Real.log (2 * (chi.conductor : ℝ) * (3 + |t|))) *
          Real.rpow (chi.conductor : ℝ) (1 / 2) *
            Real.rpow (1 + |t|) (1 / 2) := hprim
      _ ≤ 3 * (1 + Real.log (2 * (q : ℝ) * (3 + |t|))) *
          Real.sqrt (q : ℝ) * Real.rpow (1 + |t|) (1 / 2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul
            (mul_le_mul_of_nonneg_left hlogLe (by norm_num)) hsqrtCond
            hcondHalf0
            (mul_nonneg (by norm_num)
              (by
                have hcondScale : 1 ≤
                    2 * (chi.conductor : ℝ) * (3 + |t|) := by
                  nlinarith [abs_nonneg t, hcondOne]
                have := Real.log_nonneg hcondScale
                nlinarith)))
          hheight0
  have hEulerBound : (2 : ℝ) ^ q.primeFactors.card ≤
      4 * Real.sqrt (q : ℝ) :=
    two_pow_card_primeFactors_le_four_sqrt q (NeZero.ne q)
  have hprimQ0 : 0 ≤
      3 * (1 + Real.log (2 * (q : ℝ) * (3 + |t|))) *
          Real.sqrt (q : ℝ) * Real.rpow (1 + |t|) (1 / 2) := by
    positivity
  have hsqrtSq : Real.sqrt (q : ℝ) * Real.sqrt (q : ℝ) = (q : ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg q)]
  calc
    ‖DirichletCharacter.LFunction chi ((t : ℂ) * I)‖ ≤
      ‖DirichletCharacter.LFunction chi.primitiveCharacter ((t : ℂ) * I)‖ *
        (2 : ℝ) ^ q.primeFactors.card := heuler
    _ ≤ (3 * (1 + Real.log (2 * (q : ℝ) * (3 + |t|))) *
          Real.sqrt (q : ℝ) * Real.rpow (1 + |t|) (1 / 2)) *
        (4 * Real.sqrt (q : ℝ)) :=
      mul_le_mul hprimQ hEulerBound (by positivity) hprimQ0
    _ = 12 * (1 + Real.log (2 * (q : ℝ) * (3 + |t|))) *
        (q : ℝ) * Real.rpow (1 + |t|) (1 / 2) := by
      calc
        (3 * (1 + Real.log (2 * (q : ℝ) * (3 + |t|))) *
              Real.sqrt (q : ℝ) * Real.rpow (1 + |t|) (1 / 2)) *
            (4 * Real.sqrt (q : ℝ)) =
          12 * (1 + Real.log (2 * (q : ℝ) * (3 + |t|))) *
            (Real.sqrt (q : ℝ) * Real.sqrt (q : ℝ)) *
              Real.rpow (1 + |t|) (1 / 2) := by ring
        _ = 12 * (1 + Real.log (2 * (q : ℝ) * (3 + |t|))) *
            (q : ℝ) * Real.rpow (1 + |t|) (1 / 2) := by rw [hsqrtSq]

/-- Scalar Gaussian envelope for the ambient zero-line boundary. -/
theorem logarithmic_linear_gaussian_envelope
    {kappa : ℝ} (hkappa : 0 < kappa) (hkappaHalf : kappa ≤ 1 / 2)
    {q : ℕ} (hq : 1 ≤ q) (u v : ℝ) :
    12 * (1 + Real.log (2 * (q : ℝ) * (3 + |v|))) *
        (q : ℝ) * Real.rpow (1 + |v|) (1 / 2) *
        Real.exp (-((v - u) ^ 2)) ≤
      48 * (1 + kappa⁻¹) *
        Real.rpow (2 * (q : ℝ) * (3 + |u|)) (kappa + 1) := by
  let Q : ℝ := 2 * (q : ℝ) * (3 + |u|)
  have hbase := logarithmic_sqrt_gaussian_envelope
    hkappa hkappaHalf hq u v
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hQ : 1 ≤ Q := by dsimp [Q]; nlinarith [abs_nonneg u]
  have hqsqrt0 : 0 ≤ Real.rpow (q : ℝ) (1 / 2) :=
    Real.rpow_nonneg (by linarith) _
  have hqsplit : Real.rpow (q : ℝ) (1 / 2) *
      Real.rpow (q : ℝ) (1 / 2) = (q : ℝ) := by
    calc
      Real.rpow (q : ℝ) (1 / 2) * Real.rpow (q : ℝ) (1 / 2) =
          Real.rpow (q : ℝ) ((1 / 2) + (1 / 2)) :=
        (Real.rpow_add (by linarith : (0 : ℝ) < q) (1 / 2) (1 / 2)).symm
      _ = (q : ℝ) := by norm_num
  have hqQ : Real.rpow (q : ℝ) (1 / 2) ≤ Real.rpow Q (1 / 2) :=
    Real.rpow_le_rpow (by positivity) (by dsimp [Q]; nlinarith [abs_nonneg u])
      (by norm_num)
  have hQcombine : Real.rpow Q (kappa + 1 / 2) * Real.rpow Q (1 / 2) =
      Real.rpow Q (kappa + 1) := by
    calc
      Real.rpow Q (kappa + 1 / 2) * Real.rpow Q (1 / 2) =
          Real.rpow Q ((kappa + 1 / 2) + (1 / 2)) :=
        (Real.rpow_add (by linarith : 0 < Q)
          (kappa + 1 / 2) (1 / 2)).symm
      _ = Real.rpow Q (kappa + 1) := by congr 1 <;> ring
  have hfac0 : 0 ≤ 1 + kappa⁻¹ := by
    have : 0 ≤ kappa⁻¹ := inv_nonneg.mpr hkappa.le
    linarith
  have hRhs0 : 0 ≤ 12 * (1 + kappa⁻¹) *
      Real.rpow Q (kappa + 1 / 2) :=
    mul_nonneg (mul_nonneg (by norm_num) hfac0)
      (Real.rpow_nonneg (by linarith) _)
  calc
    12 * (1 + Real.log (2 * (q : ℝ) * (3 + |v|))) *
        (q : ℝ) * Real.rpow (1 + |v|) (1 / 2) *
        Real.exp (-((v - u) ^ 2)) =
      (3 * (1 + Real.log (2 * (q : ℝ) * (3 + |v|))) *
        Real.rpow (q : ℝ) (1 / 2) *
        Real.rpow (1 + |v|) (1 / 2) *
        Real.exp (-((v - u) ^ 2))) *
        (4 * Real.rpow (q : ℝ) (1 / 2)) := by
      calc
        12 * (1 + Real.log (2 * (q : ℝ) * (3 + |v|))) *
            (q : ℝ) * Real.rpow (1 + |v|) (1 / 2) *
            Real.exp (-((v - u) ^ 2)) =
          12 * (1 + Real.log (2 * (q : ℝ) * (3 + |v|))) *
            (Real.rpow (q : ℝ) (1 / 2) * Real.rpow (q : ℝ) (1 / 2)) *
            Real.rpow (1 + |v|) (1 / 2) *
            Real.exp (-((v - u) ^ 2)) := by rw [hqsplit]
        _ = (3 * (1 + Real.log (2 * (q : ℝ) * (3 + |v|))) *
            Real.rpow (q : ℝ) (1 / 2) *
            Real.rpow (1 + |v|) (1 / 2) *
            Real.exp (-((v - u) ^ 2))) *
            (4 * Real.rpow (q : ℝ) (1 / 2)) := by ring
    _ ≤ (12 * (1 + kappa⁻¹) *
        Real.rpow Q (kappa + 1 / 2)) *
        (4 * Real.rpow (q : ℝ) (1 / 2)) := by
      exact mul_le_mul_of_nonneg_right hbase (by positivity)
    _ ≤ (12 * (1 + kappa⁻¹) *
        Real.rpow Q (kappa + 1 / 2)) *
        (4 * Real.rpow Q (1 / 2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hqQ (by norm_num)) hRhs0
    _ = 48 * (1 + kappa⁻¹) * Real.rpow Q (kappa + 1) := by
      rw [← hQcombine]
      ring
    _ = 48 * (1 + kappa⁻¹) *
        Real.rpow (2 * (q : ℝ) * (3 + |u|)) (kappa + 1) := by rfl

private theorem ambientGaussian_leftBoundary
    {kappa : ℝ} (hkappa : 0 < kappa) (hkappaHalf : kappa ≤ 1 / 2)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) (u : ℝ) :
    ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ),
      ‖gaussianTwist chi u z‖ ≤
        48 * (1 + kappa⁻¹) *
          Real.rpow (2 * (q : ℝ) * (3 + |u|)) (kappa + 1) := by
  intro z hz
  have hzre : z.re = 0 := by simpa using hz
  let v : ℝ := z.im
  have hzform : z = (v : ℂ) * I := by
    apply Complex.ext <;> simp [v, hzre]
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hL := norm_ambientLFunction_imaginary_le_clean chi hchi v
  change ‖DirichletCharacter.LFunction chi z *
      Complex.exp ((z - (u : ℂ) * I) ^ 2)‖ ≤ _
  rw [norm_mul, hzform]
  have hg :
      ‖Complex.exp ((((v : ℂ) * I - (u : ℂ) * I) ^ 2))‖ =
        Real.exp (-((v - u) ^ 2)) := by
    simpa using norm_centeredGaussian u ((v : ℂ) * I)
  rw [hg]
  calc
    ‖DirichletCharacter.LFunction chi ((v : ℂ) * I)‖ *
        Real.exp (-((v - u) ^ 2)) ≤
      (12 * (1 + Real.log (2 * (q : ℝ) * (3 + |v|))) *
        (q : ℝ) * Real.rpow (1 + |v|) (1 / 2)) *
          Real.exp (-((v - u) ^ 2)) :=
      mul_le_mul_of_nonneg_right hL (Real.exp_pos _).le
    _ ≤ _ := logarithmic_linear_gaussian_envelope
      hkappa hkappaHalf hq u v

private theorem ambientGaussian_rightBoundary_wide
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

/-- Explicit ambient-character strip interpolation through `Re s = 1+r`.
No primitive restriction and no hidden epsilon-dependent constant remain. -/
theorem norm_ambientLFunction_le_wide_interp
    {kappa rWidth : ℝ} (hkappa : 0 < kappa)
    (hkappaHalf : kappa ≤ 1 / 2)
    (hr0 : 0 < rWidth) (hrHalf : rWidth ≤ 1 / 2)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) {sigma u : ℝ} (hsigma0 : 0 ≤ sigma)
    (hsigmaUpper : sigma ≤ 1 + rWidth) :
    ‖DirichletCharacter.LFunction chi
      ((sigma : ℂ) + (u : ℂ) * I)‖ ≤
      Real.rpow
        (48 * (1 + kappa⁻¹) *
          Real.rpow (2 * (q : ℝ) * (3 + |u|)) (kappa + 1))
        (1 - sigma / (1 + rWidth)) *
      Real.rpow
        (rightEdgePSeries rWidth * Real.exp ((1 + rWidth) ^ 2))
        (sigma / (1 + rWidth)) := by
  have hwidth : (0 : ℝ) < 1 + rWidth := by linarith
  have htwist :=
    Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (f := gaussianTwist chi u)
    (z := ((sigma : ℂ) + (u : ℂ) * I))
    (l := (0 : ℝ)) (u := 1 + rWidth)
    (a := 48 * (1 + kappa⁻¹) *
      Real.rpow (2 * (q : ℝ) * (3 + |u|)) (kappa + 1))
    (b := rightEdgePSeries rWidth * Real.exp ((1 + rWidth) ^ 2))
    hwidth
    (by constructor <;> simp_all)
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
    (ambientGaussian_leftBoundary hkappa hkappaHalf chi hchi u)
    (ambientGaussian_rightBoundary_wide chi rWidth hr0 u)
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
    _ ≤ _ := by simpa using htwist

end
end MAPBHPAmbientRademacherThreeLines

#print axioms MAPBHPAmbientRademacherThreeLines.norm_ambientLFunction_imaginary_le_clean
#print axioms MAPBHPAmbientRademacherThreeLines.norm_ambientLFunction_le_wide_interp
