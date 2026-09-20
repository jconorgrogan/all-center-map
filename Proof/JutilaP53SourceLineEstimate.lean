import JutilaP53LeftLineEstimate
import BHPRademacherGaussianThreeLines

/-! Source p.53 line `Re w = -1 + epsilon`, with its conductor-height exponent. -/
namespace MAPJutilaP53SourceLineEstimate
open Complex Real
open MAPJutilaP53TwoScaleContour MAPJutilaP53LeftLineEstimate
open MAPGammaCompactStripSharp MAPBHPRademacherGaussianThreeLines
noncomputable section

/-- One recurrence extends the certified exponential Gamma bound to the
source line; the only new cost is the distance `epsilon` from the pole. -/
theorem norm_Gamma_sourceStrip_le
    {epsilon t : ℝ} (heps : 0 < epsilon) (hepsHi : epsilon ≤ 1 / 2) :
    ‖Complex.Gamma ((epsilon : ℂ) + (t : ℂ) * I)‖ ≤
      (12 / epsilon) * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|) := by
  let z : ℂ := (epsilon : ℂ) + (t : ℂ) * I
  have hz : z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [z] at this
    linarith
  have hnorm : epsilon ≤ ‖z‖ := by
    have h := Complex.abs_re_le_norm z
    simpa [z, abs_of_pos heps] using h
  have hGamma := norm_Gamma_positive_strip_le_exp_pi_half
    (a := epsilon + 1) (t := t) (by linarith) (by linarith)
  have hrec := congrArg norm (Complex.Gamma_add_one z hz)
  rw [norm_mul] at hrec
  have hshift : GammaCompactStripScratch.stripPoint (epsilon + 1) t = z + 1 := by
    apply Complex.ext <;> simp [GammaCompactStripScratch.stripPoint, z] <;> ring
  rw [hshift, hrec] at hGamma
  have hprod : epsilon * ‖Complex.Gamma z‖ ≤
      12 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|) :=
    (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)).trans hGamma
  change ‖Complex.Gamma z‖ ≤ _
  calc
    _ ≤ (12 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) / epsilon :=
      (le_div_iff₀ heps).mpr (by simpa [mul_comm] using hprod)
    _ = _ := by ring

/-- The primitive p.48 estimate on the source line has exactly exponent
`1/2`: allocate half of the strip offset to the convexity epsilon. -/
theorem norm_primitiveLFunction_sourceStrip_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {epsilon sigma t : ℝ} (heps : 0 < epsilon) (hepsHi : epsilon ≤ 1 / 2)
    (hsLo : epsilon ≤ sigma) (hsHi : sigma ≤ 1) :
    ‖DirichletCharacter.LFunction chi ((sigma : ℂ) + (t : ℂ) * I)‖ ≤
      (36 * (1 + (epsilon / 2)⁻¹) * Real.rpow 6 (epsilon / 2 + 1 / 2)) *
        Real.rpow ((q : ℝ) * (1 + |t|)) (1 / 2) := by
  have hbound := norm_LFunction_le_jutila_convexity
    (eta := epsilon / 2) (u := t) (by positivity) (by linarith)
    chi hprim hchi (by linarith : 0 ≤ sigma) hsHi
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hbase : 1 ≤ (q : ℝ) * (1 + |t|) := by nlinarith [abs_nonneg t]
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hbase (by linarith))
      (show 0 ≤ 36 * (1 + (epsilon / 2)⁻¹) * Real.rpow 6 (epsilon / 2 + 1 / 2) by
        simp only [Real.rpow_eq_pow]; positivity))

/-- The source line stays a distance at least one half from the removable
quotient's origin. -/
theorem norm_scaleQuotient_sourceLine_le
    {U V epsilon t : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hepsHi : epsilon ≤ 1 / 2) :
    ‖p53ScaleRemovableQuotient U V
      (((-1 + epsilon : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      2 * (Real.rpow U (-1 + epsilon) + Real.rpow V (-1 + epsilon)) := by
  let w : ℂ := ((-1 + epsilon : ℝ) : ℂ) + (t : ℂ) * I
  have hn : (1 / 2 : ℝ) ≤ ‖w‖ := by
    have h := Complex.abs_re_le_norm w
    have hwre : w.re = -1 + epsilon := by simp [w]
    rw [hwre, abs_of_nonpos (by linarith)] at h
    linarith
  have hw : w ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  change ‖p53ScaleRemovableQuotient U V w‖ ≤ _
  rw [p53ScaleRemovableQuotient, Function.update_of_ne hw, norm_div]
  have hnum : ‖p53ScaleDifference U V w‖ ≤
      Real.rpow U (-1 + epsilon) + Real.rpow V (-1 + epsilon) := by
    have h := norm_sub_le ((U : ℂ) ^ w) ((V : ℂ) ^ w)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hU,
      Complex.norm_cpow_eq_rpow_re_of_pos hV] at h
    simpa [p53ScaleDifference, w] using h
  apply (div_le_iff₀ (by linarith : 0 < ‖w‖)).mpr
  have hsum0 : 0 ≤ Real.rpow U (-1 + epsilon) + Real.rpow V (-1 + epsilon) :=
    add_nonneg (Real.rpow_nonneg hU.le _) (Real.rpow_nonneg hV.le _)
  nlinarith [mul_nonneg hsum0 (show 0 ≤ ‖w‖ - 1 / 2 by linarith)]

/-- Pointwise source-line composition of Gamma, scale, and L factors. Its
conductor-height growth is a square root, and its endpoint exponent is
`-1+epsilon`, as on journal page 53. -/
theorem norm_integrand_sourceLine_le_of_pointwiseL
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {C : ℝ} (hC : 0 ≤ C)
    {s : ℂ} {U V epsilon t : ℝ} (hU : 0 < U) (hV : 0 < V)
    (heps : 0 < epsilon) (hepsHi : epsilon ≤ 1 / 8)
    (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 2 * epsilon)
    (hL : ‖DirichletCharacter.LFunction chi
      (((epsilon + s.re : ℝ) : ℂ) + ((s.im + t : ℝ) : ℂ) * I)‖ ≤
      C * Real.rpow ((q : ℝ) * (1 + |s.im + t|)) (1 / 2)) :
    ‖p53TwoScaleContourIntegrand chi s U V
      (((-1 + epsilon : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      ((24 / epsilon) * C) *
      Real.rpow ((q : ℝ) * (1 + |s.im|)) (1 / 2) *
      (1 + |t|) ^ 2 * Real.exp (-(Real.pi / 2) * |t|) *
      (Real.rpow U (-1 + epsilon) + Real.rpow V (-1 + epsilon)) := by
  let B := (q : ℝ) * (1 + |s.im|)
  let w : ℂ := ((-1 + epsilon : ℝ) : ℂ) + (t : ℂ) * I
  have hGamma := norm_Gamma_sourceStrip_le (t := t) heps (by linarith)
  have hpointG : w + 1 = (epsilon : ℂ) + (t : ℂ) * I := by
    apply Complex.ext <;> simp [w] <;> ring
  have hpointL : 1 + s + w = ((epsilon + s.re : ℝ) : ℂ) + ((s.im + t : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [w] <;> ring
  have hbase : (q : ℝ) * (1 + |s.im + t|) ≤ B * (1 + |t|) := by
    dsimp [B]
    have hsum := abs_add_le s.im t
    have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
    have hprod := mul_nonneg (abs_nonneg s.im) (abs_nonneg t)
    calc
      _ ≤ (q : ℝ) * ((1 + |s.im|) * (1 + |t|)) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hq
      _ = _ := by ring
  have hv : Real.rpow (1 + |t|) (1 / 2) ≤ 1 + |t| := by
    simpa using Real.rpow_le_rpow_of_exponent_le
      (show 1 ≤ 1 + |t| by linarith [abs_nonneg t]) (show (1 / 2 : ℝ) ≤ 1 by norm_num)
  have hL' : ‖DirichletCharacter.LFunction chi (1 + s + w)‖ ≤
      C * Real.rpow B (1 / 2) * (1 + |t|) := by
    rw [hpointL]
    calc
      _ ≤ C * Real.rpow ((q : ℝ) * (1 + |s.im + t|)) (1 / 2) := hL
      _ ≤ C * Real.rpow (B * (1 + |t|)) (1 / 2) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hbase (by norm_num)) hC
      _ = C * (Real.rpow B (1 / 2) * Real.rpow (1 + |t|) (1 / 2)) := by
        exact congrArg (fun y : ℝ => C * y)
          (Real.mul_rpow (show 0 ≤ B by dsimp [B]; positivity) (show 0 ≤ 1 + |t| by positivity))
      _ ≤ C * Real.rpow B (1 / 2) * (1 + |t|) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left hv (mul_nonneg hC (Real.rpow_nonneg (by dsimp [B]; positivity) _))
  have hQ := norm_scaleQuotient_sourceLine_le (t := t) hU hV (by linarith : epsilon ≤ 1 / 2)
  unfold p53TwoScaleContourIntegrand
  change ‖Complex.Gamma (w + 1) * p53ScaleRemovableQuotient U V w *
    DirichletCharacter.LFunction chi (1 + s + w)‖ ≤ _
  rw [norm_mul, norm_mul, hpointG]
  calc
    _ ≤ ((12 / epsilon) * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) *
        (2 * (Real.rpow U (-1 + epsilon) + Real.rpow V (-1 + epsilon))) *
        (C * Real.rpow B (1 / 2) * (1 + |t|)) := by
      exact mul_le_mul
        (mul_le_mul hGamma hQ (norm_nonneg _) (hGamma.trans' (norm_nonneg _))) hL'
        (norm_nonneg _)
        (mul_nonneg (hGamma.trans' (norm_nonneg _)) (hQ.trans' (norm_nonneg _)))
    _ = _ := by dsimp [B]; ring


/-- Literal source-line primitive nonprincipal integrand estimate. Its
conductor-height growth is a square root, and its endpoint exponent is
`-1+epsilon`, as on journal page 53. -/
theorem norm_primitive_integrand_sourceLine_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {s : ℂ} {U V epsilon t : ℝ} (hU : 0 < U) (hV : 0 < V)
    (heps : 0 < epsilon) (hepsHi : epsilon ≤ 1 / 8)
    (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 2 * epsilon) :
    ‖p53TwoScaleContourIntegrand chi s U V
      (((-1 + epsilon : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      ((24 / epsilon) *
        (36 * (1 + (epsilon / 2)⁻¹) * Real.rpow 6 (epsilon / 2 + 1 / 2))) *
      Real.rpow ((q : ℝ) * (1 + |s.im|)) (1 / 2) *
      (1 + |t|) ^ 2 * Real.exp (-(Real.pi / 2) * |t|) *
      (Real.rpow U (-1 + epsilon) + Real.rpow V (-1 + epsilon)) := by
  apply norm_integrand_sourceLine_le_of_pointwiseL chi
    (by simp only [Real.rpow_eq_pow]; positivity) hU hV heps hepsHi hsLo hsHi
  exact norm_primitiveLFunction_sourceStrip_le chi hprim hchi
    (t := s.im + t) heps (by linarith) (by linarith) (by linarith)

end
end MAPJutilaP53SourceLineEstimate
#print axioms MAPJutilaP53SourceLineEstimate.norm_Gamma_sourceStrip_le
#print axioms MAPJutilaP53SourceLineEstimate.norm_primitiveLFunction_sourceStrip_le

#print axioms MAPJutilaP53SourceLineEstimate.norm_primitive_integrand_sourceLine_le
