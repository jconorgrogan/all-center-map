import JutilaP53PrincipalFinitePole
import BHPPrincipalResidueBound

/-!
# Decaying envelope for the p.53 principal residue

Off the diagonal, one-separated ordinates force `|Im s| >= 1`.  The Gamma
factor then gives exponential decay while the removable scale quotient is
bounded on the exact strip `-1/2 <= Re(-s) <= 0`.
-/

namespace MAPJutilaP53PrincipalResidueEnvelope

open Complex Real
open MAPJutilaP53TwoScaleContour
open MAPJutilaP53LeftLineEstimate
open MAPGammaCompactStripSharp
open MAPBHPPrincipalResidueBound

noncomputable section

theorem norm_p53PrincipalResidue_le_offDiagonal
    (q : ℕ) [NeZero q] {s : ℂ} {U V : ℝ}
    (hU : 0 < U) (hV : 0 < V)
    (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 2)
    (hsIm : 1 ≤ |s.im|) :
    ‖p53PrincipalResidue q s U V‖ ≤
      12 * (1 + |s.im|) * Real.exp (-(Real.pi / 2) * |s.im|) *
        p53CpowEndpointBound U V (-(1 / 2)) 0 := by
  have hQ := norm_p53ScaleRemovableQuotient_horizontal_le hU hV
    (a := -(1 / 2)) (b := 0) (x := -s.re) (t := -s.im)
    (by linarith) (by linarith) (by simpa using hsIm)
  have hGamma := norm_Gamma_positive_strip_le_exp_pi_half
    (a := 1 - s.re) (t := -s.im) (by linarith) (by linarith)
  have hGammaArg :
      Complex.Gamma (1 - s) =
        Complex.Gamma
          (GammaCompactStripScratch.stripPoint (1 - s.re) (-s.im)) := by
    congr 1
    apply Complex.ext <;> simp [GammaCompactStripScratch.stripPoint]
  rw [← hGammaArg] at hGamma
  have hreg := norm_regularized_principal_one_le_one q
  have hQ' : ‖p53ScaleRemovableQuotient U V (-s)‖ ≤
      p53CpowEndpointBound U V (-(1 / 2)) 0 := by
    have harg : (((-s.re : ℝ) : ℂ) + (-s.im : ℝ) * I) = -s := by
      apply Complex.ext <;> simp
    rw [harg] at hQ
    exact hQ
  have hGamma' : ‖Complex.Gamma (1 - s)‖ ≤
      12 * (1 + |s.im|) *
        Real.exp (-(Real.pi / 2) * |s.im|) := by
    simpa using hGamma
  unfold p53PrincipalResidue
  rw [norm_mul, norm_mul]
  calc
    ‖Complex.Gamma (1 - s)‖ *
          ‖p53ScaleRemovableQuotient U V (-s)‖ *
          ‖DirichletZeros.regularizedLFunction
            (1 : DirichletCharacter ℂ q) 1‖ ≤
        (12 * (1 + |s.im|) *
          Real.exp (-(Real.pi / 2) * |s.im|)) *
          p53CpowEndpointBound U V (-(1 / 2)) 0 * 1 := by
      exact mul_le_mul
        (mul_le_mul hGamma' hQ' (norm_nonneg _)
          (by positivity)) hreg (norm_nonneg _)
          (mul_nonneg (by positivity)
            (p53CpowEndpointBound_nonneg hU hV _ _))
    _ = _ := by ring

theorem p53CpowEndpointBound_negHalf_zero_le_two
    {U V : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V) :
    p53CpowEndpointBound U V (-(1 / 2)) 0 ≤ 2 := by
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hV0 : 0 ≤ V := zero_le_one.trans hV
  have hUpow : U ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hU (by norm_num)
  have hVpow : V ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hV (by norm_num)
  unfold p53CpowEndpointBound
  norm_num
  rw [max_eq_right hUpow, max_eq_right hVpow]
  norm_num

/-- Scale-free off-diagonal residue envelope on source scales `U,V ≥ 1`. -/
theorem norm_p53PrincipalResidue_le_offDiagonal_sourceScales
    (q : ℕ) [NeZero q] {s : ℂ} {U V : ℝ}
    (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 2)
    (hsIm : 1 ≤ |s.im|) :
    ‖p53PrincipalResidue q s U V‖ ≤
      24 * (1 + |s.im|) * Real.exp (-(Real.pi / 2) * |s.im|) := by
  have hraw := norm_p53PrincipalResidue_le_offDiagonal q
    (zero_lt_one.trans_le hU) (zero_lt_one.trans_le hV)
    hsLo hsHi hsIm
  have hP := p53CpowEndpointBound_negHalf_zero_le_two hU hV
  calc
    _ ≤ 12 * (1 + |s.im|) * Real.exp (-(Real.pi / 2) * |s.im|) *
        p53CpowEndpointBound U V (-(1 / 2)) 0 := hraw
    _ ≤ 12 * (1 + |s.im|) * Real.exp (-(Real.pi / 2) * |s.im|) * 2 := by
      gcongr
    _ = _ := by ring

/-- A convenient pure exponential majorant for the residue profile. -/
theorem one_add_mul_exp_pi_half_le_two_exp_neg
    {x : ℝ} (hx : 0 ≤ x) :
    (1 + x) * Real.exp (-(Real.pi / 2) * x) ≤
      2 * Real.exp (-x) := by
  have hpi : (3 / 2 : ℝ) ≤ Real.pi / 2 := by
    nlinarith [Real.pi_gt_three]
  have hexp₁ : Real.exp (-(Real.pi / 2) * x) ≤
      Real.exp (-(3 / 2 : ℝ) * x) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hlin : 1 + x ≤ 2 * Real.exp (x / 2) := by
    have h := Real.add_one_le_exp (x / 2)
    nlinarith
  calc
    (1 + x) * Real.exp (-(Real.pi / 2) * x) ≤
        (1 + x) * Real.exp (-(3 / 2 : ℝ) * x) := by
      gcongr
    _ ≤ (2 * Real.exp (x / 2)) *
        Real.exp (-(3 / 2 : ℝ) * x) := by
      gcongr
    _ = 2 * Real.exp (-x) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem norm_p53PrincipalResidue_le_pureExp
    (q : ℕ) [NeZero q] {s : ℂ} {U V : ℝ}
    (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hsLo : 0 ≤ s.re) (hsHi : s.re ≤ 1 / 2)
    (hsIm : 1 ≤ |s.im|) :
    ‖p53PrincipalResidue q s U V‖ ≤ 48 * Real.exp (-|s.im|) := by
  have hraw := norm_p53PrincipalResidue_le_offDiagonal_sourceScales q
    hU hV hsLo hsHi hsIm
  have hprofile := one_add_mul_exp_pi_half_le_two_exp_neg
    (x := |s.im|) (abs_nonneg _)
  calc
    _ ≤ 24 * (1 + |s.im|) *
        Real.exp (-(Real.pi / 2) * |s.im|) := hraw
    _ = 24 * ((1 + |s.im|) *
        Real.exp (-(Real.pi / 2) * |s.im|)) := by ring
    _ ≤ 24 * (2 * Real.exp (-|s.im|)) := by gcongr
    _ = _ := by ring

end

end MAPJutilaP53PrincipalResidueEnvelope

#print axioms MAPJutilaP53PrincipalResidueEnvelope.norm_p53PrincipalResidue_le_offDiagonal
#print axioms MAPJutilaP53PrincipalResidueEnvelope.norm_p53PrincipalResidue_le_offDiagonal_sourceScales
#print axioms MAPJutilaP53PrincipalResidueEnvelope.one_add_mul_exp_pi_half_le_two_exp_neg
#print axioms MAPJutilaP53PrincipalResidueEnvelope.norm_p53PrincipalResidue_le_pureExp
