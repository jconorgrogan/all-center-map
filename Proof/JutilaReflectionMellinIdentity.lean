import GammaMellinInversion
import GuthMaynardHeathBrownSmoothing
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Exact Mellin identity at the start of Jutila's reflection lemma

Jutila, *Zero-density estimates for L-functions*, Acta Arith. 32 (1977),
Lemma 1 and its proof on pp. 57--58, starts from the Mellin representation
of

`exp (-(n/U)^h)`

with kernel `Gamma (1 + w/h) / w` on `Re w = c`.  This file derives that
normalization from the already certified Gamma Mellin inversion theorem.  In
particular it certifies the change of variables `w = c + i r`, `r = h t`,
the Gamma recurrence, and the complex-power scaling.  The later contour
shift and functional equation in Jutila's Lemma 1 remain separate.
-/

namespace JutilaReflectionMellinIdentity

open Complex Real MeasureTheory

noncomputable section

def jutilaMellinIntegrand (c h x r : ℝ) : ℂ :=
  Complex.Gamma
      (1 + (((c : ℂ) + (r : ℂ) * Complex.I) / (h : ℂ))) *
    (x : ℂ) ^ (-((c : ℂ) + (r : ℂ) * Complex.I)) /
      ((c : ℂ) + (r : ℂ) * Complex.I)

/-- Positive-real complex powers commute with the real power in the base.
This is the branch-safe identity needed after `r = h t`. -/
theorem cpow_neg_real_mul_eq_rpow_cpow
    {x h : ℝ} (hx : 0 < x) (z : ℂ) :
    (x : ℂ) ^ (-((h : ℂ) * z)) =
      ((Real.rpow x h : ℝ) : ℂ) ^ (-z) := by
  have hcast : ((Real.rpow x h : ℝ) : ℂ) =
      (x : ℂ) ^ (h : ℂ) := Complex.ofReal_cpow hx.le h
  rw [hcast]
  have him : (Complex.log (x : ℂ) * (h : ℂ)).im = 0 := by
    rw [← Complex.ofReal_log hx.le]
    simp
  calc
    (x : ℂ) ^ (-((h : ℂ) * z)) =
        (x : ℂ) ^ ((h : ℂ) * (-z)) := by congr 1 <;> ring
    _ = ((x : ℂ) ^ (h : ℂ)) ^ (-z) :=
      Complex.cpow_mul (-z)
        (by simpa [him] using (neg_lt_zero.mpr Real.pi_pos))
        (by simpa [him] using Real.pi_pos.le)

/-- The source integrand after the exact scale change `r = h t`.  The factor
`1/h` is the Jacobian that will cancel against `dr = h dt`. -/
theorem jutilaMellinIntegrand_scale
    {c h x t : ℝ} (hc : 0 < c) (hh : 0 < h) (hx : 0 < x) :
    jutilaMellinIntegrand c h x (h * t) =
      ((h⁻¹ : ℝ) : ℂ) *
        (Complex.Gamma (((c / h : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          ((Real.rpow x h : ℝ) : ℂ) ^
            (-(((c / h : ℝ) : ℂ) + (t : ℂ) * Complex.I))) := by
  let z : ℂ := ((c / h : ℝ) : ℂ) + (t : ℂ) * Complex.I
  let w : ℂ := (c : ℂ) + ((h * t : ℝ) : ℂ) * Complex.I
  have hhC : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  have hw : w = (h : ℂ) * z := by
    dsimp [w, z]
    push_cast
    field_simp
    <;> ring
  have hzre : z.re = c / h := by simp [z]
  have hz0 : z ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    rw [hzre] at hre
    have hre0 : c / h = 0 := by simpa using hre
    exact (div_pos hc hh).ne' hre0
  have hquot : w / (h : ℂ) = z := by rw [hw, mul_div_cancel_left₀ z hhC]
  have hcpow :
      (x : ℂ) ^ (-w) =
        ((Real.rpow x h : ℝ) : ℂ) ^ (-z) := by
    rw [hw]
    exact cpow_neg_real_mul_eq_rpow_cpow hx z
  unfold jutilaMellinIntegrand
  change Complex.Gamma (1 + w / (h : ℂ)) * (x : ℂ) ^ (-w) / w =
    ((h⁻¹ : ℝ) : ℂ) *
      (Complex.Gamma z * ((Real.rpow x h : ℝ) : ℂ) ^ (-z))
  rw [hquot, hcpow]
  rw [show 1 + z = z + 1 by ring, Complex.Gamma_add_one z hz0]
  rw [hw]
  field_simp [hhC, hz0]
  push_cast
  field_simp [hh.ne']

/-- Scaling Lebesgue measure on the vertical parameter contributes exactly
the positive factor `h`. -/
theorem integral_jutilaMellinIntegrand_eq_scaled
    {c h x : ℝ} (hh : 0 < h) :
    (∫ r : ℝ, jutilaMellinIntegrand c h x r) =
      h • ∫ t : ℝ, jutilaMellinIntegrand c h x (h * t) := by
  have hscale := Measure.integral_comp_mul_left
    (jutilaMellinIntegrand c h x) h
  rw [abs_of_pos (inv_pos.mpr hh)] at hscale
  have hscaled := congrArg (fun z : ℂ => h • z) hscale
  simpa [smul_smul, hh.ne'] using hscaled.symm

/-- Literal Jutila normalization on `Re w = c`.  This is the exact one-body
Mellin identity used termwise at the beginning of the proof of Lemma 1. -/
theorem exp_neg_rpow_eq_jutila_vertical_integral
    {c h x : ℝ} (hc : 0 < c) (hh : 0 < h) (hx : 0 < x) :
    (Real.exp (-Real.rpow x h) : ℂ) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ r : ℝ, jutilaMellinIntegrand c h x r) := by
  have hbase := MAPGammaMellinInversion.exp_neg_eq_gamma_vertical_integral
    (sigma := c / h) (x := Real.rpow x h) (div_pos hc hh)
      (Real.rpow_pos_of_pos hx h)
  rw [integral_jutilaMellinIntegrand_eq_scaled hh]
  change (Real.exp (-Real.rpow x h) : ℂ) =
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ((h : ℂ) * ∫ t : ℝ, jutilaMellinIntegrand c h x (h * t)))
  rw [show (∫ t : ℝ, jutilaMellinIntegrand c h x (h * t)) =
      ∫ t : ℝ, ((h⁻¹ : ℝ) : ℂ) *
        (Complex.Gamma (((c / h : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          ((Real.rpow x h : ℝ) : ℂ) ^
            (-(((c / h : ℝ) : ℂ) + (t : ℂ) * Complex.I))) by
        apply integral_congr_ae
        filter_upwards [] with t
        exact jutilaMellinIntegrand_scale hc hh hx]
  rw [MeasureTheory.integral_const_mul]
  simpa [smul_eq_mul, hh.ne'] using hbase

end

end JutilaReflectionMellinIdentity

#print axioms JutilaReflectionMellinIdentity.cpow_neg_real_mul_eq_rpow_cpow
#print axioms JutilaReflectionMellinIdentity.jutilaMellinIntegrand_scale
#print axioms JutilaReflectionMellinIdentity.integral_jutilaMellinIntegrand_eq_scaled
#print axioms JutilaReflectionMellinIdentity.exp_neg_rpow_eq_jutila_vertical_integral
