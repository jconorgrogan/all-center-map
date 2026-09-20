import KhaleAppendixBLFunctionFubiniCertified
import KhaleAppendixBLemma51KernelCertified
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Certified Euler/Fourier expansion for Khale Lemma 5.1

This file closes the character-valued Euler expansion, absolute Fubini
interchange, phase extraction, and the odd-sine cancellation.  Together with
the premise-free Ford transform, it inhabits the exact expansion binder
consumed by the Appendix-B reduction.
-/

set_option maxHeartbeats 800000

namespace MAPKhaleAppendixBLemma51EulerFourierCertified

open MeasureTheory
open MAPKhaleAppendixBLemma51ExpansionReduction
open MAPKhaleAppendixBLFunctionEulerCertified
open MAPKhaleAppendixBLFunctionFubiniCertified
open MAPKhaleAppendixBFirstPartAnalyticReduction
open MAPKhaleAppendixBLemma51KernelCertified
open MAPKhaleCoshSqKernelIntegrable

noncomputable section

theorem nat_cpow_affine_factor (p : ℕ) (hp : 0 < p) (x v : ℝ) :
    (p : ℂ) ^ (-affineSpectralPoint x v 0 0) =
      (Real.rpow (p : ℝ) (-x) : ℂ) *
        Complex.exp (((-(v * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [Complex.cpow_def_of_ne_zero hpC]
  change Complex.exp (Complex.log ((p : ℝ) : ℂ) * -affineSpectralPoint x v 0 0) = _
  rw [← Complex.ofReal_log (show 0 ≤ (p : ℝ) by positivity)]
  rw [show ((Real.log (p : ℝ) : ℂ) * -affineSpectralPoint x v 0 0) =
      (((-x * Real.log (p : ℝ) : ℝ) : ℂ)) +
        (((-(v * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I) by
    simp [affineSpectralPoint]
    ring]
  rw [Complex.exp_add]
  have hr : ((Real.rpow (p : ℝ) (-x) : ℝ) : ℂ) =
      Complex.exp (((-x * Real.log (p : ℝ) : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_exp]
    norm_cast
    change (p : ℝ) ^ (-x) = _
    rw [Real.rpow_def_of_pos (show 0 < (p : ℝ) by positivity)]
    congr 1
    ring
  rw [hr]


open MAPKhaleAppendixBLFunctionEulerCertified
open MAPKhaleAppendixBLemma51ExpansionReduction
open MAPKhaleAppendixBLFunctionFubiniCertified

theorem term_factor {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (j : ℕ) (hj : 0 < j) (x t a u : ℝ)
    (k : PrimePowerIndex) :
    appendixBLPrimePowerTerm (chi ^ j) (affineSpectralPoint x t a u) k =
      (((Real.rpow (k.1 : ℝ) (-x)) ^ ppExponent k / (ppExponent k : ℕ) : ℝ) : ℂ) *
        ((chi k.1) ^ (j * ppExponent k) *
          Complex.exp (((-((ppExponent k : ℝ) * (t + a*u) *
            Real.log (k.1 : ℝ)) : ℝ) : ℂ) * Complex.I)) := by
  have hp := k.1.property.pos
  have hcp := nat_cpow_affine_factor k.1 hp x (t+a*u)
  have hs : affineSpectralPoint x t a u = affineSpectralPoint x (t+a*u) 0 0 := by
    simp [affineSpectralPoint]
  unfold appendixBLPrimePowerTerm
  rw [hs, hcp]
  rw [mul_pow]
  rw [mul_pow]
  rw [← Complex.exp_nat_mul]
  have hchar : (chi ^ j) k.1 = (chi k.1) ^ j :=
    MulChar.pow_apply' chi hj.ne' k.1
  rw [hchar]
  rw [← pow_mul]
  push_cast
  ring_nf

open MAPKhaleAppendixBFirstPartAnalyticReduction

theorem term_re_phase_unit {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (j : ℕ) (hj : 0 < j)
    (sigma eta gamma u : ℝ) (k : PrimePowerIndex)
    (hunit : IsUnit (k.1 : ZMod q)) :
    (appendixBLPrimePowerTerm (chi ^ j)
      (affineSpectralPoint (sigma+eta) (j*gamma) (2*eta/Real.pi) u) k).re =
      appendixBCharacterPrimePowerWeight chi sigma eta k *
        Real.cos ((j : ℝ) * appendixBPrimePowerPhase chi gamma k +
          (2 * eta * (ppExponent k : ℝ) * Real.log (k.1 : ℝ) / Real.pi) * u) := by
  rw [term_factor chi j hj]
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hnorm : ‖chi k.1‖ = 1 := by
    simpa [hunit.unit_spec] using chi.unit_norm_eq_one hunit.unit
  have hpolar := Complex.norm_mul_exp_arg_mul_I (chi k.1)
  rw [hnorm, Complex.ofReal_one, one_mul] at hpolar
  rw [← hpolar]
  rw [← Complex.exp_nat_mul]
  rw [← Complex.exp_add]
  rw [Complex.exp_re]
  norm_num
  simp only [Complex.log_re, Complex.log_im]
  have hp0 : (0 : ℝ) ≤ (k.1 : ℝ) := by positivity
  have hargp : ((k.1 : ℂ).arg) = 0 := by
    change (((k.1 : ℝ) : ℂ).arg) = 0
    exact Complex.arg_ofReal_of_nonneg hp0
  rw [hargp]
  simp only [mul_zero, Real.exp_zero, one_mul, norm_natCast]
  rw [show (↑j * ↑(ppExponent k) * (chi k.1).arg +
      -(↑(ppExponent k) * (↑j * gamma + 2 * eta / Real.pi * u) *
        Real.log (k.1 : ℝ))) =
      -((j : ℝ) * appendixBPrimePowerPhase chi gamma k +
        (2 * eta * (ppExponent k : ℝ) * Real.log (k.1 : ℝ) / Real.pi) * u) by
    unfold appendixBPrimePowerPhase
    ring]
  rw [Real.cos_neg]
  have hweight :
      ((k.1 : ℝ) ^ (-(sigma+eta))) ^ ppExponent k /
          (ppExponent k : ℕ) =
        appendixBCharacterPrimePowerWeight chi sigma eta k := by
    unfold appendixBCharacterPrimePowerWeight
    change ((k.1 : ℝ) ^ (-(sigma + eta))) ^ ppExponent k /
      (ppExponent k : ℝ) =
      (k.1 : ℝ) ^ (-((ppExponent k : ℝ) * (sigma + eta))) *
        ‖chi k.1‖ ^ ppExponent k / (ppExponent k : ℝ)
    rw [hnorm, one_pow, mul_one]
    have hp0 : (0 : ℝ) ≤ (k.1 : ℝ) := by positivity
    rw [show -((ppExponent k : ℝ) * (sigma + eta)) =
      (-(sigma+eta)) * (ppExponent k : ℝ) by ring]
    rw [Real.rpow_mul_natCast hp0]
  rw [show -eta + -sigma = -(sigma + eta) by ring]
  rw [hweight]

theorem term_re_phase {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (j : ℕ) (hj : 0 < j)
    (sigma eta gamma u : ℝ) (k : PrimePowerIndex) :
    (appendixBLPrimePowerTerm (chi ^ j)
      (affineSpectralPoint (sigma+eta) (j*gamma) (2*eta/Real.pi) u) k).re =
      appendixBCharacterPrimePowerWeight chi sigma eta k *
        Real.cos ((j : ℝ) * appendixBPrimePowerPhase chi gamma k +
          (2 * eta * (ppExponent k : ℝ) * Real.log (k.1 : ℝ) / Real.pi) * u) := by
  by_cases hunit : IsUnit (k.1 : ZMod q)
  · exact term_re_phase_unit chi j hj sigma eta gamma u k hunit
  · have hchi : chi k.1 = 0 := chi.map_nonunit hunit
    have hchij : (chi ^ j) k.1 = 0 := by
      rw [MulChar.pow_apply' chi hj.ne' k.1, hchi]
      exact zero_pow hj.ne'
    unfold appendixBLPrimePowerTerm appendixBCharacterPrimePowerWeight
    rw [hchij, zero_mul, zero_pow (by simp [ppExponent]), zero_div]
    rw [hchi, norm_zero, zero_pow (by simp [ppExponent]), mul_zero, zero_div, zero_mul]
    simp

open MeasureTheory MAPKhaleAppendixBLemma51KernelCertified
open MAPKhaleCoshSqKernelIntegrable

theorem integral_cos_add_div_cosh_sq (theta y : ℝ) :
    (∫ u : ℝ, Real.cos (theta + y * u) / (Real.cosh u) ^ 2) =
      Real.cos theta * coshSqFourier y := by
  have hc := cos_mul_invCoshSq_integrable y
  have hs := sin_mul_invCoshSq_integrable y
  rw [show (fun u : ℝ => Real.cos (theta + y * u) / (Real.cosh u) ^ 2) =
      (fun u : ℝ => Real.cos theta *
          (Real.cos (y*u) / (Real.cosh u)^2) -
        Real.sin theta * (Real.sin (y*u) / (Real.cosh u)^2)) by
    funext u
    rw [Real.cos_add]
    ring]
  rw [integral_sub (hc.const_mul _) (hs.const_mul _)]
  rw [integral_const_mul, integral_const_mul]
  rw [integral_sin_mul_invCoshSq_eq_zero, mul_zero, sub_zero]
  rfl

theorem weighted_integral_phase {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (j : ℕ) (hj : 0 < j)
    (sigma eta gamma : ℝ) (k : PrimePowerIndex) :
    (∫ u : ℝ, weightedLPrimePowerIntegrand (chi ^ j)
      (sigma+eta) (j*gamma) (2*eta/Real.pi) k u) =
      appendixBCharacterPrimePowerWeight chi sigma eta k *
        coshSqFourier
          (2 * eta * (ppExponent k : ℝ) * Real.log (k.1 : ℝ) / Real.pi) *
        Real.cos ((j : ℝ) * appendixBPrimePowerPhase chi gamma k) := by
  let theta := (j : ℝ) * appendixBPrimePowerPhase chi gamma k
  let y := 2 * eta * (ppExponent k : ℝ) * Real.log (k.1 : ℝ) / Real.pi
  let w := appendixBCharacterPrimePowerWeight chi sigma eta k
  have hpoint (u : ℝ) : weightedLPrimePowerIntegrand (chi ^ j)
      (sigma+eta) (j*gamma) (2*eta/Real.pi) k u =
      w * (Real.cos (theta + y*u) / (Real.cosh u)^2) := by
    unfold weightedLPrimePowerIntegrand
    rw [term_re_phase chi j hj sigma eta gamma u k]
    dsimp [theta, y, w]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [integral_const_mul]
  rw [integral_cos_add_div_cosh_sq]
  dsimp [theta, y, w]
  ring

theorem appendixBLemma51EulerFourierExpansion : AppendixBLemma51EulerFourierExpansion := by
  intro q _inst chi sigma eta gamma hsigma heta
  have hx : 1 < sigma + eta := lt_of_le_of_lt hsigma (lt_add_of_pos_right sigma heta)
  let f : ℕ → PrimePowerIndex → ℝ := fun j k =>
    ∫ u : ℝ, weightedLPrimePowerIntegrand (chi ^ j)
      (sigma+eta) (j*gamma) (2*eta/Real.pi) k u
  have hf (j : ℕ) : Summable (f j) := by
    dsimp [f]
    exact integral_weightedLPrimePowerIntegrand_summable (chi ^ j) hx
  have hL (j : ℕ) : appendixBLogIntegral chi j sigma eta gamma = ∑' k, f j k := by
    have h := logNorm_affine_integral_eq_tsum_integrals (chi ^ j)
      (x := sigma+eta) (t := j*gamma) (a := 2*eta/Real.pi) hx
    calc
      appendixBLogIntegral chi j sigma eta gamma =
          ∫ u : ℝ, Real.log ‖DirichletCharacter.LFunction (chi ^ j)
            (affineSpectralPoint (sigma+eta) (j*gamma) (2*eta/Real.pi) u)‖ /
              (Real.cosh u)^2 := by
        unfold appendixBLogIntegral
        apply integral_congr_ae
        filter_upwards with u
        congr 3
        unfold affineSpectralPoint
        push_cast
        ring
      _ = ∑' k, f j k := by simpa only [f] using h
  let g : PrimePowerIndex → ℝ := fun k =>
    17.145 * f 1 k + 10.6825 * f 2 k + 4.5 * f 3 k + f 4 k
  have hg : Summable g := by
    dsimp [g]
    exact ((((hf 1).mul_left 17.145).add ((hf 2).mul_left 10.6825)).add
      ((hf 3).mul_left 4.5)).add (hf 4)
  have hterm (k : PrimePowerIndex) :
      g k = appendixBLemma51PrimePowerTerm chi sigma eta gamma k := by
    dsimp [g, f]
    have h1 := weighted_integral_phase chi 1 (by norm_num) sigma eta gamma k
    have h2 := weighted_integral_phase chi 2 (by norm_num) sigma eta gamma k
    have h3 := weighted_integral_phase chi 3 (by norm_num) sigma eta gamma k
    have h4 := weighted_integral_phase chi 4 (by norm_num) sigma eta gamma k
    norm_num at h1 h2 h3 h4
    simp only [pow_one, Nat.cast_one, one_mul]
    rw [h1, h2, h3, h4]
    unfold appendixBLemma51PrimePowerTerm
    norm_num
    ring
  have hfinal : Summable (appendixBLemma51PrimePowerTerm chi sigma eta gamma) :=
    hg.congr (fun k => hterm k)
  refine ⟨hfinal, ?_⟩
  unfold appendixBIntegralCombination
  rw [hL 1, hL 2, hL 3, hL 4]
  calc
    17.145 * ∑' k, f 1 k + 10.6825 * ∑' k, f 2 k +
        4.5 * ∑' k, f 3 k + ∑' k, f 4 k = ∑' k, g k := by
      rw [← (hf 1).tsum_mul_left, ← (hf 2).tsum_mul_left,
        ← (hf 3).tsum_mul_left]
      rw [← ((hf 1).mul_left 17.145).tsum_add ((hf 2).mul_left 10.6825)]
      rw [← (((hf 1).mul_left 17.145).add ((hf 2).mul_left 10.6825)).tsum_add
        ((hf 3).mul_left 4.5)]
      rw [← ((((hf 1).mul_left 17.145).add ((hf 2).mul_left 10.6825)).add
        ((hf 3).mul_left 4.5)).tsum_add (hf 4)]
    _ = ∑' k, appendixBLemma51PrimePowerTerm chi sigma eta gamma k :=
      tsum_congr hterm


end
end MAPKhaleAppendixBLemma51EulerFourierCertified

#print axioms MAPKhaleAppendixBLemma51EulerFourierCertified.appendixBLemma51EulerFourierExpansion
