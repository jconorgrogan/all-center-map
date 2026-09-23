import MRTProposition51Source
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Analysis.Fourier.ZMod

/-!
# Regression certificate for the rejected finite MRT Lemma 2.9 translation

The published MRT Lemma 2.9 uses a complete Dirichlet series with finitely
supported coefficients.  `MAPMRTProposition51Source.MRTLemma29` instead
truncates both the original and rescaled variables at the same `N`, without a
support premise.  The theorem `not_MRTLemma29` gives an exact counterexample,
so the old proposition must never be used as a certified source theorem.
-/

namespace MAPMRTLemma29Proof

open scoped BigOperators ZMod
open MAPMRTProposition51Source MAPMRTCorollary53Source MixedMeanFrontend
noncomputable section

theorem additive_phase_eq_stdAddChar {q : ℕ} [NeZero q] (a n : ℕ) :
    fourier (n : ℤ) (((a : ℝ) / q : ℝ) : UnitAddCircle) =
      ZMod.stdAddChar ((a * n : ℕ) : ZMod q) := by
  rw [fourier_coe_apply]
  have hcast : ((a * n : ℕ) : ZMod q) = ((a * n : ℤ) : ZMod q) := by norm_num
  rw [hcast, ZMod.stdAddChar_coe]
  push_cast
  congr 1
  ring

end
end MAPMRTLemma29Proof

namespace MAPMRTLemma29Counterexample
open scoped BigOperators ZMod
open MAPMRTProposition51Source MAPMRTCorollary53Source MixedMeanFrontend
noncomputable section

def badF (n : ℕ) : ℂ :=
  if n = 2 then 1 else if n = 4 then -(Real.sqrt 2 : ℂ) else 0

theorem badF_lhs : finiteCriticalPolynomial 2 (additiveTwist 2 1 badF) 0 =
    (Real.sqrt 2 : ℂ)⁻¹ := by
  have hIcc : Finset.Icc 1 2 = {1, 2} := by decide
  have hzero : (2 : ℤ) • (((2 : ℝ)⁻¹ : ℝ) : UnitAddCircle) = 0 := by
    rw [← QuotientAddGroup.mk_zsmul]
    norm_num
  have hphase : (↑(AddCircle.toCircle ((2 : ℤ) •
      (((1 : ℝ) / 2 : ℝ) : UnitAddCircle))) : ℂ) = 1 := by
    have hzeroDiv : (2 : ℤ) •
        (((1 : ℝ) / 2 : ℝ) : UnitAddCircle) = 0 := by
      rw [← QuotientAddGroup.mk_zsmul]
      norm_num
    rw [hzeroDiv]
    simp
  rw [finiteCriticalPolynomial, hIcc]
  norm_num [additiveTwist, badF, mellinPhase, hphase]
  rw [show (2 : ℕ) • (((1 : ℝ) / 2 : ℝ) : UnitAddCircle) = 0 by
    rw [← QuotientAddGroup.mk_nsmul]
    norm_num]
  simp


end
end MAPMRTLemma29Counterexample

namespace MAPMRTLemma29Counterexample
open scoped BigOperators ZMod
open MAPMRTProposition51Source MAPMRTCorollary53Source MixedMeanFrontend
noncomputable section

lemma badF_inner_one_two (chi : DirichletCharacter ℂ 2) :
    (∑ n ∈ Finset.Icc 1 2,
      badF (1 * n) * chi n * (Real.sqrt n : ℂ)⁻¹ *
        mellinPhase n 0) = 0 := by
  have hIcc : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hIcc]
  have hchi1 : chi ((1 : ℕ) : ZMod 2) = 1 := by simp
  have hchi2 : chi ((2 : ℕ) : ZMod 2) = 0 := by
    apply MulChar.map_nonunit
    decide
  have hchi2' : chi (2 : ZMod 2) = 0 := by
    apply MulChar.map_nonunit
    decide
  norm_num [badF, mellinPhase, hchi1, hchi2, hchi2']

lemma badF_inner_two_one (chi : DirichletCharacter ℂ 1) :
    (∑ n ∈ Finset.Icc 1 2,
      badF (2 * n) * chi n * (Real.sqrt n : ℂ)⁻¹ *
        mellinPhase n 0) = 0 := by
  have hIcc : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hIcc]
  have hall (x : ZMod 1) : chi x = 1 := by
    rw [show x = 1 from Subsingleton.elim _ _, map_one]
  simp_rw [hall]
  norm_num [badF, mellinPhase]

end
end MAPMRTLemma29Counterexample

namespace MAPMRTLemma29Counterexample
open scoped BigOperators ZMod
open MAPMRTProposition51Source MAPMRTCorollary53Source MixedMeanFrontend
noncomputable section

lemma modulusFactorizations_two :
    modulusFactorizations 2 = {(1, 2), (2, 1)} := by decide

lemma badF_rhs_inner_sum :
    (∑ z ∈ modulusFactorizations 2,
      ∑ chi : DirichletCharacter ℂ z.2,
        ‖∑ n ∈ Finset.Icc 1 2,
          badF (z.1 * n) * chi n * (Real.sqrt n : ℂ)⁻¹ *
            mellinPhase n 0‖) = 0 := by
  have h1 : (∑ chi : DirichletCharacter ℂ 2,
      ‖∑ n ∈ Finset.Icc 1 2,
        badF (1 * n) * chi n * (Real.sqrt n : ℂ)⁻¹ * mellinPhase n 0‖) = 0 := by
    apply Finset.sum_eq_zero
    intro chi hchi
    rw [badF_inner_one_two]
    simp
  have h2 : (∑ chi : DirichletCharacter ℂ 1,
      ‖∑ n ∈ Finset.Icc 1 2,
        badF (2 * n) * chi n * (Real.sqrt n : ℂ)⁻¹ * mellinPhase n 0‖) = 0 := by
    apply Finset.sum_eq_zero
    intro chi hchi
    rw [badF_inner_two_one]
    simp
  rw [modulusFactorizations_two]
  rw [Finset.sum_insert (by decide : (1, 2) ∉ ({(2, 1)} : Finset (ℕ × ℕ))),
      Finset.sum_singleton]
  change (∑ chi : DirichletCharacter ℂ 2,
      ‖∑ n ∈ Finset.Icc 1 2,
        badF n * chi n * (Real.sqrt n : ℂ)⁻¹ * mellinPhase n 0‖) +
    (∑ chi : DirichletCharacter ℂ 1,
      ‖∑ n ∈ Finset.Icc 1 2,
        badF (2 * n) * chi n * (Real.sqrt n : ℂ)⁻¹ * mellinPhase n 0‖) = 0
  rw [h2]
  simpa only [one_mul, add_zero] using h1


theorem not_MRTLemma29 : ¬ MRTLemma29 := by
  intro h
  have hbad := h 2 2 1 badF 0 (by omega) (by norm_num)
  rw [badF_lhs, badF_rhs_inner_sum] at hbad
  simp only [mul_zero] at hbad
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hinv : 0 < (Real.sqrt (2 : ℝ))⁻¹ := inv_pos.mpr hs
  have hnorm : ‖(Real.sqrt 2 : ℂ)⁻¹‖ = (Real.sqrt (2 : ℝ))⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  rw [hnorm] at hbad
  exact (not_le_of_gt hinv) hbad

end
end MAPMRTLemma29Counterexample

#print axioms MAPMRTLemma29Proof.additive_phase_eq_stdAddChar
#print axioms MAPMRTLemma29Counterexample.not_MRTLemma29
