import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace MAPFordCoshSqFourierCertified

open MeasureTheory Set
open scoped Real

noncomputable section

private def expMap (u : ℝ) : ℝ := Real.exp (2 * u)
private def expKernel (y x : ℝ) : ℂ :=
  2 * Complex.exp ((Complex.I * y / 2) * Real.log x) / (1 + x) ^ 2
private def complexCoshSqFourier (y : ℝ) : ℂ :=
  ∫ u : ℝ, Complex.exp (Complex.I * (y * u)) / (Real.cosh u : ℂ) ^ 2

private lemma expMap_image : expMap '' (Set.univ : Set ℝ) = Set.Ioi 0 := by
  ext x
  constructor
  · rintro ⟨u, -, rfl⟩
    exact Real.exp_pos _
  · intro hx
    refine ⟨Real.log x / 2, Set.mem_univ _, ?_⟩
    simp only [expMap]
    rw [show 2 * (Real.log x / 2) = Real.log x by ring, Real.exp_log hx]

private lemma expMap_injective : Function.Injective expMap := by
  intro x z h
  apply (mul_left_cancel₀ (show (2:ℝ) ≠ 0 by norm_num))
  exact Real.exp_injective h

private lemma expMap_hasDerivAt (u : ℝ) :
    HasDerivAt expMap (2 * Real.exp (2 * u)) u := by
  simpa [expMap, mul_comm] using (Real.hasDerivAt_exp (2 * u)).comp u (hasDerivAt_const_mul 2)

private lemma exp_substitution (y : ℝ) :
    (∫ x : ℝ in Set.Ioi 0, expKernel y x) = complexCoshSqFourier y := by
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := Set.univ) (f := expMap) (f' := fun u => 2 * Real.exp (2*u))
    MeasurableSet.univ
    (fun u _ => (expMap_hasDerivAt u).hasDerivWithinAt)
    expMap_injective.injOn (expKernel y)
  rw [expMap_image] at h
  rw [h]
  simp only [Measure.restrict_univ]
  unfold complexCoshSqFourier
  apply integral_congr_ae
  filter_upwards with u
  simp only [expMap, expKernel, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos (by norm_num : (0:ℝ) < 2), Real.log_exp]
  rw [Complex.real_smul]
  push_cast
  have hexp : Complex.exp (Complex.I * (y:ℂ) / 2 * (2 * (u:ℂ))) =
      Complex.exp (Complex.I * ((y*u:ℝ):ℂ)) := by congr 1 <;> push_cast <;> ring
  rw [hexp]
  have hcosh : Complex.cosh (u : ℂ) =
      (1 + Complex.exp (2 * (u : ℂ))) / (2 * Complex.exp (u : ℂ)) := by
    rw [Complex.cosh, Complex.exp_neg]
    field_simp [Complex.exp_ne_zero]
    have he2 : Complex.exp (u : ℂ) ^ 2 = Complex.exp (2 * (u : ℂ)) := by
      rw [pow_two, ← Complex.exp_add]
      congr 1
      ring
    rw [he2]
    ring
  rw [hcosh]
  have hcast : (Complex.I * ((y * u : ℝ) : ℂ)) = Complex.I * ((y : ℂ) * (u : ℂ)) := by
    push_cast
    rfl
  rw [hcast]
  field_simp [Complex.exp_ne_zero]
  have he2 : Complex.exp (u : ℂ) ^ 2 = Complex.exp (2 * (u : ℂ)) := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  rw [he2]

end
end MAPFordCoshSqFourierCertified

namespace MAPFordCoshSqFourierCertified
open MeasureTheory Set
open scoped Real
noncomputable section

private def mobius (t : ℝ) : ℝ := t / (1 - t)

private lemma mobius_image : mobius '' Set.Ioo (0:ℝ) 1 = Set.Ioi 0 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact div_pos ht.1 (sub_pos.mpr ht.2)
  · intro hx
    refine ⟨x / (1+x), ?_, ?_⟩
    · have hden : 0 < 1 + x := by have := Set.mem_Ioi.mp hx; linarith
      constructor
      · exact div_pos hx hden
      · rw [div_lt_one hden]
        linarith
    · dsimp [mobius]
      have hden : 1 + x ≠ 0 := ne_of_gt (by have := Set.mem_Ioi.mp hx; linarith)
      field_simp [hden]
      ring

private lemma mobius_injOn : Set.InjOn mobius (Set.Ioo (0:ℝ) 1) := by
  intro x hx z hz h
  dsimp [mobius] at h
  have hx1 : 1-x ≠ 0 := ne_of_gt (sub_pos.mpr hx.2)
  have hz1 : 1-z ≠ 0 := ne_of_gt (sub_pos.mpr hz.2)
  field_simp [hx1, hz1] at h
  linarith

private lemma mobius_hasDerivWithinAt (t : ℝ) (ht : t ∈ Set.Ioo (0:ℝ) 1) :
    HasDerivWithinAt mobius (1 / (1-t)^2) (Set.Ioo (0:ℝ) 1) t := by
  have hne : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht.2)
  apply HasDerivAt.hasDerivWithinAt
  have hnum := hasDerivAt_id t
  have hden := (hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)
  convert hnum.div hden hne using 1
  simp only [Function.id_def, Pi.sub_apply]
  field_simp [hne]
  ring

end
end MAPFordCoshSqFourierCertified

namespace MAPFordCoshSqFourierCertified
open MeasureTheory Set
open scoped Real
noncomputable section

private lemma mobius_substitution_beta (y : ℝ) :
    (∫ x : ℝ in Set.Ioi 0, expKernel y x) =
      2 * Complex.betaIntegral (1 + Complex.I * y / 2) (1 - Complex.I * y / 2) := by
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := Set.Ioo (0:ℝ) 1) (f := mobius) (f' := fun t => 1 / (1-t)^2)
    measurableSet_Ioo
    (fun t ht => mobius_hasDerivWithinAt t ht)
    mobius_injOn (expKernel y)
  rw [mobius_image] at h
  rw [h]
  rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [← Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Ioc :
    Set.Ioo (0:ℝ) 1 =ᵐ[MeasureTheory.volume] Set.Ioc 0 1)]
  rw [← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have ht0 : 0 < t := ht.1
  have ht1 : 0 < 1-t := sub_pos.mpr ht.2
  have hmob : 0 < mobius t := div_pos ht0 ht1
  have hder : 0 < 1 / (1-t)^2 := by positivity
  rw [abs_of_pos hder]
  rw [Complex.real_smul]
  simp only [expKernel, mobius]
  push_cast
  have hden : (1 - (t:ℂ)) ≠ 0 := by exact_mod_cast ne_of_gt ht1
  have hrat : (1 + (t:ℂ) / (1-t:ℂ)) ^ 2 = (1 / (1-t:ℂ)) ^ 2 := by
    congr 1
    field_simp [hden]
    ring
  rw [hrat]
  field_simp [hden]
  have hcpow :
      Complex.exp ((Complex.I * (y:ℂ) / 2) * (Real.log (t / (1-t)) : ℂ)) =
        (t : ℂ) ^ (Complex.I * y / 2) *
          (1 - (t:ℂ)) ^ (-(Complex.I * y / 2)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ne_of_gt ht0)]
    rw [Complex.cpow_def_of_ne_zero hden]
    rw [← Complex.exp_add]
    congr 1
    rw [Real.log_div ht0.ne' ht1.ne']
    push_cast
    rw [Complex.ofReal_log ht0.le, Complex.ofReal_log ht1.le]
    rw [show ((1-t:ℝ):ℂ) = 1-(t:ℂ) by push_cast; rfl]
    ring
  rw [show Complex.I * (y:ℂ) * (Real.log (t / (1-t)) : ℂ) / 2 =
      (Complex.I * y / 2) * (Real.log (t / (1-t)) : ℂ) by ring]
  rw [hcpow]
  congr 1
  · ring
  · ring

end
end MAPFordCoshSqFourierCertified

namespace MAPFordCoshSqFourierCertified
open MeasureTheory Set
open scoped Real
noncomputable section

private lemma complex_transform (y : ℝ) :
    complexCoshSqFourier y =
      if y = 0 then 2 else (Real.pi * y / Real.sinh (Real.pi * y / 2) : ℝ) := by
  rw [← exp_substitution y, mobius_substitution_beta]
  by_cases hy : y = 0
  · subst y
    simp [Complex.betaIntegral_eval_one_right]
  rw [if_neg hy]
  let a : ℂ := Complex.I * (y : ℂ) / 2
  have ha0 : a ≠ 0 := by
    dsimp [a]
    exact div_ne_zero (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hy)) (by norm_num)
  have hsa : (1 + a).re = 1 := by simp [a]
  have hta : (1 - a).re = 1 := by simp [a]
  have hbeta := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := 1+a) (t := 1-a) (by rw [hsa]; norm_num) (by rw [hta]; norm_num)
  have hsum : (1+a) + (1-a) = (2:ℂ) := by ring
  rw [hsum, show Complex.Gamma (2:ℂ) = 1 by norm_num] at hbeta
  have hrec := Complex.Gamma_add_one a ha0
  have href := Complex.Gamma_mul_Gamma_one_sub a
  rw [one_mul] at hbeta
  have hprod : Complex.betaIntegral (1+a) (1-a) =
      a * ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * a)) := by
    rw [← hbeta]
    rw [add_comm 1 a, hrec]
    rw [mul_assoc, href]
  have hsin : Complex.sin ((Real.pi : ℂ) * a) =
      Complex.I * (Real.sinh (Real.pi * y / 2) : ℂ) := by
    dsimp [a]
    rw [show ((Real.pi : ℂ):ℂ) * (Complex.I * (y:ℂ) / 2) =
      ((Real.pi * y / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.sin_mul_I, Complex.ofReal_sinh]
    ring
  rw [show (1 + Complex.I * (y:ℂ) / 2) = 1+a by rfl,
      show (1 - Complex.I * (y:ℂ) / 2) = 1-a by rfl]
  rw [hprod, hsin]
  have hsinh0 : Real.sinh (Real.pi * y / 2) ≠ 0 := by
    rw [Real.sinh_ne_zero]
    exact div_ne_zero (mul_ne_zero Real.pi_ne_zero hy) (by norm_num)
  push_cast
  field_simp [hsinh0, Complex.I_ne_zero]
  ring

end
end MAPFordCoshSqFourierCertified

namespace MAPFordCoshSqFourierCertified
open MeasureTheory Set
open scoped Real
noncomputable section

private lemma expKernel_integrableOn (y : ℝ) :
    IntegrableOn (expKernel y) (Set.Ioi 0) := by
  have hg : Integrable (fun x : ℝ => 2 * (1 + x^2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul 2
  apply Integrable.mono' hg.integrableOn
  · refine (show AEStronglyMeasurable (expKernel y) (volume.restrict (Set.Ioi 0)) from ?_)
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro x hx
    unfold expKernel
    apply ContinuousAt.continuousWithinAt
    have hx0 : 0 < x := Set.mem_Ioi.mp hx
    have hlog : ContinuousAt (fun z : ℝ => (Real.log z : ℂ)) x :=
      Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log hx0.ne')
    have hphase : ContinuousAt
        (fun z : ℝ => (Complex.I * (y:ℂ) / 2) * (Real.log z : ℂ)) x :=
      continuousAt_const.mul hlog
    have hnum : ContinuousAt
        (fun z : ℝ => 2 * Complex.exp ((Complex.I * (y:ℂ) / 2) * (Real.log z : ℂ))) x :=
      continuousAt_const.mul (Complex.continuous_exp.continuousAt.comp hphase)
    have hdencont : ContinuousAt (fun z : ℝ => (1 + (z:ℂ)) ^ 2) x := by fun_prop
    apply hnum.div hdencont
    push_cast
    exact pow_ne_zero _ (by exact_mod_cast ne_of_gt (by linarith : 0 < 1+x))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := Set.mem_Ioi.mp hx
    dsimp [expKernel]
    rw [norm_div, norm_mul, Complex.norm_exp]
    have hre : (((Complex.I * (y:ℂ) / 2) * (Real.log x : ℂ))).re = 0 := by simp
    rw [hre, Real.exp_zero]
    have hden : 0 < 1+x := by linarith
    have hnorm2 : ‖(2:ℂ)‖ = 2 := by norm_num
    have hnormden : ‖(1:ℂ) + (x:ℂ)‖ = 1+x := by
      norm_cast
      exact abs_of_pos hden
    rw [hnorm2, norm_pow, hnormden]
    rw [show 2 * 1 / (1+x)^2 = 2 / (1+x)^2 by ring]
    have hsq : 0 < (1+x)^2 := sq_pos_of_pos hden
    have hsq2 : 0 < 1+x^2 := by positivity
    rw [div_le_iff₀ hsq]
    rw [show 2 * (1+x^2)⁻¹ = 2 / (1+x^2) by ring]
    rw [show 2 / (1+x^2) * (1+x)^2 = (2 * (1+x)^2) / (1+x^2) by ring]
    rw [le_div_iff₀ hsq2]
    nlinarith [sq_nonneg x]

end
end MAPFordCoshSqFourierCertified

namespace MAPFordCoshSqFourierCertified
open MeasureTheory Set
open scoped Real
noncomputable section

private lemma exp_change_integrand_eq (y u : ℝ) :
    |2 * Real.exp (2*u)| • expKernel y (expMap u) =
      Complex.exp (Complex.I * (y * u)) / (Real.cosh u : ℂ) ^ 2 := by
  simp only [expMap, expKernel, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos (by norm_num : (0:ℝ) < 2), Real.log_exp]
  rw [Complex.real_smul]
  push_cast
  have hexp : Complex.exp (Complex.I * (y:ℂ) / 2 * (2 * (u:ℂ))) =
      Complex.exp (Complex.I * ((y*u:ℝ):ℂ)) := by congr 1 <;> push_cast <;> ring
  rw [hexp]
  have hcosh : Complex.cosh (u : ℂ) =
      (1 + Complex.exp (2 * (u : ℂ))) / (2 * Complex.exp (u : ℂ)) := by
    rw [Complex.cosh, Complex.exp_neg]
    field_simp [Complex.exp_ne_zero]
    have he2 : Complex.exp (u : ℂ) ^ 2 = Complex.exp (2 * (u : ℂ)) := by
      rw [pow_two, ← Complex.exp_add]
      congr 1
      ring
    rw [he2]
    ring
  rw [hcosh]
  have hcast : (Complex.I * ((y * u : ℝ) : ℂ)) = Complex.I * ((y : ℂ) * (u : ℂ)) := by
    push_cast
    rfl
  rw [hcast]
  field_simp [Complex.exp_ne_zero]
  have he2 : Complex.exp (u : ℂ) ^ 2 = Complex.exp (2 * (u : ℂ)) := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  rw [he2]

private lemma complex_integrable (y : ℝ) :
    Integrable (fun u : ℝ =>
      Complex.exp (Complex.I * (y * u)) / (Real.cosh u : ℂ) ^ 2) := by
  have hiff := MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Set.univ) (f := expMap) (f' := fun u => 2 * Real.exp (2*u))
    MeasurableSet.univ
    (fun u _ => (expMap_hasDerivAt u).hasDerivWithinAt)
    expMap_injective.injOn (expKernel y)
  rw [expMap_image] at hiff
  have htrans := hiff.mp (expKernel_integrableOn y)
  have htarget : IntegrableOn (fun u : ℝ =>
      Complex.exp (Complex.I * (y * u)) / (Real.cosh u : ℂ) ^ 2) Set.univ :=
    htrans.congr_fun (fun u _ => exp_change_integrand_eq y u) MeasurableSet.univ
  exact MeasureTheory.integrableOn_univ.mp htarget

end
end MAPFordCoshSqFourierCertified

namespace MAPFordCoshSqFourierCertified
open MeasureTheory Set
open scoped Real
noncomputable section

private lemma complex_integrand_re (y u : ℝ) :
    (Complex.exp (Complex.I * (y * u)) / (Real.cosh u : ℂ) ^ 2).re =
      Real.cos (y*u) / (Real.cosh u)^2 := by
  rw [← Complex.ofReal_pow, Complex.div_ofReal_re]
  rw [Complex.exp_re]
  simp

/-- Ford's exact Fourier transform of `sech²`, with the source's zero branch. -/
theorem fordCoshSqFourierIdentity (y : ℝ) :
    (∫ u : ℝ, Real.cos (y*u) / (Real.cosh u)^2) =
      if y = 0 then 2 else Real.pi * y / Real.sinh (Real.pi*y/2) := by
  have hi := complex_integrable y
  calc
    (∫ u : ℝ, Real.cos (y*u) / (Real.cosh u)^2) =
        ∫ u : ℝ, (Complex.exp (Complex.I * (y * u)) /
          (Real.cosh u : ℂ)^2).re := by
            apply integral_congr_ae
            filter_upwards with u
            exact (complex_integrand_re y u).symm
    _ = (complexCoshSqFourier y).re := by
          simpa only [complexCoshSqFourier] using integral_re hi
    _ = (if y = 0 then 2 else (Real.pi * y / Real.sinh (Real.pi*y/2) : ℝ)) := by
          rw [complex_transform y]
          split_ifs with hy
          · simp
          · norm_cast


end
end MAPFordCoshSqFourierCertified

#print axioms MAPFordCoshSqFourierCertified.fordCoshSqFourierIdentity
