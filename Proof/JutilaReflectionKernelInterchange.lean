import JutilaReflectionMellinIdentity

/-!
# Sum--integral interchange for Jutila's reflection kernel

This file promotes the one-frequency Mellin identity at the start of Jutila
Lemma 1 (Acta Arith. 32 (1977), pp. 57--58) to finite and countable
collections.  The countable theorem exposes the standard weighted summability
condition contributed by the source line `Re w = c`; no Dirichlet-series or
contour-shift estimate is hidden in a custom premise.
-/

namespace JutilaReflectionKernelInterchange

open Complex Real MeasureTheory Filter
open JutilaReflectionMellinIdentity
open scoped BigOperators

noncomputable section

def verticalPoint (c r : ℝ) : ℂ :=
  (c : ℂ) + (r : ℂ) * Complex.I

def jutilaKernel (c h r : ℝ) : ℂ :=
  Complex.Gamma (1 + verticalPoint c r / (h : ℂ)) /
    verticalPoint c r

theorem jutilaMellinIntegrand_eq
    (c h x r : ℝ) :
    jutilaMellinIntegrand c h x r =
      (x : ℂ) ^ (-verticalPoint c r) * jutilaKernel c h r := by
  unfold jutilaMellinIntegrand jutilaKernel verticalPoint
  ring

theorem jutilaKernel_scale
    {c h t : ℝ} (hc : 0 < c) (hh : 0 < h) :
    jutilaKernel c h (h * t) =
      ((h⁻¹ : ℝ) : ℂ) *
        Complex.Gamma (((c / h : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
  have hs := jutilaMellinIntegrand_scale
    (c := c) (h := h) (x := 1) (t := t) hc hh one_pos
  rw [jutilaMellinIntegrand_eq] at hs
  simpa [verticalPoint, jutilaKernel] using hs

/-- The reflection kernel is genuinely integrable on every positive source
line.  This is obtained from vertical Gamma integrability after the exact
scale change, not postulated. -/
theorem integrable_jutilaKernel
    {c h : ℝ} (hc : 0 < c) (hh : 0 < h) :
    Integrable (jutilaKernel c h) := by
  have hGamma := MAPGammaMellinInversion.verticalIntegrable_Gamma (div_pos hc hh)
  unfold Complex.VerticalIntegrable at hGamma
  have hscaled : Integrable (fun t : ℝ =>
      ((h⁻¹ : ℝ) : ℂ) *
        Complex.Gamma (((c / h : ℝ) : ℂ) + (t : ℂ) * Complex.I)) :=
    hGamma.const_mul ((h⁻¹ : ℝ) : ℂ)
  have hcomp : Integrable (fun t : ℝ => jutilaKernel c h (h * t)) :=
    hscaled.congr (Filter.Eventually.of_forall fun t =>
      (jutilaKernel_scale hc hh).symm)
  exact (integrable_comp_mul_left_iff (jutilaKernel c h) hh.ne').mp hcomp

theorem integrable_frequency_mul_jutilaKernel
    {c h x : ℝ} (hc : 0 < c) (hh : 0 < h) (hx : 0 < x) :
    Integrable (fun r : ℝ =>
      (x : ℂ) ^ (-verticalPoint c r) * jutilaKernel c h r) := by
  have hK := integrable_jutilaKernel hc hh
  apply hK.bdd_mul (c := Real.rpow x (-c))
  · apply Continuous.aestronglyMeasurable
    have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    rw [show (fun r : ℝ => (x : ℂ) ^ (-verticalPoint c r)) =
        (fun r : ℝ => Complex.exp
          (Complex.log (x : ℂ) * (-verticalPoint c r))) by
      funext r
      simpa using Complex.cpow_def_of_ne_zero hxC (-verticalPoint c r)]
    unfold verticalPoint
    fun_prop
  · exact Filter.Eventually.of_forall (fun r => by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp [verticalPoint])

theorem integrable_coefficient_frequency_mul_jutilaKernel
    {c h x : ℝ} (hc : 0 < c) (hh : 0 < h) (hx : 0 < x)
    (a : ℂ) :
    Integrable (fun r : ℝ => a *
      ((x : ℂ) ^ (-verticalPoint c r) * jutilaKernel c h r)) :=
  (integrable_frequency_mul_jutilaKernel hc hh hx).const_mul a

/-- Exact finite Fubini step for arbitrary positive Mellin frequencies and
coefficients. -/
theorem finite_jutilaKernel_interchange
    {ι : Type*} [DecidableEq ι]
    {c h : ℝ} (hc : 0 < c) (hh : 0 < h)
    (S : Finset ι) (a : ι → ℂ) (x : ι → ℝ)
    (hx : ∀ i ∈ S, 0 < x i) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ r : ℝ, ∑ i ∈ S, a i *
          ((x i : ℂ) ^ (-verticalPoint c r) * jutilaKernel c h r)) =
      ∑ i ∈ S, a i * (Real.exp (-Real.rpow (x i) h) : ℂ) := by
  rw [integral_finset_sum S (fun i hi =>
    integrable_coefficient_frequency_mul_jutilaKernel hc hh (hx i hi) (a i))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hInv := exp_neg_rpow_eq_jutila_vertical_integral
    (c := c) (h := h) (x := x i) hc hh (hx i hi)
  have hInv' :
      (Real.exp (-Real.rpow (x i) h) : ℂ) =
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ r : ℝ, (x i : ℂ) ^ (-verticalPoint c r) *
            jutilaKernel c h r) := by
    calc
      (Real.exp (-Real.rpow (x i) h) : ℂ) =
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ r : ℝ, jutilaMellinIntegrand c h (x i) r) := hInv
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with r
        exact jutilaMellinIntegrand_eq c h (x i) r
  rw [show (∫ r : ℝ, a i *
      ((x i : ℂ) ^ (-verticalPoint c r) * jutilaKernel c h r)) =
      a i * ∫ r : ℝ,
        ((x i : ℂ) ^ (-verticalPoint c r) * jutilaKernel c h r) by
    rw [integral_const_mul]]
  calc
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (a i * ∫ r : ℝ,
          (x i : ℂ) ^ (-verticalPoint c r) * jutilaKernel c h r)) =
      a i * ((((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ r : ℝ,
          (x i : ℂ) ^ (-verticalPoint c r) * jutilaKernel c h r)) := by ring
    _ = a i * (Real.exp (-Real.rpow (x i) h) : ℂ) := by rw [← hInv']

/-- Countable Fubini with the literal Bochner summability hypothesis. -/
theorem countable_jutilaKernel_interchange_of_summable_integral_norm
    {ι : Type*} [Countable ι]
    {c h : ℝ} (hc : 0 < c) (hh : 0 < h)
    (a : ι → ℂ) (x : ι → ℝ) (hx : ∀ i, 0 < x i)
    (hFsum : Summable fun i => ∫ r : ℝ,
      ‖a i * ((x i : ℂ) ^ (-verticalPoint c r) * jutilaKernel c h r)‖) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ r : ℝ, ∑' i : ι, a i *
          ((x i : ℂ) ^ (-verticalPoint c r) * jutilaKernel c h r)) =
      ∑' i : ι, a i * (Real.exp (-Real.rpow (x i) h) : ℂ) := by
  let F : ι → ℝ → ℂ := fun i r => a i *
    ((x i : ℂ) ^ (-verticalPoint c r) * jutilaKernel c h r)
  have hFint : ∀ i, Integrable (F i) := fun i =>
    integrable_coefficient_frequency_mul_jutilaKernel hc hh (hx i) (a i)
  have hFubini : (∑' i : ι, ∫ r : ℝ, F i r) =
      ∫ r : ℝ, ∑' i : ι, F i r :=
    integral_tsum_of_summable_integral_norm hFint (by simpa [F] using hFsum)
  calc
    (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ r : ℝ, ∑' i : ι, F i r) =
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∑' i : ι, ∫ r : ℝ, F i r)) := by rw [hFubini]
    _ = ∑' i : ι, (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ r : ℝ, F i r) := by rw [tsum_mul_left]
    _ = ∑' i : ι, a i * (Real.exp (-Real.rpow (x i) h) : ℂ) := by
      apply tsum_congr
      intro i
      have hInv := exp_neg_rpow_eq_jutila_vertical_integral
        (c := c) (h := h) (x := x i) hc hh (hx i)
      have hInv' :
          (Real.exp (-Real.rpow (x i) h) : ℂ) =
            (((1 / (2 * Real.pi) : ℝ) : ℂ) *
              ∫ r : ℝ, (x i : ℂ) ^ (-verticalPoint c r) *
                jutilaKernel c h r) := by
        calc
          (Real.exp (-Real.rpow (x i) h) : ℂ) =
              (((1 / (2 * Real.pi) : ℝ) : ℂ) *
                ∫ r : ℝ, jutilaMellinIntegrand c h (x i) r) := hInv
          _ = _ := by
            congr 1
            apply integral_congr_ae
            filter_upwards [] with r
            exact jutilaMellinIntegrand_eq c h (x i) r
      unfold F
      rw [integral_const_mul]
      calc
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (a i * ∫ r : ℝ,
              (x i : ℂ) ^ (-verticalPoint c r) * jutilaKernel c h r)) =
          a i * ((((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ r : ℝ,
              (x i : ℂ) ^ (-verticalPoint c r) * jutilaKernel c h r)) := by ring
        _ = a i * (Real.exp (-Real.rpow (x i) h) : ℂ) := by rw [← hInv']

/-- A source-usable sufficient condition: the source line contributes the
exact frequency weight `x^{-c}`. -/
theorem countable_jutilaKernel_interchange_of_weighted_summable
    {ι : Type*} [Countable ι]
    {c h : ℝ} (hc : 0 < c) (hh : 0 < h)
    (a : ι → ℂ) (x : ι → ℝ) (hx : ∀ i, 0 < x i)
    (hsum : Summable fun i => ‖a i‖ * Real.rpow (x i) (-c)) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ r : ℝ, ∑' i : ι, a i *
          ((x i : ℂ) ^ (-verticalPoint c r) * jutilaKernel c h r)) =
      ∑' i : ι, a i * (Real.exp (-Real.rpow (x i) h) : ℂ) := by
  have hK := integrable_jutilaKernel hc hh
  have hFsum : Summable fun i => ∫ r : ℝ,
      ‖a i * ((x i : ℂ) ^ (-verticalPoint c r) * jutilaKernel c h r)‖ := by
    have hscaled := hsum.mul_right (∫ r : ℝ, ‖jutilaKernel c h r‖)
    apply hscaled.congr
    intro i
    symm
    calc
      (∫ r : ℝ, ‖a i *
          ((x i : ℂ) ^ (-verticalPoint c r) * jutilaKernel c h r)‖) =
        ∫ r : ℝ, (‖a i‖ * Real.rpow (x i) (-c)) *
          ‖jutilaKernel c h r‖ := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun r => by
              change ‖a i *
                  ((x i : ℂ) ^ (-verticalPoint c r) * jutilaKernel c h r)‖ =
                (‖a i‖ * Real.rpow (x i) (-c)) * ‖jutilaKernel c h r‖
              rw [norm_mul, norm_mul,
                Complex.norm_cpow_eq_rpow_re_of_pos (hx i)]
              simp [verticalPoint, mul_assoc])
      _ = (‖a i‖ * Real.rpow (x i) (-c)) *
          ∫ r : ℝ, ‖jutilaKernel c h r‖ := by rw [integral_const_mul]
  exact countable_jutilaKernel_interchange_of_summable_integral_norm
    hc hh a x hx hFsum

end

end JutilaReflectionKernelInterchange

#print axioms JutilaReflectionKernelInterchange.integrable_jutilaKernel
#print axioms JutilaReflectionKernelInterchange.finite_jutilaKernel_interchange
#print axioms JutilaReflectionKernelInterchange.countable_jutilaKernel_interchange_of_weighted_summable
