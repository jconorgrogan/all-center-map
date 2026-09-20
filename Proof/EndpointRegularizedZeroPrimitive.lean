import APConditionalShortIntervalConnector

/-!
# The `Re rho = 0` endpoint in the truncated explicit formula

`APFoundation.regularizedZeroTerm` totalizes division by `rho`, so at
`rho = 0` it is zero rather than the required logarithmic antiderivative.
This file supplies the source-faithful continuous extension.  It lets the
explicit formula use the full closed zero rectangle from equation (2.8), with
no silent deletion of the even-character zero at the origin.
-/

namespace MAPEndpointRegularizedZeroPrimitive

open Complex MeasureTheory Set
open scoped BigOperators
open APFoundation APExplicitFormulaMajorantAdapter

noncomputable section

/-- Continuous-in-`rho` endpoint convention for `(t^rho - 1)/rho`. -/
def endpointRegularizedZeroTerm (t : ℝ) (rho : ℂ) : ℂ :=
  if rho = 0 then Real.log t else regularizedZeroTerm t rho

lemma zero_not_mem_uIcc_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ∉ Set.uIcc a b := by
  rw [Set.mem_uIcc]
  push_neg
  constructor <;> intro h
  · linarith
  · linarith

lemma cpow_neg_one_ofReal (t : ℝ) :
    (t : ℂ) ^ (-1 : ℂ) = ((t⁻¹ : ℝ) : ℂ) := by
  rw [Complex.cpow_neg_one]
  norm_num

/-- Exact antiderivative identity on a positive interval, including
`rho = 0`. -/
theorem intervalIntegral_cpow_sub_one_eq_endpointTerm_sub
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {rho : ℂ} (hrho : 0 ≤ rho.re) :
    (∫ t : ℝ in a..b, (t : ℂ) ^ (rho - 1)) =
      endpointRegularizedZeroTerm b rho -
        endpointRegularizedZeroTerm a rho := by
  by_cases hzero : rho = 0
  · subst rho
    simp only [zero_sub, endpointRegularizedZeroTerm, if_pos]
    have hfun : (fun t : ℝ => (t : ℂ) ^ (-1 : ℂ)) =
        fun t : ℝ => ((t⁻¹ : ℝ) : ℂ) := by
      funext t
      exact cpow_neg_one_ofReal t
    rw [hfun, intervalIntegral.integral_ofReal,
      integral_inv_of_pos ha hb]
    push_cast
    rw [Real.log_div hb.ne' ha.ne']
    norm_num
  · have hexp : rho - 1 ≠ (-1 : ℂ) := by
      intro h
      apply hzero
      calc
        rho = (rho - 1) + 1 := by ring
        _ = (-1 : ℂ) + 1 := by rw [h]
        _ = 0 := by ring
    rw [integral_cpow (Or.inr ⟨hexp,
      zero_not_mem_uIcc_of_pos ha hb⟩)]
    simp only [endpointRegularizedZeroTerm, if_neg hzero,
      regularizedZeroTerm]
    have hsum : rho - 1 + 1 = rho := by ring
    rw [hsum]
    field_simp
    ring_nf
    rfl

/-- Full finite-sum endpoint primitive. -/
def endpointFiniteZeroPrimitive
    (zeros : Finset ℂ) (multiplicity : ℂ → ℕ) (t : ℝ) : ℂ :=
  ∑ rho ∈ zeros,
    (multiplicity rho : ℂ) * endpointRegularizedZeroTerm t rho

/-- Full closed-rectangle finite-sum antiderivative, requiring only
`0 ≤ Re rho`. -/
theorem intervalIntegral_finiteZeroField_endpoint
    (zeros : Finset ℂ) (multiplicity : ℂ → ℕ)
    (hzeros : ∀ rho ∈ zeros, 0 ≤ rho.re)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t : ℝ in a..b, finiteZeroField zeros multiplicity t) =
      endpointFiniteZeroPrimitive zeros multiplicity b -
        endpointFiniteZeroPrimitive zeros multiplicity a := by
  classical
  unfold finiteZeroField endpointFiniteZeroPrimitive
  rw [intervalIntegral.integral_finset_sum]
  · rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro rho hrho
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral_cpow_sub_one_eq_endpointTerm_sub ha hb
        (hzeros rho hrho)]
    ring
  · intro rho hrho
    have hlocal : IntervalIntegrable
        (fun t : ℝ => (t : ℂ) ^ (rho - 1)) volume a b := by
      by_cases hpos : 0 < rho.re
      · exact intervalIntegral.intervalIntegrable_cpow' (by
          simp only [Complex.sub_re, Complex.one_re]
          linarith)
      · have hre : rho.re = 0 := le_antisymm (not_lt.mp hpos) (hzeros rho hrho)
        by_cases hz : rho = 0
        · subst rho
          simp only [zero_sub, cpow_neg_one_ofReal]
          have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume a b :=
            intervalIntegral.intervalIntegrable_inv
              (fun t ht => by
                have : 0 < t := by
                  exact (lt_min ha hb).trans_le ht.1
                exact this.ne') continuousOn_id
          constructor
          · exact Complex.ofRealCLM.integrable_comp hinv.1
          · exact Complex.ofRealCLM.integrable_comp hinv.2
        · exact intervalIntegral.intervalIntegrable_cpow
            (Or.inr (zero_not_mem_uIcc_of_pos ha hb))
    exact hlocal.const_mul _

variable {q : ℕ} [NeZero q]

/-- Endpoint-corrected multiplicity-weighted primitive on the literal closed
zero rectangle. -/
def endpointMultiplicityWeightedZeroTerm
    (chi : DirichletCharacter ℂ q) (sigma T t : ℝ) : ℂ :=
  endpointFiniteZeroPrimitive (DirichletZeros.zeroSupport chi sigma T)
    (DirichletZeros.zeroMultiplicity chi sigma T) t

/-- Every supported zero in the closed `sigma = 0` rectangle has
nonnegative real part. -/
theorem actualZero_re_nonneg (chi : DirichletCharacter ℂ q)
    {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ DirichletZeros.zeroSupport chi 0 T) :
    0 ≤ rho.re := by
  exact (PrimitiveExplicitFormulaSpine.mem_zeroRectangle_of_mem_zeroSupport
    chi 0 T hrho).1.1

/-- Exact endpoint-window identity from a source-facing real-endpoint
explicit formula.  Unlike the older adapter, this accepts the full closed
rectangle and therefore needs no false `0 < Re rho` hypothesis. -/
theorem ambientCharacterWindowError_eq_integral_zeroField_endpoint_add_remainder
    (chi : DirichletCharacter ℂ q)
    (zeros : Finset ℂ) (multiplicity : ℂ → ℕ)
    (hzeros : ∀ rho ∈ zeros, 0 ≤ rho.re)
    (remainder : ℝ → ℂ) {x Y : ℝ} (hx : 0 < x) (hY : 0 ≤ Y)
    (hformula : ∀ t ∈ ({x, x + Y} : Set ℝ),
      ambientTwistedPsi chi t =
        principalCoefficient chi * t -
          endpointFiniteZeroPrimitive zeros multiplicity t + remainder t) :
    APMaximalExplicitFormulaBridge.ambientCharacterWindowError chi
        (Finset.Ioc ⌊x⌋₊ ⌊x + Y⌋₊) Y =
      -(∫ t : ℝ in x..x + Y, finiteZeroField zeros multiplicity t) +
        (remainder (x + Y) - remainder x) := by
  rw [APMaximalExplicitFormulaBridge.ambientCharacterWindowError,
    twistedMangoldtWindow_eq_ambientTwistedPsi_sub chi hY]
  rw [hformula (x + Y) (by simp), hformula x (by simp)]
  rw [intervalIntegral_finiteZeroField_endpoint zeros multiplicity hzeros
    hx (by linarith)]
  unfold principalCoefficient
  by_cases hchi : chi = 1
  · simp [hchi]
    ring
  · simp [hchi]
    ring

/-- Norm majorant consumed by the AP Cauchy/maximal bridge, with the
`rho = 0` convention now exact. -/
theorem norm_ambientCharacterWindowError_div_le_endpoint_fieldAverage_add_remainder
    (chi : DirichletCharacter ℂ q)
    (zeros : Finset ℂ) (multiplicity : ℂ → ℕ)
    (hzeros : ∀ rho ∈ zeros, 0 ≤ rho.re)
    (remainder : ℝ → ℂ) {x Y : ℝ} (hx : 0 < x) (hY : 0 < Y)
    (hformula : ∀ t ∈ ({x, x + Y} : Set ℝ),
      ambientTwistedPsi chi t =
        principalCoefficient chi * t -
          endpointFiniteZeroPrimitive zeros multiplicity t + remainder t) :
    ‖APMaximalExplicitFormulaBridge.ambientCharacterWindowError chi
        (Finset.Ioc ⌊x⌋₊ ⌊x + Y⌋₊) Y / Y‖ ≤
      Y⁻¹ * (∫ t : ℝ in x..x + Y,
        ‖finiteZeroField zeros multiplicity t‖) +
      ‖(remainder (x + Y) - remainder x) / Y‖ := by
  rw [ambientCharacterWindowError_eq_integral_zeroField_endpoint_add_remainder
    chi zeros multiplicity hzeros remainder hx hY.le hformula]
  rw [add_div]
  refine (norm_add_le _ _).trans ?_
  have hnormInt :
      ‖∫ t : ℝ in x..x + Y, finiteZeroField zeros multiplicity t‖ ≤
        ∫ t : ℝ in x..x + Y, ‖finiteZeroField zeros multiplicity t‖ :=
    intervalIntegral.norm_integral_le_integral_norm (by linarith)
  have hYnorm : ‖(Y : ℂ)‖ = Y := by simp [abs_of_pos hY]
  calc
    ‖-(∫ t : ℝ in x..x + Y, finiteZeroField zeros multiplicity t) / Y‖ +
        ‖(remainder (x + Y) - remainder x) / Y‖ =
      Y⁻¹ * ‖∫ t : ℝ in x..x + Y,
        finiteZeroField zeros multiplicity t‖ +
        ‖(remainder (x + Y) - remainder x) / Y‖ := by
          rw [norm_div, norm_neg, hYnorm]
          ring
    _ ≤ Y⁻¹ * (∫ t : ℝ in x..x + Y,
          ‖finiteZeroField zeros multiplicity t‖) +
        ‖(remainder (x + Y) - remainder x) / Y‖ := by
          gcongr

/-- Literal full-zero-support specialization used by the remainder transfer.
The only source premise left is now the endpoint explicit formula itself. -/
theorem norm_ambientCharacterWindowError_div_le_fullZero_endpoint
    (chi : DirichletCharacter ℂ q) {T : ℝ}
    (remainder : ℝ → ℂ) {x Y : ℝ} (hx : 0 < x) (hY : 0 < Y)
    (hformula : ∀ t ∈ ({x, x + Y} : Set ℝ),
      ambientTwistedPsi chi t =
        principalCoefficient chi * t -
          endpointMultiplicityWeightedZeroTerm chi 0 T t + remainder t) :
    ‖APMaximalExplicitFormulaBridge.ambientCharacterWindowError chi
        (Finset.Ioc ⌊x⌋₊ ⌊x + Y⌋₊) Y / Y‖ ≤
      Y⁻¹ * (∫ t : ℝ in x..x + Y,
        ‖actualZeroField chi 0 T t‖) +
      ‖(remainder (x + Y) - remainder x) / Y‖ := by
  simpa only [actualZeroField, endpointMultiplicityWeightedZeroTerm] using
    norm_ambientCharacterWindowError_div_le_endpoint_fieldAverage_add_remainder
      chi (DirichletZeros.zeroSupport chi 0 T)
      (DirichletZeros.zeroMultiplicity chi 0 T)
      (fun rho hrho => actualZero_re_nonneg chi hrho)
      remainder hx hY hformula

end
end MAPEndpointRegularizedZeroPrimitive

#print axioms MAPEndpointRegularizedZeroPrimitive.intervalIntegral_cpow_sub_one_eq_endpointTerm_sub
#print axioms MAPEndpointRegularizedZeroPrimitive.intervalIntegral_finiteZeroField_endpoint
#print axioms MAPEndpointRegularizedZeroPrimitive.ambientCharacterWindowError_eq_integral_zeroField_endpoint_add_remainder
#print axioms MAPEndpointRegularizedZeroPrimitive.norm_ambientCharacterWindowError_div_le_fullZero_endpoint
