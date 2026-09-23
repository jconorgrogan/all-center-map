import AppendixA5ClosedLocalZeroCount
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import APZeroDensityCertificate
import PrimitiveExplicitFormulaSpine

/-!
# Functional-equation transport for the strict lower half of the critical strip

This file isolates the multiplicity-preserving map `ρ ↦ 1 - ρ` for a
primitive nonprincipal Dirichlet character.  It uses Mathlib's completed
functional equation and proves all nonvanishing factors locally, rather than
postulating symmetry of the zero divisor.
-/

namespace MAPFunctionalZeroTransport

open Complex Filter Topology Function
open DirichletCharacter DirichletZeros
open scoped ZMod

noncomputable section

variable {q : ℕ} [NeZero q]

/-- Inversion preserves primitivity. -/
theorem isPrimitive_inv {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) : χ⁻¹.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def,
    DirichletCharacter.conductor_inv]
  exact hprim

/-- A nonprincipal character has nonprincipal inverse. -/
theorem inverse_ne_one {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) : χ⁻¹ ≠ 1 :=
  _root_.inv_ne_one.mpr hχ

/-- A nonprincipal character cannot have level one. -/
theorem level_ne_one {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) : q ≠ 1 := by
  intro hq
  exact hχ (DirichletCharacter.level_one' χ hq)

/-- The Gauss sum of a primitive nonprincipal Dirichlet character is nonzero.
This proof works for composite levels: Fourier inversion, not a finite-field
Gauss-sum formula, is the load-bearing input. -/
theorem primitive_gaussSum_ne_zero {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    gaussSum χ ZMod.stdAddChar ≠ 0 := by
  intro hgauss
  have hdft : (ZMod.dft : (ZMod q → ℂ) ≃ₗ[ℂ] (ZMod q → ℂ)) χ = 0 := by
    funext k
    rw [hprim.fourierTransform_eq_inv_mul_gaussSum k, hgauss]
    simp
  have hzero : (χ : ZMod q → ℂ) = 0 := by
    apply (ZMod.dft : (ZMod q → ℂ) ≃ₗ[ℂ] (ZMod q → ℂ)).injective
    simpa using hdft
  have hone := congrFun hzero (1 : ZMod q)
  simpa using hone

/-- The root number occurring in Mathlib's functional equation is nonzero for
primitive nonprincipal characters. -/
theorem primitive_rootNumber_ne_zero {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    χ.rootNumber ≠ 0 := by
  unfold DirichletCharacter.rootNumber
  apply div_ne_zero
  · apply div_ne_zero
    · exact primitive_gaussSum_ne_zero hprim hχ
    · split_ifs <;> simp
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))

/-- The reciprocal gamma factor is analytic everywhere. -/
theorem analyticAt_gammaFactor_inv (χ : DirichletCharacter ℂ q) (s : ℂ) :
    AnalyticAt ℂ (fun z => (χ.gammaFactor z)⁻¹) s := by
  rcases χ.even_or_odd with heven | hodd
  · simp only [heven.gammaFactor_def]
    exact Complex.differentiable_Gammaℝ_inv.analyticAt s
  · simp only [hodd.gammaFactor_def]
    have hdiff : Differentiable ℂ (fun z : ℂ => (Complex.Gammaℝ (z + 1))⁻¹) :=
      Complex.differentiable_Gammaℝ_inv.comp (by fun_prop)
    exact hdiff.analyticAt s

/-- In positive real part, the reciprocal gamma factor does not vanish. -/
theorem gammaFactor_inv_ne_zero_of_re_pos (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) : (χ.gammaFactor s)⁻¹ ≠ 0 := by
  apply inv_ne_zero
  rcases χ.even_or_odd with heven | hodd
  · rw [heven.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · rw [hodd.gammaFactor_def]
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.one_re]
    linarith

/-- At positive real part, completing a nonprincipal L-function does not
change its analytic vanishing order. -/
theorem analyticOrderAt_LFunction_eq_completedLFunction
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) :
    analyticOrderAt (DirichletCharacter.LFunction χ) s =
      analyticOrderAt (DirichletCharacter.completedLFunction χ) s := by
  have hq : q ≠ 1 := level_ne_one hχ
  have heq :
      DirichletCharacter.LFunction χ =
        fun z => DirichletCharacter.completedLFunction χ z *
          (χ.gammaFactor z)⁻¹ := by
    funext z
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z
      (Or.inr hq)]
    rfl
  rw [analyticOrderAt_congr (Filter.Eventually.of_forall
    (fun z => congrFun heq z))]
  have hmul := analyticOrderAt_mul
    ((DirichletCharacter.differentiable_completedLFunction hχ).analyticAt s)
    (analyticAt_gammaFactor_inv χ s)
  rw [show analyticOrderAt
      (fun z => DirichletCharacter.completedLFunction χ z *
        (χ.gammaFactor z)⁻¹) s =
      analyticOrderAt (DirichletCharacter.completedLFunction χ) s +
        analyticOrderAt (fun z => (χ.gammaFactor z)⁻¹) s by
    simpa only [Pi.mul_apply] using! hmul]
  have hzero : analyticOrderAt (fun z => (χ.gammaFactor z)⁻¹) s = 0 :=
    (analyticAt_gammaFactor_inv χ s).analyticOrderAt_eq_zero.mpr
      (gammaFactor_inv_ne_zero_of_re_pos χ hs)
  rw [hzero, add_zero]

/-- For a nonprincipal character, the project's regularized function is the
ordinary entire L-function, so completion preserves analytic order in the
positive half-plane. -/
theorem analyticOrderAt_regularized_eq_completed
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) :
    analyticOrderAt (regularizedLFunction χ) s =
      analyticOrderAt (DirichletCharacter.completedLFunction χ) s := by
  rw [show regularizedLFunction χ = DirichletCharacter.LFunction χ by
    simp [regularizedLFunction, hχ]]
  exact analyticOrderAt_LFunction_eq_completedLFunction hχ hs

/-- The affine reflection `z ↦ 1-z` preserves analytic order. -/
theorem analyticOrderAt_one_sub_comp (f : ℂ → ℂ) (ρ : ℂ) :
    analyticOrderAt (fun z => f (1 - z)) (1 - ρ) =
      analyticOrderAt f ρ := by
  let g : ℂ → ℂ := fun z => 1 - z
  have hg : AnalyticAt ℂ g (1 - ρ) := by
    dsimp [g]
    fun_prop
  have hderiv : deriv g (1 - ρ) = -1 := by
    dsimp [g]
    rw [deriv_const_sub]
    have hid : deriv (fun z : ℂ => z) (1 - ρ) = 1 := by
      simpa only [id_eq] using! (deriv_id (1 - ρ : ℂ))
    rw [hid]
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := f) hg (by rw [hderiv]; norm_num)
  simpa [g, Function.comp_def] using hcomp

/-- Exact analytic-order transport for completed L-functions under the
primitive functional equation. -/
theorem analyticOrderAt_completed_transport
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (ρ : ℂ) :
    analyticOrderAt (DirichletCharacter.completedLFunction χ) ρ =
      analyticOrderAt (DirichletCharacter.completedLFunction χ⁻¹) (1 - ρ) := by
  let z₀ : ℂ := 1 - ρ
  let c : ℂ → ℂ := fun z =>
    (q : ℂ) ^ (z - 1 / 2) * χ.rootNumber
  have hcAnalytic : AnalyticAt ℂ c z₀ := by
    have hpow : Differentiable ℂ
        (fun z : ℂ => (q : ℂ) ^ (z - 1 / 2)) := by
      intro z
      exact (differentiableAt_id.sub_const (1 / 2 : ℂ)).const_cpow
        (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))
    dsimp [c]
    exact (hpow.mul (differentiable_const χ.rootNumber)).analyticAt z₀
  have hcNe : c z₀ ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero
      (Complex.cpow_ne_zero_iff.mpr
        (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q))))
      (primitive_rootNumber_ne_zero hprim hχ)
  have hfe :
      (fun z => DirichletCharacter.completedLFunction χ (1 - z)) =
        fun z => c z * DirichletCharacter.completedLFunction χ⁻¹ z := by
    funext z
    simpa [c] using hprim.completedLFunction_one_sub z
  calc
    analyticOrderAt (DirichletCharacter.completedLFunction χ) ρ =
        analyticOrderAt
          (fun z => DirichletCharacter.completedLFunction χ (1 - z)) z₀ := by
      symm
      simpa [z₀] using
        analyticOrderAt_one_sub_comp
          (DirichletCharacter.completedLFunction χ) ρ
    _ = analyticOrderAt
          (fun z => c z * DirichletCharacter.completedLFunction χ⁻¹ z) z₀ := by
      apply analyticOrderAt_congr
      exact Filter.Eventually.of_forall (fun z => congrFun hfe z)
    _ = analyticOrderAt c z₀ +
          analyticOrderAt (DirichletCharacter.completedLFunction χ⁻¹) z₀ := by
      exact analyticOrderAt_mul hcAnalytic
        ((DirichletCharacter.differentiable_completedLFunction
          (inverse_ne_one hχ)).analyticAt z₀)
    _ = analyticOrderAt
          (DirichletCharacter.completedLFunction χ⁻¹) z₀ := by
      rw [hcAnalytic.analyticOrderAt_eq_zero.mpr hcNe, zero_add]
    _ = analyticOrderAt
          (DirichletCharacter.completedLFunction χ⁻¹) (1 - ρ) := rfl

/-- Strict-lower-half transport for the project's regularized L-functions,
including exact analytic multiplicity. -/
theorem analyticOrderAt_regularized_transport
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {ρ : ℂ} (hρpos : 0 < ρ.re) (hρhalf : ρ.re < 1 / 2) :
    analyticOrderAt (regularizedLFunction χ) ρ =
      analyticOrderAt (regularizedLFunction χ⁻¹) (1 - ρ) := by
  have hreflect : 0 < (1 - ρ).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  calc
    analyticOrderAt (regularizedLFunction χ) ρ =
        analyticOrderAt (DirichletCharacter.completedLFunction χ) ρ :=
      analyticOrderAt_regularized_eq_completed hχ hρpos
    _ = analyticOrderAt
          (DirichletCharacter.completedLFunction χ⁻¹) (1 - ρ) :=
      analyticOrderAt_completed_transport hprim hχ ρ
    _ = analyticOrderAt (regularizedLFunction χ⁻¹) (1 - ρ) :=
      (analyticOrderAt_regularized_eq_completed (inverse_ne_one hχ) hreflect).symm

/-- A strict-lower supported zero reflects into the upper-half zero support
of the inverse character, at the same symmetric height. -/
theorem one_sub_mem_upper_zeroSupport
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {σ T : ℝ} {ρ : ℂ} (hρ : ρ ∈ zeroSupport χ σ T)
    (hρpos : 0 < ρ.re) (hρhalf : ρ.re < 1 / 2) :
    1 - ρ ∈ zeroSupport χ⁻¹ (1 / 2) T := by
  have hrectρ : ρ ∈ zeroRectangle σ T :=
    (zeroDivisor χ σ T).supportWithinDomain
      ((zeroSupport_mem_iff χ σ T ρ).mp hρ)
  have hrectReflect : 1 - ρ ∈ zeroRectangle (1 / 2) T := by
    rw [zeroRectangle, Complex.mem_reProdIm] at hrectρ ⊢
    constructor
    · constructor
      · simp only [Complex.sub_re, Complex.one_re, Set.mem_Icc]
        linarith
      · simp only [Complex.sub_re, Complex.one_re, Set.mem_Icc]
        linarith
    · have him : (1 - ρ).im = -ρ.im := by
        simp only [Complex.sub_im, Complex.one_im, zero_sub]
      rw [him]
      exact ⟨by linarith [hrectρ.2.2], by linarith [hrectρ.2.1]⟩
  apply (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
    χ⁻¹ (1 / 2) T hrectReflect).mpr
  have hz : regularizedLFunction χ ρ = 0 :=
    regularizedLFunction_eq_zero_of_mem_zeroSupport χ σ T hρ
  have hanχ := (differentiable_regularizedLFunction χ).analyticAt ρ
  have hanInv := (differentiable_regularizedLFunction χ⁻¹).analyticAt (1 - ρ)
  apply hanInv.analyticOrderAt_ne_zero.mp
  rw [← analyticOrderAt_regularized_transport hprim hχ hρpos hρhalf]
  exact hanχ.analyticOrderAt_ne_zero.mpr hz

/-- The reflected support point has exactly the same divisor multiplicity.
Thus the transport is strong enough for multiplicity-weighted local counts,
not merely for sets of distinct zeros. -/
theorem zeroMultiplicity_one_sub
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {σ T : ℝ} {ρ : ℂ} (hρ : ρ ∈ zeroSupport χ σ T)
    (hρpos : 0 < ρ.re) (hρhalf : ρ.re < 1 / 2) :
    zeroMultiplicity χ σ T ρ =
      zeroMultiplicity χ⁻¹ (1 / 2) T (1 - ρ) := by
  have hreflect := one_sub_mem_upper_zeroSupport hprim hχ hρ hρpos hρhalf
  have htransport := analyticOrderAt_regularized_transport
    hprim hχ hρpos hρhalf
  rw [PrimitiveExplicitFormulaSpine.analyticOrderAt_eq_zeroMultiplicity
      χ σ T hρ,
    PrimitiveExplicitFormulaSpine.analyticOrderAt_eq_zeroMultiplicity
      χ⁻¹ (1 / 2) T hreflect] at htransport
  exact ENat.coe_inj.mp htransport

/-- The zero-set consequence of the multiplicity transport. -/
theorem regularizedLFunction_one_sub_eq_zero
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {ρ : ℂ} (hρpos : 0 < ρ.re) (hρhalf : ρ.re < 1 / 2)
    (hzero : regularizedLFunction χ ρ = 0) :
    regularizedLFunction χ⁻¹ (1 - ρ) = 0 := by
  have hanχ := (differentiable_regularizedLFunction χ).analyticAt ρ
  have hanInv := (differentiable_regularizedLFunction χ⁻¹).analyticAt (1 - ρ)
  have horderχ : analyticOrderAt (regularizedLFunction χ) ρ ≠ 0 :=
    hanχ.analyticOrderAt_ne_zero.mpr hzero
  have htransport := analyticOrderAt_regularized_transport hprim hχ hρpos hρhalf
  apply hanInv.analyticOrderAt_ne_zero.mp
  rw [← htransport]
  exact horderχ

end

end MAPFunctionalZeroTransport

#print axioms MAPFunctionalZeroTransport.analyticOrderAt_regularized_transport
#print axioms MAPFunctionalZeroTransport.regularizedLFunction_one_sub_eq_zero
#print axioms MAPFunctionalZeroTransport.one_sub_mem_upper_zeroSupport
#print axioms MAPFunctionalZeroTransport.zeroMultiplicity_one_sub
