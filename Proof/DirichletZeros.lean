import Mathlib

/-!
# A finite multiplicity-aware Dirichlet L-zero count

This file constructs the zero-counting object used by the certification layer
from mathlib's meromorphic divisor. It proves finiteness and the relation to
`meromorphicOrderAt`; it proves no quantitative zero-density estimate.
-/

namespace DirichletZeros

open Set Function
open scoped Interval BigOperators

noncomputable section

variable {q : ℕ} [NeZero q]

/-- Remove the possible pole of the principal-character L-function using
mathlib's entire patch. -/
def regularizedLFunction (χ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ q
  else DirichletCharacter.LFunction χ

theorem differentiable_regularizedLFunction (χ : DirichletCharacter ℂ q) :
    Differentiable ℂ (regularizedLFunction χ) := by
  classical
  by_cases hχ : χ = 1
  · simp only [regularizedLFunction, if_pos hχ]
    exact DirichletCharacter.differentiable_LFunctionTrivChar₁ q
  · simp only [regularizedLFunction, if_neg hχ]
    exact DirichletCharacter.differentiable_LFunction hχ

theorem meromorphicOn_regularizedLFunction (χ : DirichletCharacter ℂ q)
    (U : Set ℂ) : MeromorphicOn (regularizedLFunction χ) U := by
  have h : AnalyticOnNhd ℂ (regularizedLFunction χ) U :=
    fun z _ => (differentiable_regularizedLFunction χ).analyticAt z
  exact h.meromorphicOn

/-- Closed zero-counting rectangle `σ ≤ Re ρ ≤ 1`, `|Im ρ| ≤ T`. -/
def zeroRectangle (σ T : ℝ) : Set ℂ :=
  Set.Icc σ 1 ×ℂ Set.Icc (-T) T

theorem isCompact_zeroRectangle (σ T : ℝ) : IsCompact (zeroRectangle σ T) := by
  exact isCompact_Icc.reProdIm isCompact_Icc

/-- The divisor of the regularized L-function on the closed rectangle. -/
def zeroDivisor (χ : DirichletCharacter ℂ q) (σ T : ℝ) :
    Function.locallyFinsuppWithin (zeroRectangle σ T) ℤ :=
  MeromorphicOn.divisor (regularizedLFunction χ) (zeroRectangle σ T)

theorem zeroDivisor_apply_of_mem (χ : DirichletCharacter ℂ q) (σ T : ℝ)
    {ρ : ℂ} (hρ : ρ ∈ zeroRectangle σ T) :
    zeroDivisor χ σ T ρ =
      (meromorphicOrderAt (regularizedLFunction χ) ρ).untop₀ := by
  exact MeromorphicOn.divisor_apply
    (meromorphicOn_regularizedLFunction χ (zeroRectangle σ T)) hρ

theorem zeroDivisor_nonneg_of_mem (χ : DirichletCharacter ℂ q) (σ T : ℝ)
    {ρ : ℂ} (hρ : ρ ∈ zeroRectangle σ T) :
    0 ≤ zeroDivisor χ σ T ρ := by
  rw [zeroDivisor_apply_of_mem χ σ T hρ, WithTop.untop₀_nonneg]
  exact (differentiable_regularizedLFunction χ).analyticAt ρ
    |>.meromorphicOrderAt_nonneg

theorem finite_zeroDivisor_support (χ : DirichletCharacter ℂ q) (σ T : ℝ) :
    (zeroDivisor χ σ T).support.Finite :=
  (zeroDivisor χ σ T).finiteSupport (isCompact_zeroRectangle σ T)

/-- The finite set of distinct zeros in the rectangle. -/
def zeroSupport (χ : DirichletCharacter ℂ q) (σ T : ℝ) : Finset ℂ :=
  (finite_zeroDivisor_support χ σ T).toFinset

theorem zeroSupport_mem_iff (χ : DirichletCharacter ℂ q) (σ T : ℝ) (ρ : ℂ) :
    ρ ∈ zeroSupport χ σ T ↔ zeroDivisor χ σ T ρ ≠ 0 := by
  simp [zeroSupport]

/-- Every point in the divisor support is a genuine zero of the regularized
Dirichlet L-function. In particular, the compact finite set is analytically
tethered rather than arbitrary finite data. -/
theorem regularizedLFunction_eq_zero_of_mem_zeroSupport
    (χ : DirichletCharacter ℂ q) (σ T : ℝ) {ρ : ℂ}
    (hρ : ρ ∈ zeroSupport χ σ T) : regularizedLFunction χ ρ = 0 := by
  have hdiv : zeroDivisor χ σ T ρ ≠ 0 :=
    (zeroSupport_mem_iff χ σ T ρ).mp hρ
  have hrect : ρ ∈ zeroRectangle σ T :=
    (zeroDivisor χ σ T).supportWithinDomain hdiv
  have hord : meromorphicOrderAt (regularizedLFunction χ) ρ ≠ 0 := by
    intro hord
    apply hdiv
    rw [zeroDivisor_apply_of_mem χ σ T hrect, hord]
    rfl
  by_contra hf
  apply hord
  exact ((differentiable_regularizedLFunction χ).analyticAt ρ).meromorphicNFAt
    |>.meromorphicOrderAt_eq_zero_iff.mpr hf

/-- Analytic multiplicity of a supported zero. -/
def zeroMultiplicity (χ : DirichletCharacter ℂ q) (σ T : ℝ) (ρ : ℂ) : ℕ :=
  Int.toNat (zeroDivisor χ σ T ρ)

/-- Actual zero count in the rectangle, with analytic multiplicity. -/
def dirichletZeroCount (χ : DirichletCharacter ℂ q) (σ T : ℝ) : ℕ :=
  ∑ ρ ∈ zeroSupport χ σ T, zeroMultiplicity χ σ T ρ

/-- The zero count used for an ambient character: count zeros of its primitive
inducer at its conductor. -/
def primitiveDirichletZeroCount (χ : DirichletCharacter ℂ q) (σ T : ℝ) : ℕ := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  exact dirichletZeroCount χ.primitiveCharacter σ T

end

end DirichletZeros
