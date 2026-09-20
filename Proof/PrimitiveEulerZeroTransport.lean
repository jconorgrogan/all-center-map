import ZeroDensityInterface
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Zero-free change-of-level Euler corrections in `Re s > 0`

This is the first exact connector in Appendix A's reduction from ambient to
primitive characters.  It proves that every finite Euler factor introduced by
change of level is nonzero in the half-plane used by the density theorem and
therefore contributes zero analytic order.  No density or zero-count estimate
is assumed.
-/

namespace PrimitiveEulerZeroTransport

open ZeroDensityInterface
open Filter Topology

noncomputable section

variable {q : ℕ}

/-- The finite correction in Mathlib's change-of-level identity. -/
def eulerCorrection (chi : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∏ p ∈ q.primeFactors,
    (1 - chi.primitiveCharacter p * (p : ℂ) ^ (-s))

/-- One added Euler factor is zero-free in `Re s > 0`.  The proof only uses
`|chi(p)| <= 1` and `p >= 2`. -/
theorem eulerFactor_ne_zero
    (chi : DirichletCharacter ℂ q) {p : ℕ} (hp : p ∈ q.primeFactors)
    {s : ℂ} (hs : 0 < s.re) :
    1 - chi.primitiveCharacter p * (p : ℂ) ^ (-s) ≠ 0 := by
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpPos : 0 < (p : ℝ) := by exact_mod_cast hpPrime.pos
  have hpOne : 1 < (p : ℝ) := by exact_mod_cast hpPrime.one_lt
  have hpow : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    change ‖((p : ℝ) : ℂ) ^ (-s)‖ < 1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpPos]
    have hneg : (-s).re < 0 := by simpa using neg_lt_zero.mpr hs
    exact Real.rpow_lt_one_of_one_lt_of_neg hpOne hneg
  have hcharacter : ‖chi.primitiveCharacter p‖ ≤ 1 :=
    chi.primitiveCharacter.norm_le_one p
  have hproduct :
      ‖chi.primitiveCharacter p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    calc
      ‖chi.primitiveCharacter p‖ * ‖(p : ℂ) ^ (-s)‖ ≤
          1 * ‖(p : ℂ) ^ (-s)‖ :=
        mul_le_mul_of_nonneg_right hcharacter (norm_nonneg _)
      _ < 1 := by simpa using hpow
  intro hzero
  have hone : chi.primitiveCharacter p * (p : ℂ) ^ (-s) = 1 :=
    (sub_eq_zero.mp hzero).symm
  rw [hone, norm_one] at hproduct
  exact (lt_irrefl (1 : ℝ)) hproduct

/-- The complete finite correction is zero-free in `Re s > 0`. -/
theorem eulerCorrection_ne_zero
    (chi : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    eulerCorrection chi s ≠ 0 := by
  rw [eulerCorrection, Finset.prod_ne_zero_iff]
  intro p hp
  exact eulerFactor_ne_zero chi hp hs

/-- Each Euler correction is entire as a function of `s`. -/
theorem analyticAt_eulerCorrection
    (chi : DirichletCharacter ℂ q) (s : ℂ) :
    AnalyticAt ℂ (eulerCorrection chi) s := by
  unfold eulerCorrection
  apply Finset.analyticAt_fun_prod
  intro p hp
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpow : AnalyticAt ℂ (fun z : ℂ => (p : ℂ) ^ (-z)) s := by
    have hdiff : Differentiable ℂ (fun z : ℂ => (p : ℂ) ^ (-z)) := by
      intro z
      apply DifferentiableAt.const_cpow differentiableAt_id.neg
      left
      exact_mod_cast hpPrime.ne_zero
    exact hdiff.analyticAt s
  exact analyticAt_const.sub (analyticAt_const.mul hpow)

/-- Multiplication by the finite change-of-level correction preserves the
analytic order at every point in `Re s > 0`. -/
theorem meromorphicOrderAt_eulerCorrection_mul
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    {s : ℂ} (hs : 0 < s.re) :
    meromorphicOrderAt
        (fun z => eulerCorrection chi z *
          DirichletCharacter.LFunction chi.primitiveCharacter z) s =
      meromorphicOrderAt
        (DirichletCharacter.LFunction chi.primitiveCharacter) s := by
  exact meromorphicOrderAt_mul_of_ne_zero
    (analyticAt_eulerCorrection chi s) (eulerCorrection_ne_zero chi hs)

/-- Pointwise change of level, rewritten using the named correction. -/
theorem LFunction_eq_primitive_mul_eulerCorrection
    (chi : DirichletCharacter ℂ q) [NeZero q] [NeZero chi.conductor] {s : ℂ}
    (hs : chi.primitiveCharacter ≠ 1 ∨ s ≠ 1) :
    DirichletCharacter.LFunction chi s =
      DirichletCharacter.LFunction chi.primitiveCharacter s *
        eulerCorrection chi s := by
  simpa only [eulerCorrection] using
    ZeroDensityInterface.LFunction_eq_primitive_mul_eulerFactors chi hs

/-- At a point in `Re s > 0` where the change-of-level identity is valid,
ambient and primitive L-functions have exactly the same meromorphic order.
This is the multiplicity-aware local content of Appendix A, lines 29--45. -/
theorem meromorphicOrderAt_LFunction_eq_primitive
    (chi : DirichletCharacter ℂ q) [NeZero q] [NeZero chi.conductor]
    {s : ℂ} (hre : 0 < s.re)
    (hvalid : chi.primitiveCharacter ≠ 1 ∨ s ≠ 1) :
    meromorphicOrderAt (DirichletCharacter.LFunction chi) s =
      meromorphicOrderAt
        (DirichletCharacter.LFunction chi.primitiveCharacter) s := by
  have heq :
      DirichletCharacter.LFunction chi =ᶠ[𝓝[≠] s]
        (fun z => DirichletCharacter.LFunction chi.primitiveCharacter z *
          eulerCorrection chi z) := by
    rcases hvalid with hprimitive | hsone
    · filter_upwards [] with z
      exact LFunction_eq_primitive_mul_eulerCorrection chi (Or.inl hprimitive)
    · have hevent : ∀ᶠ z : ℂ in 𝓝 s, z ≠ 1 :=
        eventually_ne_nhds hsone
      filter_upwards [hevent.filter_mono nhdsWithin_le_nhds] with z hz
      exact LFunction_eq_primitive_mul_eulerCorrection chi (Or.inr hz)
  rw [meromorphicOrderAt_congr heq]
  have horder := meromorphicOrderAt_eulerCorrection_mul chi hre
  simpa only [mul_comm] using horder

end

end PrimitiveEulerZeroTransport
