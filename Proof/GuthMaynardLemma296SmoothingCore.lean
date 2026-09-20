import GuthMaynardSourceWZeroProperties
import GuthMaynardLemma295ReflectedPairConstruction

/-!
# Finite smoothing core for the first display on p. 267

This module identifies the literal smooth sum `h_g^+` with a finite Gram
polynomial, including the global `N^{-ig}` phase, and proves the hard dyadic
coefficient is majorized by the smooth cutoff on its core.  These are the
load-bearing finite steps in `Lemma296SmoothedSecondMomentReduction`.
-/

namespace GuthMaynardLemma296SmoothingCore

open scoped BigOperators ComplexConjugate
open GuthMaynardHeathBrownMajorant
open GuthMaynardJutilaTransference
open GuthMaynardJutilaLemma29NineKTwo
open GuthMaynardJutilaReflection2941
open GuthMaynardSourceWZeroProperties
open GuthMaynardLengthComparison

noncomputable section

def lemma296BigSupport (N : ℝ) : Finset ℕ :=
  natRealIoc (N / 2) (5 * N / 2)

def lemma296SmoothCoefficient (N : ℝ) (n : ℕ) : ℝ :=
  sourceWZero ((n : ℝ) / N) (1 / 2) 1 2 (5 / 2)

def lemma296GlobalPhase (N g : ℝ) : ℂ :=
  Complex.exp (-Complex.I * ((g * Real.log N : ℝ) : ℂ))

theorem norm_lemma296GlobalPhase (N g : ℝ) :
    ‖lemma296GlobalPhase N g‖ = 1 := by
  unfold lemma296GlobalPhase
  rw [Complex.norm_exp]
  simp

/-- Exact phase identity for the smooth sum. -/
theorem sourceHPlusSum_eq_globalPhase_mul_gram
    {N : ℝ} (hN : 0 < N) (g₁ g₂ : ℝ) :
    sourceHPlusSum N (g₁ - g₂) =
      lemma296GlobalPhase N (g₁ - g₂) *
        gramPolynomial (lemma296BigSupport N)
          (fun n => (lemma296SmoothCoefficient N n : ℂ))
          negativeDirichletPhase g₂ g₁ := by
  unfold sourceHPlusSum lemma296BigSupport gramPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnmem := (mem_natRealIoc_iff (by positivity : 0 ≤ 5 * N / 2)).mp hn
  have hnposR : 0 < (n : ℝ) := by nlinarith
  have hnzero : (n : ℝ) ≠ 0 := hnposR.ne'
  have hlog : Real.log ((n : ℝ) / N) =
      Real.log n - Real.log N := Real.log_div hnzero hN.ne'
  unfold sourceHPlus lemma296SmoothCoefficient lemma296GlobalPhase
    negativeDirichletPhase
  have hphase := dirichletPhase_difference n (-g₂) (-g₁)
  let c : ℂ :=
    (sourceWZero ((n : ℝ) / N) (1 / 2) 1 2 (5 / 2) : ℂ)
  change c * Complex.exp
      (Complex.I * (((g₁ - g₂ : ℝ) : ℂ) *
        ((Real.log ((n : ℝ) / N) : ℝ) : ℂ))) =
    Complex.exp (-Complex.I * (((g₁ - g₂) * Real.log N : ℝ) : ℂ)) *
      (c * dirichletPhase n (-g₂) * star (dirichletPhase n (-g₁)))
  rw [show Complex.exp
      (-Complex.I * (((g₁ - g₂) * Real.log N : ℝ) : ℂ)) *
        (c * dirichletPhase n (-g₂) * star (dirichletPhase n (-g₁))) =
      c * (Complex.exp
        (-Complex.I * (((g₁ - g₂) * Real.log N : ℝ) : ℂ)) *
        (dirichletPhase n (-g₂) * star (dirichletPhase n (-g₁)))) by ring]
  rw [hphase, ← Complex.exp_add, hlog]
  congr 2
  push_cast
  ring

/-- Consequently the square norm of every smooth pair is exactly the square
norm of the corresponding Gram polynomial. -/
theorem norm_sourceHPlusSum_sq_eq_gram
    {N : ℝ} (hN : 0 < N) (g₁ g₂ : ℝ) :
    ‖sourceHPlusSum N (g₁ - g₂)‖ ^ 2 =
      ‖gramPolynomial (lemma296BigSupport N)
          (fun n => (lemma296SmoothCoefficient N n : ℂ))
          negativeDirichletPhase g₂ g₁‖ ^ 2 := by
  rw [sourceHPlusSum_eq_globalPhase_mul_gram hN]
  rw [norm_mul, norm_lemma296GlobalPhase, one_mul]

/-- The hard dyadic support is contained in the literal smooth support. -/
theorem realDyadicIoc_subset_lemma296BigSupport
    {N : ℝ} (hN : 0 ≤ N) :
    realDyadicIoc N ⊆ lemma296BigSupport N := by
  intro n hn
  rw [mem_realDyadicIoc_iff] at hn
  unfold lemma296BigSupport
  rw [mem_natRealIoc_iff (by positivity : 0 ≤ 5 * N / 2)]
  constructor <;> nlinarith

/-- On the hard core `(N,2N]`, the smooth coefficient is exactly one. -/
theorem lemma296SmoothCoefficient_eq_one_of_mem
    {N : ℝ} (hN : 0 < N) {n : ℕ} (hn : n ∈ realDyadicIoc N) :
    lemma296SmoothCoefficient N n = 1 := by
  have hn' := mem_realDyadicIoc_iff.mp hn
  unfold lemma296SmoothCoefficient
  apply sourceWZero_eq_one_on_core
  · exact (le_div_iff₀ hN).2 (by simpa using hn'.1.le)
  · exact (div_le_iff₀ hN).2 hn'.2

/-- The inverse-square-root hard coefficient is bounded by the smooth
coefficient times `N^{-1/2}`. -/
theorem inverseSqrtWeight_le_scale_mul_smooth
    {N : ℝ} (hN : 0 < N) {n : ℕ} (hn : n ∈ realDyadicIoc N) :
    inverseSqrtWeight n ≤
      Real.rpow N (-(1 / 2 : ℝ)) * lemma296SmoothCoefficient N n := by
  rw [lemma296SmoothCoefficient_eq_one_of_mem hN hn, mul_one]
  rw [GuthMaynardJutilaLemma29NineKTwo.inverseSqrtWeight_eq_rpow_neg_half]
  have hnLower := (mem_realDyadicIoc_iff.mp hn).1.le
  exact Real.rpow_le_rpow_of_nonpos hN hnLower (by norm_num)

end

end GuthMaynardLemma296SmoothingCore

#print axioms GuthMaynardLemma296SmoothingCore.sourceHPlusSum_eq_globalPhase_mul_gram
#print axioms GuthMaynardLemma296SmoothingCore.inverseSqrtWeight_le_scale_mul_smooth
