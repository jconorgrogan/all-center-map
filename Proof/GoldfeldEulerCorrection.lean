import GoldfeldCrossLevelStructure
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# A logarithmic bound for change-of-level Euler factors
-/

namespace MAPGoldfeldSiegel

open Complex
open scoped BigOperators

noncomputable section

/-- Expanding over squarefree divisors identifies the elementary Euler
majorant with a sub-sum of the harmonic series. -/
theorem prod_primeFactors_one_add_inv_le_one_add_log
    {N : ℕ} [NeZero N] :
    (∏ p ∈ N.primeFactors, (1 + ((p : ℝ)⁻¹))) ≤
      1 + Real.log N := by
  have hN : N ≠ 0 := NeZero.ne N
  rw [show (∏ p ∈ N.primeFactors, (1 + ((p : ℝ)⁻¹))) =
      ∑ d ∈ N.divisors with Squarefree d, ((d : ℝ)⁻¹) by
    rw [Finset.prod_one_add, Nat.sum_divisors_filter_squarefree hN]
    congr 1
    · simp [Nat.factors_eq]
    funext s
    rw [Finset.prod_inv_distrib]
    congr 1
    norm_cast]
  have hsubset : {d ∈ N.divisors | Squarefree d} ⊆ Finset.Icc 1 N := by
    intro d hd
    rw [Finset.mem_filter] at hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd.1,
      Nat.le_of_dvd (NeZero.pos N) (Nat.dvd_of_mem_divisors hd.1)⟩
  have hsum : (∑ d ∈ N.divisors with Squarefree d, ((d : ℝ)⁻¹)) ≤
      ∑ d ∈ Finset.Icc 1 N, ((d : ℝ)⁻¹) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro i hi hnot
    positivity
  calc
    (∑ d ∈ N.divisors with Squarefree d, ((d : ℝ)⁻¹)) ≤
        ∑ d ∈ Finset.Icc 1 N, ((d : ℝ)⁻¹) := hsum
    _ = (harmonic N : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast]
    _ ≤ 1 + Real.log N := harmonic_le_one_add_log N

/-- Every finite Euler correction at `s=1` is at most one logarithm of its
ambient level. -/
theorem norm_changeLevel_eulerProduct_one_le
    {M N : ℕ} [NeZero M] [NeZero N]
    (chi : DirichletCharacter ℂ M) :
    ‖∏ p ∈ N.primeFactors,
        (1 - chi p * (p : ℂ) ^ (-(1 : ℂ)))‖ ≤
      1 + Real.log N := by
  have hprod :
      ‖∏ p ∈ N.primeFactors,
          (1 - chi p * (p : ℂ) ^ (-(1 : ℂ)))‖ ≤
        ∏ p ∈ N.primeFactors, (1 + ((p : ℝ)⁻¹)) := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀
    · intro p hp
      positivity
    intro p hp
    calc
      ‖1 - chi p * (p : ℂ) ^ (-(1 : ℂ))‖ ≤
          1 + ‖chi p‖ * ‖(p : ℂ) ^ (-(1 : ℂ))‖ := by
        simpa using norm_sub_le (1 : ℂ) (chi p * (p : ℂ) ^ (-(1 : ℂ)))
      _ ≤ 1 + 1 * ‖(p : ℂ) ^ (-(1 : ℂ))‖ := by
        gcongr
        exact chi.norm_le_one p
      _ = 1 + ((p : ℝ)⁻¹) := by
        rw [Complex.cpow_neg, Complex.cpow_one]
        simp [norm_inv]
  exact hprod.trans prod_primeFactors_one_add_inv_le_one_add_log

/-- The value at one of the right lift differs from the primitive value by at
most one ambient logarithm. -/
theorem norm_rightLift_LFunction_one_le
    (a b : PrimitiveRealCharacter) :
    ‖DirichletCharacter.LFunction (rightLift a b) 1‖ ≤
      (1 + Real.log (productLevel a b)) * ‖b.LFunction 1‖ := by
  have hchange := DirichletCharacter.LFunction_changeLevel
    (Nat.dvd_mul_left b.level a.level) b.chi (s := (1 : ℂ))
      (.inl b.nonprincipal)
  have heuler := norm_changeLevel_eulerProduct_one_le
    (N := productLevel a b) b.chi
  simp only [productLevel, Nat.cast_mul] at heuler
  unfold rightLift productLevel PrimitiveRealCharacter.LFunction
  rw [hchange, norm_mul]
  simp only [Nat.cast_mul]
  calc
    ‖DirichletCharacter.LFunction b.chi 1‖ *
        ‖∏ p ∈ (a.level * b.level).primeFactors,
          (1 - b.chi p * (p : ℂ) ^ (-(1 : ℂ)))‖ ≤
      ‖DirichletCharacter.LFunction b.chi 1‖ *
        (1 + Real.log (a.level * b.level)) :=
      mul_le_mul_of_nonneg_left heuler (norm_nonneg _)
    _ = (1 + Real.log (a.level * b.level)) *
        ‖DirichletCharacter.LFunction b.chi 1‖ := by ring

end
end MAPGoldfeldSiegel

#print axioms MAPGoldfeldSiegel.prod_primeFactors_one_add_inv_le_one_add_log
#print axioms MAPGoldfeldSiegel.norm_changeLevel_eulerProduct_one_le
#print axioms MAPGoldfeldSiegel.norm_rightLift_LFunction_one_le
