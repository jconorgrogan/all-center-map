import GoldfeldFourLogAbsorption

/-!
# Unconditional exceptional-zero weight endpoints
-/

namespace MAPGoldfeldSiegel

open Filter

noncomputable section

/-- Unconditional pointwise exceptional-zero decay with an arbitrary fixed
polylogarithmic prefactor. -/
theorem eventually_prefactor_mul_exceptionalWeight_le
    {K A P : ℝ} (hK : 0 < K) (hA : 0 < A) (hP : 0 ≤ P) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q) (beta : ℝ),
        (q : ℝ) ≤ Real.rpow (Real.log X) K →
        chi ≠ 1 → chi ^ 2 = 1 →
        DirichletCharacter.LFunction chi beta = 0 →
          Real.rpow (Real.log X) P *
              Real.rpow X (2 * (beta - 1)) ≤
            Real.rpow (Real.log X) (-A) :=
  publishedSiegelRealZeroFreeRegion.eventually_prefactor_mul_weight_le
    hK hA hP

/-- Threshold form in the exact outer-quantifier order of the AP weighted
zero-mass estimate. -/
theorem exists_prefactor_mul_exceptionalWeight_le
    {K A P : ℝ} (hK : 0 < K) (hA : 0 < A) (hP : 0 ≤ P) :
    ∃ X0 : ℝ, 2 ≤ X0 ∧
      ∀ X : ℝ, X0 ≤ X →
        ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q) (beta : ℝ),
          (q : ℝ) ≤ Real.rpow (Real.log X) K →
          chi ≠ 1 → chi ^ 2 = 1 →
          DirichletCharacter.LFunction chi beta = 0 →
            Real.rpow (Real.log X) P *
                Real.rpow X (2 * (beta - 1)) ≤
              Real.rpow (Real.log X) (-A) :=
  publishedSiegelRealZeroFreeRegion.exists_prefactor_mul_weight_le hK hA hP

/-- The specialization accounting for all ambient character slots up to a
polylogarithmic level. -/
theorem exists_twoK_prefactor_mul_exceptionalWeight_le
    {K A : ℝ} (hK : 0 < K) (hA : 0 < A) :
    ∃ X0 : ℝ, 2 ≤ X0 ∧
      ∀ X : ℝ, X0 ≤ X →
        ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q) (beta : ℝ),
          (q : ℝ) ≤ Real.rpow (Real.log X) K →
          chi ≠ 1 → chi ^ 2 = 1 →
          DirichletCharacter.LFunction chi beta = 0 →
            Real.rpow (Real.log X) (2 * K) *
                Real.rpow X (2 * (beta - 1)) ≤
              Real.rpow (Real.log X) (-A) :=
  publishedSiegelRealZeroFreeRegion.exists_twoK_prefactor_mul_weight_le hK hA

end
end MAPGoldfeldSiegel

#print axioms MAPGoldfeldSiegel.eventually_prefactor_mul_exceptionalWeight_le
#print axioms MAPGoldfeldSiegel.exists_prefactor_mul_exceptionalWeight_le
#print axioms MAPGoldfeldSiegel.exists_twoK_prefactor_mul_exceptionalWeight_le
