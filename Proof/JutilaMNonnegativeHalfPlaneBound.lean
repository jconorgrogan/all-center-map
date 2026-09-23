import JutilaMEntire

/-! # Finite mollifier bound on the closed nonnegative half-plane -/
namespace MAPJutilaMNonnegativeHalfPlaneBound
open scoped BigOperators
open Complex
open MAPJutilaMEntire MAPJutilaPseudocharacterMExact
noncomputable section

theorem norm_jutilaNatPower_le_one {n : ℕ} (hn : 0 < n)
    {s : ℂ} (hs : 0 ≤ s.re) : ‖jutilaNatPower n s‖ ≤ 1 := by
  unfold jutilaNatPower
  rw [Complex.norm_natCast_cpow_of_pos hn]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn)
    (by simpa using neg_nonpos.mpr hs)

def localEulerBudget {q : ℕ} (chi : DirichletCharacter ℂ q) (r d : ℕ) : ℝ :=
  ∏ p ∈ (r / r.gcd d).primeFactors, (1 + ‖(selbergPseudoCoeff p - 1) * chi p‖)

theorem norm_localEulerProduct_le {q : ℕ} (chi : DirichletCharacter ℂ q)
    (r d : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖jutilaLocalEulerProductComplex chi r d s‖ ≤ localEulerBudget chi r d := by
  unfold jutilaLocalEulerProductComplex localEulerBudget
  apply (Finset.norm_prod_le _ _).trans
  apply Finset.prod_le_prod₀ (fun p hp => norm_nonneg _)
  intro p hp
  unfold jutilaLocalEulerFactorComplex
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖(selbergPseudoCoeff p - 1) * chi p * jutilaNatPower p s‖ :=
      norm_add_le _ _
    _ = 1 + ‖(selbergPseudoCoeff p - 1) * chi p‖ * ‖jutilaNatPower p s‖ := by
      rw [norm_one, norm_mul]
    _ ≤ 1 + ‖(selbergPseudoCoeff p - 1) * chi p‖ * 1 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (norm_jutilaNatPower_le_one (Nat.pos_of_mem_primeFactors hp) hs) (norm_nonneg _))
    _ = _ := by ring

def finiteMHalfPlaneBudget {q : ℕ} (chi : DirichletCharacter ℂ q)
    (xi : ℕ → ℂ) (D S : Finset ℕ) : ℝ :=
  ∑ r ∈ S, ‖(r : ℂ)⁻¹‖ *
    ∑ d ∈ D, ‖xi d * chi d * selbergPseudoAt r d‖ * localEulerBudget chi r d

theorem finiteMHalfPlaneBudget_nonneg {q : ℕ} (chi : DirichletCharacter ℂ q)
    (xi : ℕ → ℂ) (D S : Finset ℕ) :
    0 ≤ finiteMHalfPlaneBudget chi xi D S := by
  unfold finiteMHalfPlaneBudget localEulerBudget
  positivity

/-- No squarefree or positive-index condition on `S` is required. Its zero
index, if present, has zero inverse weight by the literal definition. -/
theorem norm_jutilaMWeightedSumComplex_le_budget
    {q : ℕ} (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    {D : Finset ℕ} (hDpos : ∀ d ∈ D, 0 < d) (S : Finset ℕ)
    {s : ℂ} (hs : 0 ≤ s.re) :
    ‖jutilaMWeightedSumComplex chi xi D S s‖ ≤ finiteMHalfPlaneBudget chi xi D S := by
  unfold jutilaMWeightedSumComplex finiteMHalfPlaneBudget
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro r hr
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  unfold jutilaMFiniteComplex
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  unfold jutilaMTermComplex
  rw [norm_mul, norm_mul]
  have hprod0 : 0 ≤ localEulerBudget chi r d := by
    unfold localEulerBudget
    positivity
  calc
    _ ≤ (‖xi d * chi d * selbergPseudoAt r d‖ * 1) * localEulerBudget chi r d :=
      mul_le_mul (mul_le_mul_of_nonneg_left (norm_jutilaNatPower_le_one (hDpos d hd) hs)
        (norm_nonneg _)) (norm_localEulerProduct_le chi r d hs)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem exists_jutilaMWeightedSumComplex_bound
    {q : ℕ} (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    {D : Finset ℕ} (hDpos : ∀ d ∈ D, 0 < d) (S : Finset ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 0 ≤ s.re →
      ‖jutilaMWeightedSumComplex chi xi D S s‖ ≤ C := by
  exact ⟨finiteMHalfPlaneBudget chi xi D S, finiteMHalfPlaneBudget_nonneg chi xi D S,
    fun s hs => norm_jutilaMWeightedSumComplex_le_budget chi xi hDpos S hs⟩
end
end MAPJutilaMNonnegativeHalfPlaneBound
#print axioms MAPJutilaMNonnegativeHalfPlaneBound.exists_jutilaMWeightedSumComplex_bound
