import GuthMaynardEnergy114DirichletKernel
import GuthMaynardEnergy114KernelEnvelope

open scoped BigOperators
open MeasureTheory
noncomputable section
namespace GuthMaynardEnergy114WeightedAverage
open CGLProofDAG GuthMaynardLemma117 GuthMaynardEnergy114DirichletKernel
open GuthMaynardEnergy114KernelEnvelope

def energy114Weight (s : ℝ) : ℝ := 1/(1+s^2)

def dirichletWeightedSquareMean (N : ℕ) (b : ℕ → ℂ) (t : ℝ) : ℝ :=
  ∫ s : ℝ, energy114Weight s * ‖dirichletPolynomial b N (t-s)‖^2

theorem dirichlet_weighted_square_integrable (N : ℕ) (b : ℕ → ℂ) (t : ℝ) :
    Integrable (fun s : ℝ => energy114Weight s * ‖dirichletPolynomial b N (t-s)‖^2) := by
  let M : ℝ := weightedCoefficientMass (Finset.Ioc N (2*N)) b
  have hM : 0 ≤ M := by dsimp [M,weightedCoefficientMass]; positivity
  have hnorm : ∀ s : ℝ, ‖dirichletPolynomial b N (t-s)‖ ≤ M := by
    intro s
    rw [← weighted_kernel_eq_dirichlet]
    exact norm_weightedPointMassFourierKernel_le_mass _ _ _ _
  have hwint : Integrable energy114Weight := inv_one_add_sq_integrable
  have hw : ∀ s : ℝ, 0 ≤ energy114Weight s := inv_one_add_sq_nonneg
  have hwcont : Continuous energy114Weight := by
    unfold energy114Weight
    apply continuous_const.div₀ (continuous_const.add (continuous_id.pow 2))
    intro s
    change (1 : ℝ)+s^2 ≠ 0
    positivity
  have hfcont : Continuous (fun s : ℝ => ‖dirichletPolynomial b N (t-s)‖^2) := by
    unfold dirichletPolynomial
    fun_prop
  apply (hwint.mul_const (M^2)).mono' (hwcont.mul hfcont).aestronglyMeasurable
  filter_upwards [] with s
  have hzero : 0 ≤ energy114Weight s * ‖dirichletPolynomial b N (t-s)‖^2 :=
    mul_nonneg (hw s) (sq_nonneg _)
  change ‖energy114Weight s * ‖dirichletPolynomial b N (t-s)‖^2‖ ≤ energy114Weight s*M^2
  simpa only [Real.norm_eq_abs, abs_of_nonneg hzero] using
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hnorm s) 2) (hw s)

theorem dirichletWeightedSquareMean_nonneg (N : ℕ) (b : ℕ → ℂ) (t : ℝ) :
    0 ≤ dirichletWeightedSquareMean N b t := by
  apply integral_nonneg
  intro s
  exact mul_nonneg (inv_one_add_sq_nonneg s) (sq_nonneg _)

/-- Exact whole-line finite-sum integration. The pointwise cubic-moment input
is explicit here and is supplied separately by a literal finite expansion. -/
theorem triple_weighted_average_le
    (N : ℕ) (b : ℕ → ℂ) (W : Finset ℝ) {M : ℝ}
    (hpoint : ∀ s : ℝ,
      (∑ a ∈ W, ∑ b0 ∈ W, ∑ c ∈ W,
        ‖dirichletPolynomial b N (a+b0-c-s)‖^2) ≤ M) :
    (∑ a ∈ W, ∑ b0 ∈ W, ∑ c ∈ W,
      dirichletWeightedSquareMean N b (a+b0-c)) ≤
      (∫ s : ℝ, energy114Weight s)*M := by
  have hInt (a b0 c : ℝ) := dirichlet_weighted_square_integrable N b (a+b0-c)
  have hInt2 (a b0 : ℝ) : Integrable (fun s : ℝ =>
      ∑ c ∈ W, energy114Weight s * ‖dirichletPolynomial b N (a+b0-c-s)‖^2) :=
    integrable_finset_sum W (fun c _ => hInt a b0 c)
  have hInt1 (a : ℝ) : Integrable (fun s : ℝ =>
      ∑ b0 ∈ W, ∑ c ∈ W, energy114Weight s * ‖dirichletPolynomial b N (a+b0-c-s)‖^2) :=
    integrable_finset_sum W (fun b0 _ => hInt2 a b0)
  have hIntAll : Integrable (fun s : ℝ =>
      ∑ a ∈ W, ∑ b0 ∈ W, ∑ c ∈ W,
        energy114Weight s * ‖dirichletPolynomial b N (a+b0-c-s)‖^2) :=
    integrable_finset_sum W (fun a _ => hInt1 a)
  have hFubini : (∫ s : ℝ,
      ∑ a ∈ W, ∑ b0 ∈ W, ∑ c ∈ W,
        energy114Weight s * ‖dirichletPolynomial b N (a+b0-c-s)‖^2) =
      ∑ a ∈ W, ∑ b0 ∈ W, ∑ c ∈ W,
        dirichletWeightedSquareMean N b (a+b0-c) := by
    rw [integral_finset_sum W (fun a _ => hInt1 a)]
    apply Finset.sum_congr rfl
    intro a ha
    rw [integral_finset_sum W (fun b0 _ => hInt2 a b0)]
    apply Finset.sum_congr rfl
    intro b0 hb
    exact integral_finset_sum W (fun c _ => hInt a b0 c)
  calc
    _ = ∫ s : ℝ, ∑ a ∈ W, ∑ b0 ∈ W, ∑ c ∈ W,
        energy114Weight s * ‖dirichletPolynomial b N (a+b0-c-s)‖^2 := hFubini.symm
    _ ≤ ∫ s : ℝ, energy114Weight s*M := by
      apply integral_mono hIntAll (inv_one_add_sq_integrable.mul_const M)
      intro s
      have hh := mul_le_mul_of_nonneg_left (hpoint s) (inv_one_add_sq_nonneg s)
      simpa only [Finset.mul_sum, energy114Weight] using! hh
    _ = (∫ s : ℝ, energy114Weight s)*M := integral_mul_const _ _

end GuthMaynardEnergy114WeightedAverage
#print axioms GuthMaynardEnergy114WeightedAverage.dirichlet_weighted_square_integrable
#print axioms GuthMaynardEnergy114WeightedAverage.dirichletWeightedSquareMean_nonneg
#print axioms GuthMaynardEnergy114WeightedAverage.triple_weighted_average_le
