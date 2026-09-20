import GuthMaynardEnergy114LocalL2
import GuthMaynardEnergy114CollarReduction
import GuthMaynardEnergy114WeightedAverage
import GuthMaynardEnergy114CubicMoment

open scoped BigOperators
open MeasureTheory
noncomputable section
namespace GuthMaynardEnergy114Actual
open CGLProofDAG GuthMaynardRatioKernelIdentity
open GuthMaynardEnergy114LocalL2 GuthMaynardEnergy114CollarReduction
open GuthMaynardEnergy114WeightedAverage GuthMaynardEnergy114DirichletKernel
open GuthMaynardEnergy114CubicMoment GuthMaynardS3LiteralLemma83Energy
open GuthMaynardEnergy114KernelEnvelope

/-- Literal energy-to-third-moment bound with a uniform constant. The whole-line
kernel, collar count and finite cubic expansion are supplied internally. -/
theorem energy_le_cubic_moment_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (b : ℕ → ℂ) (W : Finset ℝ) (V : ℝ),
      1 ≤ N → 0 ≤ V →
      (∀ n ∈ Finset.Ioc N (2*N), ‖b n‖ ≤ 1) → OneSeparated W →
      (∀ t ∈ W, V ≤ ‖dirichletPolynomial b N t‖) →
      (sourceApproximateAdditiveEnergy W : ℝ)*V^2 ≤
        C*(∑ n1 ∈ Finset.Ioc N (2*N), ∑ n2 ∈ Finset.Ioc N (2*N),
          ‖ratioDirichletKernel W ((n1 : ℝ)/(n2 : ℝ))‖^3) := by
  obtain ⟨Cl,hCl,hl⟩ := weightedPointMassFourierKernel_local_L2 (ι:=ℕ)
  let A : ℝ := ∫ s : ℝ, energy114Weight s
  have hA : 0 ≤ A := integral_nonneg inv_one_add_sq_nonneg
  let C : ℝ := 3*(Cl+1)*(A+1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro N b W V hN hV hb hsep hlarge
  let H : ℝ → ℝ := dirichletWeightedSquareMean N b
  have hH : ∀ v : ℝ, 0 ≤ H v := dirichletWeightedSquareMean_nonneg N b
  have hlocal : ∀ u v : ℝ, |u-v| ≤ 1 →
      ‖dirichletPolynomial b N u‖^2 ≤ Cl*H v := by
    intro u v huv
    have hh := hl (Finset.Ioc N (2*N)) dirichletFrequency b
      (-(Real.log (N : ℝ)/(2*Real.pi))-1) u v (dirichlet_frequency_interval hN) huv
    simpa only [weighted_kernel_eq_dirichlet,H,dirichletWeightedSquareMean,energy114Weight] using hh
  have hcol := energy_le_local_cubic_average W (dirichletPolynomial b N) H
    hV hCl hH hsep hlarge hlocal
  let M : ℝ := ∑ n1 ∈ Finset.Ioc N (2*N), ∑ n2 ∈ Finset.Ioc N (2*N),
    ‖ratioDirichletKernel W ((n1 : ℝ)/(n2 : ℝ))‖^3
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have havg := triple_weighted_average_le N b W (fun s => cubic_moment_pointwise hN W b hb s)
  have hsum : (∑ a ∈ W, ∑ b0 ∈ W, ∑ c ∈ W, H (a+b0-c)) ≤ A*M := havg
  have hmul := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 3*Cl)
  have hcoef : 3*Cl*A ≤ C := by
    dsimp [C]
    have he : 0 ≤ 3*Cl+3*A+3 := by positivity
    nlinarith only [he]
  calc
    (sourceApproximateAdditiveEnergy W : ℝ)*V^2 ≤
        3*Cl*(∑ a ∈ W, ∑ b0 ∈ W, ∑ c ∈ W, H (a+b0-c)) := hcol
    _ ≤ 3*Cl*(A*M) := hmul
    _ = (3*Cl*A)*M := by ring
    _ ≤ C*M := mul_le_mul_of_nonneg_right hcoef hM

end GuthMaynardEnergy114Actual
#print axioms GuthMaynardEnergy114Actual.energy_le_cubic_moment_uniform
