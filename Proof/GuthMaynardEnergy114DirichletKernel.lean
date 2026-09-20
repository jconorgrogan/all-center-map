import GuthMaynardLemma117Cubic
import CGLProofDAG

open scoped BigOperators
noncomputable section
namespace GuthMaynardEnergy114DirichletKernel
open GuthMaynardLemma117 CGLProofDAG

def dirichletFrequency (n : ℕ) : ℝ := -(Real.log (n : ℝ)/(2*Real.pi))

theorem weighted_kernel_eq_dirichlet (N : ℕ) (b : ℕ → ℂ) (t : ℝ) :
    weightedPointMassFourierKernel (Finset.Ioc N (2*N)) dirichletFrequency b t =
      dirichletPolynomial b N t := by
  unfold weightedPointMassFourierKernel dirichletPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  apply congrArg Complex.exp
  have hr : -(2*Real.pi*dirichletFrequency n*t) = t*Real.log (n : ℝ) := by
    dsimp [dirichletFrequency]
    field_simp [Real.pi_ne_zero]
  calc
    -((2*Real.pi*dirichletFrequency n*t : ℝ) : ℂ)*Complex.I =
        ((-(2*Real.pi*dirichletFrequency n*t) : ℝ) : ℂ)*Complex.I := by simp
    _ = ((t*Real.log (n : ℝ) : ℝ) : ℂ)*Complex.I := by rw [hr]
    _ = Complex.I*(t*Real.log (n : ℝ)) := by push_cast; ring

/-- All dyadic Dirichlet frequencies fit in a translate of one fixed unit
interval. Its location may depend on N; its width and all kernel constants do
not. This avoids a spurious logarithmic frequency-radius loss. -/
theorem dirichlet_frequency_interval {N : ℕ} (hN : 1 ≤ N) :
    ∀ n ∈ Finset.Ioc N (2*N),
      -(Real.log (N : ℝ)/(2*Real.pi))-1 ≤ dirichletFrequency n ∧
      dirichletFrequency n ≤ (-(Real.log (N : ℝ)/(2*Real.pi))-1)+1 := by
  intro n hn
  have hh := Finset.mem_Ioc.mp hn
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt hh.1)
  have hnN : (n : ℝ) ≤ 2*(N : ℝ) := by exact_mod_cast hh.2
  have hloglo : Real.log (N : ℝ) ≤ Real.log (n : ℝ) := Real.log_le_log hNp hNn
  have hloghi : Real.log (n : ℝ) ≤ Real.log 2+Real.log (N : ℝ) := by
    have ht := Real.log_le_log hnp hnN
    rwa [Real.log_mul (by norm_num) hNp.ne'] at ht
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hd : 0 < 2*Real.pi := by positivity
  have hpi := Real.pi_gt_three
  have hlo := div_le_div_of_nonneg_right hloglo hd.le
  have hhi : Real.log (n : ℝ)/(2*Real.pi) ≤ Real.log (N : ℝ)/(2*Real.pi)+1 := by
    apply (div_le_iff₀ hd).2
    have hid : (Real.log (N : ℝ)/(2*Real.pi)+1)*(2*Real.pi) =
        Real.log (N : ℝ)+2*Real.pi := by field_simp
    rw [hid]
    linarith only [hloghi,hlog2,hpi]
  dsimp [dirichletFrequency]
  constructor <;> linarith only [hlo,hhi]

end GuthMaynardEnergy114DirichletKernel
#print axioms GuthMaynardEnergy114DirichletKernel.weighted_kernel_eq_dirichlet
#print axioms GuthMaynardEnergy114DirichletKernel.dirichlet_frequency_interval
