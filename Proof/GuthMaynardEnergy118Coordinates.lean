import GuthMaynardS3LiteralLemma83Energy
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open scoped BigOperators
open MeasureTheory
noncomputable section
namespace GuthMaynardEnergy118Coordinates
open GuthMaynardRatioKernelIdentity GuthMaynardS3LiteralLemma83Energy

theorem pointMass_eq_log_scaled (W : Finset ℝ) (u : ℝ) :
    pointMassFourierKernel W u = logDirichletKernel W ((-(2*Real.pi))*u) := by
  unfold pointMassFourierKernel logDirichletKernel
  apply Finset.sum_congr rfl
  intro t ht
  congr 1
  push_cast
  ring

private theorem scaled_mem_unit_iff (u : ℝ) :
    (-(2*Real.pi))*u ∈ Set.Icc (-1 : ℝ) 1 ↔
      u ∈ Set.Icc ((-1 : ℝ)/(2*Real.pi)) (1/(2*Real.pi)) := by
  have hc : 0 < 2*Real.pi := by positivity
  simp only [Set.mem_Icc]
  constructor
  · rintro ⟨hlo,hhi⟩
    constructor
    · apply (div_le_iff₀ hc).2
      nlinarith
    · apply (le_div_iff₀ hc).2
      nlinarith
  · rintro ⟨hlo,hhi⟩
    have hl := (div_le_iff₀ hc).1 hlo
    have hh := (le_div_iff₀ hc).1 hhi
    constructor <;> nlinarith

/-- Exact sign, scale and Jacobian for the compact moments used in the
rational log-frequency packing estimate. -/
theorem compact_pointMass_moment_eq_log (W : Finset ℝ) (p : ℕ) :
    (∫ u : ℝ in Set.Icc ((-1 : ℝ)/(2*Real.pi)) (1/(2*Real.pi)),
      ‖pointMassFourierKernel W u‖^p) =
      (1/(2*Real.pi)) * (∫ t : ℝ in Set.Icc (-1 : ℝ) 1,
        ‖logDirichletKernel W t‖^p) := by
  let g : ℝ → ℝ := (Set.Icc (-1 : ℝ) 1).indicator
    (fun t => ‖logDirichletKernel W t‖^p)
  have heq : (Set.Icc ((-1 : ℝ)/(2*Real.pi)) (1/(2*Real.pi))).indicator
      (fun u => ‖pointMassFourierKernel W u‖^p) =
      (fun u => g ((-(2*Real.pi))*u)) := by
    funext u
    by_cases hu : u ∈ Set.Icc ((-1 : ℝ)/(2*Real.pi)) (1/(2*Real.pi))
    · have hv := (scaled_mem_unit_iff u).2 hu
      simp only [g,Set.indicator_of_mem hu,Set.indicator_of_mem hv,pointMass_eq_log_scaled]
    · have hv : (-(2*Real.pi))*u ∉ Set.Icc (-1 : ℝ) 1 :=
        fun h => hu ((scaled_mem_unit_iff u).1 h)
      simp only [g,Set.indicator_of_notMem hu,Set.indicator_of_notMem hv]
  rw [← integral_indicator measurableSet_Icc, heq,
    Measure.integral_comp_mul_left g (-(2*Real.pi))]
  have hc : 0 < 2*Real.pi := by positivity
  have hfac : |(-(2*Real.pi))⁻¹| = 1/(2*Real.pi) := by
    rw [abs_inv,abs_neg,abs_of_pos hc,one_div]
  rw [hfac,smul_eq_mul]
  congr 1
  exact integral_indicator measurableSet_Icc

end GuthMaynardEnergy118Coordinates
#print axioms GuthMaynardEnergy118Coordinates.compact_pointMass_moment_eq_log
