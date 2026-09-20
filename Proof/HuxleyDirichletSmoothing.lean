import HuxleyKFiniteInterchange
import HuxleyKCutoff
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Dirichlet-series input to Huxley 1973 (2.7)

This module specializes the countable Mellin/Fubini connector to positive
integer frequencies carrying one Dirichlet character.  It proves the exact
`n⁻²` summability required on the source line `Re w = 2`; no zero-density or
large-value estimate is used.
-/

namespace MAPHuxleyDirichletSmoothing

open Complex Real MeasureTheory Filter
open scoped BigOperators LSeries.notation

noncomputable section

abbrev PositiveNat := {n : ℕ // 0 < n}

def dirichletCoefficient {q : ℕ} (χ : DirichletCharacter ℂ q)
    (s : ℂ) (n : PositiveNat) : ℂ :=
  χ (n : ℕ) / ((n : ℕ) : ℂ) ^ s

def dirichletRatio (U : ℝ) (n : PositiveNat) : ℝ := (n : ℝ) / U

private theorem ratio_pos {U : ℝ} (hU : 0 < U) (n : PositiveNat) :
    0 < dirichletRatio U n := by
  exact div_pos (Nat.cast_pos.mpr n.property) hU

private theorem weighted_dirichletCoefficient_eq
    {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} {U : ℝ}
    (hU : 0 < U) (n : PositiveNat) :
    ‖dirichletCoefficient χ s n‖ * Real.rpow (dirichletRatio U n) (-2) =
      ‖χ (n : ℕ)‖ * U ^ 2 *
        Real.rpow (n : ℝ) (-s.re - 2) := by
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr n.property
  have hn0 : 0 ≤ (n : ℝ) := hn.le
  have hU0 : 0 ≤ U := hU.le
  unfold dirichletCoefficient dirichletRatio
  simp only [Real.rpow_eq_pow]
  rw [norm_div, Complex.norm_natCast_cpow_of_pos n.property]
  rw [Real.div_rpow hn0 hU0]
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
    Real.rpow_neg hU0, Real.rpow_two]
  rw [div_inv_eq_mul]
  rw [div_eq_mul_inv, ← Real.rpow_neg hn0]
  rw [show -s.re - 2 = -s.re + (-2) by ring, Real.rpow_add hn]
  ring

/-- The exact summability needed to justify the Dirichlet-series Fubini step
in (2.7).  The sharp half-plane is `Re s > -1`, since the source line is
`Re w = 2`. -/
theorem summable_weighted_dirichletCoefficient
    {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} {U : ℝ}
    (hs : -1 < s.re) (hU : 0 < U) :
    Summable fun n : PositiveNat =>
      ‖dirichletCoefficient χ s n‖ * Real.rpow (dirichletRatio U n) (-2) := by
  let p : ℝ := -s.re - 2
  have hp : p < -1 := by dsimp [p]; linarith
  have hnat : Summable fun n : ℕ => Real.rpow (n : ℝ) p :=
    Real.summable_nat_rpow.mpr hp
  have hsub : Summable fun n : PositiveNat => Real.rpow (n : ℝ) p := by
    simpa only [Function.comp_apply] using hnat.subtype {n : ℕ | 0 < n}
  have hmajor : Summable fun n : PositiveNat =>
      U ^ 2 * Real.rpow (n : ℝ) p := hsub.mul_left (U ^ 2)
  refine Summable.of_nonneg_of_le
    (f := fun n : PositiveNat => U ^ 2 * Real.rpow (n : ℝ) p) ?_ ?_ hmajor
  · intro n
    exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (ratio_pos hU n).le _)
  · intro n
    rw [weighted_dirichletCoefficient_eq χ hU]
    have hχ : ‖χ (n : ℕ)‖ ≤ 1 := χ.norm_le_one (n : ZMod q)
    have hpow : 0 ≤ Real.rpow (n : ℝ) p := Real.rpow_nonneg (by positivity) _
    have hU2 : 0 ≤ U ^ 2 := sq_nonneg U
    calc
      ‖χ (n : ℕ)‖ * U ^ 2 * Real.rpow (n : ℝ) (-s.re - 2) =
          (‖χ (n : ℕ)‖ * U ^ 2) * Real.rpow (n : ℝ) p := by rfl
      _ ≤ (1 * U ^ 2) * Real.rpow (n : ℝ) p := by gcongr
      _ = U ^ 2 * Real.rpow (n : ℝ) p := by ring

/-- Countable Mellin inversion for the positive-integer Dirichlet
coefficients.  This is equation (2.7) before rewriting the termwise sum as
Mathlib's `LSeries` on the left and as the printed `b(n,U)` on the right. -/
theorem positiveNat_huxleyKernel_interchange
    {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} {U : ℝ}
    (hs : -1 < s.re) (hU : 0 < U) :
    (1 / (2 * Real.pi)) •
        ∫ t : ℝ, ∑' n : PositiveNat, dirichletCoefficient χ s n *
          (((dirichletRatio U n : ℝ) : ℂ) ^
              (-((2 : ℂ) + (t : ℂ) * I)) *
            MAPHuxleyReflectionKernelAlgebra.huxleyK
              ((2 : ℂ) + (t : ℂ) * I)) =
      ∑' n : PositiveNat, dirichletCoefficient χ s n *
        MAPHuxleyKMellin.huxleyKWeight (dirichletRatio U n) := by
  exact
    MAPHuxleyKFiniteInterchange.countable_huxleyKernel_interchange_of_weighted_summable
      (dirichletCoefficient χ s) (dirichletRatio U) (ratio_pos hU)
      (summable_weighted_dirichletCoefficient χ hs hU)

private theorem ratio_cpow_neg
    {U : ℝ} (hU : 0 < U) (n : PositiveNat) (w : ℂ) :
    (((dirichletRatio U n : ℝ) : ℂ) ^ (-w)) =
      (((n : ℕ) : ℂ) ^ (-w)) * ((U : ℂ) ^ w) := by
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr n.property
  have hr : 0 < dirichletRatio U n := ratio_pos hU n
  have hnC : (((n : ℕ) : ℂ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr n.property.ne'
  have hUC : (U : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU.ne'
  have hrC : ((dirichletRatio U n : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hr.ne'
  rw [show (((n : ℕ) : ℂ)) = (((n : ℝ) : ℂ)) by norm_cast]
  rw [Complex.cpow_def_of_ne_zero hrC,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hn.ne'),
    Complex.cpow_def_of_ne_zero hUC]
  rw [← Complex.ofReal_log hr.le, ← Complex.ofReal_log hn.le,
    ← Complex.ofReal_log hU.le]
  unfold dirichletRatio
  rw [Real.log_div hn.ne' hU.ne']
  push_cast
  rw [← Complex.exp_add]
  congr 1
  ring

private theorem coefficient_ratio_kernel_eq_term
    {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} {U : ℝ}
    (hU : 0 < U) (n : PositiveNat) (w : ℂ) :
    dirichletCoefficient χ s n *
        (((dirichletRatio U n : ℝ) : ℂ) ^ (-w) *
          MAPHuxleyReflectionKernelAlgebra.huxleyK w) =
      MAPHuxleyReflectionKernelAlgebra.huxleyK w * (U : ℂ) ^ w *
        LSeries.term (fun m : ℕ => χ m) (s + w) n := by
  have hnC : (((n : ℕ) : ℂ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr n.property.ne'
  have hns : (((n : ℕ) : ℂ) ^ s) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
  have hnw : (((n : ℕ) : ℂ) ^ w) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
  unfold dirichletCoefficient
  rw [ratio_cpow_neg hU n w,
    LSeries.term_of_ne_zero n.property.ne']
  rw [Complex.cpow_neg]
  rw [Complex.cpow_add s w hnC]
  field_simp [hns, hnw]

private theorem positiveNat_tsum_LSeries
    {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℂ) :
    (∑' n : PositiveNat, LSeries.term (fun m : ℕ => χ m) z n) =
      LSeries (fun m : ℕ => χ m) z := by
  change (∑' n : {n : ℕ // 0 < n},
      LSeries.term (fun m : ℕ => χ m) z n) = _
  rw [show (∑' n : {n : ℕ // 0 < n},
      LSeries.term (fun m : ℕ => χ m) z n) =
      ∑' n : ℕ, {n : ℕ | 0 < n}.indicator
        (fun n => LSeries.term (fun m : ℕ => χ m) z n) n by
      exact tsum_subtype {n : ℕ | 0 < n}
        (fun n => LSeries.term (fun m : ℕ => χ m) z n)]
  unfold LSeries
  apply tsum_congr
  intro n
  by_cases hn : 0 < n
  · rw [Set.indicator_of_mem (show n ∈ {n : ℕ | 0 < n} from hn)]
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    rw [Set.indicator_of_notMem (show (0 : ℕ) ∉ {n : ℕ | 0 < n} by simp)]
    simp [LSeries.term_zero]

private theorem positiveNat_integrand_eq_LSeries
    {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} {U : ℝ}
    (hs : -1 < s.re) (hU : 0 < U) (t : ℝ) :
    (∑' n : PositiveNat, dirichletCoefficient χ s n *
      (((dirichletRatio U n : ℝ) : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * I)) *
        MAPHuxleyReflectionKernelAlgebra.huxleyK
          ((2 : ℂ) + (t : ℂ) * I))) =
      MAPHuxleyReflectionKernelAlgebra.huxleyK
          ((2 : ℂ) + (t : ℂ) * I) *
        (U : ℂ) ^ ((2 : ℂ) + (t : ℂ) * I) *
        LSeries (fun m : ℕ => χ m)
          (s + ((2 : ℂ) + (t : ℂ) * I)) := by
  let w : ℂ := (2 : ℂ) + (t : ℂ) * I
  have hz : 1 < (s + w).re := by
    dsimp [w]
    norm_num
    linarith
  calc
    (∑' n : PositiveNat, dirichletCoefficient χ s n *
      (((dirichletRatio U n : ℝ) : ℂ) ^ (-w) *
        MAPHuxleyReflectionKernelAlgebra.huxleyK w)) =
      ∑' n : PositiveNat,
        MAPHuxleyReflectionKernelAlgebra.huxleyK w * (U : ℂ) ^ w *
          LSeries.term (fun m : ℕ => χ m) (s + w) n := by
            apply tsum_congr
            intro n
            exact coefficient_ratio_kernel_eq_term χ hU n w
    _ = MAPHuxleyReflectionKernelAlgebra.huxleyK w * (U : ℂ) ^ w *
        (∑' n : PositiveNat,
          LSeries.term (fun m : ℕ => χ m) (s + w) n) := by
            rw [tsum_mul_left]
    _ = MAPHuxleyReflectionKernelAlgebra.huxleyK w * (U : ℂ) ^ w *
        LSeries (fun m : ℕ => χ m) (s + w) := by
          rw [positiveNat_tsum_LSeries χ (s + w)]

private theorem huxleyKWeight_ratio_eq_cutoff
    {m U : ℝ} (hm : 0 < m) (hU : 0 < U) :
    MAPHuxleyKMellin.huxleyKWeight (m / U) =
      (MAPHuxleyHalaszFront.huxleyCutoffWeight m U : ℂ) := by
  calc
    MAPHuxleyKMellin.huxleyKWeight (m / U) =
        mellinInv 2 MAPHuxleyReflectionKernelAlgebra.huxleyK (m / U) :=
      (MAPHuxleyKMellin.mellinInv_huxleyK_eq_weight (div_pos hm hU)).symm
    _ = (MAPHuxleyHalaszFront.huxleyCutoffWeight m U : ℂ) :=
      MAPHuxleyKCutoff.mellinInv_huxleyK_eq_cutoff hm hU

/-- Literal Huxley 1973 equation (2.7) on the real-line parametrization of
`Re w = 2`, for one Dirichlet character and every `Re s > -1`.  The right
side is indexed by positive integers and uses the repository's exact printed
coefficient `b(n,U)`. -/
theorem literal_dirichlet_huxley_equation_2_7
    {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} {U : ℝ}
    (hs : -1 < s.re) (hU : 0 < U) :
    (1 / (2 * Real.pi)) •
        ∫ t : ℝ,
          MAPHuxleyReflectionKernelAlgebra.huxleyK
              ((2 : ℂ) + (t : ℂ) * I) *
            (U : ℂ) ^ ((2 : ℂ) + (t : ℂ) * I) *
            LSeries (fun m : ℕ => χ m)
              (s + ((2 : ℂ) + (t : ℂ) * I)) =
      ∑' n : PositiveNat, dirichletCoefficient χ s n *
        (MAPHuxleyHalaszFront.huxleyCutoffWeight (n : ℝ) U : ℂ) := by
  calc
    (1 / (2 * Real.pi)) •
        ∫ t : ℝ,
          MAPHuxleyReflectionKernelAlgebra.huxleyK
              ((2 : ℂ) + (t : ℂ) * I) *
            (U : ℂ) ^ ((2 : ℂ) + (t : ℂ) * I) *
            LSeries (fun m : ℕ => χ m)
              (s + ((2 : ℂ) + (t : ℂ) * I)) =
      (1 / (2 * Real.pi)) •
        ∫ t : ℝ, ∑' n : PositiveNat, dirichletCoefficient χ s n *
          (((dirichletRatio U n : ℝ) : ℂ) ^
              (-((2 : ℂ) + (t : ℂ) * I)) *
            MAPHuxleyReflectionKernelAlgebra.huxleyK
              ((2 : ℂ) + (t : ℂ) * I)) := by
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun t =>
          (positiveNat_integrand_eq_LSeries χ hs hU t).symm)
    _ = ∑' n : PositiveNat, dirichletCoefficient χ s n *
        MAPHuxleyKMellin.huxleyKWeight (dirichletRatio U n) :=
      positiveNat_huxleyKernel_interchange χ hs hU
    _ = ∑' n : PositiveNat, dirichletCoefficient χ s n *
        (MAPHuxleyHalaszFront.huxleyCutoffWeight (n : ℝ) U : ℂ) := by
      apply tsum_congr
      intro n
      rw [show dirichletRatio U n = (n : ℝ) / U by rfl,
        huxleyKWeight_ratio_eq_cutoff
          (Nat.cast_pos.mpr n.property) hU]

end

end MAPHuxleyDirichletSmoothing

#print axioms MAPHuxleyDirichletSmoothing.summable_weighted_dirichletCoefficient
#print axioms MAPHuxleyDirichletSmoothing.positiveNat_huxleyKernel_interchange
#print axioms MAPHuxleyDirichletSmoothing.literal_dirichlet_huxley_equation_2_7
