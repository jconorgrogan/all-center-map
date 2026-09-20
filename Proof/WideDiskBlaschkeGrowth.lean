import WideDiskBlaschkeAssembly
import CompactDeflatedBorelBridge
import Mathlib.Analysis.Complex.AbsMax

/-!
# Quantitative growth of the radius-three Blaschke fill

The literal regularized L-function circle bound transfers, with no loss, to
its finite canonical-factor fill.  Maximum modulus and the Euler-product
center lower bound then give the outer-disk logarithmic ratio needed by the
pointwise Borel--Caratheodory estimate.
-/

namespace WideDiskBlaschkeGrowth

open Complex Set Metric DirichletZeros
open WideDiskLFunctionGrowth FiniteBlaschkeAlgebra MAPLocalZeroWindow
open WideDiskBlaschkeAssembly CompactDeflatedBorelBridge

noncomputable section

/-- The canonical filling is analytic on the closed radius-three disk.  At a
supported point this is the multiplicity cancellation theorem; elsewhere the
raw product is already analytic and agrees locally with its normal form. -/
theorem analyticOnNhd_analyticWideBlaschkeDeflated_closedBall
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    AnalyticOnNhd ℂ (analyticWideBlaschkeDeflated χ t)
      (Metric.closedBall (wideCenter t) wideRadius) := by
  intro z hz
  by_cases hzF : z ∈ wideZeroSupport χ t
  · exact analyticOnNhd_analyticWideBlaschkeDeflated_ball χ t z
      (mem_ball_of_mem_wideZeroSupport χ hzF)
  · have hprodAn : AnalyticAt ℂ (wideBlaschkeProduct χ t) z := by
      change AnalyticAt ℂ
        (fun w : ℂ => ∏ ρ ∈ wideZeroSupport χ t,
          shiftedCanonicalFactor (wideCenter t) wideRadius ρ w ^
            wideZeroMultiplicity χ t ρ) z
      apply Finset.analyticAt_fun_prod
      intro ρ hρ
      have hzρ : z ≠ ρ := by
        intro h
        apply hzF
        rwa [h]
      change AnalyticAt ℂ
        ((shiftedCanonicalFactor (wideCenter t) wideRadius ρ) ^
          wideZeroMultiplicity χ t ρ) z
      have hne : z - wideCenter t ≠ ρ - wideCenter t :=
        fun h => hzρ (sub_left_inj.mp h)
      have hcan := Complex.analyticOnNhd_canonicalFactor wideRadius
        (ρ - wideCenter t) (z - wideCenter t) hne
      have hsub : AnalyticAt ℂ (fun w : ℂ => w - wideCenter t) z := by fun_prop
      exact (AnalyticAt.comp (f := fun w : ℂ => w - wideCenter t)
        (x := z) hcan hsub).pow _
    have hrawAn : AnalyticAt ℂ (rawWideBlaschkeDeflated χ t) z :=
      ((differentiable_regularizedLFunction χ).analyticAt z).mul hprodAn
    have hrawMer : MeromorphicOn (rawWideBlaschkeDeflated χ t) Set.univ := by
      apply MeromorphicOn.mul
      · exact (analyticOnNhd_univ_iff_differentiable.mpr
          (differentiable_regularizedLFunction χ)).meromorphicOn
      · change MeromorphicOn
          (fun w : ℂ => ∏ ρ ∈ wideZeroSupport χ t,
            shiftedCanonicalFactor (wideCenter t) wideRadius ρ w ^
              wideZeroMultiplicity χ t ρ) Set.univ
        apply MeromorphicOn.fun_prod
        intro ρ hρ
        change MeromorphicOn
          ((shiftedCanonicalFactor (wideCenter t) wideRadius ρ) ^
            wideZeroMultiplicity χ t ρ) Set.univ
        apply MeromorphicOn.pow
        intro w hw
        unfold shiftedCanonicalFactor Complex.canonicalFactor
        fun_prop
    have hnf := meromorphicNFOn_toMeromorphicNFOn
      (rawWideBlaschkeDeflated χ t) Set.univ
    apply (hnf (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hrawMer (Set.mem_univ z)]
    exact hrawAn.meromorphicOrderAt_nonneg

/-- Maximum-modulus transfer of the exact wide-circle estimate to the full
closed disk. -/
theorem norm_analyticWideBlaschkeDeflated_le_on_closedBall
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {t : ℝ} {z : ℂ} (hz : z ∈ Metric.closedBall (wideCenter t) wideRadius) :
    ‖analyticWideBlaschkeDeflated χ t z‖ ≤
      7200 * (arithmeticScale q t) ^ 2 := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    Metric.isBounded_ball
    ((analyticOnNhd_analyticWideBlaschkeDeflated_closedBall χ t).differentiableOn
      |>.diffContOnCl_ball subset_rfl)
  · intro w hw
    have hwsphere : w ∈ Metric.sphere (wideCenter t) wideRadius :=
      frontier_ball_subset_sphere hw
    rw [norm_analyticWideBlaschkeDeflated_eq_regularized_on_sphere χ hwsphere]
    exact norm_regularizedLFunction_wideCircle_le χ hχ hwsphere
  · rw [closure_ball _ (by norm_num [wideRadius])]
    exact hz

/-- Explicit log-norm-ratio estimate throughout the open wide disk. -/
theorem log_analyticWideBlaschkeDeflated_ratio_le
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {t : ℝ} {z : ℂ} (hz : z ∈ Metric.ball (wideCenter t) wideRadius) :
    Real.log
        (‖analyticWideBlaschkeDeflated χ t z‖ /
          ‖analyticWideBlaschkeDeflated χ t (wideCenter t)‖) ≤
      Real.log 21600 + 2 * Real.log (arithmeticScale q t) := by
  have hupper := norm_analyticWideBlaschkeDeflated_le_on_closedBall χ hχ
    (show z ∈ Metric.closedBall (wideCenter t) wideRadius by
      rw [Metric.mem_closedBall]
      exact (Metric.mem_ball.mp hz).le)
  have hcenterLower : (1 / 3 : ℝ) ≤
      ‖analyticWideBlaschkeDeflated χ t (wideCenter t)‖ :=
    (one_third_le_norm_regularizedLFunction_wideCenter χ hχ t).trans
      (norm_regularizedLFunction_center_le_analyticWideBlaschkeDeflated χ t)
  have hcenterPos : 0 <
      ‖analyticWideBlaschkeDeflated χ t (wideCenter t)‖ := by linarith
  have hratio :
      ‖analyticWideBlaschkeDeflated χ t z‖ /
          ‖analyticWideBlaschkeDeflated χ t (wideCenter t)‖ ≤
        21600 * (arithmeticScale q t) ^ 2 := by
    apply (div_le_iff₀ hcenterPos).2
    have hone : 1 ≤ 3 *
        ‖analyticWideBlaschkeDeflated χ t (wideCenter t)‖ := by linarith
    calc
      ‖analyticWideBlaschkeDeflated χ t z‖ ≤
          7200 * (arithmeticScale q t) ^ 2 := hupper
      _ ≤ (21600 * (arithmeticScale q t) ^ 2) *
          ‖analyticWideBlaschkeDeflated χ t (wideCenter t)‖ := by
        nlinarith [sq_nonneg (arithmeticScale q t)]
  have hscale : 0 < arithmeticScale q t :=
    lt_of_lt_of_le zero_lt_one
      (MAPPrimitiveLFixedStrip.one_le_arithmeticScale t)
  have hlogeq :
      Real.log (21600 * (arithmeticScale q t) ^ 2) =
        Real.log 21600 + 2 * Real.log (arithmeticScale q t) := by
    rw [Real.log_mul (by norm_num : (21600 : ℝ) ≠ 0)
      (pow_ne_zero 2 hscale.ne'), Real.log_pow]
    norm_num
  have hzpos : 0 < ‖analyticWideBlaschkeDeflated χ t z‖ :=
    norm_pos_iff.mpr (analyticWideBlaschkeDeflated_ne_zero_ball χ t hz)
  calc
    Real.log
        (‖analyticWideBlaschkeDeflated χ t z‖ /
          ‖analyticWideBlaschkeDeflated χ t (wideCenter t)‖) ≤
        Real.log (21600 * (arithmeticScale q t) ^ 2) :=
      Real.log_le_log (div_pos hzpos hcenterPos) hratio
    _ = Real.log 21600 + 2 * Real.log (arithmeticScale q t) := hlogeq

/-- Quantitative logarithmic derivative of the literal finite Blaschke fill
on the radius-two inner disk. -/
theorem norm_logDeriv_analyticWideBlaschkeDeflated_le
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {t : ℝ} {s : ℂ} (hs : dist s (wideCenter t) < 2) :
    ‖logDeriv (analyticWideBlaschkeDeflated χ t) s‖ ≤
      20 * (Real.log 21600 + 2 * Real.log (arithmeticScale q t)) := by
  let M := Real.log 21600 + 2 * Real.log (arithmeticScale q t)
  have hM : 0 < M := by
    have hscale : 1 ≤ arithmeticScale q t :=
      MAPPrimitiveLFixedStrip.one_le_arithmeticScale t
    dsimp [M]
    have hlog21600 : 0 < Real.log (21600 : ℝ) :=
      Real.log_pos (by norm_num)
    have hlogscale : 0 ≤ Real.log (arithmeticScale q t) :=
      Real.log_nonneg hscale
    linarith
  have hbase := norm_logDeriv_le_of_scaled_log_norm_ratio_le_at
    (g := analyticWideBlaschkeDeflated χ t)
    (c := wideCenter t) (s := s) (r := (2 : ℝ)) (M := M)
    (by norm_num)
    (by simpa [wideRadius] using
      (analyticOnNhd_analyticWideBlaschkeDeflated_ball χ t).differentiableOn)
    (fun z hz => analyticWideBlaschkeDeflated_ne_zero_ball χ t (by simpa [wideRadius] using hz))
    hM
    (fun z hz => log_analyticWideBlaschkeDeflated_ratio_le χ hχ
      (by simpa [wideRadius] using hz)) hs
  dsimp [M] at hbase ⊢
  convert hbase using 1 <;> ring

end

end WideDiskBlaschkeGrowth
