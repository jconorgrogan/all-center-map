import ZeroFreeSiegelSpine
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Meromorphic.FactorizedRational

/-!
# Borel--Caratheodory bridge for the Dirichlet-L zero-free spine

This module preserves two premise-free analytic ingredients toward the uniform
primitive logarithmic-derivative remainder estimate:

* a quantitative fixed-disk Borel--Caratheodory bound for a nonvanishing
  holomorphic function, and
* an entire canonical normal-form filling of the quotient obtained by removing
  the zeros in a radius-`3 / 2` disk about `2 + it`, with the multiplicities
  supplied by the actual `DirichletZeros` divisor.

It deliberately does not assert the missing uniform outer-circle log-norm bound
and therefore does not instantiate `UniformPrimitiveLogDerivativeRemainderBound`.
-/

namespace MAPZeroFreeSiegelSpine

open Complex Set Metric Filter Topology DirichletZeros MAPLocalZeroWindow
open scoped BigOperators

noncomputable section

/-- A quantitative Borel--Caratheodory logarithmic-derivative lemma on a fixed disk. -/
theorem norm_logDeriv_le_of_log_norm_ratio_le
    {g : ℂ → ℂ} {c s : ℂ} {M : ℝ}
    (hg : DifferentiableOn ℂ g (ball c (3 / 2 : ℝ)))
    (hgn : ∀ z ∈ ball c (3 / 2 : ℝ), g z ≠ 0)
    (hM : 0 < M)
    (hlog : ∀ z ∈ ball c (3 / 2 : ℝ),
      Real.log (‖g z‖ / ‖g c‖) ≤ M)
    (hs : dist s c < 1) :
    ‖logDeriv g s‖ ≤ 40 * M := by
  have hc : c ∈ ball c (3 / 2 : ℝ) := by simp
  have hgc : g c ≠ 0 := hgn c hc
  have hgan : AnalyticOnNhd ℂ g (ball c (3 / 2 : ℝ)) :=
    hg.analyticOnNhd isOpen_ball
  have hld : DifferentiableOn ℂ (logDeriv g) (ball c (3 / 2 : ℝ)) := by
    intro z hz
    have hgz : AnalyticAt ℂ g z := hgan z hz
    simpa only [logDeriv_apply] using!
      (hgz.deriv.div hgz (hgn z hz)).differentiableAt.differentiableWithinAt
  obtain ⟨H, hHc, hH⟩ :=
    hld.isExactOn_ball.with_val_at c (0 : ℂ)
  have hHdiff : DifferentiableOn ℂ H (ball c (3 / 2 : ℝ)) := by
    intro z hz
    exact (hH z hz).differentiableAt.differentiableWithinAt
  let eH : ℂ → ℂ := fun z => Complex.exp (H z)
  have heHdiff : DifferentiableOn ℂ eH (ball c (3 / 2 : ℝ)) := by
    intro z hz
    exact Complex.differentiableAt_exp.comp z
      (hH z hz).differentiableAt |>.differentiableWithinAt
  have heHne : ∀ z ∈ ball c (3 / 2 : ℝ), eH z ≠ 0 := by
    intro z hz
    exact Complex.exp_ne_zero _
  have hlogEq : Set.EqOn (logDeriv eH) (logDeriv g)
      (ball c (3 / 2 : ℝ)) := by
    intro z hz
    rw [show eH = Complex.exp ∘ H by rfl,
      logDeriv_comp Complex.differentiableAt_exp (hH z hz).differentiableAt,
      Complex.logDeriv_exp, Pi.one_apply, one_mul, (hH z hz).deriv]
  obtain ⟨a, ha, hea⟩ :=
    (logDeriv_eqOn_iff heHdiff hg isOpen_ball isPreconnected_ball
      hgn heHne).mp hlogEq
  have haeq : a = (g c)⁻¹ := by
    rw [← one_div]
    apply (eq_div_iff hgc).2
    have hcEq := hea hc
    dsimp [eH] at hcEq
    rw [hHc, Complex.exp_zero] at hcEq
    exact hcEq.symm
  have hHre : ∀ z ∈ ball c (3 / 2 : ℝ),
      (H z).re = Real.log (‖g z‖ / ‖g c‖) := by
    intro z hz
    have hzEq := hea hz
    dsimp [eH] at hzEq
    have hnorm := congrArg norm hzEq
    rw [Complex.norm_exp, norm_mul, haeq, norm_inv] at hnorm
    have hratio : ‖g z‖ / ‖g c‖ = Real.exp (H z).re := by
      simpa [div_eq_inv_mul, mul_comm] using hnorm.symm
    rw [hratio, Real.log_exp]
  let K : ℂ → ℂ := fun w => H (c + w)
  have hKdiff : DifferentiableOn ℂ K (ball 0 (3 / 2 : ℝ)) := by
    intro w hw
    have hcw : c + w ∈ ball c (3 / 2 : ℝ) := by
      simpa [mem_ball, dist_eq_norm] using hw
    exact (hH (c + w) hcw).differentiableAt.comp w
      (differentiableAt_const c |>.add differentiableAt_id) |>.differentiableWithinAt
  have hKmap : MapsTo K (ball 0 (3 / 2 : ℝ)) {z | z.re ≤ M} := by
    intro w hw
    have hcw : c + w ∈ ball c (3 / 2 : ℝ) := by
      simpa [mem_ball, dist_eq_norm] using hw
    change (H (c + w)).re ≤ M
    rw [hHre (c + w) hcw]
    exact hlog (c + w) hcw
  have hKzero : K 0 = 0 := by simpa [K] using hHc
  have hBorel : ∀ w ∈ ball 0 (3 / 2 : ℝ),
      ‖K w‖ ≤ 2 * M * ‖w‖ / ((3 / 2 : ℝ) - ‖w‖) := by
    intro w hw
    exact Complex.borelCaratheodory_zero hM hKdiff hKmap
      (by norm_num) hw hKzero
  have hclosed : closedBall s (1 / 4 : ℝ) ⊆ ball c (3 / 2 : ℝ) := by
    intro z hz
    rw [mem_closedBall] at hz
    rw [mem_ball]
    calc
      dist z c ≤ dist z s + dist s c := dist_triangle z s c
      _ < (1 / 4 : ℝ) + 1 := add_lt_add_of_le_of_lt hz hs
      _ < 3 / 2 := by norm_num
  have hHcircle : ∀ z ∈ sphere s (1 / 4 : ℝ), ‖H z‖ ≤ 10 * M := by
    intro z hz
    have hzclosed : z ∈ closedBall s (1 / 4 : ℝ) := sphere_subset_closedBall hz
    have hzc : z ∈ ball c (3 / 2 : ℝ) := hclosed hzclosed
    have hzcNorm : ‖z - c‖ < (5 / 4 : ℝ) := by
      rw [← dist_eq_norm]
      calc
        dist z c ≤ dist z s + dist s c := dist_triangle z s c
        _ < (1 / 4 : ℝ) + 1 := by
          rw [mem_sphere] at hz
          exact add_lt_add_of_le_of_lt hz.le hs
        _ = 5 / 4 := by norm_num
    have hBw := hBorel (z - c) (by simpa [mem_ball, dist_eq_norm] using hzc)
    change ‖H z‖ ≤ 10 * M
    have hK : K (z - c) = H z := by simp [K]
    rw [hK] at hBw
    have hden : 0 < (3 / 2 : ℝ) - ‖z - c‖ := by linarith
    calc
      ‖H z‖ ≤ 2 * M * ‖z - c‖ / ((3 / 2 : ℝ) - ‖z - c‖) := hBw
      _ ≤ 10 * M := by
        apply (div_le_iff₀ hden).2
        nlinarith [norm_nonneg (z - c), hM.le]
  have hHdc : DiffContOnCl ℂ H (ball s (1 / 4 : ℝ)) :=
    hHdiff.diffContOnCl_ball hclosed
  have hderiv := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (f := H) (c := s) (R := (1 / 4 : ℝ)) (C := 10 * M)
    (by norm_num) hHdc hHcircle
  have hsball : s ∈ ball c (3 / 2 : ℝ) := by
    rw [mem_ball]
    linarith
  rw [(hH s hsball).deriv] at hderiv
  norm_num at hderiv ⊢
  linarith

/-- Fixed Borel center for the local logarithmic derivative. -/
def logDerivativeCenter (t : ℝ) : ℂ := 2 + Complex.I * t

/-- Zeros in the closed radius-3/2 disk about 2+it, cut from the actual compact divisor. -/
def innerZeroSupport {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) : Finset ℂ :=
  (zeroSupport χ (1 / 2) (|t| + 2)).filter fun ρ =>
    dist ρ (logDerivativeCenter t) ≤ 3 / 2

/-- The analytic-multiplicity product for the inner Borel disk. -/
def innerZeroProduct {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) (s : ℂ) : ℂ :=
  ∏ ρ ∈ innerZeroSupport χ t,
    (s - ρ) ^ zeroMultiplicity χ (1 / 2) (|t| + 2) ρ

/-- Raw quotient before filling its removable singularities. -/
def rawInnerDeflated {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) (s : ℂ) : ℂ :=
  regularizedLFunction χ s / innerZeroProduct χ t s

/-- Canonical normal-form filling of the raw quotient's removable singularities. -/
def analyticInnerDeflated {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ → ℂ :=
  toMeromorphicNFOn (rawInnerDeflated χ t) Set.univ

private theorem innerZeroProduct_order
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ)
    {ρ : ℂ} (hρ : ρ ∈ innerZeroSupport χ t) :
    meromorphicOrderAt (innerZeroProduct χ t) ρ =
      (zeroMultiplicity χ (1 / 2) (|t| + 2) ρ : ℤ) := by
  change meromorphicOrderAt
    (fun s : ℂ => ∏ z ∈ innerZeroSupport χ t,
      (s - z) ^ zeroMultiplicity χ (1 / 2) (|t| + 2) z) ρ = _
  rw [meromorphicOrderAt_fun_prod]
  · rw [Finset.sum_eq_single ρ]
    · change meromorphicOrderAt
        ((· - ρ) ^ zeroMultiplicity χ (1 / 2) (|t| + 2) ρ) ρ = _
      exact meromorphicOrderAt_pow_id_sub_const
    · intro z hz hzρ
      have hne : ρ - z ≠ 0 := sub_ne_zero.mpr hzρ.symm
      have han : AnalyticAt ℂ
          (fun s : ℂ => (s - z) ^ zeroMultiplicity χ (1 / 2) (|t| + 2) z) ρ := by
        fun_prop
      rw [han.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
        (pow_ne_zero _ hne)]
    · exact fun h => (h hρ).elim
  · intro z hz
    fun_prop

private theorem innerZeroProduct_ne_zero_of_not_mem
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ)
    {s : ℂ} (hs : s ∉ innerZeroSupport χ t) :
    innerZeroProduct χ t s ≠ 0 := by
  simp only [innerZeroProduct, Finset.prod_ne_zero_iff]
  intro ρ hρ
  exact pow_ne_zero _ (sub_ne_zero.mpr fun h => hs (h ▸ hρ))

private theorem rawInnerDeflated_meromorphic
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    MeromorphicOn (rawInnerDeflated χ t) Set.univ := by
  apply MeromorphicOn.div
  · exact (analyticOnNhd_univ_iff_differentiable.mpr
      (differentiable_regularizedLFunction χ)).meromorphicOn
  · have hpDiff : Differentiable ℂ (innerZeroProduct χ t) := by
      change Differentiable ℂ
        (fun s : ℂ => ∏ ρ ∈ innerZeroSupport χ t,
          (s - ρ) ^ zeroMultiplicity χ (1 / 2) (|t| + 2) ρ)
      fun_prop
    exact (analyticOnNhd_univ_iff_differentiable.mpr hpDiff).meromorphicOn

private theorem meromorphicOrderAt_regularized_eq_multiplicity
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ innerZeroSupport χ t) :
    meromorphicOrderAt (regularizedLFunction χ) ρ =
      (zeroMultiplicity χ (1 / 2) (|t| + 2) ρ : ℤ) := by
  have hbase : ρ ∈ zeroSupport χ (1 / 2) (|t| + 2) :=
    (Finset.mem_filter.mp hρ).1
  have han := (differentiable_regularizedLFunction χ).analyticAt ρ
  rw [han.meromorphicOrderAt_eq,
    PrimitiveExplicitFormulaSpine.analyticOrderAt_eq_zeroMultiplicity
      χ (1 / 2) (|t| + 2) hbase]
  simp

/-- The canonical inner quotient is entire: every pole of the raw quotient is removable. -/
theorem analyticOnNhd_analyticInnerDeflated
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    AnalyticOnNhd ℂ (analyticInnerDeflated χ t) Set.univ := by
  let raw := rawInnerDeflated χ t
  have hraw : MeromorphicOn raw Set.univ := rawInnerDeflated_meromorphic χ t
  have hnf : MeromorphicNFOn (toMeromorphicNFOn raw Set.univ) Set.univ :=
    meromorphicNFOn_toMeromorphicNFOn raw Set.univ
  have hpDiff : Differentiable ℂ (innerZeroProduct χ t) := by
    change Differentiable ℂ
      (fun s : ℂ => ∏ ρ ∈ innerZeroSupport χ t,
        (s - ρ) ^ zeroMultiplicity χ (1 / 2) (|t| + 2) ρ)
    fun_prop
  have hpAn : AnalyticOnNhd ℂ (innerZeroProduct χ t) Set.univ :=
    analyticOnNhd_univ_iff_differentiable.mpr hpDiff
  intro z hz
  apply (hnf hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_toMeromorphicNFOn hraw hz]
  change 0 ≤ meromorphicOrderAt
    (regularizedLFunction χ / innerZeroProduct χ t) z
  rw [meromorphicOrderAt_div
    ((differentiable_regularizedLFunction χ).analyticAt z).meromorphicAt
    (hpAn z (Set.mem_univ z)).meromorphicAt]
  by_cases hzs : z ∈ innerZeroSupport χ t
  · rw [innerZeroProduct_order χ t hzs,
      meromorphicOrderAt_regularized_eq_multiplicity χ hzs]
    simp
  · have hp0 : meromorphicOrderAt (innerZeroProduct χ t) z = 0 := by
      have hpAnalytic : AnalyticAt ℂ (innerZeroProduct χ t) z :=
        hpAn z (Set.mem_univ z)
      exact hpAnalytic.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
        (innerZeroProduct_ne_zero_of_not_mem χ t hzs)
    rw [hp0, sub_zero]
    exact ((differentiable_regularizedLFunction χ).analyticAt z).meromorphicNFAt
      |>.meromorphicOrderAt_nonneg_iff_analyticAt.mpr
        ((differentiable_regularizedLFunction χ).analyticAt z)

end
end MAPZeroFreeSiegelSpine

#print axioms MAPZeroFreeSiegelSpine.norm_logDeriv_le_of_log_norm_ratio_le
#print axioms MAPZeroFreeSiegelSpine.analyticOnNhd_analyticInnerDeflated
