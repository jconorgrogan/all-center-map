import FiniteBlaschkeAlgebra
import WideDiskLFunctionGrowth
import PrimitiveExplicitFormulaSpine
import APZeroDensityCertificate

/-!
# Radius-three finite Blaschke assembly for regularized Dirichlet L-functions

This implements the canonical decomposition missing from Mathlib's individual
`canonicalFactor` API, using the actual compact divisor and analytic
multiplicities already certified in `PrimitiveExplicitFormulaSpine`.
-/

namespace WideDiskBlaschkeAssembly

open Complex Set Metric DirichletZeros PrimitiveExplicitFormulaSpine
open WideDiskLFunctionGrowth FiniteBlaschkeAlgebra
open scoped BigOperators

noncomputable section

def wideZeroSupport
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) : Finset ℂ :=
  (zeroSupport χ (-1) (|t| + 3)).filter fun ρ =>
    dist ρ (wideCenter t) < wideRadius

def wideZeroMultiplicity
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) (ρ : ℂ) : ℕ :=
  zeroMultiplicity χ (-1) (|t| + 3) ρ

def wideBlaschkeProduct
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) (z : ℂ) : ℂ :=
  finiteBlaschkeProduct (wideCenter t) wideRadius
    (wideZeroSupport χ t) (wideZeroMultiplicity χ t) z

def rawWideBlaschkeDeflated
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) (z : ℂ) : ℂ :=
  regularizedLFunction χ z * wideBlaschkeProduct χ t z

def analyticWideBlaschkeDeflated
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ → ℂ :=
  toMeromorphicNFOn (rawWideBlaschkeDeflated χ t) Set.univ

theorem mem_ball_of_mem_wideZeroSupport
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ wideZeroSupport χ t) :
    ρ ∈ Metric.ball (wideCenter t) wideRadius := by
  exact (Finset.mem_filter.mp hρ).2

theorem mem_baseZeroSupport_of_mem_wideZeroSupport
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ wideZeroSupport χ t) :
    ρ ∈ zeroSupport χ (-1) (|t| + 3) :=
  (Finset.mem_filter.mp hρ).1

theorem wideCenter_not_mem_wideZeroSupport
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    wideCenter t ∉ wideZeroSupport χ t := by
  intro hc
  have hbase := mem_baseZeroSupport_of_mem_wideZeroSupport χ hc
  have hre := MAPMellinDetectorLeaf.re_lt_one_of_mem_zeroSupport χ hbase
  simpa [wideCenter] using hre

/-- Every numerator zero in the open radius-three disk belongs to the literal
filtered compact support. -/
theorem mem_wideZeroSupport_of_eq_zero_of_mem_ball
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {t : ℝ} {z : ℂ} (hz : z ∈ Metric.ball (wideCenter t) wideRadius)
    (hzero : regularizedLFunction χ z = 0) :
    z ∈ wideZeroSupport χ t := by
  have hnorm : ‖z - wideCenter t‖ < 3 := by
    simpa [Metric.mem_ball, dist_eq_norm, wideRadius] using hz
  have hreDiff : |z.re - 2| < 3 := by
    simpa [wideCenter] using
      (Complex.abs_re_le_norm (z - wideCenter t)).trans_lt hnorm
  have himDiff : |z.im - t| < 3 := by
    simpa [wideCenter] using
      (Complex.abs_im_le_norm (z - wideCenter t)).trans_lt hnorm
  have hzlo : -1 ≤ z.re := by
    have := neg_le_abs (z.re - 2)
    linarith
  have hzhi : z.re ≤ 1 := by
    by_contra hnot
    have hone : 1 ≤ z.re := le_of_not_ge hnot
    exact (MAPMellinDetectorLeaf.regularizedLFunction_ne_zero_of_one_le_re
      χ hone) hzero
  have hzabs : |z.im| ≤ |t| + 3 := by
    have htri : |z.im| ≤ |z.im - t| + |t| := by
      calc
        |z.im| = |(z.im - t) + t| := by ring_nf
        _ ≤ |z.im - t| + |t| := abs_add_le _ _
    linarith
  have hzrect : z ∈ zeroRectangle (-1) (|t| + 3) := by
    constructor
    · exact ⟨hzlo, hzhi⟩
    · exact (abs_le.mp hzabs)
  have hbase : z ∈ zeroSupport χ (-1) (|t| + 3) :=
    (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
      χ (-1) (|t| + 3) hzrect).2 hzero
  rw [wideZeroSupport, Finset.mem_filter]
  exact ⟨hbase, hz⟩

private theorem meromorphicOn_shiftedCanonicalFactor
    (c : ℂ) (R : ℝ) (ρ : ℂ) :
    MeromorphicOn (shiftedCanonicalFactor c R ρ) Set.univ := by
  intro z hz
  unfold shiftedCanonicalFactor Complex.canonicalFactor
  fun_prop

private theorem meromorphicOrderAt_shiftedCanonicalFactor_self
    {c ρ : ℂ} {R : ℝ} (hρ : ρ ∈ Metric.ball c R) :
    meromorphicOrderAt (shiftedCanonicalFactor c R ρ) ρ = -1 := by
  have hρ' : ρ - c ∈ Metric.ball (0 : ℂ) R := by
    simpa [Metric.mem_ball, dist_eq_norm] using hρ
  have hcomp : shiftedCanonicalFactor c R ρ =
      Complex.canonicalFactor R (ρ - c) ∘ (fun z : ℂ => z - c) := rfl
  rw [hcomp, meromorphicOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by simp)]
  simpa using Complex.meromorphicOrderAt_canonicalFactor hρ'

private theorem analyticAt_shiftedCanonicalFactor_of_ne
    {c ρ z : ℂ} {R : ℝ} (hzρ : z ≠ ρ) :
    AnalyticAt ℂ (shiftedCanonicalFactor c R ρ) z := by
  have hne : z - c ≠ ρ - c := fun h => hzρ (sub_left_inj.mp h)
  have houter : z - c ∈ ({ρ - c} : Set ℂ)ᶜ := hne
  have hcan := Complex.analyticOnNhd_canonicalFactor R (ρ - c)
    (z - c) houter
  change AnalyticAt ℂ
    (Complex.canonicalFactor R (ρ - c) ∘ (fun w : ℂ => w - c)) z
  have hsub : AnalyticAt ℂ (fun w : ℂ => w - c) z := by fun_prop
  exact AnalyticAt.comp (f := fun w : ℂ => w - c) (x := z) hcan hsub

private theorem shiftedCanonicalFactor_ne_zero_in_closedBall
    {c ρ z : ℂ} {R : ℝ}
    (hρ : ρ ∈ Metric.ball c R) (hz : z ∈ Metric.closedBall c R)
    (hzρ : z ≠ ρ) :
    shiftedCanonicalFactor c R ρ z ≠ 0 := by
  apply Complex.canonicalFactor_ne_zero
  · simpa [Metric.mem_ball, dist_eq_norm] using hρ
  · simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  · intro h
    exact hzρ (sub_left_inj.mp h)

private theorem meromorphicOn_wideBlaschkeProduct
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    MeromorphicOn (wideBlaschkeProduct χ t) Set.univ := by
  change MeromorphicOn
    (fun z : ℂ => ∏ ρ ∈ wideZeroSupport χ t,
      (shiftedCanonicalFactor (wideCenter t) wideRadius ρ z) ^
        wideZeroMultiplicity χ t ρ) Set.univ
  exact MeromorphicOn.fun_prod
    (s := wideZeroSupport χ t) fun ρ hρ =>
      (meromorphicOn_shiftedCanonicalFactor
        (wideCenter t) wideRadius ρ).pow (wideZeroMultiplicity χ t ρ)

private theorem meromorphicOn_rawWideBlaschkeDeflated
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    MeromorphicOn (rawWideBlaschkeDeflated χ t) Set.univ := by
  apply MeromorphicOn.mul
  · exact (analyticOnNhd_univ_iff_differentiable.mpr
      (differentiable_regularizedLFunction χ)).meromorphicOn
  · exact meromorphicOn_wideBlaschkeProduct χ t

private theorem meromorphicOrderAt_regularized_eq_wideMultiplicity
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ wideZeroSupport χ t) :
    meromorphicOrderAt (regularizedLFunction χ) ρ =
      (wideZeroMultiplicity χ t ρ : ℤ) := by
  have hbase := mem_baseZeroSupport_of_mem_wideZeroSupport χ hρ
  have han := (differentiable_regularizedLFunction χ).analyticAt ρ
  rw [han.meromorphicOrderAt_eq,
    PrimitiveExplicitFormulaSpine.analyticOrderAt_eq_zeroMultiplicity
      χ (-1) (|t| + 3) hbase]
  simp [wideZeroMultiplicity]

private theorem meromorphicOrderAt_wideBlaschkeProduct_at_mem
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ wideZeroSupport χ t) :
    meromorphicOrderAt (wideBlaschkeProduct χ t) ρ =
      -(wideZeroMultiplicity χ t ρ : ℤ) := by
  change meromorphicOrderAt
    (fun z : ℂ => ∏ τ ∈ wideZeroSupport χ t,
      (shiftedCanonicalFactor (wideCenter t) wideRadius τ z) ^
        wideZeroMultiplicity χ t τ) ρ = _
  rw [meromorphicOrderAt_fun_prod]
  · rw [Finset.sum_eq_single ρ]
    · rw [show (fun z =>
          shiftedCanonicalFactor (wideCenter t) wideRadius ρ z ^
            wideZeroMultiplicity χ t ρ) =
          (shiftedCanonicalFactor (wideCenter t) wideRadius ρ) ^
            wideZeroMultiplicity χ t ρ by rfl,
        meromorphicOrderAt_pow]
      · rw [meromorphicOrderAt_shiftedCanonicalFactor_self
          (mem_ball_of_mem_wideZeroSupport χ hρ)]
        change
          (((wideZeroMultiplicity χ t ρ : ℤ) : WithTop ℤ) *
            ((-1 : ℤ) : WithTop ℤ)) =
          ((-(wideZeroMultiplicity χ t ρ : ℤ) : ℤ) : WithTop ℤ)
        rw [← WithTop.coe_mul]
        congr 1
        exact mul_neg_one _
      · exact (meromorphicOn_shiftedCanonicalFactor
          (wideCenter t) wideRadius ρ) ρ (Set.mem_univ ρ)
    · intro τ hτ hτρ
      have han := analyticAt_shiftedCanonicalFactor_of_ne
        (c := wideCenter t) (R := wideRadius) hτρ.symm
      have hρclosed : ρ ∈
          Metric.closedBall (wideCenter t) wideRadius := by
        rw [Metric.mem_closedBall]
        exact (Metric.mem_ball.mp
          (mem_ball_of_mem_wideZeroSupport χ hρ)).le
      have hne := shiftedCanonicalFactor_ne_zero_in_closedBall
        (mem_ball_of_mem_wideZeroSupport χ hτ) hρclosed hτρ.symm
      have hanPow := han.pow (wideZeroMultiplicity χ t τ)
      change meromorphicOrderAt
        ((shiftedCanonicalFactor (wideCenter t) wideRadius τ) ^
          wideZeroMultiplicity χ t τ) ρ = 0
      rw [hanPow.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
        (pow_ne_zero _ hne)]
    · exact fun h => (h hρ).elim
  · intro τ hτ
    exact ((meromorphicOn_shiftedCanonicalFactor
      (wideCenter t) wideRadius τ).pow _) ρ (Set.mem_univ ρ)

private theorem analyticAt_wideBlaschkeProduct_of_not_mem_closedBall
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {t : ℝ} {z : ℂ}
    (hz : z ∈ Metric.closedBall (wideCenter t) wideRadius)
    (hzF : z ∉ wideZeroSupport χ t) :
    AnalyticAt ℂ (wideBlaschkeProduct χ t) z := by
  change AnalyticAt ℂ
    (fun w : ℂ => ∏ ρ ∈ wideZeroSupport χ t,
      (shiftedCanonicalFactor (wideCenter t) wideRadius ρ w) ^
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
  exact (analyticAt_shiftedCanonicalFactor_of_ne hzρ).pow _

private theorem wideBlaschkeProduct_ne_zero_of_not_mem_closedBall
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {t : ℝ} {z : ℂ}
    (hz : z ∈ Metric.closedBall (wideCenter t) wideRadius)
    (hzF : z ∉ wideZeroSupport χ t) :
    wideBlaschkeProduct χ t z ≠ 0 := by
  simp only [wideBlaschkeProduct, finiteBlaschkeProduct,
    Finset.prod_ne_zero_iff]
  intro ρ hρ
  exact pow_ne_zero _ (shiftedCanonicalFactor_ne_zero_in_closedBall
    (mem_ball_of_mem_wideZeroSupport χ hρ) hz
    (fun h => hzF (h ▸ hρ)))

private theorem meromorphicOrderAt_raw_eq_zero_in_ball
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {t : ℝ} {z : ℂ}
    (hz : z ∈ Metric.ball (wideCenter t) wideRadius) :
    meromorphicOrderAt (rawWideBlaschkeDeflated χ t) z = 0 := by
  have hnumM := ((differentiable_regularizedLFunction χ).analyticAt z).meromorphicAt
  have hprodM := (meromorphicOn_wideBlaschkeProduct χ t) z (Set.mem_univ z)
  change meromorphicOrderAt
    (regularizedLFunction χ * wideBlaschkeProduct χ t) z = 0
  rw [meromorphicOrderAt_mul hnumM hprodM]
  by_cases hzF : z ∈ wideZeroSupport χ t
  · rw [meromorphicOrderAt_regularized_eq_wideMultiplicity χ hzF,
      meromorphicOrderAt_wideBlaschkeProduct_at_mem χ hzF]
    simp
  · have hL : regularizedLFunction χ z ≠ 0 := fun hzero =>
      hzF (mem_wideZeroSupport_of_eq_zero_of_mem_ball χ hz hzero)
    have hzclosed : z ∈
        Metric.closedBall (wideCenter t) wideRadius := by
      rw [Metric.mem_closedBall]
      exact (Metric.mem_ball.mp hz).le
    have hprodAn := analyticAt_wideBlaschkeProduct_of_not_mem_closedBall
      χ hzclosed hzF
    have hprod0 := wideBlaschkeProduct_ne_zero_of_not_mem_closedBall
      χ hzclosed hzF
    rw [((differentiable_regularizedLFunction χ).analyticAt z).meromorphicNFAt
        |>.meromorphicOrderAt_eq_zero_iff.mpr hL,
      hprodAn.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hprod0]
    simp

/-- The canonical filling is analytic throughout the radius-three disk. -/
theorem analyticOnNhd_analyticWideBlaschkeDeflated_ball
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    AnalyticOnNhd ℂ (analyticWideBlaschkeDeflated χ t)
      (Metric.ball (wideCenter t) wideRadius) := by
  have hraw := meromorphicOn_rawWideBlaschkeDeflated χ t
  have hnf := meromorphicNFOn_toMeromorphicNFOn
    (rawWideBlaschkeDeflated χ t) Set.univ
  intro z hz
  apply (hnf (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  change 0 ≤ meromorphicOrderAt
    (toMeromorphicNFOn (rawWideBlaschkeDeflated χ t) Set.univ) z
  rw [meromorphicOrderAt_toMeromorphicNFOn hraw (Set.mem_univ z),
    meromorphicOrderAt_raw_eq_zero_in_ball χ hz]

/-- All numerator zeros in the disk are cancelled, so the filled factor is
nonzero throughout the disk. -/
theorem analyticWideBlaschkeDeflated_ne_zero_ball
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ)
    {z : ℂ} (hz : z ∈ Metric.ball (wideCenter t) wideRadius) :
    analyticWideBlaschkeDeflated χ t z ≠ 0 := by
  have han := analyticOnNhd_analyticWideBlaschkeDeflated_ball χ t z hz
  apply han.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp
  unfold analyticWideBlaschkeDeflated
  rw [meromorphicOrderAt_toMeromorphicNFOn
    (meromorphicOn_rawWideBlaschkeDeflated χ t) (Set.mem_univ z),
    meromorphicOrderAt_raw_eq_zero_in_ball χ hz]

private theorem analyticWideBlaschkeDeflated_eq_raw_of_not_mem
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {t : ℝ} {z : ℂ}
    (hz : z ∈ Metric.closedBall (wideCenter t) wideRadius)
    (hzF : z ∉ wideZeroSupport χ t) :
    analyticWideBlaschkeDeflated χ t z = rawWideBlaschkeDeflated χ t z := by
  have hrawAn : AnalyticAt ℂ (rawWideBlaschkeDeflated χ t) z := by
    exact ((differentiable_regularizedLFunction χ).analyticAt z).mul
      (analyticAt_wideBlaschkeProduct_of_not_mem_closedBall χ hz hzF)
  unfold analyticWideBlaschkeDeflated
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt
    (meromorphicOn_rawWideBlaschkeDeflated χ t) (Set.mem_univ z),
    toMeromorphicNFAt_eq_self.mpr hrawAn.meromorphicNFAt]

/-- Exact boundary norm preservation for the filled radius-three Blaschke
factor. -/
theorem norm_analyticWideBlaschkeDeflated_eq_regularized_on_sphere
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {t : ℝ} {z : ℂ}
    (hz : z ∈ Metric.sphere (wideCenter t) wideRadius) :
    ‖analyticWideBlaschkeDeflated χ t z‖ = ‖regularizedLFunction χ z‖ := by
  have hzclosed : z ∈ Metric.closedBall (wideCenter t) wideRadius :=
    Metric.sphere_subset_closedBall hz
  have hzF : z ∉ wideZeroSupport χ t := by
    intro hzmem
    have hzball := mem_ball_of_mem_wideZeroSupport χ hzmem
    rw [Metric.mem_ball] at hzball
    rw [Metric.mem_sphere] at hz
    linarith
  rw [analyticWideBlaschkeDeflated_eq_raw_of_not_mem χ hzclosed hzF]
  unfold rawWideBlaschkeDeflated wideBlaschkeProduct
  exact norm_mul_finiteBlaschkeProduct_eq_on_sphere
    (regularizedLFunction χ)
    (fun ρ hρ => mem_ball_of_mem_wideZeroSupport χ hρ) hz

/-- Exact center monotonicity: removal of interior zeros cannot decrease the
norm at the Euler-product center. -/
theorem norm_regularizedLFunction_center_le_analyticWideBlaschkeDeflated
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖regularizedLFunction χ (wideCenter t)‖ ≤
      ‖analyticWideBlaschkeDeflated χ t (wideCenter t)‖ := by
  have hcclosed : wideCenter t ∈
      Metric.closedBall (wideCenter t) wideRadius := by
    simp [wideRadius]
  have hcF := wideCenter_not_mem_wideZeroSupport χ t
  rw [analyticWideBlaschkeDeflated_eq_raw_of_not_mem χ hcclosed hcF]
  unfold rawWideBlaschkeDeflated wideBlaschkeProduct
  exact norm_le_norm_mul_finiteBlaschkeProduct_center
    (regularizedLFunction χ) (by norm_num [wideRadius])
    (fun ρ hρ => mem_ball_of_mem_wideZeroSupport χ hρ) hcF

end

end WideDiskBlaschkeAssembly
