import WideDiskBlaschkeGrowth

/-!
# Exact local logarithmic derivative from the radius-three Blaschke fill
-/

namespace WideDiskLocalLogDerivative

open Complex ComplexConjugate Set Metric Filter Topology DirichletZeros
  PrimitiveExplicitFormulaSpine
open WideDiskLFunctionGrowth FiniteBlaschkeAlgebra WideDiskBlaschkeAssembly
open WideDiskBlaschkeGrowth MAPLocalZeroWindow
open ZeroDistanceLogDerivativeBounds
open scoped BigOperators

noncomputable section

def shiftedCanonicalNumerator (c ρ : ℂ) (R : ℝ) (z : ℂ) : ℂ :=
  (R : ℂ) ^ 2 - conj (ρ - c) * (z - c)

private theorem shiftedCanonicalFactor_eq_num_div
    (c ρ : ℂ) (R : ℝ) :
    shiftedCanonicalFactor c R ρ = fun z =>
      shiftedCanonicalNumerator c ρ R z / ((R : ℂ) * (z - ρ)) := by
  funext z
  unfold shiftedCanonicalFactor Complex.canonicalFactor
    shiftedCanonicalNumerator
  congr 1
  ring

/-- A canonical factor contributes the negative pole term plus the
logarithmic derivative of its zero-free numerator. -/
theorem logDeriv_shiftedCanonicalFactor_add_inv
    {c ρ s : ℂ} {R : ℝ} (hR : R ≠ 0) (hsρ : s ≠ ρ)
    (hnum : shiftedCanonicalNumerator c ρ R s ≠ 0) :
    logDeriv (shiftedCanonicalFactor c R ρ) s + 1 / (s - ρ) =
      logDeriv (shiftedCanonicalNumerator c ρ R) s := by
  rw [shiftedCanonicalFactor_eq_num_div]
  have hden : (R : ℂ) * (s - ρ) ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr hR) (sub_ne_zero.mpr hsρ)
  rw [logDeriv_div s hnum hden
    (by unfold shiftedCanonicalNumerator; fun_prop) (by fun_prop)]
  have hlinear :
      logDeriv (fun z : ℂ => (R : ℂ) * (z - ρ)) s = 1 / (s - ρ) := by
    rw [logDeriv_const_mul s (R : ℂ) (ofReal_ne_zero.mpr hR)]
    simp [logDeriv_apply]
  rw [hlinear]
  ring

/-- The canonical numerator has logarithmic derivative of norm at most one
on the radius-two disk when its pole lies in the radius-three disk. -/
theorem norm_logDeriv_shiftedCanonicalNumerator_le_one
    {c ρ s : ℂ} (hρ : ρ ∈ Metric.ball c 3)
    (hs : s ∈ Metric.ball c 2) :
    ‖logDeriv (shiftedCanonicalNumerator c ρ 3) s‖ ≤ 1 := by
  have hρn : ‖ρ - c‖ < 3 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hρ
  have hsn : ‖s - c‖ < 2 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hs
  have hprod : ‖conj (ρ - c) * (s - c)‖ < 6 := by
    rw [norm_mul, norm_conj]
    nlinarith [norm_nonneg (ρ - c), norm_nonneg (s - c)]
  have hdenLower : 3 < ‖shiftedCanonicalNumerator c ρ 3 s‖ := by
    have hrev := norm_sub_norm_le
      ((3 : ℂ) ^ 2) (conj (ρ - c) * (s - c))
    have hrev' :
        9 - ‖conj (ρ - c) * (s - c)‖ ≤
          ‖shiftedCanonicalNumerator c ρ 3 s‖ := by
      norm_num [shiftedCanonicalNumerator, pow_two] at hrev ⊢
      exact hrev
    linarith
  have hderiv : deriv (shiftedCanonicalNumerator c ρ 3) s = -conj (ρ - c) := by
    have hlin : HasDerivAt (fun z : ℂ => z - c) 1 s :=
      (hasDerivAt_id s).sub_const c
    have hmul : HasDerivAt
        (fun z : ℂ => conj (ρ - c) * (z - c)) (conj (ρ - c)) s := by
      convert (hasDerivAt_const s (conj (ρ - c))).mul hlin using 1 <;> simp
    have hconst : HasDerivAt (fun _z : ℂ => (3 : ℂ) ^ 2) 0 s :=
      hasDerivAt_const s _
    change deriv
      (fun z : ℂ => (3 : ℂ) ^ 2 - conj (ρ - c) * (z - c)) s = _
    simpa only [Pi.sub_apply, zero_sub] using (hconst.sub hmul).deriv
  rw [logDeriv_apply, hderiv, norm_div, norm_neg, norm_conj]
  exact (div_le_one (by positivity)).2 (hρn.le.trans (le_of_lt hdenLower))

private theorem wideBlaschkeProduct_ne_zero_at
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {t : ℝ} {s : ℂ}
    (hs : s ∈ Metric.ball (wideCenter t) 2)
    (hsF : s ∉ wideZeroSupport χ t) :
    wideBlaschkeProduct χ t s ≠ 0 := by
  simp only [wideBlaschkeProduct, finiteBlaschkeProduct,
    Finset.prod_ne_zero_iff]
  intro ρ hρ
  apply pow_ne_zero
  apply Complex.canonicalFactor_ne_zero
  · simpa [shiftedCanonicalFactor, Metric.mem_ball, dist_eq_norm, wideRadius]
      using mem_ball_of_mem_wideZeroSupport χ hρ
  · have hsclosed : s - wideCenter t ∈ Metric.closedBall (0 : ℂ) wideRadius := by
      rw [Metric.mem_closedBall, dist_zero_right]
      have := Metric.mem_ball.mp hs
      simpa [dist_eq_norm, wideRadius] using this.le.trans (by norm_num)
    exact hsclosed
  · intro h
    apply hsF
    have hsρ : s = ρ := sub_left_inj.mp h
    rwa [hsρ]

private theorem regularizedLFunction_ne_zero_at
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {t : ℝ} {s : ℂ}
    (hs : s ∈ Metric.ball (wideCenter t) 2)
    (hsF : s ∉ wideZeroSupport χ t) :
    regularizedLFunction χ s ≠ 0 := by
  intro hzero
  apply hsF
  apply mem_wideZeroSupport_of_eq_zero_of_mem_ball χ
  · rw [Metric.mem_ball] at hs ⊢
    simpa [wideRadius] using hs.trans (by norm_num)
  · exact hzero

private theorem logDeriv_analyticWide_eq_raw_at
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {t : ℝ} {s : ℂ}
    (hs : s ∈ Metric.ball (wideCenter t) 2)
    (hsF : s ∉ wideZeroSupport χ t) :
    logDeriv (analyticWideBlaschkeDeflated χ t) s =
      logDeriv (rawWideBlaschkeDeflated χ t) s := by
  have hprodAn : AnalyticAt ℂ (wideBlaschkeProduct χ t) s := by
    change AnalyticAt ℂ
      (fun z : ℂ => ∏ ρ ∈ wideZeroSupport χ t,
        shiftedCanonicalFactor (wideCenter t) wideRadius ρ z ^
          wideZeroMultiplicity χ t ρ) s
    apply Finset.analyticAt_fun_prod
    intro ρ hρ
    have hsρ : s ≠ ρ := by
      intro h
      apply hsF
      rwa [h]
    change AnalyticAt ℂ
      ((shiftedCanonicalFactor (wideCenter t) wideRadius ρ) ^
        wideZeroMultiplicity χ t ρ) s
    have hne : s - wideCenter t ≠ ρ - wideCenter t :=
      fun h => hsρ (sub_left_inj.mp h)
    have hcan := Complex.analyticOnNhd_canonicalFactor wideRadius
      (ρ - wideCenter t) (s - wideCenter t) hne
    have hsub : AnalyticAt ℂ (fun z : ℂ => z - wideCenter t) s := by fun_prop
    exact (AnalyticAt.comp (f := fun z : ℂ => z - wideCenter t)
      (x := s) hcan hsub).pow _
  have hrawAn : AnalyticAt ℂ (rawWideBlaschkeDeflated χ t) s :=
    ((differentiable_regularizedLFunction χ).analyticAt s).mul hprodAn
  have hrawMer : MeromorphicOn (rawWideBlaschkeDeflated χ t) Set.univ := by
    apply MeromorphicOn.mul
    · exact (analyticOnNhd_univ_iff_differentiable.mpr
        (differentiable_regularizedLFunction χ)).meromorphicOn
    · change MeromorphicOn
        (fun z : ℂ => ∏ ρ ∈ wideZeroSupport χ t,
          shiftedCanonicalFactor (wideCenter t) wideRadius ρ z ^
            wideZeroMultiplicity χ t ρ) Set.univ
      apply MeromorphicOn.fun_prod
      intro ρ hρ
      change MeromorphicOn
        ((shiftedCanonicalFactor (wideCenter t) wideRadius ρ) ^
          wideZeroMultiplicity χ t ρ) Set.univ
      apply MeromorphicOn.pow
      intro z hz
      unfold shiftedCanonicalFactor Complex.canonicalFactor
      fun_prop
  have heqNF : toMeromorphicNFAt (rawWideBlaschkeDeflated χ t) s =
      rawWideBlaschkeDeflated χ t :=
    toMeromorphicNFAt_eq_self.mpr hrawAn.meromorphicNFAt
  have hevent : analyticWideBlaschkeDeflated χ t =ᶠ[𝓝 s]
      rawWideBlaschkeDeflated χ t := by
    exact (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hrawMer
      (Set.mem_univ s)).trans (Filter.Eventually.of_forall fun z => by rw [heqNF])
  unfold logDeriv
  simp only [Pi.div_apply]
  rw [hevent.deriv_eq, hevent.eq_of_nhds]

/-- Exact local zero-deflated identity.  The only difference between the
Blaschke fill and subtracting the literal local pole sum is the sum of the
zero-free canonical numerator logarithmic derivatives. -/
theorem localDeflatedLogDeriv_eq_blaschke_sub_correction
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {t : ℝ} {s : ℂ}
    (hs : s ∈ Metric.ball (wideCenter t) 2)
    (hsF : s ∉ wideZeroSupport χ t) :
    logDeriv (regularizedLFunction χ) s -
        ∑ ρ ∈ wideZeroSupport χ t,
          (wideZeroMultiplicity χ t ρ : ℂ) / (s - ρ) =
      logDeriv (analyticWideBlaschkeDeflated χ t) s -
        ∑ ρ ∈ wideZeroSupport χ t,
          (wideZeroMultiplicity χ t ρ : ℂ) *
            logDeriv (shiftedCanonicalNumerator (wideCenter t) ρ wideRadius) s := by
  have hL := regularizedLFunction_ne_zero_at χ hs hsF
  have hB := wideBlaschkeProduct_ne_zero_at χ hs hsF
  rw [logDeriv_analyticWide_eq_raw_at χ hs hsF]
  change logDeriv (regularizedLFunction χ) s - _ =
    logDeriv (fun z => regularizedLFunction χ z * wideBlaschkeProduct χ t z) s - _
  rw [logDeriv_mul s hL hB
    (differentiable_regularizedLFunction χ).differentiableAt]
  · change logDeriv (regularizedLFunction χ) s - _ =
      (logDeriv (regularizedLFunction χ) s +
        logDeriv (fun z : ℂ => ∏ ρ ∈ wideZeroSupport χ t,
          shiftedCanonicalFactor (wideCenter t) wideRadius ρ z ^
            wideZeroMultiplicity χ t ρ) s) - _
    rw [logDeriv_prod]
    ·
      have hfactor (ρ : ℂ) (hρ : ρ ∈ wideZeroSupport χ t) :
          logDeriv (shiftedCanonicalFactor (wideCenter t) wideRadius ρ) s +
              1 / (s - ρ) =
            logDeriv (shiftedCanonicalNumerator
              (wideCenter t) ρ wideRadius) s := by
        apply logDeriv_shiftedCanonicalFactor_add_inv
        · norm_num [wideRadius]
        · intro h
          apply hsF
          rwa [h]
        · have hρball := mem_ball_of_mem_wideZeroSupport χ hρ
          have hsclosed : s ∈ Metric.closedBall (wideCenter t) wideRadius := by
            rw [Metric.mem_closedBall]
            exact (Metric.mem_ball.mp hs).le.trans (by norm_num [wideRadius])
          have hcan := Complex.canonicalFactor_ne_zero
            (by simpa [Metric.mem_ball, dist_eq_norm] using hρball)
            (by simpa [Metric.mem_closedBall, dist_eq_norm] using hsclosed)
            (fun h => (show s ≠ ρ by intro e; apply hsF; rwa [e])
              (sub_left_inj.mp h))
          intro hnum
          apply hcan
          change shiftedCanonicalFactor (wideCenter t) wideRadius ρ s = 0
          rw [shiftedCanonicalFactor_eq_num_div]
          change shiftedCanonicalNumerator (wideCenter t) ρ wideRadius s /
            ((wideRadius : ℂ) * (s - ρ)) = 0
          rw [hnum, zero_div]
      have hsum :
          (∑ ρ ∈ wideZeroSupport χ t,
              logDeriv (fun z =>
                shiftedCanonicalFactor (wideCenter t) wideRadius ρ z ^
                  wideZeroMultiplicity χ t ρ) s) +
            (∑ ρ ∈ wideZeroSupport χ t,
              (wideZeroMultiplicity χ t ρ : ℂ) / (s - ρ)) =
          ∑ ρ ∈ wideZeroSupport χ t,
            (wideZeroMultiplicity χ t ρ : ℂ) *
              logDeriv (shiftedCanonicalNumerator
                (wideCenter t) ρ wideRadius) s := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro ρ hρ
        have hsρ : s ≠ ρ := by intro h; apply hsF; rwa [h]
        have hne : s - wideCenter t ≠ ρ - wideCenter t :=
          fun h => hsρ (sub_left_inj.mp h)
        have hcan := Complex.analyticOnNhd_canonicalFactor wideRadius
          (ρ - wideCenter t) (s - wideCenter t) hne
        have hsub : AnalyticAt ℂ (fun z : ℂ => z - wideCenter t) s := by fun_prop
        have hdiff : DifferentiableAt ℂ
            (shiftedCanonicalFactor (wideCenter t) wideRadius ρ) s :=
          (AnalyticAt.comp (f := fun z : ℂ => z - wideCenter t)
            (x := s) hcan hsub).differentiableAt
        rw [logDeriv_fun_pow hdiff]
        have heq := hfactor ρ hρ
        push_cast
        linear_combination (wideZeroMultiplicity χ t ρ : ℂ) * heq
      linear_combination -hsum
    · intro ρ hρ
      have hp := wideBlaschkeProduct_ne_zero_at χ hs hsF
      simp only [wideBlaschkeProduct, finiteBlaschkeProduct,
        Finset.prod_ne_zero_iff] at hp
      exact hp ρ hρ
    · intro ρ hρ
      have hsρ : s ≠ ρ := by intro h; apply hsF; rwa [h]
      change DifferentiableAt ℂ
        ((shiftedCanonicalFactor (wideCenter t) wideRadius ρ) ^
          wideZeroMultiplicity χ t ρ) s
      have hne : s - wideCenter t ≠ ρ - wideCenter t :=
        fun h => hsρ (sub_left_inj.mp h)
      have hcan := Complex.analyticOnNhd_canonicalFactor wideRadius
        (ρ - wideCenter t) (s - wideCenter t) hne
      have hsub : AnalyticAt ℂ (fun z : ℂ => z - wideCenter t) s := by fun_prop
      exact ((AnalyticAt.comp (f := fun z : ℂ => z - wideCenter t)
        (x := s) hcan hsub).pow _).differentiableAt
  · change DifferentiableAt ℂ
      (fun z : ℂ => ∏ ρ ∈ wideZeroSupport χ t,
        shiftedCanonicalFactor (wideCenter t) wideRadius ρ z ^
          wideZeroMultiplicity χ t ρ) s
    apply DifferentiableAt.fun_finsetProd
    intro ρ hρ
    have hsρ : s ≠ ρ := by intro h; apply hsF; rwa [h]
    change DifferentiableAt ℂ
      ((shiftedCanonicalFactor (wideCenter t) wideRadius ρ) ^
        wideZeroMultiplicity χ t ρ) s
    have hne : s - wideCenter t ≠ ρ - wideCenter t :=
      fun h => hsρ (sub_left_inj.mp h)
    have hcan := Complex.analyticOnNhd_canonicalFactor wideRadius
      (ρ - wideCenter t) (s - wideCenter t) hne
    have hsub : AnalyticAt ℂ (fun z : ℂ => z - wideCenter t) s := by fun_prop
    exact ((AnalyticAt.comp (f := fun z : ℂ => z - wideCenter t)
      (x := s) hcan hsub).pow _).differentiableAt

/-- Fully quantitative bound for the literal locally zero-deflated
logarithmic derivative.  The remaining finite term is exactly the local
multiplicity mass, with coefficient one. -/
theorem norm_localDeflatedLogDeriv_le
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {t : ℝ} {s : ℂ} (hs : s ∈ Metric.ball (wideCenter t) 2)
    (hsF : s ∉ wideZeroSupport χ t) :
    ‖logDeriv (regularizedLFunction χ) s -
        ∑ ρ ∈ wideZeroSupport χ t,
          (wideZeroMultiplicity χ t ρ : ℂ) / (s - ρ)‖ ≤
      20 * (Real.log 21600 +
        2 * Real.log (arithmeticScale q t)) +
      ∑ ρ ∈ wideZeroSupport χ t,
        (wideZeroMultiplicity χ t ρ : ℝ) := by
  have hid := localDeflatedLogDeriv_eq_blaschke_sub_correction χ hs hsF
  rw [hid]
  have hB := norm_logDeriv_analyticWideBlaschkeDeflated_le χ hχ
    (Metric.mem_ball.mp hs)
  have hcorr :
      ‖∑ ρ ∈ wideZeroSupport χ t,
          (wideZeroMultiplicity χ t ρ : ℂ) *
            logDeriv (shiftedCanonicalNumerator
              (wideCenter t) ρ wideRadius) s‖ ≤
        ∑ ρ ∈ wideZeroSupport χ t,
          (wideZeroMultiplicity χ t ρ : ℝ) := by
    calc
      ‖∑ ρ ∈ wideZeroSupport χ t,
          (wideZeroMultiplicity χ t ρ : ℂ) *
            logDeriv (shiftedCanonicalNumerator
              (wideCenter t) ρ wideRadius) s‖ ≤
          ∑ ρ ∈ wideZeroSupport χ t,
            ‖(wideZeroMultiplicity χ t ρ : ℂ) *
              logDeriv (shiftedCanonicalNumerator
                (wideCenter t) ρ wideRadius) s‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ wideZeroSupport χ t,
          (wideZeroMultiplicity χ t ρ : ℝ) := by
        apply Finset.sum_le_sum
        intro ρ hρ
        rw [norm_mul, norm_natCast]
        have hnum := norm_logDeriv_shiftedCanonicalNumerator_le_one
          (c := wideCenter t) (ρ := ρ) (s := s)
          (by simpa [wideRadius] using mem_ball_of_mem_wideZeroSupport χ hρ) hs
        exact (mul_le_mul_of_nonneg_left hnum (Nat.cast_nonneg _)).trans_eq
          (mul_one _)
  exact (norm_sub_le _ _).trans (add_le_add hB hcorr)

/-- Exact signed bridge from the local Blaschke fill to the literal compact
rectangle quotient.  No triangle inequality has yet been applied: the final
two finite sums retain their signs, so buffered-aperture cancellation remains
available to the endpoint argument. -/
theorem logDeriv_compactZeroDeflated_eq_blaschke_add_signedMismatch
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a H t : ℝ} {s : ℂ}
    (hs : s ∈ Metric.ball (wideCenter t) 2)
    (hsF : s ∉ wideZeroSupport χ t)
    (hL : regularizedLFunction χ s ≠ 0) :
    logDeriv (compactZeroDeflatedRegularizedLFunction χ a H) s =
      logDeriv (analyticWideBlaschkeDeflated χ t) s -
        (∑ ρ ∈ wideZeroSupport χ t,
          (wideZeroMultiplicity χ t ρ : ℂ) *
            logDeriv (shiftedCanonicalNumerator
              (wideCenter t) ρ wideRadius) s) +
        (∑ ρ ∈ wideZeroSupport χ t,
          (wideZeroMultiplicity χ t ρ : ℂ) / (s - ρ)) -
        (∑ ρ ∈ zeroSupport χ a H,
          (zeroMultiplicity χ a H ρ : ℂ) / (s - ρ)) := by
  have hsupp : s ∉ zeroSupport χ a H := by
    intro hsupp
    exact hL (regularizedLFunction_eq_zero_of_mem_zeroSupport χ a H hsupp)
  have hP : zeroFactorProduct χ a H s ≠ 0 :=
    zeroFactorProduct_ne_zero_of_not_mem χ a H hsupp
  have hPdiff : DifferentiableAt ℂ (zeroFactorProduct χ a H) s := by
    change DifferentiableAt ℂ
      (fun z => ∏ ρ ∈ zeroSupport χ a H,
        (z - ρ) ^ zeroMultiplicity χ a H ρ) s
    fun_prop
  have hdiv := logDeriv_div s hL hP
    (differentiable_regularizedLFunction χ).differentiableAt hPdiff
  rw [logDeriv_zeroFactorProduct χ a H hsupp] at hdiv
  change logDeriv (compactZeroDeflatedRegularizedLFunction χ a H) s = _ at hdiv
  have hlocal := localDeflatedLogDeriv_eq_blaschke_sub_correction χ hs hsF
  rw [hdiv]
  linear_combination hlocal

/-- The signed local/global pole mismatch is exactly the difference of the
two set differences.  Common zeros cancel with their analytic
multiplicities before any norm or triangle inequality is taken. -/
theorem signedPoleMismatch_eq_sdiff
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (a H t : ℝ) (s : ℂ) :
    (∑ ρ ∈ wideZeroSupport χ t,
        (wideZeroMultiplicity χ t ρ : ℂ) / (s - ρ)) -
      (∑ ρ ∈ zeroSupport χ a H,
        (zeroMultiplicity χ a H ρ : ℂ) / (s - ρ)) =
    (∑ ρ ∈ wideZeroSupport χ t \ zeroSupport χ a H,
        (wideZeroMultiplicity χ t ρ : ℂ) / (s - ρ)) -
      (∑ ρ ∈ zeroSupport χ a H \ wideZeroSupport χ t,
        (zeroMultiplicity χ a H ρ : ℂ) / (s - ρ)) := by
  let A := wideZeroSupport χ t
  let B := zeroSupport χ a H
  let I := A ∩ B
  have hIA : I ⊆ A := Finset.inter_subset_left
  have hIB : I ⊆ B := Finset.inter_subset_right
  have hAminus : A \ I = A \ B := by
    ext ρ
    simp only [Finset.mem_sdiff]
    change (ρ ∈ A ∧ ρ ∉ A ∩ B) ↔ (ρ ∈ A ∧ ρ ∉ B)
    simp only [Finset.mem_inter]
    tauto
  have hBminus : B \ I = B \ A := by
    ext ρ
    simp only [Finset.mem_sdiff]
    change (ρ ∈ B ∧ ρ ∉ A ∩ B) ↔ (ρ ∈ B ∧ ρ ∉ A)
    simp only [Finset.mem_inter]
    tauto
  have hinter :
      (∑ ρ ∈ I, (wideZeroMultiplicity χ t ρ : ℂ) / (s - ρ)) =
        ∑ ρ ∈ I, (zeroMultiplicity χ a H ρ : ℂ) / (s - ρ) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hρA : ρ ∈ A := hIA hρ
    have hρB : ρ ∈ B := hIB hρ
    have hwideBase : ρ ∈ zeroSupport χ (-1) (|t| + 3) :=
      mem_baseZeroSupport_of_mem_wideZeroSupport χ hρA
    have hwideRect : ρ ∈ zeroRectangle (-1) (|t| + 3) :=
      (zeroDivisor χ (-1) (|t| + 3)).supportWithinDomain
        ((zeroSupport_mem_iff χ (-1) (|t| + 3) ρ).mp hwideBase)
    have hglobalRect : ρ ∈ zeroRectangle a H :=
      (zeroDivisor χ a H).supportWithinDomain
        ((zeroSupport_mem_iff χ a H ρ).mp hρB)
    have hmult := MAPMellinDetectorLeaf.zeroMultiplicity_eq_of_mem_rectangles
      χ hwideRect hglobalRect
    simp only [wideZeroMultiplicity]
    rw [hmult]
  change
    (∑ ρ ∈ A, (wideZeroMultiplicity χ t ρ : ℂ) / (s - ρ)) -
      (∑ ρ ∈ B, (zeroMultiplicity χ a H ρ : ℂ) / (s - ρ)) = _
  rw [← Finset.sum_sdiff hIA, ← Finset.sum_sdiff hIB,
    hAminus, hBminus, hinter]
  ring

/-- Norm form of the signed bridge.  The far/global term is left as the norm
of its literal signed finite mismatch rather than being replaced by a
pointwise zero-gap estimate. -/
theorem norm_logDeriv_compactZeroDeflated_le_blaschke_add_signedMismatch
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {a H t : ℝ} {s : ℂ}
    (hs : s ∈ Metric.ball (wideCenter t) 2)
    (hsF : s ∉ wideZeroSupport χ t)
    (hL : regularizedLFunction χ s ≠ 0) :
    ‖logDeriv (compactZeroDeflatedRegularizedLFunction χ a H) s‖ ≤
      20 * (Real.log 21600 + 2 * Real.log (arithmeticScale q t)) +
      (∑ ρ ∈ wideZeroSupport χ t,
        (wideZeroMultiplicity χ t ρ : ℝ)) +
      ‖(∑ ρ ∈ wideZeroSupport χ t,
          (wideZeroMultiplicity χ t ρ : ℂ) / (s - ρ)) -
        (∑ ρ ∈ zeroSupport χ a H,
          (zeroMultiplicity χ a H ρ : ℂ) / (s - ρ))‖ := by
  have hexact :=
    logDeriv_compactZeroDeflated_eq_blaschke_add_signedMismatch
      χ (a := a) (H := H) hs hsF hL
  rw [hexact]
  have hB := norm_logDeriv_analyticWideBlaschkeDeflated_le χ hχ
    (Metric.mem_ball.mp hs)
  have hcorr :
      ‖∑ ρ ∈ wideZeroSupport χ t,
          (wideZeroMultiplicity χ t ρ : ℂ) *
            logDeriv (shiftedCanonicalNumerator
              (wideCenter t) ρ wideRadius) s‖ ≤
        ∑ ρ ∈ wideZeroSupport χ t,
          (wideZeroMultiplicity χ t ρ : ℝ) := by
    calc
      ‖∑ ρ ∈ wideZeroSupport χ t,
          (wideZeroMultiplicity χ t ρ : ℂ) *
            logDeriv (shiftedCanonicalNumerator
              (wideCenter t) ρ wideRadius) s‖ ≤
          ∑ ρ ∈ wideZeroSupport χ t,
            ‖(wideZeroMultiplicity χ t ρ : ℂ) *
              logDeriv (shiftedCanonicalNumerator
                (wideCenter t) ρ wideRadius) s‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ wideZeroSupport χ t,
          (wideZeroMultiplicity χ t ρ : ℝ) := by
        apply Finset.sum_le_sum
        intro ρ hρ
        rw [norm_mul, norm_natCast]
        have hnum := norm_logDeriv_shiftedCanonicalNumerator_le_one
          (c := wideCenter t) (ρ := ρ) (s := s)
          (by simpa [wideRadius] using mem_ball_of_mem_wideZeroSupport χ hρ) hs
        exact (mul_le_mul_of_nonneg_left hnum (Nat.cast_nonneg _)).trans_eq
          (mul_one _)
  have htri := norm_add_le
    (logDeriv (analyticWideBlaschkeDeflated χ t) s -
      ∑ ρ ∈ wideZeroSupport χ t,
        (wideZeroMultiplicity χ t ρ : ℂ) *
          logDeriv (shiftedCanonicalNumerator
            (wideCenter t) ρ wideRadius) s)
    ((∑ ρ ∈ wideZeroSupport χ t,
        (wideZeroMultiplicity χ t ρ : ℂ) / (s - ρ)) -
      (∑ ρ ∈ zeroSupport χ a H,
        (zeroMultiplicity χ a H ρ : ℂ) / (s - ρ)))
  have hfirst := (norm_sub_le
    (logDeriv (analyticWideBlaschkeDeflated χ t) s)
    (∑ ρ ∈ wideZeroSupport χ t,
      (wideZeroMultiplicity χ t ρ : ℂ) *
        logDeriv (shiftedCanonicalNumerator
          (wideCenter t) ρ wideRadius) s)).trans
    (add_le_add hB hcorr)
  simpa only [sub_eq_add_neg, add_assoc] using
    htri.trans (add_le_add_left hfirst _)

end

end WideDiskLocalLogDerivative
