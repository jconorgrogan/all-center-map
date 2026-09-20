import ZeroDistanceLogDerivativeBounds

/-!
# Canonical compact-deflated quotient and Borel bridge

The raw compact quotient used by the contour algebra takes the field value
`0 / 0` at supported zeros, so it is not the right function on which to apply
Borel--Caratheodory.  This file fills exactly those removable singularities,
proves that the filled quotient is entire, and identifies its logarithmic
derivative with the raw quotient away from the divisor.  The final theorem
then isolates the literal remaining analytic input: an outer-disk log-norm
ratio for this concrete filled quotient.
-/

namespace CompactDeflatedBorelBridge

open Complex Set Metric Filter Topology DirichletZeros PrimitiveExplicitFormulaSpine
open ZeroDistanceLogDerivativeBounds

noncomputable section

/-- Canonical normal-form filling of the literal compact zero-deflated
regularized L-function. -/
def compactZeroDeflatedNF
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a H : ℝ) : ℂ → ℂ :=
  toMeromorphicNFOn
    (compactZeroDeflatedRegularizedLFunction χ a H) Set.univ

private theorem zeroFactorProduct_order
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a H : ℝ)
    {ρ : ℂ} (hρ : ρ ∈ zeroSupport χ a H) :
    meromorphicOrderAt (zeroFactorProduct χ a H) ρ =
      (zeroMultiplicity χ a H ρ : ℤ) := by
  change meromorphicOrderAt
    (fun s : ℂ => ∏ z ∈ zeroSupport χ a H,
      (s - z) ^ zeroMultiplicity χ a H z) ρ = _
  rw [meromorphicOrderAt_fun_prod]
  · rw [Finset.sum_eq_single ρ]
    · change meromorphicOrderAt
        ((· - ρ) ^ zeroMultiplicity χ a H ρ) ρ = _
      exact meromorphicOrderAt_pow_id_sub_const
    · intro z hz hzρ
      have hne : ρ - z ≠ 0 := sub_ne_zero.mpr hzρ.symm
      have han : AnalyticAt ℂ
          (fun s : ℂ => (s - z) ^ zeroMultiplicity χ a H z) ρ := by
        fun_prop
      rw [han.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
        (pow_ne_zero _ hne)]
    · exact fun h => (h hρ).elim
  · intro z hz
    fun_prop

private theorem rawCompactDeflated_meromorphic
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a H : ℝ) :
    MeromorphicOn (compactZeroDeflatedRegularizedLFunction χ a H)
      Set.univ := by
  apply MeromorphicOn.div
  · exact (analyticOnNhd_univ_iff_differentiable.mpr
      (differentiable_regularizedLFunction χ)).meromorphicOn
  · have hpDiff : Differentiable ℂ (zeroFactorProduct χ a H) := by
      change Differentiable ℂ
        (fun s : ℂ => ∏ ρ ∈ zeroSupport χ a H,
          (s - ρ) ^ zeroMultiplicity χ a H ρ)
      fun_prop
    exact (analyticOnNhd_univ_iff_differentiable.mpr hpDiff).meromorphicOn

private theorem meromorphicOrderAt_regularized_eq_multiplicity
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a H : ℝ)
    {ρ : ℂ} (hρ : ρ ∈ zeroSupport χ a H) :
    meromorphicOrderAt (regularizedLFunction χ) ρ =
      (zeroMultiplicity χ a H ρ : ℤ) := by
  have han := (differentiable_regularizedLFunction χ).analyticAt ρ
  rw [han.meromorphicOrderAt_eq,
    PrimitiveExplicitFormulaSpine.analyticOrderAt_eq_zeroMultiplicity
      χ a H hρ]
  simp

/-- The filled compact quotient is entire.  This uses the actual analytic
multiplicity of every point in `zeroSupport`; no zero-count estimate enters. -/
theorem analyticOnNhd_compactZeroDeflatedNF
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a H : ℝ) :
    AnalyticOnNhd ℂ (compactZeroDeflatedNF χ a H) Set.univ := by
  let raw := compactZeroDeflatedRegularizedLFunction χ a H
  have hraw : MeromorphicOn raw Set.univ :=
    rawCompactDeflated_meromorphic χ a H
  have hnf : MeromorphicNFOn (toMeromorphicNFOn raw Set.univ) Set.univ :=
    meromorphicNFOn_toMeromorphicNFOn raw Set.univ
  have hpDiff : Differentiable ℂ (zeroFactorProduct χ a H) := by
    change Differentiable ℂ
      (fun s : ℂ => ∏ ρ ∈ zeroSupport χ a H,
        (s - ρ) ^ zeroMultiplicity χ a H ρ)
    fun_prop
  have hpAn : AnalyticOnNhd ℂ (zeroFactorProduct χ a H) Set.univ :=
    analyticOnNhd_univ_iff_differentiable.mpr hpDiff
  intro z hz
  apply (hnf hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_toMeromorphicNFOn hraw hz]
  change 0 ≤ meromorphicOrderAt
    (regularizedLFunction χ / zeroFactorProduct χ a H) z
  rw [meromorphicOrderAt_div
    ((differentiable_regularizedLFunction χ).analyticAt z).meromorphicAt
    (hpAn z (Set.mem_univ z)).meromorphicAt]
  by_cases hzs : z ∈ zeroSupport χ a H
  · rw [zeroFactorProduct_order χ a H hzs,
      meromorphicOrderAt_regularized_eq_multiplicity χ a H hzs]
    simp
  · have hp0 : meromorphicOrderAt (zeroFactorProduct χ a H) z = 0 := by
      have hpAnalytic : AnalyticAt ℂ (zeroFactorProduct χ a H) z :=
        hpAn z (Set.mem_univ z)
      exact hpAnalytic.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
        (zeroFactorProduct_ne_zero_of_not_mem χ a H hzs)
    rw [hp0, sub_zero]
    exact ((differentiable_regularizedLFunction χ).analyticAt z).meromorphicNFAt
      |>.meromorphicOrderAt_nonneg_iff_analyticAt.mpr
        ((differentiable_regularizedLFunction χ).analyticAt z)

/-- The filled quotient is nonzero wherever every zero of the numerator has
been included in the compact divisor.  This is the precise deterministic
zero-cover condition needed on a Borel disk. -/
theorem compactZeroDeflatedNF_ne_zero_of_zero_covered
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a H : ℝ)
    {s : ℂ}
    (hcover : regularizedLFunction χ s = 0 → s ∈ zeroSupport χ a H) :
    compactZeroDeflatedNF χ a H s ≠ 0 := by
  have hraw : MeromorphicOn
      (compactZeroDeflatedRegularizedLFunction χ a H) Set.univ :=
    rawCompactDeflated_meromorphic χ a H
  have han : AnalyticAt ℂ (compactZeroDeflatedNF χ a H) s :=
    analyticOnNhd_compactZeroDeflatedNF χ a H s (Set.mem_univ s)
  apply han.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp
  unfold compactZeroDeflatedNF
  rw [meromorphicOrderAt_toMeromorphicNFOn hraw (Set.mem_univ s)]
  change meromorphicOrderAt
    (regularizedLFunction χ / zeroFactorProduct χ a H) s = 0
  have hnumAn := (differentiable_regularizedLFunction χ).analyticAt s
  have hdenAn : AnalyticAt ℂ (zeroFactorProduct χ a H) s := by
    change AnalyticAt ℂ
      (fun z : ℂ => ∏ ρ ∈ zeroSupport χ a H,
        (z - ρ) ^ zeroMultiplicity χ a H ρ) s
    fun_prop
  rw [meromorphicOrderAt_div hnumAn.meromorphicAt hdenAn.meromorphicAt]
  by_cases hsupp : s ∈ zeroSupport χ a H
  · rw [zeroFactorProduct_order χ a H hsupp,
      meromorphicOrderAt_regularized_eq_multiplicity χ a H hsupp]
    simp
  · have hL : regularizedLFunction χ s ≠ 0 := fun h => hsupp (hcover h)
    have hP : zeroFactorProduct χ a H s ≠ 0 :=
      zeroFactorProduct_ne_zero_of_not_mem χ a H hsupp
    rw [hnumAn.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hL,
      hdenAn.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hP]
    simp

/-- A disk is covered by the compact divisor when its leftmost real part is
at least `a` and its imaginary aperture stays inside `[-H,H]`.  The right
edge needs no geometric hypothesis: the Euler product rules out zeros with
real part at least one. -/
theorem zeroSupport_covers_ball_of_margins
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a H r : ℝ} {s : ℂ}
    (hre : a + 3 * r / 2 ≤ s.re)
    (him : |s.im| + 3 * r / 2 ≤ H) :
    ∀ z ∈ Metric.ball s (3 * r / 2),
      regularizedLFunction χ z = 0 → z ∈ zeroSupport χ a H := by
  intro z hz hzero
  have hnorm : ‖z - s‖ < 3 * r / 2 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hreDiff : |z.re - s.re| < 3 * r / 2 :=
    (Complex.abs_re_le_norm (z - s)).trans_lt (by simpa using hnorm)
  have himDiff : |z.im - s.im| < 3 * r / 2 :=
    (Complex.abs_im_le_norm (z - s)).trans_lt (by simpa using hnorm)
  have hza : a ≤ z.re := by
    have := neg_le_abs (z.re - s.re)
    linarith
  have hzone : z.re ≤ 1 := by
    by_contra hnot
    have hone : 1 ≤ z.re := le_of_not_ge hnot
    exact (MAPMellinDetectorLeaf.regularizedLFunction_ne_zero_of_one_le_re
      χ hone) hzero
  have hzabs : |z.im| ≤ H := by
    have htri : |z.im| ≤ |z.im - s.im| + |s.im| := by
      calc
        |z.im| = |(z.im - s.im) + s.im| := by ring_nf
        _ ≤ |z.im - s.im| + |s.im| := abs_add_le _ _
    linarith
  have hzrect : z ∈ zeroRectangle a H := by
    constructor
    · exact ⟨hza, hzone⟩
    · exact (abs_le.mp hzabs)
  exact (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
    χ a H hzrect).2 hzero

/-- Away from the finite divisor, normal-form filling changes neither the
value nor the logarithmic derivative of the raw compact quotient. -/
theorem logDeriv_compactZeroDeflatedNF_eq_raw
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a H : ℝ)
    {s : ℂ} (hs : s ∉ zeroSupport χ a H) :
    logDeriv (compactZeroDeflatedNF χ a H) s =
      logDeriv (compactZeroDeflatedRegularizedLFunction χ a H) s := by
  let raw := compactZeroDeflatedRegularizedLFunction χ a H
  have hrawMer : MeromorphicOn raw Set.univ :=
    rawCompactDeflated_meromorphic χ a H
  have hP : zeroFactorProduct χ a H s ≠ 0 :=
    zeroFactorProduct_ne_zero_of_not_mem χ a H hs
  have hrawAn : AnalyticAt ℂ raw s := by
    have hnum : AnalyticAt ℂ (regularizedLFunction χ) s :=
      (differentiable_regularizedLFunction χ).analyticAt s
    have hden : AnalyticAt ℂ (zeroFactorProduct χ a H) s := by
      change AnalyticAt ℂ
        (fun z : ℂ => ∏ ρ ∈ zeroSupport χ a H,
          (z - ρ) ^ zeroMultiplicity χ a H ρ) s
      fun_prop
    exact hnum.div hden hP
  have heqNF : toMeromorphicNFAt raw s = raw :=
    toMeromorphicNFAt_eq_self.mpr hrawAn.meromorphicNFAt
  have hevent : compactZeroDeflatedNF χ a H =ᶠ[𝓝 s] raw := by
    exact (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hrawMer
      (Set.mem_univ s)).trans (Filter.Eventually.of_forall fun z => by
        rw [heqNF])
  unfold logDeriv
  simp only [Pi.div_apply]
  change deriv (compactZeroDeflatedNF χ a H) s /
      compactZeroDeflatedNF χ a H s = deriv raw s / raw s
  rw [hevent.deriv_eq, hevent.eq_of_nhds]

/-- Scale-invariant Borel--Caratheodory conversion.  The conclusion is at the
disk center, exactly the form needed pointwise along a selected contour side. -/
theorem norm_logDeriv_le_of_scaled_log_norm_ratio_le
    {g : ℂ → ℂ} {c : ℂ} {r M : ℝ}
    (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (Metric.ball c (3 * r / 2)))
    (hgn : ∀ z ∈ Metric.ball c (3 * r / 2), g z ≠ 0)
    (hM : 0 < M)
    (hlog : ∀ z ∈ Metric.ball c (3 * r / 2),
      Real.log (‖g z‖ / ‖g c‖) ≤ M) :
    ‖logDeriv g c‖ ≤ 40 * M / r := by
  let G : ℂ → ℂ := fun w => g (c + (r : ℂ) * w)
  have hmap : ∀ w ∈ Metric.ball (0 : ℂ) (3 / 2 : ℝ),
      c + (r : ℂ) * w ∈ Metric.ball c (3 * r / 2) := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
    have hwnorm : ‖w‖ < (3 / 2 : ℝ) := by simpa using hw
    have hmul := mul_lt_mul_of_pos_left hwnorm hr
    rw [show c + (r : ℂ) * w - c = (r : ℂ) * w by ring, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith
  have hGdiff : DifferentiableOn ℂ G (Metric.ball 0 (3 / 2 : ℝ)) := by
    intro w hw
    exact DifferentiableAt.differentiableWithinAt
      (((hg (c + (r : ℂ) * w) (hmap w hw)).differentiableAt
        (isOpen_ball.mem_nhds (hmap w hw))).comp w
        ((differentiableAt_const c).add
          ((differentiableAt_const (r : ℂ)).mul differentiableAt_id)))
  have hGne : ∀ w ∈ Metric.ball (0 : ℂ) (3 / 2 : ℝ), G w ≠ 0 := by
    intro w hw
    exact hgn _ (hmap w hw)
  have hGlog : ∀ w ∈ Metric.ball (0 : ℂ) (3 / 2 : ℝ),
      Real.log (‖G w‖ / ‖G 0‖) ≤ M := by
    intro w hw
    simpa [G] using hlog _ (hmap w hw)
  have hB := MAPZeroFreeSiegelSpine.norm_logDeriv_le_of_log_norm_ratio_le
    hGdiff hGne hM hGlog (s := (0 : ℂ)) (by simp)
  have hchain : logDeriv G 0 = logDeriv g c * (r : ℂ) := by
    have hgAt : DifferentiableAt ℂ g c := by
      have hcball : c ∈ Metric.ball c (3 * r / 2) := by
        simpa using (show (0 : ℝ) < 3 * r / 2 by positivity)
      exact (hg c hcball).differentiableAt (isOpen_ball.mem_nhds hcball)
    rw [show G = g ∘ (fun w : ℂ => c + (r : ℂ) * w) by rfl,
      logDeriv_comp (by simpa using hgAt) (by fun_prop)]
    simp
  rw [hchain, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr] at hB
  exact (le_div_iff₀ hr).2 (by simpa [mul_comm, mul_left_comm] using hB)

/-- Scale-invariant Borel--Caratheodory conversion at any point of the inner
disk.  A radius-three outer disk (`r = 2`) therefore controls every point at
distance strictly less than two from its center with constant `20*M`. -/
theorem norm_logDeriv_le_of_scaled_log_norm_ratio_le_at
    {g : ℂ → ℂ} {c s : ℂ} {r M : ℝ}
    (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (Metric.ball c (3 * r / 2)))
    (hgn : ∀ z ∈ Metric.ball c (3 * r / 2), g z ≠ 0)
    (hM : 0 < M)
    (hlog : ∀ z ∈ Metric.ball c (3 * r / 2),
      Real.log (‖g z‖ / ‖g c‖) ≤ M)
    (hs : dist s c < r) :
    ‖logDeriv g s‖ ≤ 40 * M / r := by
  let G : ℂ → ℂ := fun w => g (c + (r : ℂ) * w)
  let w : ℂ := (s - c) / (r : ℂ)
  have hmap : ∀ u ∈ Metric.ball (0 : ℂ) (3 / 2 : ℝ),
      c + (r : ℂ) * u ∈ Metric.ball c (3 * r / 2) := by
    intro u hu
    rw [Metric.mem_ball, dist_eq_norm] at hu ⊢
    have hunorm : ‖u‖ < (3 / 2 : ℝ) := by simpa using hu
    have hmul := mul_lt_mul_of_pos_left hunorm hr
    rw [show c + (r : ℂ) * u - c = (r : ℂ) * u by ring, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith
  have hGdiff : DifferentiableOn ℂ G (Metric.ball 0 (3 / 2 : ℝ)) := by
    intro u hu
    exact DifferentiableAt.differentiableWithinAt
      (((hg (c + (r : ℂ) * u) (hmap u hu)).differentiableAt
        (isOpen_ball.mem_nhds (hmap u hu))).comp u
        ((differentiableAt_const c).add
          ((differentiableAt_const (r : ℂ)).mul differentiableAt_id)))
  have hGne : ∀ u ∈ Metric.ball (0 : ℂ) (3 / 2 : ℝ), G u ≠ 0 := by
    intro u hu
    exact hgn _ (hmap u hu)
  have hGlog : ∀ u ∈ Metric.ball (0 : ℂ) (3 / 2 : ℝ),
      Real.log (‖G u‖ / ‖G 0‖) ≤ M := by
    intro u hu
    simpa [G] using hlog _ (hmap u hu)
  have hw : dist w 0 < 1 := by
    rw [dist_zero_right]
    dsimp [w]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr]
    rw [div_lt_one hr]
    simpa [dist_eq_norm] using hs
  have hB := MAPZeroFreeSiegelSpine.norm_logDeriv_le_of_log_norm_ratio_le
    hGdiff hGne hM hGlog hw
  have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hpoint : c + (r : ℂ) * w = s := by
    dsimp [w]
    field_simp
    ring
  have hchain : logDeriv G w = logDeriv g s * (r : ℂ) := by
    have hgAt : DifferentiableAt ℂ g s := by
      have hsball : s ∈ Metric.ball c (3 * r / 2) := by
        rw [Metric.mem_ball]
        linarith
      exact (hg s hsball).differentiableAt (isOpen_ball.mem_nhds hsball)
    rw [show G = g ∘ (fun u : ℂ => c + (r : ℂ) * u) by rfl,
      logDeriv_comp (by simpa [hpoint] using hgAt) (by fun_prop)]
    simp [hpoint]
  rw [hchain, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr] at hB
  exact (le_div_iff₀ hr).2 (by simpa [mul_comm, mul_left_comm] using hB)

/-- Exact deterministic consumer for the contour's literal raw compact
quotient.  The two remaining hypotheses are stated on the concrete canonical
filling: local zero-freeness and its outer-disk log-norm ratio. -/
theorem norm_logDeriv_compactZeroDeflated_le_of_log_norm_ratio
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a H : ℝ)
    {s : ℂ} (hs : s ∉ zeroSupport χ a H) {r M : ℝ}
    (hr : 0 < r)
    (hzeroFree : ∀ z ∈ Metric.ball s (3 * r / 2),
      compactZeroDeflatedNF χ a H z ≠ 0)
    (hM : 0 < M)
    (hlog : ∀ z ∈ Metric.ball s (3 * r / 2),
      Real.log
        (‖compactZeroDeflatedNF χ a H z‖ /
          ‖compactZeroDeflatedNF χ a H s‖) ≤ M) :
    ‖logDeriv (compactZeroDeflatedRegularizedLFunction χ a H) s‖ ≤
      40 * M / r := by
  rw [← logDeriv_compactZeroDeflatedNF_eq_raw χ a H hs]
  exact norm_logDeriv_le_of_scaled_log_norm_ratio_le hr
    (fun z hz =>
      (analyticOnNhd_compactZeroDeflatedNF χ a H z (Set.mem_univ z))
        |>.differentiableWithinAt)
    hzeroFree hM hlog

/-- Version in which local zero-freeness is discharged by the literal
statement that the compact divisor covers every numerator zero in the disk.
After a buffered rectangle selection this cover is pure coordinate geometry;
the sole quantitative analytic premise is then `hlog`. -/
theorem norm_logDeriv_compactZeroDeflated_le_of_zero_cover_log_norm_ratio
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a H : ℝ)
    {s : ℂ} (hs : s ∉ zeroSupport χ a H) {r M : ℝ}
    (hr : 0 < r)
    (hcover : ∀ z ∈ Metric.ball s (3 * r / 2),
      regularizedLFunction χ z = 0 → z ∈ zeroSupport χ a H)
    (hM : 0 < M)
    (hlog : ∀ z ∈ Metric.ball s (3 * r / 2),
      Real.log
        (‖compactZeroDeflatedNF χ a H z‖ /
          ‖compactZeroDeflatedNF χ a H s‖) ≤ M) :
    ‖logDeriv (compactZeroDeflatedRegularizedLFunction χ a H) s‖ ≤
      40 * M / r := by
  exact norm_logDeriv_compactZeroDeflated_le_of_log_norm_ratio
    χ a H hs hr
    (fun z hz => compactZeroDeflatedNF_ne_zero_of_zero_covered
      χ a H (hcover z hz))
    hM hlog

/-- The narrow source-facing contour theorem.  All divisor legality and disk
zero-freeness are discharged by explicit margins.  Its only non-elementary
premise is the concrete outer-disk logarithmic norm ratio `hlog`. -/
theorem norm_logDeriv_compactZeroDeflated_le_of_margins_log_norm_ratio
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a H r M : ℝ} {s : ℂ} (hs : s ∉ zeroSupport χ a H)
    (hr : 0 < r)
    (hre : a + 3 * r / 2 ≤ s.re)
    (him : |s.im| + 3 * r / 2 ≤ H)
    (hM : 0 < M)
    (hlog : ∀ z ∈ Metric.ball s (3 * r / 2),
      Real.log
        (‖compactZeroDeflatedNF χ a H z‖ /
          ‖compactZeroDeflatedNF χ a H s‖) ≤ M) :
    ‖logDeriv (compactZeroDeflatedRegularizedLFunction χ a H) s‖ ≤
      40 * M / r := by
  exact norm_logDeriv_compactZeroDeflated_le_of_zero_cover_log_norm_ratio
    χ a H hs hr (zeroSupport_covers_ball_of_margins χ hre him) hM hlog

/-- Clearance-normalized form used after `BufferedQuantitativeAperture`.
Taking Borel scale `r = 2d/3` makes its outer disk exactly `ball s d` and
turns the constant `40/r` into `60/d`. -/
theorem norm_logDeriv_compactZeroDeflated_le_sixty_mul_div_distance
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a H d M : ℝ} {s : ℂ} (hd : 0 < d)
    (hdist : ∀ ρ ∈ zeroSupport χ a H, d ≤ ‖s - ρ‖)
    (hre : a + d ≤ s.re)
    (him : |s.im| + d ≤ H)
    (hM : 0 < M)
    (hlog : ∀ z ∈ Metric.ball s d,
      Real.log
        (‖compactZeroDeflatedNF χ a H z‖ /
          ‖compactZeroDeflatedNF χ a H s‖) ≤ M) :
    ‖logDeriv (compactZeroDeflatedRegularizedLFunction χ a H) s‖ ≤
      60 * M / d := by
  have hs : s ∉ zeroSupport χ a H := by
    intro hsupp
    have hzero := hdist s hsupp
    simp at hzero
    linarith
  have hr : 0 < 2 * d / 3 := by positivity
  have hradius : 3 * (2 * d / 3) / 2 = d := by ring
  have hbase :=
    norm_logDeriv_compactZeroDeflated_le_of_margins_log_norm_ratio
      χ hs hr (by simpa [hradius] using hre) (by simpa [hradius] using him)
      hM (by simpa [hradius] using hlog)
  calc
    ‖logDeriv (compactZeroDeflatedRegularizedLFunction χ a H) s‖
        ≤ 40 * M / (2 * d / 3) := hbase
    _ = 60 * M / d := by field_simp; ring

end

end CompactDeflatedBorelBridge
