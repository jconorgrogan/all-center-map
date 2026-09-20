import PostA5TypeIFourierAssembly
/-! Uniform Fourier removal on 0≤beta−sigma≤1/2, covering every zero up to
beta=1 in the low-sigma density count. The fixed derivative envelope changes
from exp(3/5) to exp(1); no parameter-dependent loss is introduced. -/
namespace MAPMontgomeryFullStripFourier
open scoped BigOperators FourierTransform SchwartzMap
open Set Complex MeasureTheory
open PostA5TypeIFourierAssembly MAPAppendixA4PostA5SetAdapter
noncomputable section
theorem norm_pow_mul_exp_le_uniform_of_baseDerivative_ne_zero
    {a x : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2)
    (m r : ℕ) (hne : detectorBaseDerivative r x ≠ 0) :
    ‖(((-a : ℝ) : ℂ) ^ m * (Real.exp (-a * x) : ℂ))‖ ≤
      Real.exp (1) := by
  have hxTs : x ∈ tsupport (fun y : ℝ => detectorBaseDerivative r y) :=
    subset_tsupport _ hne
  have hx : x ∈ Set.Icc (-2 : ℝ) 2 :=
    tsupport_detectorBaseDerivative_subset r hxTs
  have ha1 : a ≤ 1 := by linarith
  have hpow : a ^ m ≤ 1 := pow_le_one₀ ha0 ha1
  have hxlow : -2 ≤ x := hx.1
  have hax : 0 ≤ a * (x + 2) :=
    mul_nonneg ha0 (by linarith)
  have h2a : 2 * a ≤ 1 := by linarith
  have hexponent : -a * x ≤ 1 := by
    nlinarith
  have hexp : Real.exp (-a * x) ≤ Real.exp (1) :=
    Real.exp_le_exp.mpr hexponent
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_neg, abs_of_nonneg ha0, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_pos _).le]
  calc
    a ^ m * Real.exp (-a * x) ≤ 1 * Real.exp (1) :=
      mul_le_mul hpow hexp (Real.exp_pos _).le (by norm_num)
    _ = Real.exp (1) := one_mul _

/-- Explicit fixed-bump constant controlling the `n`th physical derivative
uniformly for `0 ≤ a ≤ 1/2`. -/
def detectorDerivativeL1Constant (n : ℕ) : ℝ :=
  Real.exp (1) *
    ∑ r ∈ Finset.range (n + 1), (n.choose r : ℝ) *
      ∫ x : ℝ, ‖detectorBaseDerivative r x‖

theorem detectorDerivativeL1Constant_nonneg (n : ℕ) :
    0 ≤ detectorDerivativeL1Constant n := by
  unfold detectorDerivativeL1Constant
  positivity

theorem norm_iteratedDeriv_detectorRealPartCutoff_base_le
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n
        (fun y : ℝ => detectorRealPartCutoff a 1 y) x‖ ≤
      ∑ r ∈ Finset.range (n + 1),
        Real.exp (1) * (n.choose r : ℝ) *
          ‖detectorBaseDerivative r x‖ := by
  rw [iteratedDeriv_detectorRealPartCutoff_base]
  apply norm_sum_le_of_le
  intro r hr
  by_cases hzero : detectorBaseDerivative r x = 0
  · simp [hzero]
  · rw [norm_mul, norm_mul]
    have hfactor :=
      norm_pow_mul_exp_le_uniform_of_baseDerivative_ne_zero
        ha0 ha (n - r) r hzero
    have hchoose : ‖(n.choose r : ℂ)‖ = (n.choose r : ℝ) := by simp
    rw [hchoose]
    calc
      (n.choose r : ℝ) * ‖detectorBaseDerivative r x‖ *
          ‖(((-a : ℝ) : ℂ) ^ (n - r) * (Real.exp (-a * x) : ℂ))‖ ≤
        (n.choose r : ℝ) * ‖detectorBaseDerivative r x‖ *
          Real.exp (1) :=
        mul_le_mul_of_nonneg_left hfactor
          (mul_nonneg (by positivity) (norm_nonneg _))
      _ = Real.exp (1) * (n.choose r : ℝ) *
          ‖detectorBaseDerivative r x‖ := by ring

/-- Uniform physical-space `L¹` derivative bound for the fixed-center cutoff.
All dependence on the smooth bump is retained in the explicit finite constant
`detectorDerivativeL1Constant n`; neither `a` nor `D` occurs in it. -/
theorem integral_norm_iteratedDeriv_detectorRealPartCutoff_base_le
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (n : ℕ) :
    (∫ x : ℝ, ‖iteratedDeriv n
        (fun y : ℝ => detectorRealPartCutoff a 1 y) x‖) ≤
      detectorDerivativeL1Constant n := by
  let f : 𝓢(ℝ, ℂ) := detectorRealPartCutoff a 1
  have hleft : Integrable (fun x : ℝ =>
      ‖iteratedDeriv n (fun y : ℝ => detectorRealPartCutoff a 1 y) x‖) := by
    have h := (schwartzIteratedDerivative n f).integrable
      (μ := (volume : Measure ℝ)) |>.norm
    simpa [f, schwartzIteratedDerivative_apply] using h
  have hterm : ∀ r ∈ Finset.range (n + 1), Integrable (fun x : ℝ =>
      Real.exp (1) * (n.choose r : ℝ) *
        ‖detectorBaseDerivative r x‖) := by
    intro r hr
    exact ((detectorBaseDerivative r).integrable
      (μ := (volume : Measure ℝ))).norm.const_mul
      (Real.exp (1) * (n.choose r : ℝ))
  have hright : Integrable (fun x : ℝ =>
      ∑ r ∈ Finset.range (n + 1),
        Real.exp (1) * (n.choose r : ℝ) *
          ‖detectorBaseDerivative r x‖) :=
    integrable_finsetSum _ hterm
  calc
    (∫ x : ℝ, ‖iteratedDeriv n
        (fun y : ℝ => detectorRealPartCutoff a 1 y) x‖) ≤
      ∫ x : ℝ, ∑ r ∈ Finset.range (n + 1),
        Real.exp (1) * (n.choose r : ℝ) *
          ‖detectorBaseDerivative r x‖ := by
      exact MeasureTheory.integral_mono hleft hright
        (norm_iteratedDeriv_detectorRealPartCutoff_base_le ha0 ha n)
    _ = detectorDerivativeL1Constant n := by
      rw [MeasureTheory.integral_finsetSum _ hterm]
      simp_rw [MeasureTheory.integral_const_mul]
      unfold detectorDerivativeL1Constant
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring

/-- Integration by parts, expressed through mathlib's exact Fourier theorem:
the `q`th Fourier seminorm is controlled by the uniform `L¹` norm of the
`q`th physical derivative. -/
theorem seminorm_fourier_detectorRealPartCutoff_base_le
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (q : ℕ) :
    SchwartzMap.seminorm ℂ q 0
        (𝓕 (detectorRealPartCutoff a 1) : 𝓢(ℝ, ℂ)) ≤
      detectorDerivativeL1Constant q := by
  let f : 𝓢(ℝ, ℂ) := detectorRealPartCutoff a 1
  apply SchwartzMap.seminorm_le_bound' ℂ q 0
    (𝓕 f : 𝓢(ℝ, ℂ)) (detectorDerivativeL1Constant_nonneg q)
  intro xi
  rw [iteratedDeriv_zero]
  have hInt : ∀ m : ℕ, (m : ℕ∞) ≤ ⊤ →
      Integrable (iteratedDeriv m (fun x : ℝ => f x)) := by
    intro m hm
    have h := (schwartzIteratedDerivative m f).integrable
      (μ := (volume : Measure ℝ))
    apply h.congr
    filter_upwards with x
    exact schwartzIteratedDerivative_apply m f x
  have hfourier := Real.fourier_iteratedDeriv
    (f.smooth ⊤) hInt (show (q : ℕ∞) ≤ ⊤ from le_top)
  have hraw := VectorFourier.norm_fourierIntegral_le_integral_norm
    𝐞 volume (innerₗ ℝ)
      (iteratedDeriv q (fun x : ℝ => f x)) xi
  change ‖𝓕 (iteratedDeriv q (fun x : ℝ => f x)) xi‖ ≤ _ at hraw
  rw [congrFun hfourier xi] at hraw
  have hfFourier :
      𝓕 (fun x : ℝ => f x) xi = ((𝓕 f : 𝓢(ℝ, ℂ)) xi) := by
    exact congrFun (SchwartzMap.fourier_coe f).symm xi
  rw [hfFourier] at hraw
  have htwoPi : (1 : ℝ) ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hscale : (1 : ℝ) ≤ (2 * Real.pi) ^ q := one_le_pow₀ htwoPi
  have hnormScale :
      ‖((2 * (Real.pi : ℂ) * Complex.I * (xi : ℂ)) ^ q) •
          ((𝓕 f : 𝓢(ℝ, ℂ)) xi)‖ =
        (2 * Real.pi) ^ q * |xi| ^ q *
          ‖((𝓕 f : 𝓢(ℝ, ℂ)) xi)‖ := by
    change ‖((2 * (Real.pi : ℂ) * Complex.I * (xi : ℂ)) ^ q) *
      ((𝓕 f : 𝓢(ℝ, ℂ)) xi)‖ = _
    rw [norm_mul, norm_pow]
    simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs]
    rw [abs_of_pos Real.pi_pos]
    have hnormTwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by
      calc
        ‖(2 : ℂ)‖ = ‖(2 : ℝ)‖ := Complex.norm_real _
        _ = |(2 : ℝ)| := Real.norm_eq_abs _
        _ = 2 := abs_of_nonneg (by norm_num)
    rw [hnormTwo]
    ring
  rw [hnormScale] at hraw
  calc
    |xi| ^ q * ‖((𝓕 f : 𝓢(ℝ, ℂ)) xi)‖ ≤
        (2 * Real.pi) ^ q *
          (|xi| ^ q * ‖((𝓕 f : 𝓢(ℝ, ℂ)) xi)‖) := by
      exact le_mul_of_one_le_left
        (mul_nonneg (pow_nonneg (abs_nonneg xi) q) (norm_nonneg _)) hscale
    _ = (2 * Real.pi) ^ q * |xi| ^ q *
          ‖((𝓕 f : 𝓢(ℝ, ℂ)) xi)‖ := by ring
    _ ≤ ∫ x : ℝ, ‖iteratedDeriv q
          (fun y : ℝ => detectorRealPartCutoff a 1 y) x‖ := by
      simpa [f] using hraw
    _ ≤ detectorDerivativeL1Constant q :=
      integral_norm_iteratedDeriv_detectorRealPartCutoff_base_le ha0 ha q

/-- Explicit constant for the `k`th weighted Fourier moment.  It depends only
on the fixed bump and `k`; in particular it is independent of `a` and `D`. -/
def detectorFourierMomentConstant (k : ℕ) : ℝ :=
  (2 ^ (volume : Measure ℝ).integrablePower *
      ∫ xi : ℝ,
        (1 + ‖xi‖) ^ (-((volume : Measure ℝ).integrablePower : ℝ))) *
    (detectorDerivativeL1Constant 0 +
      detectorDerivativeL1Constant
        (k + (volume : Measure ℝ).integrablePower))

theorem detectorFourierMomentConstant_nonneg (k : ℕ) :
    0 ≤ detectorFourierMomentConstant k := by
  unfold detectorFourierMomentConstant
  apply mul_nonneg
  · apply mul_nonneg (by positivity)
    exact integral_nonneg fun xi => Real.rpow_nonneg (by positivity) _
  · exact add_nonneg (detectorDerivativeL1Constant_nonneg 0)
      (detectorDerivativeL1Constant_nonneg _)

/-- Uniform weighted Fourier moment at center one, obtained by the explicit
physical derivative bounds and integration by parts. -/
theorem integral_pow_mul_norm_fourier_detectorRealPartCutoff_base_le
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (k : ℕ) :
    (∫ xi : ℝ, |xi| ^ k *
        ‖((𝓕 (detectorRealPartCutoff a 1) : 𝓢(ℝ, ℂ)) xi)‖) ≤
      detectorFourierMomentConstant k := by
  let F : 𝓢(ℝ, ℂ) :=
    (𝓕 (detectorRealPartCutoff a 1) : 𝓢(ℝ, ℂ))
  have hgeneral :=
    SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℂ
      (volume : Measure ℝ) F k 0
  have hzero : SchwartzMap.seminorm ℂ 0 0 F ≤
      detectorDerivativeL1Constant 0 := by
    exact seminorm_fourier_detectorRealPartCutoff_base_le ha0 ha 0
  have hhigh : SchwartzMap.seminorm ℂ
      (k + (volume : Measure ℝ).integrablePower) 0 F ≤
      detectorDerivativeL1Constant
        (k + (volume : Measure ℝ).integrablePower) := by
    exact seminorm_fourier_detectorRealPartCutoff_base_le ha0 ha _
  have hpref : 0 ≤
      2 ^ (volume : Measure ℝ).integrablePower *
        ∫ xi : ℝ,
          (1 + ‖xi‖) ^ (-((volume : Measure ℝ).integrablePower : ℝ)) := by
    apply mul_nonneg (by positivity)
    exact integral_nonneg fun xi => Real.rpow_nonneg (by positivity) _
  calc
    (∫ xi : ℝ, |xi| ^ k *
        ‖((𝓕 (detectorRealPartCutoff a 1) : 𝓢(ℝ, ℂ)) xi)‖) ≤
      (2 ^ (volume : Measure ℝ).integrablePower *
        ∫ xi : ℝ,
          (1 + ‖xi‖) ^ (-((volume : Measure ℝ).integrablePower : ℝ))) *
        (SchwartzMap.seminorm ℂ 0 0 F +
          SchwartzMap.seminorm ℂ
            (k + (volume : Measure ℝ).integrablePower) 0 F) := by
      simpa [F, Real.norm_eq_abs, norm_iteratedFDeriv_zero] using hgeneral
    _ ≤ (2 ^ (volume : Measure ℝ).integrablePower *
        ∫ xi : ℝ,
          (1 + ‖xi‖) ^ (-((volume : Measure ℝ).integrablePower : ℝ))) *
        (detectorDerivativeL1Constant 0 +
          detectorDerivativeL1Constant
            (k + (volume : Measure ℝ).integrablePower)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hzero hhigh) hpref
    _ = detectorFourierMomentConstant k := rfl


theorem integral_pow_mul_norm_fourier_detectorRealPartCutoff_le
    {a : ℝ} {D : ℕ} (hD : 1 ≤ D)
    (ha0 : 0 ≤ a) (ha : a ≤ 1/2) (k : ℕ) :
    (∫ xi : ℝ, |xi|^k * ‖((𝓕 (detectorRealPartCutoff a D) : 𝓢(ℝ, ℂ)) xi)‖) ≤
      detectorFourierMomentConstant k := by
  exact (integral_pow_mul_norm_fourier_detectorRealPartCutoff_le_base hD ha0 k).trans
    (integral_pow_mul_norm_fourier_detectorRealPartCutoff_base_le ha0 ha k)

/-- The central Fourier L1 mass is uniformly bounded independently of H. -/
theorem central_fourier_mass_le
    {a : ℝ} {D : ℕ} (hD : 1 ≤ D) (ha0 : 0 ≤ a) (ha : a ≤ 1/2)
    (H : ℝ) :
    (∫ xi in Set.Icc (-H) H,
      ‖((𝓕 (detectorRealPartCutoff a D) : 𝓢(ℝ, ℂ)) xi)‖) ≤
      detectorFourierMomentConstant 0 := by
  have h := integral_pow_mul_norm_fourier_detectorRealPartCutoff_le hD ha0 ha 0
  simp only [pow_zero, one_mul] at h
  apply le_trans _ h
  exact MeasureTheory.setIntegral_le_integral
    (𝓕 (detectorRealPartCutoff a D) : 𝓢(ℝ, ℂ)).integrable.norm
    (Filter.Eventually.of_forall fun xi => norm_nonneg _)

/-- Arbitrary-power tail at the complete compact real-part range. -/
theorem fourier_tail_le
    {a H : ℝ} {D : ℕ} (hD : 1 ≤ D) (ha0 : 0 ≤ a) (ha : a ≤ 1/2)
    (k : ℕ) (hH : 0 < H) :
    (∫ xi in (Set.Icc (-H) H)ᶜ,
      ‖((𝓕 (detectorRealPartCutoff a D) : 𝓢(ℝ, ℂ)) xi)‖) ≤
      (H^k)⁻¹ * detectorFourierMomentConstant k := by
  exact (integral_compl_Icc_norm_fourier_le_inv_pow_mul
    (detectorRealPartCutoff a D) k hH).trans
    (mul_le_mul_of_nonneg_left
      (integral_pow_mul_norm_fourier_detectorRealPartCutoff_le hD ha0 ha k)
      (inv_nonneg.mpr (pow_nonneg hH.le k)))
end
end MAPMontgomeryFullStripFourier
#print axioms MAPMontgomeryFullStripFourier.central_fourier_mass_le
#print axioms MAPMontgomeryFullStripFourier.fourier_tail_le
