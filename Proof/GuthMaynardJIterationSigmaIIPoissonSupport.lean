import GuthMaynardJIterationSigmaIIAssembly

open scoped BigOperators Real FourierTransform ComplexConjugate ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-! Source-faithful cutoff support and second-Poisson tail insertion. -/

theorem sigmaIIZ2Finite_eq_tsum_of_support
    (ellRange : Finset ℤ) (psi2 : ℝ → ℝ)
    (M2 T m2 m2' u u' : ℝ)
    (hsupport : ∀ ell : ℤ,
      ell ∉ ellRange → psi2 (M2 * (ell : ℝ) / T) = 0) :
    sigmaIIZ2Finite ellRange psi2 M2 T m2 m2' u u' =
      ∑' ell : ℤ,
        (psi2 (M2 * (ell : ℝ) / T) : ℂ) *
          sourcePhase ((m2' * u' - m2 * u) * (ell : ℝ)) := by
  unfold sigmaIIZ2Finite
  rw [tsum_eq_sum (s := ellRange)]
  · apply Finset.sum_congr rfl
    intro ell hell
    congr 2
    ring
  · intro ell hell
    rw [hsupport ell hell]
    simp

theorem sigmaIIZ2Finite_eq_secondPoisson
    (ellRange : Finset ℤ) (psi2 : ℝ → ℝ)
    (hcompact : HasCompactSupport (fun x : ℝ => (psi2 x : ℂ)))
    (hsmooth : ContDiff ℝ ∞ (fun x : ℝ => (psi2 x : ℂ)))
    {M2 T : ℝ} (hM2 : 0 < M2) (hT : 0 < T)
    (m2 m2' u u' : ℝ)
    (hsupport : ∀ ell : ℤ,
      ell ∉ ellRange → psi2 (M2 * (ell : ℝ) / T) = 0) :
    sigmaIIZ2Finite ellRange psi2 M2 T m2 m2' u u' =
      (T / M2 : ℝ) • ∑' j : ℤ,
        FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ))
          (((j : ℝ) - (m2' * u' - m2 * u)) / (M2 / T)) := by
  rw [sigmaIIZ2Finite_eq_tsum_of_support ellRange psi2 M2 T m2 m2' u u'
    hsupport]
  exact second_poisson_source_scale (fun x : ℝ => (psi2 x : ℂ))
    hcompact hsmooth hM2 hT (m2' * u' - m2 * u)

def schwartzIntegerRetained (F : ℝ → ℂ) (A B y : ℝ) (j : ℤ) : ℂ :=
  if |((j : ℝ) - y) / A| < B then F (((j : ℝ) - y) / A) else 0

theorem summable_scaledShiftedQuadraticWeight
    {A : ℝ} (hA : 0 < A) (y : ℝ) :
    Summable (scaledShiftedQuadraticWeight A y) := by
  let coeff : ℝ := (1 + |y| / A) ^ 2 * max 1 (A ^ 2)
  have hmajor_sum : Summable (fun j : ℤ =>
      coeff * integerQuadraticEnvelope j) :=
    summable_integerQuadraticEnvelope.mul_left coeff
  apply hmajor_sum.of_nonneg_of_le
  · intro j
    unfold scaledShiftedQuadraticWeight
    positivity
  · intro j
    exact scaledShiftedQuadraticWeight_le_envelope hA y j

theorem summable_shiftedFourierSeries_of_decay
    (F : ℝ → ℂ) {K A : ℝ}
    (hA : 0 < A)
    (hdecay : ∀ xi, ‖F xi‖ ≤ K / (1 + |xi|) ^ 2) (y : ℝ) :
    Summable (fun j : ℤ => F (((j : ℝ) - y) / A)) := by
  have hweight := summable_scaledShiftedQuadraticWeight hA y
  apply (hweight.mul_left K).of_norm_bounded
  intro j
  calc
    ‖F (((j : ℝ) - y) / A)‖ ≤
        K / (1 + |((j : ℝ) - y) / A|) ^ 2 :=
      hdecay (((j : ℝ) - y) / A)
    _ = K * scaledShiftedQuadraticWeight A y j := by
      unfold scaledShiftedQuadraticWeight
      ring

theorem summable_schwartzIntegerRetained_of_decay
    (F : ℝ → ℂ) {K A B : ℝ}
    (hA : 0 < A)
    (hdecay : ∀ xi, ‖F xi‖ ≤ K / (1 + |xi|) ^ 2) (y : ℝ) :
    Summable (schwartzIntegerRetained F A B y) := by
  have hfull := summable_shiftedFourierSeries_of_decay F hA hdecay y
  apply Summable.of_norm
  apply hfull.norm.of_nonneg_of_le
  · intro j
    positivity
  · intro j
    unfold schwartzIntegerRetained
    split_ifs
    · exact le_rfl
    · simp

theorem summable_schwartzIntegerTail_of_decay
    (F : ℝ → ℂ) {K A B : ℝ}
    (hA : 0 < A)
    (hdecay : ∀ xi, ‖F xi‖ ≤ K / (1 + |xi|) ^ 2) (y : ℝ) :
    Summable (schwartzIntegerTail F A B y) := by
  have hfull := summable_shiftedFourierSeries_of_decay F hA hdecay y
  apply Summable.of_norm
  apply hfull.norm.of_nonneg_of_le
  · intro j
    positivity
  · intro j
    unfold schwartzIntegerTail
    split_ifs
    · exact le_rfl
    · simp

theorem shiftedFourierSeries_eq_retained_add_tail
    (F : ℝ → ℂ) {K A B : ℝ}
    (hA : 0 < A)
    (hdecay : ∀ xi, ‖F xi‖ ≤ K / (1 + |xi|) ^ 2) (y : ℝ) :
    (∑' j : ℤ, F (((j : ℝ) - y) / A)) =
      (∑' j : ℤ, schwartzIntegerRetained F A B y j) +
        ∑' j : ℤ, schwartzIntegerTail F A B y j := by
  have hretained := summable_schwartzIntegerRetained_of_decay
    F hA hdecay y (B := B)
  have htail := summable_schwartzIntegerTail_of_decay
    F hA hdecay y (B := B)
  rw [← hretained.tsum_add htail]
  apply tsum_congr
  intro j
  unfold schwartzIntegerRetained schwartzIntegerTail
  by_cases h : |((j : ℝ) - y) / A| < B
  · rw [if_pos h, if_neg (not_le.mpr h)]
    simp
  · rw [if_neg h, if_pos (le_of_not_gt h)]
    simp

def sourceSecondPoissonRetained (F : ℝ → ℂ)
    (M2 T B y : ℝ) : ℂ :=
  (T / M2 : ℝ) •
    ∑' j : ℤ, schwartzIntegerRetained F (M2 / T) B y j

theorem sourceSecondPoisson_eq_retained_add_tail
    (F : ℝ → ℂ) {K M2 T B : ℝ}
    (hM2 : 0 < M2) (hT : 0 < T)
    (hdecay : ∀ xi, ‖F xi‖ ≤ K / (1 + |xi|) ^ 2) (y : ℝ) :
    (T / M2 : ℝ) •
        (∑' j : ℤ, F (((j : ℝ) - y) / (M2 / T))) =
      sourceSecondPoissonRetained F M2 T B y +
        sourceSecondPoissonTail F M2 T B y := by
  rw [shiftedFourierSeries_eq_retained_add_tail F
    (div_pos hM2 hT) hdecay y]
  rw [smul_add]
  rfl

theorem sigmaIIZ2Finite_eq_retained_add_tail
    (ellRange : Finset ℤ) (psi2 : ℝ → ℝ)
    (hcompact : HasCompactSupport (fun x : ℝ => (psi2 x : ℂ)))
    (hsmooth : ContDiff ℝ ∞ (fun x : ℝ => (psi2 x : ℂ)))
    {K M2 T B : ℝ} (hM2 : 0 < M2) (hT : 0 < T)
    (hdecay : ∀ xi,
      ‖FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)) xi‖ ≤
        K / (1 + |xi|) ^ 2)
    (m2 m2' u u' : ℝ)
    (hsupport : ∀ ell : ℤ,
      ell ∉ ellRange → psi2 (M2 * (ell : ℝ) / T) = 0) :
    sigmaIIZ2Finite ellRange psi2 M2 T m2 m2' u u' =
      sourceSecondPoissonRetained
          (FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)))
          M2 T B (m2' * u' - m2 * u) +
        sourceSecondPoissonTail
          (FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)))
          M2 T B (m2' * u' - m2 * u) := by
  rw [sigmaIIZ2Finite_eq_secondPoisson ellRange psi2 hcompact hsmooth
    hM2 hT m2 m2' u u' hsupport]
  exact sourceSecondPoisson_eq_retained_add_tail _ hM2 hT hdecay _

/-- The certified uniform truncation error after the finite `ell` sum has
been identified with the full second-Poisson series.  Both the exact
`T/M2` factor and the affine shift `m2' u' - m2 u` remain visible. -/
theorem norm_sigmaIIZ2Finite_sub_retained_le_time_neg100
    (ellRange : Finset ℤ) (psi2 : ℝ → ℝ)
    (hcompact : HasCompactSupport (fun x : ℝ => (psi2 x : ℂ)))
    (hsmooth : ContDiff ℝ ∞ (fun x : ℝ => (psi2 x : ℂ)))
    (q : ℕ) {K0 K M2 T B Y C : ℝ}
    (hK : 0 ≤ K)
    (hM2 : 0 < M2) (hT : 0 < T) (hB : 0 < B) (hY : 0 ≤ Y)
    (hdecay2 : ∀ xi,
      ‖FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)) xi‖ ≤
        K0 / (1 + |xi|) ^ 2)
    (hdecay : ∀ xi,
      ‖FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)) xi‖ ≤
        K / (1 + |xi|) ^ (q + 2))
    (hbudget :
      (T / M2) * K *
        ((1 + Y / (M2 / T)) ^ 2 * max 1 ((M2 / T) ^ 2) *
          integerQuadraticMass) * T ^ 100 ≤ C * B ^ q)
    (m2 m2' u u' : ℝ)
    (hy : |m2' * u' - m2 * u| ≤ Y)
    (hsupport : ∀ ell : ℤ,
      ell ∉ ellRange → psi2 (M2 * (ell : ℝ) / T) = 0) :
    ‖sigmaIIZ2Finite ellRange psi2 M2 T m2 m2' u u' -
        sourceSecondPoissonRetained
          (FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)))
          M2 T B (m2' * u' - m2 * u)‖ ≤ C / T ^ 100 := by
  rw [sigmaIIZ2Finite_eq_retained_add_tail ellRange psi2 hcompact hsmooth
    hM2 hT hdecay2 m2 m2' u u' hsupport]
  rw [add_sub_cancel_left]
  exact norm_sourceSecondPoissonTail_le_time_neg100 _ q hK hM2 hT hB hY
    hdecay hbudget hy

def sigmaIIZPairRetainedKernel
    (psi2 : ℝ → ℝ) (f : ℝ → ℝ)
    (M2 T M3 Ctau B : ℝ) (m2 m2' : ℤ) (z : ℝ × ℝ) : ℂ :=
  ((f z.1 * f z.2 : ℝ) : ℂ) *
    (sigmaIIZ1 M3 Ctau (m2 : ℝ) (m2' : ℝ) z.1 z.2 *
      sourceSecondPoissonRetained
        (FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)))
        M2 T B ((m2' : ℝ) * z.2 - (m2 : ℝ) * z.1))

def sigmaIIZPairTailKernel
    (psi2 : ℝ → ℝ) (f : ℝ → ℝ)
    (M2 T M3 Ctau B : ℝ) (m2 m2' : ℤ) (z : ℝ × ℝ) : ℂ :=
  ((f z.1 * f z.2 : ℝ) : ℂ) *
    (sigmaIIZ1 M3 Ctau (m2 : ℝ) (m2' : ℝ) z.1 z.2 *
      sourceSecondPoissonTail
        (FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)))
        M2 T B ((m2' : ℝ) * z.2 - (m2 : ℝ) * z.1))

/-- Exact insertion of the retained/full-Poisson split at the pair-kernel
level used by `sigmaIIFinite_eq_re_product`. -/
theorem sigmaIIZPairKernel_eq_retained_add_tail
    (ellRange : Finset ℤ) (psi2 : ℝ → ℝ) (f : ℝ → ℝ)
    (hcompact : HasCompactSupport (fun x : ℝ => (psi2 x : ℂ)))
    (hsmooth : ContDiff ℝ ∞ (fun x : ℝ => (psi2 x : ℂ)))
    {K0 M2 T : ℝ} (hM2 : 0 < M2) (hT : 0 < T)
    (hdecay2 : ∀ xi,
      ‖FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)) xi‖ ≤
        K0 / (1 + |xi|) ^ 2)
    (M3 Ctau B : ℝ) (m2 m2' : ℤ) (z : ℝ × ℝ)
    (hsupport : ∀ ell : ℤ,
      ell ∉ ellRange → psi2 (M2 * (ell : ℝ) / T) = 0) :
    sigmaIIZPairKernel ellRange psi2 f M2 T M3 Ctau m2 m2' z =
      sigmaIIZPairRetainedKernel psi2 f M2 T M3 Ctau B m2 m2' z +
        sigmaIIZPairTailKernel psi2 f M2 T M3 Ctau B m2 m2' z := by
  unfold sigmaIIZPairKernel sigmaIIZPairRetainedKernel sigmaIIZPairTailKernel
  rw [sigmaIIZ2Finite_eq_retained_add_tail ellRange psi2 hcompact hsmooth
    hM2 hT hdecay2 (m2 : ℝ) (m2' : ℝ) z.1 z.2 hsupport]
  ring

/-- Pointwise error majorant ready for Tonelli after the certified tail is
inserted into the product-space kernel. -/
theorem norm_sigmaIIZPairTailKernel_le_time_neg100
    (psi2 : ℝ → ℝ) (f : ℝ → ℝ) (q : ℕ)
    {K M2 T B Y C M3 Ctau : ℝ}
    (hK : 0 ≤ K) (hM2 : 0 < M2) (hT : 0 < T)
    (hB : 0 < B) (hY : 0 ≤ Y) (hCtau : 0 ≤ Ctau)
    (hdecay : ∀ xi,
      ‖FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)) xi‖ ≤
        K / (1 + |xi|) ^ (q + 2))
    (hbudget :
      (T / M2) * K *
        ((1 + Y / (M2 / T)) ^ 2 * max 1 ((M2 / T) ^ 2) *
          integerQuadraticMass) * T ^ 100 ≤ C * B ^ q)
    (m2 m2' : ℤ) (z : ℝ × ℝ)
    (hy : |(m2' : ℝ) * z.2 - (m2 : ℝ) * z.1| ≤ Y) :
    ‖sigmaIIZPairTailKernel psi2 f M2 T M3 Ctau B m2 m2' z‖ ≤
      |f z.1 * f z.2| * (2 * Ctau) * (C / T ^ 100) := by
  have hZ1 : ‖sigmaIIZ1 M3 Ctau (m2 : ℝ) (m2' : ℝ) z.1 z.2‖ ≤
      2 * Ctau := by
    exact norm_sourcePhase_intervalIntegral_le hCtau
      (((m2' : ℝ) / M3) * z.2 - ((m2 : ℝ) / M3) * z.1)
  have htail : ‖sourceSecondPoissonTail
      (FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)))
      M2 T B ((m2' : ℝ) * z.2 - (m2 : ℝ) * z.1)‖ ≤ C / T ^ 100 :=
    norm_sourceSecondPoissonTail_le_time_neg100 _ q hK hM2 hT hB hY
      hdecay hbudget hy
  have hprod :
      ‖sigmaIIZ1 M3 Ctau (m2 : ℝ) (m2' : ℝ) z.1 z.2‖ *
          ‖sourceSecondPoissonTail
            (FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)))
            M2 T B ((m2' : ℝ) * z.2 - (m2 : ℝ) * z.1)‖ ≤
        (2 * Ctau) * (C / T ^ 100) := by
    exact mul_le_mul hZ1 htail (norm_nonneg _)
      (mul_nonneg (by norm_num) hCtau)
  unfold sigmaIIZPairTailKernel
  rw [norm_mul, norm_mul]
  calc
    ‖((f z.1 * f z.2 : ℝ) : ℂ)‖ *
          (‖sigmaIIZ1 M3 Ctau (m2 : ℝ) (m2' : ℝ) z.1 z.2‖ *
            ‖sourceSecondPoissonTail
              (FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)))
              M2 T B ((m2' : ℝ) * z.2 - (m2 : ℝ) * z.1)‖) ≤
        ‖((f z.1 * f z.2 : ℝ) : ℂ)‖ *
          ((2 * Ctau) * (C / T ^ 100)) :=
      mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = |f z.1 * f z.2| * (2 * Ctau) * (C / T ^ 100) := by
      simp only [Complex.norm_real, Real.norm_eq_abs]
      ring

/-- The certified pair-kernel tail remains negligible after the complete
product-space integration.  The support condition is only required where the
literal factor `f(u) f(u')` is nonzero. -/
theorem norm_integral_sigmaIIZPairTailKernel_le_time_neg100
    (psi2 : ℝ → ℝ) (f : ℝ → ℝ) (hf : Integrable f) (q : ℕ)
    {K M2 T B Y C M3 Ctau : ℝ}
    (hK : 0 ≤ K) (hM2 : 0 < M2) (hT : 0 < T)
    (hB : 0 < B) (hY : 0 ≤ Y) (hCtau : 0 ≤ Ctau)
    (hdecay : ∀ xi,
      ‖FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)) xi‖ ≤
        K / (1 + |xi|) ^ (q + 2))
    (hbudget :
      (T / M2) * K *
        ((1 + Y / (M2 / T)) ^ 2 * max 1 ((M2 / T) ^ 2) *
          integerQuadraticMass) * T ^ 100 ≤ C * B ^ q)
    (m2 m2' : ℤ)
    (hy : ∀ z : ℝ × ℝ, f z.1 * f z.2 ≠ 0 →
      |(m2' : ℝ) * z.2 - (m2 : ℝ) * z.1| ≤ Y) :
    ‖∫ z : ℝ × ℝ,
        sigmaIIZPairTailKernel psi2 f M2 T M3 Ctau B m2 m2' z‖ ≤
      (∫ u : ℝ, |f u|) ^ 2 * (2 * Ctau) * (C / T ^ 100) := by
  let D : ℝ := (2 * Ctau) * (C / T ^ 100)
  let g : ℝ × ℝ → ℝ := fun z => |f z.1| * |f z.2| * D
  have hg : Integrable g (volume.prod volume) := by
    exact (hf.norm.mul_prod hf.norm).mul_const D
  have hpoint : ∀ z : ℝ × ℝ,
      ‖sigmaIIZPairTailKernel psi2 f M2 T M3 Ctau B m2 m2' z‖ ≤ g z := by
    intro z
    by_cases hz : f z.1 * f z.2 = 0
    · unfold sigmaIIZPairTailKernel g
      rw [hz]
      rw [← abs_mul, hz]
      simp
    · have h := norm_sigmaIIZPairTailKernel_le_time_neg100
        (M3 := M3) psi2 f q hK hM2 hT hB hY hCtau hdecay hbudget
          m2 m2' z (hy z hz)
      simpa only [g, D, abs_mul, mul_assoc] using h
  refine (norm_integral_le_of_norm_le hg
    (Filter.Eventually.of_forall hpoint)).trans_eq ?_
  have hprodint :
      (∫ z : ℝ × ℝ, |f z.1| * |f z.2| ∂volume.prod volume) =
        (∫ u : ℝ, |f u|) * ∫ u : ℝ, |f u| := by
    simpa using (integral_prod_mul (μ := volume) (ν := volume)
      (fun u : ℝ => |f u|) (fun u : ℝ => |f u|))
  unfold g D
  rw [integral_mul_const, hprodint]
  ring

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.sigmaIIZ2Finite_eq_tsum_of_support
#print axioms GuthMaynardJIteration.sigmaIIZ2Finite_eq_secondPoisson
#print axioms GuthMaynardJIteration.summable_scaledShiftedQuadraticWeight
#print axioms GuthMaynardJIteration.summable_shiftedFourierSeries_of_decay
#print axioms GuthMaynardJIteration.summable_schwartzIntegerRetained_of_decay
#print axioms GuthMaynardJIteration.summable_schwartzIntegerTail_of_decay
#print axioms GuthMaynardJIteration.shiftedFourierSeries_eq_retained_add_tail
#print axioms GuthMaynardJIteration.sourceSecondPoisson_eq_retained_add_tail
#print axioms GuthMaynardJIteration.sigmaIIZ2Finite_eq_retained_add_tail
#print axioms GuthMaynardJIteration.norm_sigmaIIZ2Finite_sub_retained_le_time_neg100
#print axioms GuthMaynardJIteration.sigmaIIZPairKernel_eq_retained_add_tail
#print axioms GuthMaynardJIteration.norm_sigmaIIZPairTailKernel_le_time_neg100
#print axioms GuthMaynardJIteration.norm_integral_sigmaIIZPairTailKernel_le_time_neg100
