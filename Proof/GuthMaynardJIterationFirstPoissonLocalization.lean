import GuthMaynardJIterationSigmaIIPoissonSupport

/-!
# First Poisson localization in Guth--Maynard Lemma 9.2

This file formalizes TeX lines 1541--1552 of
`LargevaluesDirichlet17.tex`.  It specializes the certified scaled Poisson
formula at scale `1 / M₃`, splits the resulting integer series into the
source window and its complement, and bounds the complement by an explicit
Schwartz seminorm.  The factor multiplying this series is the literal Fourier
dilation sum, with the required absolute Jacobian `|m₂ / m₁|`.
-/

open scoped BigOperators Real FourierTransform ContDiff

noncomputable section
namespace GuthMaynardJIteration

/-- The integer sum to which the first Poisson summation is applied. -/
def sourceFirstPoissonSum
    (psi1 : ℝ → ℂ) (M3 m1 xi : ℝ) : ℂ :=
  ∑' m3 : ℤ,
    psi1 ((m3 : ℝ) / M3) * sourcePhase ((xi / m1) * (m3 : ℝ))

/-- The retained first-Poisson series.  Its defining condition is
`|M₃ (ℓ - ξ/m₁)| < B`. -/
def sourceFirstPoissonRetained
    (F : ℝ → ℂ) (M3 B m1 xi : ℝ) : ℂ :=
  sourceSecondPoissonRetained F 1 M3 B (xi / m1)

/-- The complementary first-Poisson tail, including the exact factor `M₃`. -/
def sourceFirstPoissonTail
    (F : ℝ → ℂ) (M3 B m1 xi : ℝ) : ℂ :=
  sourceSecondPoissonTail F 1 M3 B (xi / m1)

/-- The corrected `m₂` coefficient after Fourier dilation.  The absolute
value is forced by the Lebesgue change of variables when `m₁` can be
negative. -/
def sourceCorrectedM2FourierInner
    (m2Range : Finset ℤ) (fhat : ℝ → ℂ) (m1 : ℤ) (xi : ℝ) : ℂ :=
  ∑ m2 ∈ m2Range,
    ((|((m2 : ℝ) / (m1 : ℝ))| : ℝ) : ℂ) *
      fhat (((m2 : ℝ) / (m1 : ℝ)) * xi)

/-- The finite `m₂`-sum of Fourier dilations is exactly the corrected
absolute-Jacobian inner sum. -/
theorem sum_source_fourier_dilation_eq_corrected_inner
    (m2Range : Finset ℤ) (f : ℝ → ℂ) (m1 : ℤ)
    (hm1 : m1 ≠ 0) (hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0) (xi : ℝ) :
    (∑ m2 ∈ m2Range,
        FourierTransform.fourier
          (fun u : ℝ => f ((m1 : ℝ) * u / (m2 : ℝ))) xi) =
      sourceCorrectedM2FourierInner m2Range
        (FourierTransform.fourier f) m1 xi := by
  unfold sourceCorrectedM2FourierInner
  apply Finset.sum_congr rfl
  intro m2 hm2mem
  exact source_fourier_dilation f
    (m1 := (m1 : ℝ)) (m2 := (m2 : ℝ))
    (by exact_mod_cast hm1) (by exact_mod_cast hm2 m2 hm2mem) xi

theorem firstPoissonFrequency_eq
    {M3 : ℝ} (hM3 : 0 < M3) (ell : ℤ) (y : ℝ) :
    ((ell : ℝ) - y) / (1 / M3) = M3 * ((ell : ℝ) - y) := by
  field_simp [hM3.ne']

/-- Exact first Poisson formula in the source normalization. -/
theorem sourceFirstPoissonSum_eq_full
    (psi1 : ℝ → ℂ) (hcompact : HasCompactSupport psi1)
    (hsmooth : ContDiff ℝ ∞ psi1)
    {M3 m1 : ℝ} (hM3 : 0 < M3) (hm1 : m1 ≠ 0) (xi : ℝ) :
    sourceFirstPoissonSum psi1 M3 m1 xi =
      (M3 : ℝ) • ∑' ell : ℤ,
        FourierTransform.fourier psi1
          (M3 * ((ell : ℝ) - xi / m1)) := by
  unfold sourceFirstPoissonSum
  have h := second_poisson_source_scale psi1 hcompact hsmooth
    (show 0 < (1 : ℝ) by norm_num) hM3 (xi / m1)
  simpa only [one_mul, div_one, firstPoissonFrequency_eq hM3] using h

/-- Exact retained/tail split after first Poisson summation. -/
theorem sourceFirstPoissonSum_eq_retained_add_tail
    (psi1 : ℝ → ℂ) (hcompact : HasCompactSupport psi1)
    (hsmooth : ContDiff ℝ ∞ psi1)
    {K0 M3 B m1 : ℝ} (hM3 : 0 < M3) (hm1 : m1 ≠ 0)
    (hdecay2 : ∀ z,
      ‖FourierTransform.fourier psi1 z‖ ≤ K0 / (1 + |z|) ^ 2)
    (xi : ℝ) :
    sourceFirstPoissonSum psi1 M3 m1 xi =
      sourceFirstPoissonRetained
          (FourierTransform.fourier psi1) M3 B m1 xi +
        sourceFirstPoissonTail
          (FourierTransform.fourier psi1) M3 B m1 xi := by
  unfold sourceFirstPoissonRetained sourceFirstPoissonTail
  rw [sourceFirstPoissonSum_eq_full psi1 hcompact hsmooth hM3 hm1 xi]
  have h := sourceSecondPoisson_eq_retained_add_tail
    (FourierTransform.fourier psi1)
    (show 0 < (1 : ℝ) by norm_num) hM3 hdecay2 (xi / m1) (B := B)
  simpa only [div_one, firstPoissonFrequency_eq hM3] using h

/-- The normalized retained condition is precisely the source window in
`ξ - m₁ℓ`; no dyadic replacement of `|m₁|` has yet been made. -/
theorem firstPoissonLocalization_iff
    {M3 m1 : ℝ} (hM3 : 0 < M3) (hm1 : m1 ≠ 0)
    (B xi : ℝ) (ell : ℤ) :
    |M3 * ((ell : ℝ) - xi / m1)| < B ↔
      |xi - m1 * (ell : ℝ)| < (|m1| / M3) * B := by
  have hm1abs : 0 < |m1| := abs_pos.mpr hm1
  have hshift : (ell : ℝ) - xi / m1 =
      (m1 * (ell : ℝ) - xi) / m1 := by
    field_simp [hm1]
  rw [hshift, abs_mul, abs_of_pos hM3, abs_div,
    abs_sub_comm (m1 * (ell : ℝ)) xi]
  constructor
  · intro h
    have h' : M3 * |xi - m1 * (ell : ℝ)| < B * |m1| := by
      exact (div_lt_iff₀ hm1abs).mp (by simpa [mul_div_assoc] using h)
    rw [div_mul_eq_mul_div, lt_div_iff₀ hM3]
    simpa [mul_comm, mul_left_comm, mul_assoc] using h'
  · intro h
    have h' : M3 * |xi - m1 * (ell : ℝ)| < B * |m1| := by
      rw [div_mul_eq_mul_div, lt_div_iff₀ hM3] at h
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    have hquot :
        (M3 * |xi - m1 * (ell : ℝ)|) / |m1| < B :=
      (div_lt_iff₀ hm1abs).mpr h'
    simpa [mul_div_assoc] using hquot

/-- An explicit seminorm tail for the first Poisson series, uniform for
`|ξ/m₁| ≤ Y`. -/
theorem norm_sourceFirstPoissonTail_le
    (F : ℝ → ℂ) (q : ℕ) {K M3 B Y m1 : ℝ}
    (hK : 0 ≤ K) (hM3 : 0 < M3) (hB : 0 < B) (hY : 0 ≤ Y)
    (hdecay : ∀ z, ‖F z‖ ≤ K / (1 + |z|) ^ (q + 2))
    (hm1 : m1 ≠ 0) {xi : ℝ} (hxi : |xi / m1| ≤ Y) :
    ‖sourceFirstPoissonTail F M3 B m1 xi‖ ≤
      M3 * K *
        ((1 / B ^ q) *
          ((1 + Y / (1 / M3)) ^ 2 * max 1 ((1 / M3) ^ 2) *
            integerQuadraticMass)) := by
  unfold sourceFirstPoissonTail
  simpa only [div_one] using
    (norm_sourceSecondPoissonTail_le F q hK
      (show 0 < (1 : ℝ) by norm_num) hM3 hB hY hdecay hxi)

/-- Uniform `O(T⁻¹⁰⁰)` first-Poisson truncation.  The hypothesis records
the exact Schwartz seminorm/cutoff budget, including the outer `M₃`. -/
theorem norm_sourceFirstPoissonTail_le_time_neg100
    (F : ℝ → ℂ) (q : ℕ) {K M3 B Y C T m1 : ℝ}
    (hK : 0 ≤ K) (hM3 : 0 < M3) (hB : 0 < B) (hY : 0 ≤ Y)
    (hT : 0 < T)
    (hdecay : ∀ z, ‖F z‖ ≤ K / (1 + |z|) ^ (q + 2))
    (hbudget :
      M3 * K *
        ((1 + Y / (1 / M3)) ^ 2 * max 1 ((1 / M3) ^ 2) *
          integerQuadraticMass) * T ^ 100 ≤ C * B ^ q)
    (hm1 : m1 ≠ 0) {xi : ℝ} (hxi : |xi / m1| ≤ Y) :
    ‖sourceFirstPoissonTail F M3 B m1 xi‖ ≤ C / T ^ 100 := by
  refine (norm_sourceFirstPoissonTail_le F q hK hM3 hB hY
    hdecay hm1 hxi).trans ?_
  have hBq : 0 < B ^ q := pow_pos hB _
  have hT100 : 0 < T ^ 100 := pow_pos hT _
  calc
    M3 * K *
        ((1 / B ^ q) *
          ((1 + Y / (1 / M3)) ^ 2 * max 1 ((1 / M3) ^ 2) *
            integerQuadraticMass)) =
      (M3 * K *
        ((1 + Y / (1 / M3)) ^ 2 * max 1 ((1 / M3) ^ 2) *
          integerQuadraticMass)) / B ^ q := by ring
    _ ≤ (C * B ^ q / T ^ 100) / B ^ q := by
      gcongr
      exact (le_div_iff₀ hT100).2 (by simpa [mul_assoc] using hbudget)
    _ = C / T ^ 100 := by field_simp [hBq.ne', hT100.ne']

/-- Source-shaped full first-Poisson contribution for one `m₁`. -/
def sourceFirstPoissonContribution
    (F : ℝ → ℂ) (m2Range : Finset ℤ) (fhat : ℝ → ℂ)
    (M3 : ℝ) (m1 : ℤ) (xi : ℝ) : ℂ :=
  ((M3 : ℝ) • ∑' ell : ℤ,
      F (M3 * ((ell : ℝ) - xi / (m1 : ℝ)))) *
    sourceCorrectedM2FourierInner m2Range fhat m1 xi

/-- Retained source contribution, using the certified cutoff rather than an
informal `\lessapprox` range. -/
def sourceFirstPoissonRetainedContribution
    (F : ℝ → ℂ) (m2Range : Finset ℤ) (fhat : ℝ → ℂ)
    (M3 B : ℝ) (m1 : ℤ) (xi : ℝ) : ℂ :=
  sourceFirstPoissonRetained F M3 B (m1 : ℝ) xi *
    sourceCorrectedM2FourierInner m2Range fhat m1 xi

/-- The error in one `m₁` contribution is exactly the first-Poisson tail
times the corrected `|m₂/m₁|` Fourier inner sum. -/
theorem sourceFirstPoissonContribution_sub_retained
    (F : ℝ → ℂ) (m2Range : Finset ℤ) (fhat : ℝ → ℂ)
    {K0 M3 B : ℝ} (hM3 : 0 < M3)
    (hdecay2 : ∀ z, ‖F z‖ ≤ K0 / (1 + |z|) ^ 2)
    (m1 : ℤ) (hm1 : m1 ≠ 0) (xi : ℝ) :
    sourceFirstPoissonContribution F m2Range fhat M3 m1 xi -
        sourceFirstPoissonRetainedContribution F m2Range fhat M3 B m1 xi =
      sourceFirstPoissonTail F M3 B (m1 : ℝ) xi *
        sourceCorrectedM2FourierInner m2Range fhat m1 xi := by
  unfold sourceFirstPoissonContribution sourceFirstPoissonRetainedContribution
  have hsplit := sourceSecondPoisson_eq_retained_add_tail F
    (show 0 < (1 : ℝ) by norm_num) hM3 hdecay2 (xi / (m1 : ℝ)) (B := B)
  have hfull :
      (M3 : ℝ) • ∑' ell : ℤ,
          F (M3 * ((ell : ℝ) - xi / (m1 : ℝ))) =
        sourceFirstPoissonRetained F M3 B (m1 : ℝ) xi +
          sourceFirstPoissonTail F M3 B (m1 : ℝ) xi := by
    unfold sourceFirstPoissonRetained sourceFirstPoissonTail
    simpa only [div_one, firstPoissonFrequency_eq hM3] using hsplit
  rw [hfull]
  ring

/-- One-contribution `T⁻¹⁰⁰` error with the corrected Fourier inner
left explicit, ready for the finite `m₁` triangle inequality in (9.7). -/
theorem norm_sourceFirstPoissonContribution_sub_retained_le_time_neg100
    (F : ℝ → ℂ) (m2Range : Finset ℤ) (fhat : ℝ → ℂ)
    (q : ℕ) {K0 K M3 B Y C T : ℝ}
    (hK : 0 ≤ K) (hM3 : 0 < M3) (hB : 0 < B) (hY : 0 ≤ Y)
    (hT : 0 < T)
    (hdecay2 : ∀ z, ‖F z‖ ≤ K0 / (1 + |z|) ^ 2)
    (hdecay : ∀ z, ‖F z‖ ≤ K / (1 + |z|) ^ (q + 2))
    (hbudget :
      M3 * K *
        ((1 + Y / (1 / M3)) ^ 2 * max 1 ((1 / M3) ^ 2) *
          integerQuadraticMass) * T ^ 100 ≤ C * B ^ q)
    (m1 : ℤ) (hm1 : m1 ≠ 0) (xi : ℝ)
    (hxi : |xi / (m1 : ℝ)| ≤ Y) :
    ‖sourceFirstPoissonContribution F m2Range fhat M3 m1 xi -
        sourceFirstPoissonRetainedContribution F m2Range fhat M3 B m1 xi‖ ≤
      (C / T ^ 100) *
        ‖sourceCorrectedM2FourierInner m2Range fhat m1 xi‖ := by
  rw [sourceFirstPoissonContribution_sub_retained F m2Range fhat
    hM3 hdecay2 m1 hm1 xi, norm_mul]
  gcongr
  exact norm_sourceFirstPoissonTail_le_time_neg100 F q hK hM3 hB hY hT
    hdecay hbudget (by exact_mod_cast hm1) hxi

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.sum_source_fourier_dilation_eq_corrected_inner
#print axioms GuthMaynardJIteration.sourceFirstPoissonSum_eq_full
#print axioms GuthMaynardJIteration.sourceFirstPoissonSum_eq_retained_add_tail
#print axioms GuthMaynardJIteration.firstPoissonLocalization_iff
#print axioms GuthMaynardJIteration.norm_sourceFirstPoissonTail_le
#print axioms GuthMaynardJIteration.norm_sourceFirstPoissonTail_le_time_neg100
#print axioms GuthMaynardJIteration.sourceFirstPoissonContribution_sub_retained
#print axioms GuthMaynardJIteration.norm_sourceFirstPoissonContribution_sub_retained_le_time_neg100
