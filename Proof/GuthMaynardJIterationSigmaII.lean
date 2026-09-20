import GuthMaynardJIterationTail

open scoped BigOperators Real FourierTransform ComplexConjugate
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-! First source-faithful finite layer of TeX 1606--1611. -/

/-- The affine frequency forced by `xi = ell*m1 + (m1/M3)*tau`.
The TeX's later `M1` is not used here. -/
def sigmaIIAffineFrequency (M3 : ℝ) (ell m2 : ℤ) (tau : ℝ) : ℝ :=
  (ell : ℝ) * (m2 : ℝ) + ((m2 : ℝ) / M3) * tau

def sigmaIIFourierSummand (M3 : ℝ) (fhat : ℝ → ℂ)
    (ell m2 : ℤ) (tau : ℝ) : ℂ :=
  (m2 : ℂ) * fhat (sigmaIIAffineFrequency M3 ell m2 tau)

/-- One composed identity records both source corrections in the actual
medium-frequency chain: the signed dilation contributes `|m2/m1|`, while
the affine substitution contributes the forced denominator `M3`. -/
theorem source_corrected_dilation_at_affine_frequency
    (f : ℝ → ℂ) {m1 m2 M3 : ℝ}
    (hm1 : m1 ≠ 0) (hm2 : m2 ≠ 0) (hM3 : M3 ≠ 0)
    (ell tau : ℝ) :
    FourierTransform.fourier (fun u : ℝ => f (m1 * u / m2))
        (ell * m1 + (m1 / M3) * tau) =
      |m2 / m1| • FourierTransform.fourier f
        (ell * m2 + (m2 / M3) * tau) := by
  rw [source_fourier_dilation f hm1 hm2]
  congr 2
  exact congrArg (FourierTransform.fourier f)
    (source_frequency_affine_argument hm1 hM3 ell m2 tau)

/-- Literal finite-range version of the corrected `Sigma_II` at TeX 1606.
Both ranges are explicit, as is the cutoff half-width `Ctau`. -/
def sigmaIIFinite (ellRange m2Range : Finset ℤ)
    (psi2 : ℝ → ℝ) (fhat : ℝ → ℂ)
    (M2 T M3 Ctau : ℝ) : ℝ :=
  ∑ ell ∈ ellRange,
    psi2 (M2 * (ell : ℝ) / T) *
      ∫ tau in -Ctau..Ctau,
        ‖∑ m2 ∈ m2Range, sigmaIIFourierSummand M3 fhat ell m2 tau‖ ^ 2

/-- The exact conjugate double sum produced by expanding the square in
`sigmaIIFinite`. -/
def sigmaIIFiniteExpanded (ellRange m2Range : Finset ℤ)
    (psi2 : ℝ → ℝ) (fhat : ℝ → ℂ)
    (M2 T M3 Ctau : ℝ) : ℝ :=
  ∑ ell ∈ ellRange,
    psi2 (M2 * (ell : ℝ) / T) *
      ∫ tau in -Ctau..Ctau,
        ∑ m2 ∈ m2Range, ∑ m2' ∈ m2Range,
          (sigmaIIFourierSummand M3 fhat ell m2 tau *
            conj (sigmaIIFourierSummand M3 fhat ell m2' tau)).re

/-- Same exact finite expansion, with both finite coefficient sums moved
outside the bounded `tau` integral. -/
def sigmaIIFiniteExpandedIntegrated (ellRange m2Range : Finset ℤ)
    (psi2 : ℝ → ℝ) (fhat : ℝ → ℂ)
    (M2 T M3 Ctau : ℝ) : ℝ :=
  ∑ ell ∈ ellRange,
    psi2 (M2 * (ell : ℝ) / T) *
      ∑ m2 ∈ m2Range, ∑ m2' ∈ m2Range,
        ∫ tau in -Ctau..Ctau,
          (sigmaIIFourierSummand M3 fhat ell m2 tau *
            conj (sigmaIIFourierSummand M3 fhat ell m2' tau)).re

theorem norm_sq_finset_sum_eq_re_double_sum
    {ι : Type*} (s : Finset ι) (A : ι → ℂ) :
    ‖∑ i ∈ s, A i‖ ^ 2 =
      (∑ i ∈ s, ∑ j ∈ s, A i * conj (A j)).re := by
  let z : ℂ := ∑ i ∈ s, A i
  calc
    ‖z‖ ^ 2 = Complex.normSq z := Complex.sq_norm z
    _ = (z * conj z).re := by rw [Complex.mul_conj]; simp
    _ = (∑ i ∈ s, ∑ j ∈ s, A i * conj (A j)).re := by
      dsimp only [z]
      rw [map_sum, Finset.sum_mul]
      simp only [Finset.mul_sum]

theorem sigmaIIFinite_eq_expanded
    (ellRange m2Range : Finset ℤ)
    (psi2 : ℝ → ℝ) (fhat : ℝ → ℂ)
    (M2 T M3 Ctau : ℝ) :
    sigmaIIFinite ellRange m2Range psi2 fhat M2 T M3 Ctau =
      sigmaIIFiniteExpanded ellRange m2Range psi2 fhat M2 T M3 Ctau := by
  unfold sigmaIIFinite sigmaIIFiniteExpanded
  apply Finset.sum_congr rfl
  intro ell hell
  congr 1
  apply intervalIntegral.integral_congr
  intro tau htau
  simpa only [Complex.re_sum] using
    (norm_sq_finset_sum_eq_re_double_sum m2Range
      (fun m2 => sigmaIIFourierSummand M3 fhat ell m2 tau))

theorem sigmaIIFourierSummand_mul_conj
    (M3 : ℝ) (fhat : ℝ → ℂ) (ell m2 m2' : ℤ) (tau : ℝ) :
    sigmaIIFourierSummand M3 fhat ell m2 tau *
        conj (sigmaIIFourierSummand M3 fhat ell m2' tau) =
      ((m2 : ℝ) * (m2' : ℝ) : ℂ) *
        (fhat (sigmaIIAffineFrequency M3 ell m2 tau) *
          conj (fhat (sigmaIIAffineFrequency M3 ell m2' tau))) := by
  unfold sigmaIIFourierSummand
  simp only [map_mul, map_intCast]
  push_cast
  ring

theorem intervalIntegral_finset_double_sum
    {ι : Type*} (s : Finset ι) (F : ι → ι → ℝ → ℝ)
    (hF : ∀ i ∈ s, ∀ j ∈ s, Continuous (F i j))
    (a b : ℝ) :
    (∫ x in a..b, ∑ i ∈ s, ∑ j ∈ s, F i j x) =
      ∑ i ∈ s, ∑ j ∈ s, ∫ x in a..b, F i j x := by
  calc
    (∫ x in a..b, ∑ i ∈ s, ∑ j ∈ s, F i j x) =
        ∑ i ∈ s, ∫ x in a..b, ∑ j ∈ s, F i j x := by
      apply intervalIntegral.integral_finsetSum
      intro i hi
      apply Continuous.intervalIntegrable
      apply continuous_finsetSum
      intro j hj
      exact hF i hi j hj
    _ = ∑ i ∈ s, ∑ j ∈ s, ∫ x in a..b, F i j x := by
      apply Finset.sum_congr rfl
      intro i hi
      apply intervalIntegral.integral_finsetSum
      intro j hj
      exact (hF i hi j hj).intervalIntegrable a b

theorem sigmaIIFiniteExpanded_eq_integrated
    (ellRange m2Range : Finset ℤ)
    (psi2 : ℝ → ℝ) (fhat : ℝ → ℂ) (hfhat : Continuous fhat)
    (M2 T M3 Ctau : ℝ) :
    sigmaIIFiniteExpanded ellRange m2Range psi2 fhat M2 T M3 Ctau =
      sigmaIIFiniteExpandedIntegrated ellRange m2Range psi2 fhat M2 T M3 Ctau := by
  unfold sigmaIIFiniteExpanded sigmaIIFiniteExpandedIntegrated
  apply Finset.sum_congr rfl
  intro ell hell
  congr 1
  apply intervalIntegral_finset_double_sum
  intro m2 hm2 m2' hm2'
  unfold sigmaIIFourierSummand sigmaIIAffineFrequency
  fun_prop

theorem sigmaIIFinite_eq_integrated
    (ellRange m2Range : Finset ℤ)
    (psi2 : ℝ → ℝ) (fhat : ℝ → ℂ) (hfhat : Continuous fhat)
    (M2 T M3 Ctau : ℝ) :
    sigmaIIFinite ellRange m2Range psi2 fhat M2 T M3 Ctau =
      sigmaIIFiniteExpandedIntegrated ellRange m2Range psi2 fhat M2 T M3 Ctau := by
  rw [sigmaIIFinite_eq_expanded]
  exact sigmaIIFiniteExpanded_eq_integrated ellRange m2Range psi2 fhat hfhat
    M2 T M3 Ctau

/-! ## Exact second-Poisson tail specialization -/

/-- The discarded part of the source's second Poisson sum, including the
exact outer factor `T / M2`. -/
def sourceSecondPoissonTail (F : ℝ → ℂ) (M2 T B y : ℝ) : ℂ :=
  (T / M2 : ℝ) •
    ∑' j : ℤ, schwartzIntegerTail F (M2 / T) B y j

theorem norm_sourceSecondPoissonTail_le
    (F : ℝ → ℂ) (q : ℕ) {K M2 T B Y : ℝ}
    (hK : 0 ≤ K) (hM2 : 0 < M2) (hT : 0 < T)
    (hB : 0 < B) (hY : 0 ≤ Y)
    (hdecay : ∀ xi, ‖F xi‖ ≤ K / (1 + |xi|) ^ (q + 2))
    {y : ℝ} (hy : |y| ≤ Y) :
    ‖sourceSecondPoissonTail F M2 T B y‖ ≤
      (T / M2) * K *
        ((1 / B ^ q) *
          ((1 + Y / (M2 / T)) ^ 2 * max 1 ((M2 / T) ^ 2) *
            integerQuadraticMass)) := by
  have hscale : 0 < M2 / T := div_pos hM2 hT
  have hbase := norm_tsum_schwartzIntegerTail_le_uniform
    F q hK hscale hB hY hdecay hy
  unfold sourceSecondPoissonTail
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hT hM2)]
  calc
    (T / M2) * ‖∑' j : ℤ, schwartzIntegerTail F (M2 / T) B y j‖ ≤
        (T / M2) *
          (K * ((1 / B ^ q) *
            ((1 + Y / (M2 / T)) ^ 2 * max 1 ((M2 / T) ^ 2) *
              integerQuadraticMass))) := by gcongr
    _ = _ := by ring

/-- Uniform `T^-100` tail after restoring the source's exact `T/M2`
Poisson factor.  The budget visibly pays for that factor. -/
theorem norm_sourceSecondPoissonTail_le_time_neg100
    (F : ℝ → ℂ) (q : ℕ) {K M2 T B Y C : ℝ}
    (hK : 0 ≤ K) (hM2 : 0 < M2) (hT : 0 < T)
    (hB : 0 < B) (hY : 0 ≤ Y)
    (hdecay : ∀ xi, ‖F xi‖ ≤ K / (1 + |xi|) ^ (q + 2))
    (hbudget :
      (T / M2) * K *
        ((1 + Y / (M2 / T)) ^ 2 * max 1 ((M2 / T) ^ 2) *
          integerQuadraticMass) * T ^ 100 ≤ C * B ^ q)
    {y : ℝ} (hy : |y| ≤ Y) :
    ‖sourceSecondPoissonTail F M2 T B y‖ ≤ C / T ^ 100 := by
  refine (norm_sourceSecondPoissonTail_le
    F q hK hM2 hT hB hY hdecay hy).trans ?_
  have hBq : 0 < B ^ q := pow_pos hB _
  have hT100 : 0 < T ^ 100 := pow_pos hT _
  calc
    (T / M2) * K *
        ((1 / B ^ q) *
          ((1 + Y / (M2 / T)) ^ 2 * max 1 ((M2 / T) ^ 2) *
            integerQuadraticMass)) =
      ((T / M2) * K *
        ((1 + Y / (M2 / T)) ^ 2 * max 1 ((M2 / T) ^ 2) *
          integerQuadraticMass)) / B ^ q := by ring
    _ ≤ (C * B ^ q / T ^ 100) / B ^ q := by
      gcongr
      exact (le_div_iff₀ hT100).2 (by simpa [mul_assoc] using hbudget)
    _ = C / T ^ 100 := by field_simp [hBq.ne', hT100.ne']

/-- Literal Tonelli instantiation for the shifted decay weights which
majorize the discarded Poisson frequencies. -/
theorem integral_tsum_scaledShiftedDecayTail_mul
    {alpha : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) (q : ℕ) {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) (y : ℝ) (g : alpha → ℝ)
    (hg0 : ∀ x, 0 ≤ g x) (hg : Integrable g mu) :
    (∫ x, ∑' j : ℤ, scaledShiftedDecayTail q A B y j * g x ∂mu) =
        ∑' j : ℤ, ∫ x, scaledShiftedDecayTail q A B y j * g x ∂mu ∧
      (∑' j : ℤ, ∫ x, scaledShiftedDecayTail q A B y j * g x ∂mu) ≤
        (∑' j : ℤ, scaledShiftedDecayTail q A B y j) * ∫ x, g x ∂mu := by
  apply integral_tsum_of_summable_majorant mu
    (fun j x => scaledShiftedDecayTail q A B y j * g x)
    (scaledShiftedDecayTail q A B y) g
    (summable_scaledShiftedDecayTail q hA hB y) hg0 hg
  · intro j x
    exact mul_nonneg (by
      unfold scaledShiftedDecayTail
      split_ifs <;> positivity) (hg0 x)
  · intro j
    exact (hg.const_mul (scaledShiftedDecayTail q A B y j)).aestronglyMeasurable
  · intro j x
    exact le_rfl

def sourceAffineCenter (m2 m2' u : ℝ) (j : ℤ) : ℝ :=
  (m2 * u + (j : ℝ)) / m2'

/-- The Tonelli-localized integer sum welded to affine smoothing at the
source center `(m2*u+j)/m2'`.  The radius retains the exact
`(M2/m2')*B/T` before any dyadic simplification. -/
theorem tsum_poissonLocalizedIntegral_le_sourceAffineSmoothing
    {m2 m2' M2 B T u : ℝ} (hm2' : 0 < m2') (hT : 0 < T)
    (psi f : ℝ → ℝ)
    (hf0 : ∀ u', 0 ≤ f u') (hpsi0 : ∀ z, 0 ≤ psi z)
    (hpsi_major : ∀ z, |z| ≤ (M2 / m2') * B → 1 ≤ psi z)
    (hlocal : ∀ j : ℤ, IntegrableOn (fun u' => T * f u')
      {u' | |(j : ℝ) - m2' * u' + m2 * u| ≤ (M2 / T) * B})
    (hsmooth : ∀ j : ℤ, Integrable
      (fun u' => T * psi (T * (sourceAffineCenter m2 m2' u j - u')) * f u'))
    (hsum : Summable
      (fun j : ℤ => affineSmoothing T psi f (sourceAffineCenter m2 m2' u j))) :
    (∑' j : ℤ, ∫ u' in
        {u' | |(j : ℝ) - m2' * u' + m2 * u| ≤ (M2 / T) * B},
          T * f u') ≤
      ∑' j : ℤ, affineSmoothing T psi f (sourceAffineCenter m2 m2' u j) := by
  have hset (j : ℤ) :
      {u' : ℝ | |(j : ℝ) - m2' * u' + m2 * u| ≤ (M2 / T) * B} =
        Metric.closedBall (sourceAffineCenter m2 m2' u j)
          ((M2 / m2') * B / T) := by
    ext u'
    exact poissonLocalization_iff_mem_affineBall hm2' hT
      m2 (j : ℝ) u u' B
  simp_rw [hset]
  exact tsum_source_localized_integral_le_affineSmoothing
    (C := (M2 / m2') * B) hT
    (fun j : ℤ => sourceAffineCenter m2 m2' u j) psi f
    hf0 hpsi0 hpsi_major
    (fun j => by simpa [hset j] using hlocal j) hsmooth hsum

/-! ## Exact low/medium/high frequency bookkeeping from TeX 1556--1562 -/

def lowFrequencyRegion (a : ℝ) : Set ℝ := {xi | |xi| ≤ a}

def mediumFrequencyRegion (a b : ℝ) : Set ℝ :=
  {xi | a < |xi| ∧ |xi| ≤ b}

def highFrequencyRegion (b : ℝ) : Set ℝ := {xi | b < |xi|}

theorem measurableSet_lowFrequencyRegion (a : ℝ) :
    MeasurableSet (lowFrequencyRegion a) := by
  exact measurableSet_le continuous_abs.measurable measurable_const

theorem measurableSet_mediumFrequencyRegion (a b : ℝ) :
    MeasurableSet (mediumFrequencyRegion a b) := by
  exact (measurableSet_lt measurable_const continuous_abs.measurable).inter
    (measurableSet_le continuous_abs.measurable measurable_const)

theorem measurableSet_highFrequencyRegion (b : ℝ) :
    MeasurableSet (highFrequencyRegion b) := by
  exact measurableSet_lt measurable_const continuous_abs.measurable

theorem low_union_medium_union_high (a b : ℝ) :
    (lowFrequencyRegion a ∪ mediumFrequencyRegion a b) ∪
      highFrequencyRegion b = Set.univ := by
  ext xi
  simp only [lowFrequencyRegion, mediumFrequencyRegion, highFrequencyRegion,
    Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  by_cases hlow : |xi| ≤ a
  · exact Or.inl (Or.inl hlow)
  · have halow : a < |xi| := lt_of_not_ge hlow
    by_cases hhigh : |xi| ≤ b
    · exact Or.inl (Or.inr ⟨halow, hhigh⟩)
    · exact Or.inr (lt_of_not_ge hhigh)

theorem disjoint_low_medium (a b : ℝ) :
    Disjoint (lowFrequencyRegion a) (mediumFrequencyRegion a b) := by
  apply Set.disjoint_left.2
  intro xi hlow hmed
  exact (not_lt_of_ge hlow) hmed.1

theorem disjoint_lowUnionMedium_high (a b : ℝ) (hab : a ≤ b) :
    Disjoint (lowFrequencyRegion a ∪ mediumFrequencyRegion a b)
      (highFrequencyRegion b) := by
  apply Set.disjoint_left.2
  intro xi hlm hhigh
  change b < |xi| at hhigh
  rcases hlm with hlow | hmed
  · change |xi| ≤ a at hlow
    exact (not_lt_of_ge (le_trans hlow hab)) hhigh
  · change a < |xi| ∧ |xi| ≤ b at hmed
    exact (not_lt_of_ge hmed.2) hhigh

/-- Exact three-way integral partition.  It is the equality at TeX 1559,
with no boundary loss or implicit overlap. -/
theorem integral_eq_low_add_medium_add_high
    (F : ℝ → ℝ) (hF : Integrable F)
    (a b : ℝ) (hab : a ≤ b) :
    (∫ xi : ℝ, F xi) =
      (∫ xi in lowFrequencyRegion a, F xi) +
      (∫ xi in mediumFrequencyRegion a b, F xi) +
      ∫ xi in highFrequencyRegion b, F xi := by
  let L := lowFrequencyRegion a
  let R := mediumFrequencyRegion a b
  let H := highFrequencyRegion b
  have hL : MeasurableSet L := measurableSet_lowFrequencyRegion a
  have hR : MeasurableSet R := measurableSet_mediumFrequencyRegion a b
  have hH : MeasurableSet H := measurableSet_highFrequencyRegion b
  have hLR : Disjoint L R := disjoint_low_medium a b
  have hLRH : Disjoint (L ∪ R) H := disjoint_lowUnionMedium_high a b hab
  have hall : (L ∪ R) ∪ H = Set.univ := low_union_medium_union_high a b
  calc
    (∫ xi : ℝ, F xi) = ∫ xi in (L ∪ R) ∪ H, F xi := by
      rw [hall]
      simp
    _ = (∫ xi in L ∪ R, F xi) + ∫ xi in H, F xi :=
      setIntegral_union₀ hLRH.aedisjoint hH.nullMeasurableSet
        hF.integrableOn hF.integrableOn
    _ = ((∫ xi in L, F xi) + ∫ xi in R, F xi) +
        ∫ xi in H, F xi := by
      rw [setIntegral_union₀ hLR.aedisjoint hR.nullMeasurableSet
        hF.integrableOn hF.integrableOn]
    _ = _ := by rfl

def sourceLowFrequencyCutoff (T eta M1 M3 : ℝ) : ℝ :=
  Real.rpow T eta * M1 / M3

def sourceHighFrequencyCutoff (T : ℝ) : ℝ := T ^ 6

/-- Source specialization of the low/medium/high split, retaining both the
`T^eta M1/M3` lower transition and the literal `T^6` high cutoff. -/
theorem sourceFrequencyIntegralSplit
    (ghat : ℝ → ℂ) (hghat : Integrable (fun xi => ‖ghat xi‖ ^ 2))
    (T eta M1 M3 : ℝ)
    (hcut : sourceLowFrequencyCutoff T eta M1 M3 ≤
      sourceHighFrequencyCutoff T) :
    (∫ xi : ℝ, ‖ghat xi‖ ^ 2) =
      (∫ xi in lowFrequencyRegion (sourceLowFrequencyCutoff T eta M1 M3),
        ‖ghat xi‖ ^ 2) +
      (∫ xi in mediumFrequencyRegion
        (sourceLowFrequencyCutoff T eta M1 M3)
        (sourceHighFrequencyCutoff T), ‖ghat xi‖ ^ 2) +
      ∫ xi in highFrequencyRegion (sourceHighFrequencyCutoff T),
        ‖ghat xi‖ ^ 2 :=
  integral_eq_low_add_medium_add_high (fun xi => ‖ghat xi‖ ^ 2) hghat
    (sourceLowFrequencyCutoff T eta M1 M3)
    (sourceHighFrequencyCutoff T) hcut

/-- Deterministic bookkeeping which assembles separately proved low,
medium, and high estimates without changing their loss parameters. -/
theorem sourceFrequencyIntegral_le_of_region_bounds
    (ghat : ℝ → ℂ) (hghat : Integrable (fun xi => ‖ghat xi‖ ^ 2))
    (T eta M1 M3 lowBound mediumBound highBound : ℝ)
    (hcut : sourceLowFrequencyCutoff T eta M1 M3 ≤
      sourceHighFrequencyCutoff T)
    (hlow : (∫ xi in
      lowFrequencyRegion (sourceLowFrequencyCutoff T eta M1 M3),
        ‖ghat xi‖ ^ 2) ≤ lowBound)
    (hmedium : (∫ xi in mediumFrequencyRegion
      (sourceLowFrequencyCutoff T eta M1 M3)
      (sourceHighFrequencyCutoff T), ‖ghat xi‖ ^ 2) ≤ mediumBound)
    (hhigh : (∫ xi in highFrequencyRegion (sourceHighFrequencyCutoff T),
      ‖ghat xi‖ ^ 2) ≤ highBound) :
    (∫ xi : ℝ, ‖ghat xi‖ ^ 2) ≤
      lowBound + mediumBound + highBound := by
  rw [sourceFrequencyIntegralSplit ghat hghat T eta M1 M3 hcut]
  linarith

/-- The exact low-frequency volume estimate used before inserting the
source's pointwise bound for `ghat`. -/
theorem integral_lowFrequencyRegion_le_two_mul
    (F : ℝ → ℝ) {a S : ℝ} (ha : 0 ≤ a)
    (hF : IntegrableOn F (lowFrequencyRegion a))
    (hbound : ∀ xi ∈ lowFrequencyRegion a, F xi ≤ S) :
    (∫ xi in lowFrequencyRegion a, F xi) ≤ 2 * a * S := by
  have hset : lowFrequencyRegion a = Set.Icc (-a) a := by
    ext xi
    simp [lowFrequencyRegion, abs_le]
  have hconst : IntegrableOn (fun _ : ℝ => S) (lowFrequencyRegion a) := by
    rw [hset]
    apply integrableOn_const
    · rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    · simp
  calc
    (∫ xi in lowFrequencyRegion a, F xi) ≤
        ∫ _xi in lowFrequencyRegion a, S :=
      setIntegral_mono_on hF hconst (measurableSet_lowFrequencyRegion a) hbound
    _ = volume.real (lowFrequencyRegion a) * S := by
      rw [setIntegral_const, smul_eq_mul]
    _ = 2 * a * S := by
      rw [hset, Real.volume_real_Icc_of_le (by linarith)]
      ring

/-- Low region bound in the exact Guth--Maynard cutoff
`T^eta*M1/M3`. -/
theorem sourceLowFrequencyIntegral_le
    (ghat : ℝ → ℂ) {T eta M1 M3 S : ℝ}
    (hcut0 : 0 ≤ sourceLowFrequencyCutoff T eta M1 M3)
    (hghat : IntegrableOn (fun xi => ‖ghat xi‖ ^ 2)
      (lowFrequencyRegion (sourceLowFrequencyCutoff T eta M1 M3)))
    (hpoint : ∀ xi ∈ lowFrequencyRegion
      (sourceLowFrequencyCutoff T eta M1 M3), ‖ghat xi‖ ^ 2 ≤ S) :
    (∫ xi in lowFrequencyRegion (sourceLowFrequencyCutoff T eta M1 M3),
      ‖ghat xi‖ ^ 2) ≤
        2 * sourceLowFrequencyCutoff T eta M1 M3 * S :=
  integral_lowFrequencyRegion_le_two_mul
    (fun xi => ‖ghat xi‖ ^ 2) hcut0 hghat hpoint


end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.source_corrected_dilation_at_affine_frequency
#print axioms GuthMaynardJIteration.norm_sq_finset_sum_eq_re_double_sum
#print axioms GuthMaynardJIteration.sigmaIIFinite_eq_expanded
#print axioms GuthMaynardJIteration.sigmaIIFourierSummand_mul_conj
#print axioms GuthMaynardJIteration.intervalIntegral_finset_double_sum
#print axioms GuthMaynardJIteration.sigmaIIFiniteExpanded_eq_integrated
#print axioms GuthMaynardJIteration.sigmaIIFinite_eq_integrated
#print axioms GuthMaynardJIteration.norm_sourceSecondPoissonTail_le
#print axioms GuthMaynardJIteration.norm_sourceSecondPoissonTail_le_time_neg100
#print axioms GuthMaynardJIteration.integral_tsum_scaledShiftedDecayTail_mul
#print axioms GuthMaynardJIteration.tsum_poissonLocalizedIntegral_le_sourceAffineSmoothing
#print axioms GuthMaynardJIteration.measurableSet_lowFrequencyRegion
#print axioms GuthMaynardJIteration.measurableSet_mediumFrequencyRegion
#print axioms GuthMaynardJIteration.measurableSet_highFrequencyRegion
#print axioms GuthMaynardJIteration.low_union_medium_union_high
#print axioms GuthMaynardJIteration.disjoint_low_medium
#print axioms GuthMaynardJIteration.disjoint_lowUnionMedium_high
#print axioms GuthMaynardJIteration.integral_eq_low_add_medium_add_high
#print axioms GuthMaynardJIteration.sourceFrequencyIntegralSplit
#print axioms GuthMaynardJIteration.sourceFrequencyIntegral_le_of_region_bounds
#print axioms GuthMaynardJIteration.integral_lowFrequencyRegion_le_two_mul
#print axioms GuthMaynardJIteration.sourceLowFrequencyIntegral_le
