import GuthMaynardJIterationMediumSmoothing

open scoped BigOperators Real FourierTransform
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-- Pointwise retained pair-kernel bound with the source's exact cancellation
of the Poisson `T` against the localized mass `T f(u')`.  The remaining
outside scale is `1/M2`. -/
theorem norm_sigmaIIZPairRetainedKernel_le_indicatorMass
    (psi2 f : ℝ → ℝ) {K M2 T M3 Ctau B : ℝ}
    (hM2 : 0 < M2) (hT : 0 < T)
    (hCtau : 0 ≤ Ctau) (hB : 0 ≤ B)
    (hF : ∀ xi,
      ‖FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)) xi‖ ≤ K)
    (m2 m2' : ℤ) (u u' : ℝ)
    (hfu : 0 ≤ f u) (hfu' : 0 ≤ f u') :
    ‖sigmaIIZPairRetainedKernel psi2 f M2 T M3 Ctau B m2 m2' (u, u')‖ ≤
      ((2 * Ctau * K) / M2) * f u *
        (∑' j : ℤ,
          poissonRetainedIndicator (M2 / T) B
            ((m2' : ℝ) * u' - (m2 : ℝ) * u) j * (T * f u')) := by
  let y : ℝ := (m2' : ℝ) * u' - (m2 : ℝ) * u
  have hA : 0 < M2 / T := div_pos hM2 hT
  have hind := summable_poissonRetainedIndicator hA hB y
  have hZ1 : ‖sigmaIIZ1 M3 Ctau (m2 : ℝ) (m2' : ℝ) u u'‖ ≤
      2 * Ctau := by
    exact norm_sourcePhase_intervalIntegral_le hCtau
      (((m2' : ℝ) / M3) * u' - ((m2 : ℝ) / M3) * u)
  have hZ2 : ‖sourceSecondPoissonRetained
      (FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)))
      M2 T B y‖ ≤
      (T / M2) * K * ∑' j : ℤ,
        poissonRetainedIndicator (M2 / T) B y j :=
    norm_sourceSecondPoissonRetained_le_indicator _ hM2 hT hB hF y
  have hmass : (∑' j : ℤ,
      poissonRetainedIndicator (M2 / T) B y j * (T * f u')) =
      (T * f u') * ∑' j : ℤ,
        poissonRetainedIndicator (M2 / T) B y j := by
    calc
      (∑' j : ℤ, poissonRetainedIndicator (M2 / T) B y j * (T * f u')) =
        (∑' j : ℤ, poissonRetainedIndicator (M2 / T) B y j) *
          (T * f u') := hind.tsum_mul_right _
      _ = _ := by ring
  unfold sigmaIIZPairRetainedKernel
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hfu hfu')]
  rw [hmass]
  have hleft :
      (f u * f u') *
          (‖sigmaIIZ1 M3 Ctau (m2 : ℝ) (m2' : ℝ) u u'‖ *
            ‖sourceSecondPoissonRetained
              (FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)))
              M2 T B y‖) ≤
        (f u * f u') *
          ((2 * Ctau) *
            ((T / M2) * K * ∑' j : ℤ,
              poissonRetainedIndicator (M2 / T) B y j)) := by
    apply mul_le_mul_of_nonneg_left
    · exact mul_le_mul hZ1 hZ2
        (norm_nonneg _)
        (mul_nonneg (by norm_num) hCtau)
    · exact mul_nonneg hfu hfu'
  refine hleft.trans_eq ?_
  field_simp [hM2.ne']

theorem integrable_tsum_retainedIndicator_affine
    {m2 m2' M2 T B Y u : ℝ}
    (hM2 : 0 < M2) (hT : 0 < T) (hB : 0 ≤ B) (hY : 0 ≤ Y)
    (f : ℝ → ℝ) (hf : Integrable f) (hf0 : ∀ u', 0 ≤ f u')
    (hy : ∀ u', f u' ≠ 0 → |m2' * u' - m2 * u| ≤ Y) :
    Integrable (fun u' : ℝ =>
      ∑' j : ℤ, poissonRetainedIndicator (M2 / T) B
        (m2' * u' - m2 * u) j * (T * f u')) := by
  let A : ℝ := M2 / T
  let W : ℝ := (1 + B) ^ 2 * (1 + Y / A) ^ 2 * max 1 (A ^ 2)
  let mass : ℝ := W * integerQuadraticMass
  let y : ℝ → ℝ := fun u' => m2' * u' - m2 * u
  let g : ℝ → ℝ := fun u' => T * f u'
  let H : ℝ → ℝ := fun u' =>
    ∑' j : ℤ, poissonRetainedIndicator A B (y u') j * g u'
  have hA : 0 < A := div_pos hM2 hT
  have hW : 0 ≤ W := by
    dsimp only [W]
    positivity
  have hIQM : 0 ≤ integerQuadraticMass := by
    unfold integerQuadraticMass
    exact tsum_nonneg fun j => by
      unfold integerQuadraticEnvelope
      split_ifs <;> positivity
  have hmass : 0 ≤ mass := mul_nonneg hW hIQM
  have hyMeas : Measurable y := by
    dsimp only [y]
    fun_prop
  have htermMeas : ∀ j : ℤ, AEStronglyMeasurable
      (fun u' => poissonRetainedIndicator A B (y u') j * g u') := by
    intro j
    exact (measurable_poissonRetainedIndicator_comp y hyMeas j).aestronglyMeasurable.mul
      (hf.const_mul T).aestronglyMeasurable
  have hHMeas : AEStronglyMeasurable H := by
    apply AEMeasurable.aestronglyMeasurable
    exact AEMeasurable.tsum fun j => (htermMeas j).aemeasurable
  have hGInt : Integrable (fun u' => mass * g u') := by
    exact (hf.const_mul T).const_mul mass
  apply hGInt.mono' hHMeas
  apply Filter.Eventually.of_forall
  intro u'
  let weights : ℤ → ℝ := fun j => W * integerQuadraticEnvelope j
  let phi : ℤ → ℝ := fun j =>
    poissonRetainedIndicator A B (y u') j * g u'
  have hg0 : 0 ≤ g u' := by
    dsimp only [g]
    exact mul_nonneg hT.le (hf0 u')
  have hweights : Summable weights :=
    summable_integerQuadraticEnvelope.mul_left W
  have hphi0 : ∀ j, 0 ≤ phi j := by
    intro j
    exact mul_nonneg (by
      unfold poissonRetainedIndicator
      split_ifs <;> positivity) hg0
  have hmajor : ∀ j, phi j ≤ weights j * g u' := by
    intro j
    by_cases hgu : g u' = 0
    · simp [phi, hgu]
    · have hfu : f u' ≠ 0 := by
        intro hzero
        exact hgu (by simp [g, hzero])
      exact mul_le_mul_of_nonneg_right
        (poissonRetainedIndicator_le_uniformEnvelope hA hB hY (hy u' hfu) j)
        hg0
  have hphiSum : Summable phi :=
    (hweights.mul_right (g u')).of_nonneg_of_le hphi0 hmajor
  have hH0 : 0 ≤ H u' := by
    dsimp only [H, phi]
    exact tsum_nonneg hphi0
  rw [Real.norm_eq_abs, abs_of_nonneg hH0]
  calc
    H u' = ∑' j : ℤ, phi j := by rfl
    _ ≤ ∑' j : ℤ, weights j * g u' :=
      Summable.tsum_le_tsum hmajor hphiSum (hweights.mul_right (g u'))
    _ = (∑' j : ℤ, weights j) * g u' :=
      hweights.tsum_mul_right (g u')
    _ = mass * g u' := by
      dsimp only [weights, mass]
      rw [summable_integerQuadraticEnvelope.tsum_mul_left]
      rfl

/-- Integrate the retained pair kernel in `u'` and invoke the certified
Tonelli-to-affine-smoothing weld. -/
theorem integral_norm_sigmaIIZPairRetainedKernel_le_smoothing
    (psi2 psi f : ℝ → ℝ) {K M2 T M3 Ctau B Y : ℝ}
    (hK : 0 ≤ K) (hM2 : 0 < M2) (hT : 0 < T)
    (hCtau : 0 ≤ Ctau) (hB : 0 ≤ B) (hY : 0 ≤ Y)
    (hf : Integrable f) (hf0 : ∀ v, 0 ≤ f v)
    (hpsi0 : ∀ z, 0 ≤ psi z)
    (hF : ∀ xi,
      ‖FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)) xi‖ ≤ K)
    (m2 m2' : ℤ) (hm2' : 0 < (m2' : ℝ)) (u : ℝ)
    (hy : ∀ u', f u' ≠ 0 →
      |(m2' : ℝ) * u' - (m2 : ℝ) * u| ≤ Y)
    (hpsi_major : ∀ z, |z| ≤ (M2 / (m2' : ℝ)) * B → 1 ≤ psi z)
    (hlocal : ∀ j : ℤ, IntegrableOn (fun u' => T * f u')
      {u' | |(j : ℝ) - (m2' : ℝ) * u' + (m2 : ℝ) * u| ≤
        (M2 / T) * B})
    (hsmooth : ∀ j : ℤ, Integrable
      (fun u' => T * psi (T *
        (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j - u')) * f u'))
    (hsum : Summable (fun j : ℤ =>
      affineSmoothing T psi f
        (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j))) :
    (∫ u' : ℝ,
      ‖sigmaIIZPairRetainedKernel psi2 f M2 T M3 Ctau B m2 m2' (u, u')‖) ≤
      ((2 * Ctau * K) / M2) * f u *
        ∑' j : ℤ, affineSmoothing T psi f
          (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j) := by
  let c : ℝ := ((2 * Ctau * K) / M2) * f u
  have hc : 0 ≤ c := by
    dsimp only [c]
    exact mul_nonneg
      (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCtau) hK) hM2.le)
      (hf0 u)
  have hindicatorInt : Integrable (fun u' : ℝ =>
      ∑' j : ℤ, poissonRetainedIndicator (M2 / T) B
        ((m2' : ℝ) * u' - (m2 : ℝ) * u) j * (T * f u')) :=
    integrable_tsum_retainedIndicator_affine hM2 hT hB hY f hf hf0 hy
  have hpoint : ∀ u' : ℝ,
      ‖sigmaIIZPairRetainedKernel psi2 f M2 T M3 Ctau B m2 m2' (u, u')‖ ≤
        c * (∑' j : ℤ, poissonRetainedIndicator (M2 / T) B
          ((m2' : ℝ) * u' - (m2 : ℝ) * u) j * (T * f u')) := by
    intro u'
    exact norm_sigmaIIZPairRetainedKernel_le_indicatorMass psi2 f hM2 hT
      hCtau hB hF m2 m2' u u' (hf0 u) (hf0 u')
  have hrightInt : Integrable (fun u' : ℝ =>
      c * (∑' j : ℤ, poissonRetainedIndicator (M2 / T) B
        ((m2' : ℝ) * u' - (m2 : ℝ) * u) j * (T * f u'))) :=
    hindicatorInt.const_mul c
  have hfirst :
      (∫ u' : ℝ,
        ‖sigmaIIZPairRetainedKernel psi2 f M2 T M3 Ctau B m2 m2' (u, u')‖) ≤
      c * ∫ u' : ℝ, ∑' j : ℤ,
        poissonRetainedIndicator (M2 / T) B
          ((m2' : ℝ) * u' - (m2 : ℝ) * u) j * (T * f u') := by
    calc
      _ ≤ ∫ u' : ℝ, c * (∑' j : ℤ,
          poissonRetainedIndicator (M2 / T) B
            ((m2' : ℝ) * u' - (m2 : ℝ) * u) j * (T * f u')) := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
        · exact hrightInt
        · exact Filter.Eventually.of_forall hpoint
      _ = _ := by rw [integral_const_mul]
  refine hfirst.trans ?_
  dsimp only [c]
  apply mul_le_mul_of_nonneg_left _ hc
  exact integral_tsum_retainedIndicator_affine_le_smoothing hm2' hM2 hT
    hB hY psi f hf hf0 hpsi0 hy hpsi_major hlocal hsmooth hsum

/-- Exact dyadic coefficient accounting: the pair coefficient
`|m2*m2'|`, combined with the retained Poisson scale `1/M2`, leaves one
factor of `M2`. -/
theorem sourceDyadicPairCoefficient_le_M2
    {M2 Ctau K c : ℝ} (hM2 : 0 < M2)
    (hCtau : 0 ≤ Ctau) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (m2 m2' : ℤ)
    (hm2 : |(m2 : ℝ)| ≤ c * M2)
    (hm2' : |(m2' : ℝ)| ≤ c * M2) :
    |(m2 : ℝ) * (m2' : ℝ)| * ((2 * Ctau * K) / M2) ≤
      (2 * Ctau * K) * c ^ 2 * M2 := by
  have hcM : 0 ≤ c * M2 := mul_nonneg hc hM2.le
  have hpair : |(m2 : ℝ)| * |(m2' : ℝ)| ≤ (c * M2) ^ 2 := by
    calc
      |(m2 : ℝ)| * |(m2' : ℝ)| ≤ (c * M2) * (c * M2) :=
        mul_le_mul hm2 hm2' (abs_nonneg _) hcM
      _ = _ := by ring
  rw [abs_mul]
  calc
    |(m2 : ℝ)| * |(m2' : ℝ)| * ((2 * Ctau * K) / M2) ≤
        (c * M2) ^ 2 * ((2 * Ctau * K) / M2) := by
      exact mul_le_mul_of_nonneg_right hpair
        (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCtau) hK) hM2.le)
    _ = (2 * Ctau * K) * c ^ 2 * M2 := by
      field_simp [hM2.ne']

/-- Tracking the preceding medium-frequency factor `(M1+M3)` now gives the
literal source scale `M2*(M1+M3)`. -/
theorem sourceMediumOutsideFactor_le
    {M1 M2 M3 Ctau K c X : ℝ}
    (hM1 : 0 ≤ M1) (hM2 : 0 < M2) (hM3 : 0 ≤ M3)
    (hCtau : 0 ≤ Ctau) (hK : 0 ≤ K) (hc : 0 ≤ c) (hX : 0 ≤ X)
    (m2 m2' : ℤ)
    (hm2 : |(m2 : ℝ)| ≤ c * M2)
    (hm2' : |(m2' : ℝ)| ≤ c * M2) :
    (M1 + M3) *
        (|(m2 : ℝ) * (m2' : ℝ)| * ((2 * Ctau * K) / M2)) * X ≤
      (M2 * (M1 + M3)) * (2 * Ctau * K * c ^ 2) * X := by
  have hpair := sourceDyadicPairCoefficient_le_M2 hM2 hCtau hK hc
    m2 m2' hm2 hm2'
  calc
    (M1 + M3) *
        (|(m2 : ℝ) * (m2' : ℝ)| * ((2 * Ctau * K) / M2)) * X ≤
      (M1 + M3) * ((2 * Ctau * K) * c ^ 2 * M2) * X := by
        gcongr
    _ = (M2 * (M1 + M3)) * (2 * Ctau * K * c ^ 2) * X := by ring

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.norm_sigmaIIZPairRetainedKernel_le_indicatorMass
#print axioms GuthMaynardJIteration.integrable_tsum_retainedIndicator_affine
#print axioms GuthMaynardJIteration.integral_norm_sigmaIIZPairRetainedKernel_le_smoothing
#print axioms GuthMaynardJIteration.sourceDyadicPairCoefficient_le_M2
#print axioms GuthMaynardJIteration.sourceMediumOutsideFactor_le
