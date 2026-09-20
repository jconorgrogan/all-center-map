import JutilaReflectionDirichletIdentity
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Jutila's literal two-scale smoothing identity

The first display in the proof of Jutila's Lemma 1 (Acta Arith. 32
(1977), p. 58) uses the difference of scales `2N` and `N`.  This file
forms that exact difference from the certified one-scale Mellin identities.
The scale difference is essential: its numerator vanishes at `w = 0`, so
the apparent pole contributed by the factor `1 / w` is removable.

The subsequent contour shift to `Re (s+w) = -1/2` is not asserted here.
-/

namespace JutilaTwoScaleSmoothing

open Complex Real MeasureTheory Set Filter
open scoped BigOperators LSeries.notation
open JutilaReflectionKernelInterchange
open JutilaReflectionDirichletIdentity

noncomputable section

def twoScaleArithmeticWeight (N h : ℝ) (n : PositiveNat) : ℝ :=
  Real.exp (-Real.rpow (dirichletRatio (2 * N) n) h) -
    Real.exp (-Real.rpow (dirichletRatio N n) h)

def twoScaleSpectralFactor (N : ℝ) (w : ℂ) : ℂ :=
  ((2 * N : ℝ) : ℂ) ^ w - (N : ℂ) ^ w

theorem twoScaleSpectralFactor_zero (N : ℝ) :
    twoScaleSpectralFactor N 0 = 0 := by
  simp [twoScaleSpectralFactor]

def twoScaleRemovableQuotient (N : ℝ) : ℂ → ℂ :=
  Function.update
    (fun w : ℂ => twoScaleSpectralFactor N w / w)
    0
    (Complex.log (((2 * N : ℝ) : ℂ)) - Complex.log (N : ℂ))

/-- The two-scale numerator cancels the `1/w` pole at the origin.  This is
the exact removable-singularity step needed before the contour can cross
`w = 0`. -/
theorem continuousAt_twoScaleRemovableQuotient_zero
    {N : ℝ} (hN : 0 < N) :
    ContinuousAt (twoScaleRemovableQuotient N) 0 := by
  have h2N : ((2 * N : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) hN.ne')
  have hNC : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  have hA := (hasDerivAt_id' (0 : ℂ)).const_cpow (c := ((2 * N : ℝ) : ℂ))
    (Or.inl h2N)
  have hB := (hasDerivAt_id' (0 : ℂ)).const_cpow (c := (N : ℂ))
    (Or.inl hNC)
  have hdiff := hA.sub hB
  have hcont := hdiff.continuousAt_div
  simpa [twoScaleRemovableQuotient, twoScaleSpectralFactor] using hcont

theorem analyticAt_twoScaleRemovableQuotient_zero
    {N : ℝ} (hN : 0 < N) :
    AnalyticAt ℂ (twoScaleRemovableQuotient N) 0 := by
  have h2N : ((2 * N : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) hN.ne')
  have hNC : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · filter_upwards [self_mem_nhdsWithin] with w hw
    have hw0 : w ≠ 0 := by simpa using hw
    have hbase : DifferentiableAt ℂ (fun u : ℂ => twoScaleSpectralFactor N u / u) w := by
      apply DifferentiableAt.div _ differentiableAt_id hw0
      exact
      ((hasDerivAt_id' w).const_cpow (c := ((2 * N : ℝ) : ℂ)) (Or.inl h2N)).differentiableAt.sub
        ((hasDerivAt_id' w).const_cpow (c := (N : ℂ)) (Or.inl hNC)).differentiableAt
    refine hbase.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hw0] with u hu
    simp [twoScaleRemovableQuotient, Function.update_of_ne hu]
  · exact continuousAt_twoScaleRemovableQuotient_zero hN

theorem differentiableAt_twoScaleRemovableQuotient
    {N : ℝ} (hN : 0 < N) (w : ℂ) :
    DifferentiableAt ℂ (twoScaleRemovableQuotient N) w := by
  rcases eq_or_ne w 0 with rfl | hw
  · exact (analyticAt_twoScaleRemovableQuotient_zero hN).differentiableAt
  · have h2N : ((2 * N : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) hN.ne')
    have hNC : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
    have hbase : DifferentiableAt ℂ (fun u : ℂ => twoScaleSpectralFactor N u / u) w := by
      apply DifferentiableAt.div _ differentiableAt_id hw
      exact
        ((hasDerivAt_id' w).const_cpow (c := ((2 * N : ℝ) : ℂ)) (Or.inl h2N)).differentiableAt.sub
          ((hasDerivAt_id' w).const_cpow (c := (N : ℂ)) (Or.inl hNC)).differentiableAt
    refine hbase.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hw] with u hu
    simp [twoScaleRemovableQuotient, Function.update_of_ne hu]

def twoScaleContourIntegrand
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (s : ℂ)
    (N h : ℝ) (w : ℂ) : ℂ :=
  Complex.Gamma (1 + w / (h : ℂ)) *
    twoScaleRemovableQuotient N w *
      DirichletCharacter.LFunction chi (s + w)

/-- Away from the possible pole of a principal L-function and from gamma
poles, Jutila's literal two-scale contour integrand is holomorphic. -/
theorem differentiableAt_twoScaleContourIntegrand
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hchi : chi ≠ 1) (s : ℂ) {N h : ℝ} (hN : 0 < N)
    (w : ℂ) (hGammaStrip : 0 < (1 + w / (h : ℂ)).re) :
    DifferentiableAt ℂ (twoScaleContourIntegrand chi s N h) w := by
  have hGammaNoPole : ∀ n : ℕ, (1 + w / (h : ℂ)) ≠ -(n : ℂ) := by
    intro n hn
    have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [hn] at hGammaStrip
    norm_num [Complex.neg_re] at hGammaStrip
    nlinarith
  have hGamma : DifferentiableAt ℂ
      (fun u : ℂ => Complex.Gamma (1 + u / (h : ℂ))) w := by
    have hOuter := Complex.differentiableAt_Gamma
      (1 + w / (h : ℂ)) hGammaNoPole
    exact hOuter.comp w (by fun_prop)
  have hL : DifferentiableAt ℂ
      (fun u : ℂ => DirichletCharacter.LFunction chi (s + u)) w := by
    exact (DirichletCharacter.differentiable_LFunction hchi (s + w)).comp w (by fun_prop)
  exact (hGamma.mul (differentiableAt_twoScaleRemovableQuotient hN w)).mul hL

/-- Exact finite-rectangle contour shift for the nonprincipal two-scale
integrand.  Horizontal edges are still present; sending them to infinity is
the next analytic estimate in Jutila's proof. -/
theorem twoScaleContourIntegrand_boundary_rectangle
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hchi : chi ≠ 1) (s : ℂ) {N h : ℝ} (hN : 0 < N)
    (z w : ℂ)
    (hGammaStrip : ∀ u ∈ (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im),
      0 < (1 + u / (h : ℂ)).re) :
    (∫ x : ℝ in z.re..w.re,
          twoScaleContourIntegrand chi s N h (x + z.im * Complex.I)) -
        (∫ x : ℝ in z.re..w.re,
          twoScaleContourIntegrand chi s N h (x + w.im * Complex.I)) +
        Complex.I • (∫ y : ℝ in z.im..w.im,
          twoScaleContourIntegrand chi s N h (w.re + y * Complex.I)) -
        Complex.I • (∫ y : ℝ in z.im..w.im,
          twoScaleContourIntegrand chi s N h (z.re + y * Complex.I)) = 0 := by
  apply Complex.integral_boundary_rect_eq_zero_of_differentiableOn
  intro u hu
  exact (differentiableAt_twoScaleContourIntegrand hchi s hN u
    (hGammaStrip u hu)).differentiableWithinAt

def principalTwoScaleIntegrandInLArgument
    (s : ℂ) (N h : ℝ) (z : ℂ) : ℂ :=
  Complex.Gamma (1 + (z - s) / (h : ℂ)) *
    twoScaleRemovableQuotient N (z - s) * riemannZeta z

/-- Exact principal-character residue crossed in Jutila's first contour
shift.  The later numerical estimate that this residue has size `< 1` is
separate; here Lean certifies the residue formula itself. -/
theorem principalTwoScaleIntegrand_residue_one
    (s : ℂ) {N h : ℝ} (hN : 0 < N)
    (hGammaNoPole : ∀ n : ℕ,
      (1 + ((1 : ℂ) - s) / (h : ℂ)) ≠ -(n : ℂ)) :
    Tendsto
      (fun z : ℂ => (z - 1) * principalTwoScaleIntegrandInLArgument s N h z)
      (nhdsWithin (1 : ℂ) ({(1 : ℂ)}ᶜ))
      (nhds (Complex.Gamma (1 + ((1 : ℂ) - s) / (h : ℂ)) *
        twoScaleRemovableQuotient N ((1 : ℂ) - s))) := by
  let A : ℂ → ℂ := fun z =>
    Complex.Gamma (1 + (z - s) / (h : ℂ)) *
      twoScaleRemovableQuotient N (z - s)
  have hGamma : DifferentiableAt ℂ
      (fun z : ℂ => Complex.Gamma (1 + (z - s) / (h : ℂ))) 1 := by
    exact (Complex.differentiableAt_Gamma
      (1 + ((1 : ℂ) - s) / (h : ℂ)) hGammaNoPole).comp 1 (by fun_prop)
  have hQuot : DifferentiableAt ℂ
      (fun z : ℂ => twoScaleRemovableQuotient N (z - s)) 1 := by
    exact (differentiableAt_twoScaleRemovableQuotient hN ((1 : ℂ) - s)).comp 1 (by fun_prop)
  have hA : ContinuousAt A 1 := (hGamma.mul hQuot).continuousAt
  have hAt : A 1 = Complex.Gamma (1 + ((1 : ℂ) - s) / (h : ℂ)) *
      twoScaleRemovableQuotient N ((1 : ℂ) - s) := rfl
  have hprod := (hA.tendsto.mono_left inf_le_left).mul riemannZeta_residue_one
  convert hprod using 1
  · funext z
    unfold principalTwoScaleIntegrandInLArgument A
    ring
  · rw [hAt]
    ring

theorem oneScaleSpectralIntegrand_sub_factor
    {q : ℕ} (chi : DirichletCharacter ℂ q) (s : ℂ)
    (N h r : ℝ) :
    jutilaKernel 2 h r * (((2 * N : ℝ) : ℂ) ^ (verticalPoint 2 r)) *
          LSeries (fun m : ℕ => chi m) (s + verticalPoint 2 r) -
        jutilaKernel 2 h r * (N : ℂ) ^ (verticalPoint 2 r) *
          LSeries (fun m : ℕ => chi m) (s + verticalPoint 2 r) =
      jutilaKernel 2 h r *
        twoScaleSpectralFactor N (verticalPoint 2 r) *
          LSeries (fun m : ℕ => chi m) (s + verticalPoint 2 r) := by
  unfold twoScaleSpectralFactor
  ring

/-- Exact two-scale identity, kept as a difference of the two certified
source-line integrals and two certified smoothed series.  This avoids
silently assuming either an extra summability lemma or the later contour
shift merely to combine the two differences. -/
theorem literal_twoScale_dirichlet_smoothing_identity
    {q : ℕ} (chi : DirichletCharacter ℂ q) {s : ℂ} {N h : ℝ}
    (hs : -1 < s.re) (hN : 0 < N) (hh : 0 < h) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ r : ℝ,
            jutilaKernel 2 h r * (((2 * N : ℝ) : ℂ) ^ (verticalPoint 2 r)) *
              LSeries (fun m : ℕ => chi m) (s + verticalPoint 2 r)) -
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ r : ℝ,
            jutilaKernel 2 h r * (N : ℂ) ^ (verticalPoint 2 r) *
              LSeries (fun m : ℕ => chi m) (s + verticalPoint 2 r)) =
      (∑' n : PositiveNat, dirichletCoefficient chi s n *
          (Real.exp (-Real.rpow (dirichletRatio (2 * N) n) h) : ℂ)) -
        ∑' n : PositiveNat, dirichletCoefficient chi s n *
          (Real.exp (-Real.rpow (dirichletRatio N n) h) : ℂ) := by
  have h2N : 0 < 2 * N := mul_pos (by norm_num) hN
  have hTwo := literal_dirichlet_exp_smoothing_identity chi hs h2N hh
  have hOne := literal_dirichlet_exp_smoothing_identity chi hs hN hh
  rw [hTwo, hOne]

theorem twoScaleArithmeticTerm_eq
    {q : ℕ} (chi : DirichletCharacter ℂ q) (s : ℂ)
    (N h : ℝ) (n : PositiveNat) :
    dirichletCoefficient chi s n *
          (Real.exp (-Real.rpow (dirichletRatio (2 * N) n) h) : ℂ) -
        dirichletCoefficient chi s n *
          (Real.exp (-Real.rpow (dirichletRatio N n) h) : ℂ) =
      dirichletCoefficient chi s n *
        (twoScaleArithmeticWeight N h n : ℂ) := by
  unfold twoScaleArithmeticWeight
  push_cast
  ring

end

end JutilaTwoScaleSmoothing

#print axioms JutilaTwoScaleSmoothing.literal_twoScale_dirichlet_smoothing_identity
#print axioms JutilaTwoScaleSmoothing.twoScaleSpectralFactor_zero
#print axioms JutilaTwoScaleSmoothing.continuousAt_twoScaleRemovableQuotient_zero
#print axioms JutilaTwoScaleSmoothing.analyticAt_twoScaleRemovableQuotient_zero
#print axioms JutilaTwoScaleSmoothing.twoScaleContourIntegrand_boundary_rectangle
#print axioms JutilaTwoScaleSmoothing.principalTwoScaleIntegrand_residue_one
