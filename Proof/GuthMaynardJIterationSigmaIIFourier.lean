import GuthMaynardJIterationSigmaII

open scoped BigOperators Real FourierTransform ComplexConjugate
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

theorem norm_sourcePhase (x : ℝ) : ‖sourcePhase x‖ = 1 := by
  unfold sourcePhase
  rw [Complex.norm_exp]
  simp

theorem conj_sourcePhase (x : ℝ) : conj (sourcePhase x) = sourcePhase (-x) := by
  unfold sourcePhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem sourcePhase_add (x y : ℝ) :
    sourcePhase (x + y) = sourcePhase x * sourcePhase y := by
  unfold sourcePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Fourier transform of a real function in the paper's `e(-xi*u)`
notation. -/
theorem fourier_ofReal_eq_integral_sourcePhase (f : ℝ → ℝ) (xi : ℝ) :
    FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) xi =
      ∫ u : ℝ, sourcePhase (-xi * u) * (f u : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with u
  rw [smul_eq_mul]
  congr 1
  unfold sourcePhase
  congr 1
  push_cast
  ring

theorem conj_fourier_ofReal_eq_integral_sourcePhase
    (f : ℝ → ℝ) (xi : ℝ) :
    conj (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) xi) =
      ∫ u : ℝ, sourcePhase (xi * u) * (f u : ℂ) := by
  rw [fourier_ofReal_eq_integral_sourcePhase]
  calc
    conj (∫ u : ℝ, sourcePhase (-xi * u) * (f u : ℂ)) =
        ∫ u : ℝ, conj (sourcePhase (-xi * u) * (f u : ℂ)) := by
      exact (Complex.conjCLE.integral_comp_comm
        (fun u : ℝ => sourcePhase (-xi * u) * (f u : ℂ))).symm
    _ = ∫ u : ℝ, sourcePhase (xi * u) * (f u : ℂ) := by
      apply integral_congr_ae
      filter_upwards with u
      simp only [map_mul, Complex.conj_ofReal]
      rw [conj_sourcePhase]
      congr 2
      ring

def fourierPairKernel (f : ℝ → ℝ) (xi xi' u u' : ℝ) : ℂ :=
  ((f u * f u' : ℝ) : ℂ) * sourcePhase (xi' * u' - xi * u)

/-- The exact iterated-integral expansion behind TeX 1611.  This is an
identity of Bochner integrals; no interchange of the two infinite integrals
is being smuggled into the statement. -/
theorem fourier_mul_conj_eq_iteratedIntegral
    (f : ℝ → ℝ) (xi xi' : ℝ) :
    FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) xi *
        conj (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) xi') =
      ∫ u : ℝ, ∫ u' : ℝ, fourierPairKernel f xi xi' u u' := by
  rw [fourier_ofReal_eq_integral_sourcePhase,
    conj_fourier_ofReal_eq_integral_sourcePhase]
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with u
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u'
  unfold fourierPairKernel
  calc
    sourcePhase (-xi * u) * (f u : ℂ) *
        (sourcePhase (xi' * u') * (f u' : ℂ)) =
      ((f u * f u' : ℝ) : ℂ) *
        (sourcePhase (-xi * u) * sourcePhase (xi' * u')) := by
          push_cast
          ring
    _ = ((f u * f u' : ℝ) : ℂ) *
        sourcePhase (xi' * u' - xi * u) := by
          rw [← sourcePhase_add]
          congr 2
          ring

def sigmaIIZ1 (M3 Ctau m2 m2' u u' : ℝ) : ℂ :=
  ∫ tau in -Ctau..Ctau,
    sourcePhase (tau * ((m2' / M3) * u' - (m2 / M3) * u))

def sigmaIIZ2Finite (ellRange : Finset ℤ) (psi2 : ℝ → ℝ)
    (M2 T m2 m2' u u' : ℝ) : ℂ :=
  ∑ ell ∈ ellRange,
    (psi2 (M2 * (ell : ℝ) / T) : ℂ) *
      sourcePhase ((ell : ℝ) * (m2' * u' - m2 * u))

theorem sigmaII_affine_pair_phase
    {M3 : ℝ} (hM3 : M3 ≠ 0)
    (ell m2 m2' : ℤ) (tau u u' : ℝ) :
    sourcePhase
        (sigmaIIAffineFrequency M3 ell m2' tau * u' -
          sigmaIIAffineFrequency M3 ell m2 tau * u) =
      sourcePhase (tau * (((m2' : ℝ) / M3) * u' -
        ((m2 : ℝ) / M3) * u)) *
      sourcePhase ((ell : ℝ) * ((m2' : ℝ) * u' - (m2 : ℝ) * u)) := by
  rw [← sourcePhase_add]
  congr 1
  unfold sigmaIIAffineFrequency
  field_simp [hM3]
  ring

/-- Exact finite `Z1*Z2` factorization of the `ell,tau` phase, retaining
`M3` in `Z1`. -/
theorem sigmaII_phase_sum_integral_eq_Z1_mul_Z2
    (ellRange : Finset ℤ) (psi2 : ℝ → ℝ)
    {M3 : ℝ} (hM3 : M3 ≠ 0)
    (M2 T Ctau : ℝ) (m2 m2' : ℤ) (u u' : ℝ) :
    (∑ ell ∈ ellRange,
      (psi2 (M2 * (ell : ℝ) / T) : ℂ) *
        ∫ tau in -Ctau..Ctau,
          sourcePhase
            (sigmaIIAffineFrequency M3 ell m2' tau * u' -
              sigmaIIAffineFrequency M3 ell m2 tau * u)) =
      sigmaIIZ1 M3 Ctau (m2 : ℝ) (m2' : ℝ) u u' *
        sigmaIIZ2Finite ellRange psi2 M2 T (m2 : ℝ) (m2' : ℝ) u u' := by
  unfold sigmaIIZ1 sigmaIIZ2Finite
  simp_rw [sigmaII_affine_pair_phase hM3]
  simp_rw [intervalIntegral.integral_mul_const]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ell hell
  ring

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.norm_sourcePhase
#print axioms GuthMaynardJIteration.conj_sourcePhase
#print axioms GuthMaynardJIteration.sourcePhase_add
#print axioms GuthMaynardJIteration.fourier_ofReal_eq_integral_sourcePhase
#print axioms GuthMaynardJIteration.conj_fourier_ofReal_eq_integral_sourcePhase
#print axioms GuthMaynardJIteration.fourier_mul_conj_eq_iteratedIntegral
#print axioms GuthMaynardJIteration.sigmaII_affine_pair_phase
#print axioms GuthMaynardJIteration.sigmaII_phase_sum_integral_eq_Z1_mul_Z2
