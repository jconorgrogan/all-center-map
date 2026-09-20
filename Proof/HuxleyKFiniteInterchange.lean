import HuxleyKMellin

/-!
# Finite sum/integral interchange for Huxley's kernel

This is the finite algebraic core of Huxley 1973 (2.7).  It keeps all
absolute-convergence work visible: each positive Mellin frequency is a
bounded multiplier of the certified vertically integrable kernel `K`.
The passage from the absolutely convergent Dirichlet `L`-series to this
finite identity is deliberately not claimed here.
-/

namespace MAPHuxleyKFiniteInterchange

open Complex Real MeasureTheory Filter
open scoped BigOperators

noncomputable section

private def verticalPoint (t : ℝ) : ℂ := (2 : ℂ) + (t : ℂ) * I

private theorem integrable_frequency_mul_huxleyK {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ =>
      (x : ℂ) ^ (-verticalPoint t) *
        MAPHuxleyReflectionKernelAlgebra.huxleyK (verticalPoint t)) := by
  have hK := MAPHuxleyKMellin.verticalIntegrable_huxleyK
  unfold Complex.VerticalIntegrable at hK
  apply hK.bdd_mul (c := Real.rpow x (-2))
  · apply Continuous.aestronglyMeasurable
    have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    rw [show (fun t : ℝ => (x : ℂ) ^ (-verticalPoint t)) =
        (fun t : ℝ => Complex.exp (Complex.log (x : ℂ) * (-verticalPoint t))) by
      funext t
      simpa using Complex.cpow_def_of_ne_zero hxC (-verticalPoint t)]
    unfold verticalPoint
    fun_prop
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp [verticalPoint])

/-- Every coefficient-weighted summand in the finite expansion is
integrable on the source line. -/
theorem integrable_coefficient_frequency_mul_huxleyK
    {x : ℝ} (hx : 0 < x) (c : ℂ) :
    Integrable (fun t : ℝ => c *
      ((x : ℂ) ^ (-verticalPoint t) *
        MAPHuxleyReflectionKernelAlgebra.huxleyK (verticalPoint t))) :=
  (integrable_frequency_mul_huxleyK hx).const_mul c

/-- Exact finite interchange underlying (2.7).  This theorem is valid for
an arbitrary finite collection of positive Mellin frequencies and arbitrary
complex coefficients. -/
theorem finite_huxleyKernel_interchange
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c : ι → ℂ) (x : ι → ℝ)
    (hx : ∀ i ∈ S, 0 < x i) :
    (1 / (2 * Real.pi)) •
        ∫ t : ℝ, ∑ i ∈ S, c i *
          ((x i : ℂ) ^ (-verticalPoint t) *
            MAPHuxleyReflectionKernelAlgebra.huxleyK (verticalPoint t)) =
      ∑ i ∈ S, c i * MAPHuxleyKMellin.huxleyKWeight (x i) := by
  rw [integral_finset_sum S (fun i hi =>
    integrable_coefficient_frequency_mul_huxleyK (hx i hi) (c i))]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hInv := MAPHuxleyKMellin.mellinInv_huxleyK_eq_weight (hx i hi)
  unfold mellinInv at hInv
  have hInv' :
      (1 / (2 * Real.pi)) •
          ∫ t : ℝ, (x i : ℂ) ^ (-verticalPoint t) *
            MAPHuxleyReflectionKernelAlgebra.huxleyK (verticalPoint t) =
        MAPHuxleyKMellin.huxleyKWeight (x i) := by
    simpa only [verticalPoint, smul_eq_mul, mul_comm] using hInv
  calc
    (1 / (2 * Real.pi)) •
        ∫ t : ℝ, c i * ((x i : ℂ) ^ (-verticalPoint t) *
          MAPHuxleyReflectionKernelAlgebra.huxleyK (verticalPoint t)) =
      (1 / (2 * Real.pi)) •
        (c i * ∫ t : ℝ, (x i : ℂ) ^ (-verticalPoint t) *
          MAPHuxleyReflectionKernelAlgebra.huxleyK (verticalPoint t)) := by
            rw [integral_const_mul]
    _ = c i * ((1 / (2 * Real.pi)) •
        ∫ t : ℝ, (x i : ℂ) ^ (-verticalPoint t) *
          MAPHuxleyReflectionKernelAlgebra.huxleyK (verticalPoint t)) := by
            rw [Complex.real_smul, Complex.real_smul]
            ring
    _ = c i * MAPHuxleyKMellin.huxleyKWeight (x i) := by rw [hInv']

/-- Countable Fubini version of the preceding identity.  The hypothesis is
the exact standard Bochner condition used by `integral_tsum`: summability of
the integrals of the termwise norms.  Thus this does not hide a Dirichlet
series estimate or a density theorem in a custom proposition. -/
theorem countable_huxleyKernel_interchange_of_summable_integral_norm
    {ι : Type*} [Countable ι]
    (c : ι → ℂ) (x : ι → ℝ) (hx : ∀ i, 0 < x i)
    (hFsum : Summable fun i => ∫ t : ℝ,
      ‖c i * ((x i : ℂ) ^ (-verticalPoint t) *
        MAPHuxleyReflectionKernelAlgebra.huxleyK (verticalPoint t))‖) :
    (1 / (2 * Real.pi)) •
        ∫ t : ℝ, ∑' i : ι, c i *
          ((x i : ℂ) ^ (-verticalPoint t) *
            MAPHuxleyReflectionKernelAlgebra.huxleyK (verticalPoint t)) =
      ∑' i : ι, c i * MAPHuxleyKMellin.huxleyKWeight (x i) := by
  let F : ι → ℝ → ℂ := fun i t => c i *
    ((x i : ℂ) ^ (-verticalPoint t) *
      MAPHuxleyReflectionKernelAlgebra.huxleyK (verticalPoint t))
  have hFint : ∀ i, Integrable (F i) := fun i =>
    integrable_coefficient_frequency_mul_huxleyK (hx i) (c i)
  have hFubini : (∑' i : ι, ∫ t : ℝ, F i t) =
      ∫ t : ℝ, ∑' i : ι, F i t :=
    integral_tsum_of_summable_integral_norm hFint (by simpa [F] using hFsum)
  calc
    (1 / (2 * Real.pi)) • ∫ t : ℝ, ∑' i : ι, F i t =
        (1 / (2 * Real.pi)) • (∑' i : ι, ∫ t : ℝ, F i t) := by rw [hFubini]
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∑' i : ι, ∫ t : ℝ, F i t) := by rw [Complex.real_smul]
    _ = ∑' i : ι, ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, F i t := by rw [tsum_mul_left]
    _ = ∑' i : ι, c i * MAPHuxleyKMellin.huxleyKWeight (x i) := by
      apply tsum_congr
      intro i
      have hInv := MAPHuxleyKMellin.mellinInv_huxleyK_eq_weight (hx i)
      unfold mellinInv at hInv
      have hInv' :
          ((1 / (2 * Real.pi) : ℝ) : ℂ) *
              ∫ t : ℝ, (x i : ℂ) ^ (-verticalPoint t) *
                MAPHuxleyReflectionKernelAlgebra.huxleyK (verticalPoint t) =
            MAPHuxleyKMellin.huxleyKWeight (x i) := by
        simpa only [verticalPoint, Complex.real_smul, smul_eq_mul] using hInv
      unfold F
      rw [integral_const_mul]
      rw [← hInv']
      ring

/-- A source-usable sufficient condition for the Fubini hypothesis: the
coefficient sequence is summable after the exact `x^-2` decay contributed by
the source line `Re w = 2`. -/
theorem countable_huxleyKernel_interchange_of_weighted_summable
    {ι : Type*} [Countable ι]
    (c : ι → ℂ) (x : ι → ℝ) (hx : ∀ i, 0 < x i)
    (hsum : Summable fun i => ‖c i‖ * Real.rpow (x i) (-2)) :
    (1 / (2 * Real.pi)) •
        ∫ t : ℝ, ∑' i : ι, c i *
          ((x i : ℂ) ^ (-verticalPoint t) *
            MAPHuxleyReflectionKernelAlgebra.huxleyK (verticalPoint t)) =
      ∑' i : ι, c i * MAPHuxleyKMellin.huxleyKWeight (x i) := by
  have hK := MAPHuxleyKMellin.verticalIntegrable_huxleyK
  unfold Complex.VerticalIntegrable at hK
  have hFsum : Summable fun i => ∫ t : ℝ,
      ‖c i * ((x i : ℂ) ^ (-verticalPoint t) *
        MAPHuxleyReflectionKernelAlgebra.huxleyK (verticalPoint t))‖ := by
    have hscaled := hsum.mul_right
      (∫ t : ℝ, ‖MAPHuxleyReflectionKernelAlgebra.huxleyK (verticalPoint t)‖)
    apply hscaled.congr
    intro i
    symm
    calc
      (∫ t : ℝ, ‖c i * ((x i : ℂ) ^ (-verticalPoint t) *
          MAPHuxleyReflectionKernelAlgebra.huxleyK (verticalPoint t))‖) =
        ∫ t : ℝ, (‖c i‖ * Real.rpow (x i) (-2)) *
          ‖MAPHuxleyReflectionKernelAlgebra.huxleyK (verticalPoint t)‖ := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun t => by
              change ‖c i * ((x i : ℂ) ^ (-verticalPoint t) *
                  MAPHuxleyReflectionKernelAlgebra.huxleyK (verticalPoint t))‖ =
                (‖c i‖ * Real.rpow (x i) (-2)) *
                  ‖MAPHuxleyReflectionKernelAlgebra.huxleyK (verticalPoint t)‖
              rw [norm_mul, norm_mul,
                Complex.norm_cpow_eq_rpow_re_of_pos (hx i)]
              simp [verticalPoint, mul_assoc])
      _ = (‖c i‖ * Real.rpow (x i) (-2)) *
          ∫ t : ℝ, ‖MAPHuxleyReflectionKernelAlgebra.huxleyK
            (verticalPoint t)‖ := by rw [integral_const_mul]
  exact countable_huxleyKernel_interchange_of_summable_integral_norm
    c x hx hFsum

end

end MAPHuxleyKFiniteInterchange

#print axioms MAPHuxleyKFiniteInterchange.integrable_coefficient_frequency_mul_huxleyK
#print axioms MAPHuxleyKFiniteInterchange.finite_huxleyKernel_interchange
#print axioms MAPHuxleyKFiniteInterchange.countable_huxleyKernel_interchange_of_summable_integral_norm
#print axioms MAPHuxleyKFiniteInterchange.countable_huxleyKernel_interchange_of_weighted_summable
