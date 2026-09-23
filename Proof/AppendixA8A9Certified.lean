import Mathlib


/-!
# Uniform scalar core of Appendix (A.8)

The scaled-cutoff Leibniz calculation reduces to uniform boundedness of
`x^m exp(-x/2)` on `x ≥ 0`.  This file proves an explicit bound, eliminating
that analytic subleaf without any compactness or asymptotic premise.
-/

namespace AppendixTypeIPower

open MeasureTheory Set

noncomputable section

/-- Explicit domination of a polynomial by exponential decay.  The constant
`2^m m!` is not optimized, but is uniform and is exactly what the (A.8)
scaling argument needs. -/
theorem pow_mul_exp_neg_half_le (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ m * Real.exp (-x / 2) ≤ 2 ^ m * (m.factorial : ℝ) := by
  have hfact : (0 : ℝ) < (m.factorial : ℝ) := by positivity
  have hseries := Real.pow_div_factorial_le_exp (x / 2) (show 0 ≤ x / 2 by positivity) m
  have hpow : (x / 2) ^ m ≤ (m.factorial : ℝ) * Real.exp (x / 2) := by
    exact (by simpa [mul_comm] using (div_le_iff₀ hfact).mp hseries)
  have hdecay := mul_le_mul_of_nonneg_right hpow (Real.exp_pos (-x / 2)).le
  have hdecay' : (x / 2) ^ m * Real.exp (-x / 2) ≤ (m.factorial : ℝ) := by
    calc
      (x / 2) ^ m * Real.exp (-x / 2) ≤
          ((m.factorial : ℝ) * Real.exp (x / 2)) * Real.exp (-x / 2) := hdecay
      _ = (m.factorial : ℝ) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
        simp
  calc
    x ^ m * Real.exp (-x / 2) =
        2 ^ m * ((x / 2) ^ m * Real.exp (-x / 2)) := by
          rw [div_pow]
          push_cast
          field_simp
    _ ≤ 2 ^ m * (m.factorial : ℝ) :=
      mul_le_mul_of_nonneg_left hdecay' (by positivity)


/-- Every iterated derivative of the decaying exponential, with the sign and
normalization used in (A.8). -/
theorem iteratedDeriv_exp_neg_mul (n : ℕ) (a : ℝ) :
    iteratedDeriv n (fun u : ℝ => Real.exp (-a * u)) =
      fun u : ℝ => (-a) ^ n * Real.exp (-a * u) := by
  induction n with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
      rw [show n + 1 = n.succ by rfl, iteratedDeriv_succ, ih]
      funext u
      have hinner : HasDerivAt (fun u : ℝ => -a * u) (-a) u := by
        simpa using (hasDerivAt_id u).const_mul (-a)
      have hexp : HasDerivAt (fun u : ℝ => Real.exp (-a * u))
          (Real.exp (-a * u) * (-a)) u := hinner.exp
      have hmul := hexp.const_mul ((-a) ^ n)
      simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hmul.deriv



/-- Uniform decay bound after the scale change `x=aL`; this is the exact
factor used term-by-term in the Leibniz expansion. -/
theorem pow_mul_exp_neg_mul_le_scaled
    (m : ℕ) {a L u : ℝ} (ha : 0 ≤ a) (hL : 0 < L) (hu : L / 2 ≤ u) :
    a ^ m * Real.exp (-a * u) ≤
      (L⁻¹) ^ m * (2 ^ m * (m.factorial : ℝ)) := by
  have hmono : Real.exp (-a * u) ≤ Real.exp (-(a * L) / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hfirst : a ^ m * Real.exp (-a * u) ≤
      a ^ m * Real.exp (-(a * L) / 2) :=
    mul_le_mul_of_nonneg_left hmono (pow_nonneg ha m)
  have hscalar := pow_mul_exp_neg_half_le m (mul_nonneg ha hL.le)
  calc
    a ^ m * Real.exp (-a * u) ≤
        a ^ m * Real.exp (-(a * L) / 2) := hfirst
    _ = (L⁻¹) ^ m * ((a * L) ^ m * Real.exp (-(a * L) / 2)) := by
      have hcancel : (L⁻¹) ^ m * L ^ m = 1 := by
        rw [← mul_pow]
        simp [hL.ne']
      rw [mul_pow]
      calc
        a ^ m * Real.exp (-(a * L) / 2) =
            a ^ m * 1 * Real.exp (-(a * L) / 2) := by ring
        _ = a ^ m * ((L⁻¹) ^ m * L ^ m) * Real.exp (-(a * L) / 2) := by
          rw [hcancel]
        _ = (L⁻¹) ^ m * (a ^ m * L ^ m * Real.exp (-(a * L) / 2)) := by ring
    _ ≤ (L⁻¹) ^ m * (2 ^ m * (m.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hscalar (pow_nonneg (inv_nonneg.mpr hL.le) m)

/-- The concrete scaled cutoff family from (A.8). -/
def scaledCutoff (ζ : ℝ → ℝ) (a L : ℝ) : ℝ → ℝ :=
  (fun u => ζ (u / L)) * fun u => Real.exp (-a * u)

/-- Exact Leibniz expansion for the `j`-th derivative of the scaled cutoff.
No estimate is assumed here. -/
theorem iteratedDeriv_scaledCutoff
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (↑(⊤ : ℕ∞)) ζ)
    (a L : ℝ) (j : ℕ) :
    iteratedDeriv j (scaledCutoff ζ a L) = fun u : ℝ =>
      ∑ r ∈ Finset.range (j + 1),
        (j.choose r : ℝ) * (L⁻¹) ^ r * iteratedDeriv r ζ (u / L) *
          ((-a) ^ (j - r) * Real.exp (-a * u)) := by
  have hζj : ContDiff ℝ (↑j) ζ := hζ.of_le (by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top))
  have hf : ContDiff ℝ (↑j) (fun u : ℝ => ζ (u / L)) := by
    have hlin : ContDiff ℝ (↑j) (fun u : ℝ => L⁻¹ * u) := by fun_prop
    simpa [Function.comp_def, div_eq_inv_mul] using hζj.comp hlin
  have hg : ContDiff ℝ (↑j) (fun u : ℝ => Real.exp (-a * u)) := by fun_prop
  funext u
  change iteratedDeriv j
    ((fun u : ℝ => ζ (u / L)) * fun u : ℝ => Real.exp (-a * u)) u = _
  rw [iteratedDeriv_mul hf.contDiffAt hg.contDiffAt]
  apply Finset.sum_congr rfl
  intro r hr
  have hrle : r ≤ j := by simpa using Finset.mem_range.mp hr
  have hζr : ContDiff ℝ (↑r) ζ := hζ.of_le (by exact_mod_cast (show (r : ℕ∞) ≤ ⊤ from le_top))
  have hscale := congrFun (iteratedDeriv_comp_const_mul hζr L⁻¹) u
  have hexp := congrFun (iteratedDeriv_exp_neg_mul (j - r) a) u
  rw [show iteratedDeriv r (fun u : ℝ => ζ (u / L)) u =
      (L⁻¹) ^ r * iteratedDeriv r ζ (u / L) by
        simpa [div_eq_inv_mul] using hscale]
  rw [hexp]
  ring



/-- The scaled derivative is supported in `[L/2,2L]` when every derivative
of the fixed cutoff is supported in `[1/2,2]`. -/
theorem iteratedDeriv_scaledCutoff_eq_zero_of_not_mem
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (↑(⊤ : ℕ∞)) ζ)
    (hsupport : ∀ r v, v ∉ Set.Icc (1 / 2 : ℝ) 2 → iteratedDeriv r ζ v = 0)
    (j : ℕ) {a L u : ℝ} (hL : 0 < L)
    (hu : u ∉ Set.Icc (L / 2) (2 * L)) :
    iteratedDeriv j (scaledCutoff ζ a L) u = 0 := by
  have hvnot : u / L ∉ Set.Icc (1 / 2 : ℝ) 2 := by
    intro hv
    apply hu
    rcases hv with ⟨hvlo, hvhi⟩
    constructor
    · have := (le_div_iff₀ hL).mp hvlo
      nlinarith
    · have := (div_le_iff₀ hL).mp hvhi
      nlinarith
  rw [congrFun (iteratedDeriv_scaledCutoff ζ hζ a L j) u]
  apply Finset.sum_eq_zero
  intro r hr
  rw [hsupport r (u / L) hvnot]
  ring

/-- Explicit cutoff-dependent constant for the `j`-th Leibniz expansion. -/
def scaledCutoffConstant (C : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (j + 1),
    (j.choose r : ℝ) * C r * (2 ^ (j - r) * ((j - r).factorial : ℝ))

/-- Pointwise `L^{-j}` bound on the scaled support.  The hypotheses describe
only the fixed cutoff's derivative suprema; no scaled-family estimate is
assumed. -/
theorem abs_iteratedDeriv_scaledCutoff_le
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (↑(⊤ : ℕ∞)) ζ)
    (C : ℕ → ℝ) (hCnonneg : ∀ r, 0 ≤ C r)
    (hC : ∀ r v, |iteratedDeriv r ζ v| ≤ C r)
    (j : ℕ) {a L u : ℝ} (ha : 0 ≤ a) (hL : 0 < L) (hu : L / 2 ≤ u) :
    |iteratedDeriv j (scaledCutoff ζ a L) u| ≤
      (L⁻¹) ^ j * scaledCutoffConstant C j := by
  rw [congrFun (iteratedDeriv_scaledCutoff ζ hζ a L j) u]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  unfold scaledCutoffConstant
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have hrle : r ≤ j := by simpa using Finset.mem_range.mp hr
  let m := j - r
  have hinv : 0 ≤ L⁻¹ := inv_nonneg.mpr hL.le
  have hdecay := pow_mul_exp_neg_mul_le_scaled m ha hL hu
  have hchoose : 0 ≤ (j.choose r : ℝ) := by positivity
  have hprod :
      |iteratedDeriv r ζ (u / L)| * (a ^ m * Real.exp (-a * u)) ≤
        C r * ((L⁻¹) ^ m * (2 ^ m * (m.factorial : ℝ))) := by
    exact mul_le_mul (hC r (u / L)) hdecay
      (mul_nonneg (pow_nonneg ha m) (Real.exp_pos _).le) (hCnonneg r)
  have hpref : 0 ≤ (j.choose r : ℝ) * (L⁻¹) ^ r :=
    mul_nonneg hchoose (pow_nonneg hinv r)
  have hterm :
      |(j.choose r : ℝ) * (L⁻¹) ^ r * iteratedDeriv r ζ (u / L) *
          ((-a) ^ m * Real.exp (-a * u))| ≤
        (j.choose r : ℝ) * (L⁻¹) ^ r * C r *
          ((L⁻¹) ^ m * (2 ^ m * (m.factorial : ℝ))) := by
    have hmul := mul_le_mul_of_nonneg_left hprod hpref
    simpa [abs_mul, Nat.abs_cast, abs_pow, abs_neg, abs_of_nonneg ha,
      Real.abs_exp, abs_of_nonneg hinv, abs_of_pos hL, mul_assoc] using hmul
  calc
    |(j.choose r : ℝ) * (L⁻¹) ^ r * iteratedDeriv r ζ (u / L) *
        ((-a) ^ (j - r) * Real.exp (-a * u))| ≤
      (j.choose r : ℝ) * (L⁻¹) ^ r * C r *
        ((L⁻¹) ^ m * (2 ^ m * (m.factorial : ℝ))) := by simpa [m] using hterm
    _ = (L⁻¹) ^ j *
        ((j.choose r : ℝ) * C r *
          (2 ^ (j - r) * ((j - r).factorial : ℝ))) := by
      dsimp [m]
      have hpow : (L⁻¹) ^ r * (L⁻¹) ^ (j - r) = (L⁻¹) ^ j := by
        rw [← pow_add, Nat.add_sub_of_le hrle]
      calc
        (j.choose r : ℝ) * (L⁻¹) ^ r * C r *
            ((L⁻¹) ^ (j - r) * (2 ^ (j - r) * ((j - r).factorial : ℝ))) =
          ((L⁻¹) ^ r * (L⁻¹) ^ (j - r)) *
            ((j.choose r : ℝ) * C r *
              (2 ^ (j - r) * ((j - r).factorial : ℝ))) := by ring
        _ = (L⁻¹) ^ j *
            ((j.choose r : ℝ) * C r *
              (2 ^ (j - r) * ((j - r).factorial : ℝ))) := by rw [hpow]


/-- Exact `L¹` scaling asserted in (A.8), with an explicit constant depending
only on the fixed cutoff derivative bounds.  Multiplying out the right side
gives `O_j(L^{1-j})`.

The only cutoff hypotheses are smoothness, support of its derivatives in the
fixed interval `[1/2,2]`, and fixed derivative suprema.  No estimate for the
scaled family is supplied as a premise. -/
theorem integral_abs_iteratedDeriv_scaledCutoff_le
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (↑(⊤ : ℕ∞)) ζ)
    (hsupport : ∀ r v, v ∉ Set.Icc (1 / 2 : ℝ) 2 → iteratedDeriv r ζ v = 0)
    (C : ℕ → ℝ) (hCnonneg : ∀ r, 0 ≤ C r)
    (hC : ∀ r v, |iteratedDeriv r ζ v| ≤ C r)
    (j : ℕ) {a L : ℝ} (ha : 0 ≤ a) (hL : 0 < L) :
    (∫ u : ℝ, |iteratedDeriv j (scaledCutoff ζ a L) u|) ≤
      ((L⁻¹) ^ j * scaledCutoffConstant C j) * (3 * L / 2) := by
  let I : Set ℝ := Set.Icc (L / 2) (2 * L)
  have hscaled : ContDiff ℝ (↑(⊤ : ℕ∞)) (scaledCutoff ζ a L) := by
    have hf : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun u : ℝ => ζ (u / L)) := by
      have hlin : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun u : ℝ => L⁻¹ * u) := by fun_prop
      simpa [Function.comp_def, div_eq_inv_mul] using hζ.comp hlin
    have hg : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun u : ℝ => Real.exp (-a * u)) := by fun_prop
    simpa only [scaledCutoff] using! hf.mul hg
  have hcont : Continuous (fun u : ℝ =>
      |iteratedDeriv j (scaledCutoff ζ a L) u|) :=
    (hscaled.continuous_iteratedDeriv j
      (by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top))).abs
  have hfint : IntegrableOn (fun u : ℝ =>
      |iteratedDeriv j (scaledCutoff ζ a L) u|) I :=
    hcont.integrableOn_Icc
  have hIfinite : (volume : Measure ℝ) I ≠ ⊤ :=
    ne_of_lt (by simpa [I] using (measure_Icc_lt_top :
      (volume : Measure ℝ) (Set.Icc (L / 2) (2 * L)) < ⊤))
  have hconstint : IntegrableOn (fun _ : ℝ =>
      (L⁻¹) ^ j * scaledCutoffConstant C j) I := integrableOn_const hIfinite
  have hzero : ∀ u ∉ I,
      |iteratedDeriv j (scaledCutoff ζ a L) u| = 0 := by
    intro u hu
    rw [iteratedDeriv_scaledCutoff_eq_zero_of_not_mem ζ hζ hsupport j hL hu]
    simp
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  calc
    (∫ u : ℝ in I, |iteratedDeriv j (scaledCutoff ζ a L) u|) ≤
        ∫ _u : ℝ in I, ((L⁻¹) ^ j * scaledCutoffConstant C j) := by
      apply MeasureTheory.setIntegral_mono_on hfint hconstint measurableSet_Icc
      intro u hu
      exact abs_iteratedDeriv_scaledCutoff_le ζ hζ C hCnonneg hC j ha hL hu.1
    _ = ((L⁻¹) ^ j * scaledCutoffConstant C j) * (3 * L / 2) := by
      rw [MeasureTheory.setIntegral_const]
      have hvol : (volume : Measure ℝ).real I = 3 * L / 2 := by
        dsimp [I]
        rw [Measure.real, Real.volume_Icc]
        rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * L - L / 2)]
        ring
      rw [hvol]
      simp [smul_eq_mul, mul_comm]

end

end AppendixTypeIPower



open scoped FourierTransform ComplexConjugate
open MeasureTheory Set

namespace FourierRealPartRemoval

noncomputable section

open SchwartzMap

def positiveFourierPhase (u ξ : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * u * ξ : ℝ) * Complex.I)

theorem fourier_inversion_pointwise (ψ : 𝓢(ℝ, ℂ)) (u : ℝ) :
    ψ u = ∫ ξ : ℝ, positiveFourierPhase u ξ * (𝓕 ψ) ξ := by
  have h := congrArg (fun f : 𝓢(ℝ, ℂ) ↦ f u)
    (FourierTransform.fourierInv_fourier_eq (F := 𝓢(ℝ, ℂ)) ψ)
  change 𝓕⁻ (𝓕 ψ : 𝓢(ℝ, ℂ)) u = ψ u at h
  rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe, Real.fourierInv_eq'] at h
  simpa [positiveFourierPhase, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc,
    SchwartzMap.fourier_coe] using h.symm

private theorem integrable_phase_mul_fourier (ψ : 𝓢(ℝ, ℂ)) (a : ℂ) (u : ℝ) :
    Integrable (fun ξ : ℝ ↦ a * (positiveFourierPhase u ξ * (𝓕 ψ) ξ)) := by
  have hbase : Integrable (fun ξ : ℝ ↦ a * (𝓕 ψ : 𝓢(ℝ, ℂ)) ξ) :=
    ((𝓕 ψ : 𝓢(ℝ, ℂ)).integrable).const_mul a
  let g : ℝ → ℂ := fun ξ ↦ a * (positiveFourierPhase u ξ * (𝓕 ψ) ξ)
  have hg : AEStronglyMeasurable g := by
    apply Continuous.aestronglyMeasurable
    dsimp [g, positiveFourierPhase]
    fun_prop
  have hnorm : ∀ᵐ ξ : ℝ, ‖g ξ‖ ≤ ‖a * (𝓕 ψ : 𝓢(ℝ, ℂ)) ξ‖ := by
    filter_upwards with ξ
    simp [g, positiveFourierPhase, Complex.norm_exp]
  have : Integrable g := hbase.norm.mono' hg hnorm
  exact this

/-- Exact finite-sum version of the Appendix A.9 real-part-removal identity.

The phase convention here is the analyst's Fourier convention used by mathlib:
`𝓕 f ξ = ∫ exp (-2π i uξ) f u du`. -/
theorem finite_fourier_real_part_removal {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (u : ι → ℝ) (ψ : 𝓢(ℝ, ℂ)) :
    ∑ i ∈ s, a i * ψ (u i) =
      ∫ ξ : ℝ, (𝓕 ψ : 𝓢(ℝ, ℂ)) ξ * ∑ i ∈ s, a i * positiveFourierPhase (u i) ξ := by
  calc
    ∑ i ∈ s, a i * ψ (u i) =
        ∑ i ∈ s, a i * (∫ ξ : ℝ,
          positiveFourierPhase (u i) ξ * (𝓕 ψ : 𝓢(ℝ, ℂ)) ξ) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [fourier_inversion_pointwise]
    _ = ∑ i ∈ s, ∫ ξ : ℝ,
        a i * (positiveFourierPhase (u i) ξ * (𝓕 ψ : 𝓢(ℝ, ℂ)) ξ) := by
          simp_rw [MeasureTheory.integral_const_mul]
    _ = ∫ ξ : ℝ, ∑ i ∈ s,
        a i * (positiveFourierPhase (u i) ξ * (𝓕 ψ : 𝓢(ℝ, ℂ)) ξ) := by
          symm
          apply MeasureTheory.integral_finsetSum
          intro i hi
          exact integrable_phase_mul_fourier ψ (a i) (u i)
    _ = ∫ ξ : ℝ, (𝓕 ψ : 𝓢(ℝ, ℂ)) ξ *
        ∑ i ∈ s, a i * positiveFourierPhase (u i) ξ := by
          apply integral_congr_ae
          filter_upwards with ξ
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring

def dirichletWeight (x σ t : ℝ) : ℂ :=
  Complex.exp ((-(σ * x) : ℂ) - Complex.I * (t * x))

def finiteDirichletBlock {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (x : ι → ℝ) (σ t : ℝ) : ℂ :=
  ∑ i ∈ s, c i * dirichletWeight (x i) σ t

/-- Literal A.9 after spelling out the finite Dirichlet block.  The only
hypothesis is the exact cutoff equality on the finitely many logarithms in the
block; no Fourier estimate or tail estimate is assumed.  Mathlib's Fourier
sign convention produces `γ - 2πξ`; replacing `ξ` by `-ξ` gives the manuscript's
display with `γ + 2πξ`. -/
theorem finite_dirichlet_real_part_removal {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (x : ι → ℝ) (σ β γ : ℝ) (ψ : 𝓢(ℝ, ℂ))
    (hψ : ∀ i ∈ s, ψ (x i) = Complex.exp (-((β - σ) * x i))) :
    finiteDirichletBlock s c x β γ =
      ∫ ξ : ℝ, (𝓕 ψ : 𝓢(ℝ, ℂ)) ξ *
        finiteDirichletBlock s c x σ (γ - 2 * Real.pi * ξ) := by
  calc
    finiteDirichletBlock s c x β γ =
        ∑ i ∈ s, (c i * dirichletWeight (x i) σ γ) * ψ (x i) := by
          unfold finiteDirichletBlock
          apply Finset.sum_congr rfl
          intro i hi
          rw [hψ i hi]
          unfold dirichletWeight
          rw [mul_assoc, ← Complex.exp_add]
          congr 2
          ring

    _ = ∫ ξ : ℝ, (𝓕 ψ : 𝓢(ℝ, ℂ)) ξ *
          ∑ i ∈ s, (c i * dirichletWeight (x i) σ γ) *
            positiveFourierPhase (x i) ξ :=
      finite_fourier_real_part_removal s
        (fun i ↦ c i * dirichletWeight (x i) σ γ) x ψ
    _ = ∫ ξ : ℝ, (𝓕 ψ : 𝓢(ℝ, ℂ)) ξ *
          finiteDirichletBlock s c x σ (γ - 2 * Real.pi * ξ) := by
          apply integral_congr_ae
          filter_upwards with ξ
          congr 1
          unfold finiteDirichletBlock
          apply Finset.sum_congr rfl
          intro i hi
          unfold positiveFourierPhase dirichletWeight
          rw [mul_assoc, ← Complex.exp_add]
          congr 2
          push_cast
          ring

def fourierTailSet (H : ℝ) : Set ℝ := {ξ | H ≤ |ξ|}

/-- A premise-free arbitrary-power Fourier-tail estimate for every Schwartz
function.  This is the quantitative tail mechanism needed after A.8: the tail
is controlled by a weighted global moment, and the power `k` is selectable. -/
theorem schwartz_tail_pow_bound (f : 𝓢(ℝ, ℂ)) (H : ℝ) (k : ℕ) (hH : 0 ≤ H) :
    H ^ k * (∫ ξ : ℝ in fourierTailSet H, ‖f ξ‖) ≤
      ∫ ξ : ℝ, |ξ| ^ k * ‖f ξ‖ := by
  have hlo : Integrable (fun ξ : ℝ ↦ H ^ k * ‖f ξ‖) :=
    f.integrable.norm.const_mul (H ^ k)
  have hhi : Integrable (fun ξ : ℝ ↦ |ξ| ^ k * ‖f ξ‖) := by
    simpa [Real.norm_eq_abs] using f.integrable_pow_mul (volume : Measure ℝ) k
  have hs : MeasurableSet (fourierTailSet H) := by
    exact measurableSet_le measurable_const (measurable_id.norm)
  calc
    H ^ k * (∫ ξ : ℝ in fourierTailSet H, ‖f ξ‖) =
        ∫ ξ : ℝ in fourierTailSet H, H ^ k * ‖f ξ‖ := by
          rw [MeasureTheory.integral_const_mul]
    _ ≤ ∫ ξ : ℝ in fourierTailSet H, |ξ| ^ k * ‖f ξ‖ := by
          apply MeasureTheory.setIntegral_mono_on hlo.integrableOn hhi.integrableOn hs
          intro ξ hξ
          dsimp [fourierTailSet] at hξ
          gcongr
    _ ≤ ∫ ξ : ℝ, |ξ| ^ k * ‖f ξ‖ := by
          exact MeasureTheory.setIntegral_le_integral hhi (ae_of_all _ fun ξ ↦ by positivity)

/-- The actual Fourier transform tail of a Schwartz cutoff has arbitrary
polynomial decay, with a fully explicit intrinsic moment on the right. -/
theorem fourier_tail_pow_bound (ψ : 𝓢(ℝ, ℂ)) (H : ℝ) (k : ℕ) (hH : 0 ≤ H) :
    H ^ k * (∫ ξ : ℝ in fourierTailSet H, ‖(𝓕 ψ : 𝓢(ℝ, ℂ)) ξ‖) ≤
      ∫ ξ : ℝ, |ξ| ^ k * ‖(𝓕 ψ : 𝓢(ℝ, ℂ)) ξ‖ :=
  schwartz_tail_pow_bound (𝓕 ψ : 𝓢(ℝ, ℂ)) H k hH

theorem fourier_tail_le_inv_pow_mul (ψ : 𝓢(ℝ, ℂ)) (H : ℝ) (k : ℕ) (hH : 0 < H) :
    (∫ ξ : ℝ in fourierTailSet H, ‖(𝓕 ψ : 𝓢(ℝ, ℂ)) ξ‖) ≤
      (H ^ k)⁻¹ * (∫ ξ : ℝ, |ξ| ^ k * ‖(𝓕 ψ : 𝓢(ℝ, ℂ)) ξ‖) := by
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ (pow_pos hH k)).2
  rw [mul_comm]
  exact fourier_tail_pow_bound ψ H k hH.le

/-- Completely explicit version in terms of pinned-mathlib Schwartz seminorms.
No decay estimate is supplied as a hypothesis. -/
theorem fourier_tail_pow_bound_by_seminorm (ψ : 𝓢(ℝ, ℂ))
    (H : ℝ) (k : ℕ) (hH : 0 ≤ H) :
    H ^ k * (∫ ξ : ℝ in fourierTailSet H, ‖(𝓕 ψ : 𝓢(ℝ, ℂ)) ξ‖) ≤
      2 ^ (volume : Measure ℝ).integrablePower *
        (∫ ξ : ℝ, (1 + ‖ξ‖) ^ (-((volume : Measure ℝ).integrablePower : ℝ))) *
        (SchwartzMap.seminorm ℂ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) +
          SchwartzMap.seminorm ℂ (k + (volume : Measure ℝ).integrablePower) 0
            (𝓕 ψ : 𝓢(ℝ, ℂ))) := by
  apply (fourier_tail_pow_bound ψ H k hH).trans
  simpa [Real.norm_eq_abs] using
    SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℂ (volume : Measure ℝ)
      (𝓕 ψ : 𝓢(ℝ, ℂ)) k 0

end

end FourierRealPartRemoval


#print axioms AppendixTypeIPower.pow_mul_exp_neg_half_le
#print axioms AppendixTypeIPower.iteratedDeriv_exp_neg_mul
#print axioms AppendixTypeIPower.pow_mul_exp_neg_mul_le_scaled
#print axioms AppendixTypeIPower.iteratedDeriv_scaledCutoff
#print axioms AppendixTypeIPower.abs_iteratedDeriv_scaledCutoff_le
#print axioms AppendixTypeIPower.iteratedDeriv_scaledCutoff_eq_zero_of_not_mem
#print axioms AppendixTypeIPower.integral_abs_iteratedDeriv_scaledCutoff_le
#print axioms FourierRealPartRemoval.fourier_inversion_pointwise
#print axioms FourierRealPartRemoval.finite_fourier_real_part_removal
#print axioms FourierRealPartRemoval.finite_dirichlet_real_part_removal
#print axioms FourierRealPartRemoval.fourier_tail_le_inv_pow_mul
#print axioms FourierRealPartRemoval.fourier_tail_pow_bound_by_seminorm
