import JutilaPseudocharacterMExact
import JutilaLemma6MellinIntegral
import JutilaLemma6MellinIntegralSharp

/-!
# Absolute Mellin-error bound in Jutila Lemma 6

This file combines the literal finite `M(it,chi,psi_r)` sum with the certified
Gamma--L integral.  It leaves only the exact Mellin identity (2.11), the
exponent inequality (2.8), and the elementary cut-off tail as source work.
-/

namespace MAPJutilaLemma6ErrorBound

open scoped BigOperators
open Complex Real MeasureTheory
open MAPJutilaPseudocharacterMExact
open MAPJutilaPseudocharacterMollifierSum
open MAPJutilaLemma6MellinIntegral
open MAPJutilaLemma6MellinIntegralSharp
open MAPJutilaLemma6GammaKernel
open MAPJutilaP48ConvexityAdapter

noncomputable section

def jutilaMWeightedSum {q : ℕ}
    (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    (D S : Finset ℕ) (v : ℝ) : ℂ :=
  ∑ r ∈ S,
    ((r : ℂ)⁻¹ * jutilaMFinite chi xi D r v)

def lemmaSixMellinErrorIntegrand {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    (D S : Finset ℕ) (beta t X u : ℝ) : ℂ :=
  Complex.Gamma ((-beta : ℝ) + (u : ℂ) * I) *
    DirichletCharacter.LFunction chi (((t + u : ℝ) : ℂ) * I) *
    (X : ℂ) ^ ((-beta : ℝ) + (u : ℂ) * I) *
    jutilaMWeightedSum chi xi D S (t + u)

/-- Regression test for the interface bug caught during the source descent:
once `R ≥ 4`, the whole interval `1 ≤ r ≤ R` cannot be the primed Jutila
system because it contains the nonsquarefree integer `4`. -/
theorem not_all_Icc_squarefree_of_four_le {R : ℕ} (hR : 4 ≤ R) :
    ¬ (∀ r ∈ Finset.Icc 1 R, Squarefree r) := by
  intro h
  have hfour : Squarefree (4 : ℕ) := h 4 (Finset.mem_Icc.mpr ⟨by omega, hR⟩)
  rw [Nat.squarefree_iff_prime_squarefree] at hfour
  exact hfour 2 (by norm_num) (by norm_num)

theorem norm_jutilaMWeightedSum_le
    {q : ℕ} (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    {D S : Finset ℕ} {z2 R : ℕ}
    (hDcard : D.card ≤ z2) (hDpos : ∀ d ∈ D, 0 < d)
    (hxi : ∀ d ∈ D, ‖xi d‖ ≤ 1)
    (hS : S ⊆ Finset.Icc 1 R)
    (hrsq : ∀ r ∈ S, Squarefree r)
    (hrcop : ∀ r ∈ S, r.Coprime q)
    (v : ℝ) :
    ‖jutilaMWeightedSum chi xi D S v‖ ≤
      (z2 : ℝ) * (R : ℝ) * (harmonic R : ℝ) ^ 4 := by
  have hsum := sum_inv_mul_norm_jutilaMFinite_selected_le
    chi xi hDcard hDpos hxi hS hrsq hrcop v
  calc
    ‖jutilaMWeightedSum chi xi D S v‖ ≤
        ∑ r ∈ S,
          ‖(r : ℂ)⁻¹ * jutilaMFinite chi xi D r v‖ := by
      unfold jutilaMWeightedSum
      exact norm_sum_le _ _
    _ = ∑ r ∈ S,
          (r : ℝ)⁻¹ * ‖jutilaMFinite chi xi D r v‖ := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [norm_mul, norm_inv]
      simp
    _ ≤ (z2 : ℝ) * (R : ℝ) * (harmonic R : ℝ) ^ 4 := hsum

private theorem gamma_vertical_continuous
    {beta omega : ℝ} (homega : 0 < omega)
    (hbetaLow : 4 / 5 ≤ beta) (hbetaHigh : beta ≤ 1 - omega) :
    Continuous (fun u : ℝ =>
      Complex.Gamma ((-beta : ℝ) + (u : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hpole : ∀ m : ℕ,
      ((-beta : ℝ) + (u : ℂ) * I) ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    simp at hre
    have hbetaPos : 0 < beta := by linarith
    have hbetaLt : beta < 1 := by linarith
    rcases m with _ | m
    · norm_num at hre
      linarith
    · have hmOne : (1 : ℝ) ≤ Nat.succ m := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
      linarith
  exact (Complex.continuousAt_Gamma _ hpole).comp_of_eq
    (by fun_prop) rfl

theorem continuous_lemmaSixGammaLNorm
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1)
    {beta omega : ℝ} (homega : 0 < omega)
    (hbetaLow : 4 / 5 ≤ beta) (hbetaHigh : beta ≤ 1 - omega)
    (t : ℝ) :
    Continuous (fun u : ℝ => lemmaSixGammaLNorm chi beta t u) := by
  unfold lemmaSixGammaLNorm
  apply Continuous.mul
  · exact (gamma_vertical_continuous homega hbetaLow hbetaHigh).norm
  · exact ((DirichletCharacter.differentiable_LFunction hchi).continuous.comp
      (by fun_prop)).norm

theorem integrable_lemmaSixGammaLNorm
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {beta omega : ℝ} (homega : 0 < omega)
    (hbetaLow : 4 / 5 ≤ beta) (hbetaHigh : beta ≤ 1 - omega)
    (t : ℝ) :
    Integrable (fun u : ℝ => lemmaSixGammaLNorm chi beta t u) := by
  let K : ℝ := 2 * lemmaSixGammaSqConstant omega *
    p48ConvexityConstant * Real.rpow (q : ℝ) p48HeightExponent * (1 + |t|)
  have hmajor : Integrable (fun u : ℝ => K * (1 + u ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul K
  apply hmajor.mono'
  · exact (continuous_lemmaSixGammaLNorm chi hchi homega
      hbetaLow hbetaHigh t).aestronglyMeasurable
  · filter_upwards with u
    have hnonneg : 0 ≤ lemmaSixGammaLNorm chi beta t u := by
      unfold lemmaSixGammaLNorm
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    simpa only [K] using lemmaSixGammaLNorm_le_cauchy
      chi hprim hchi homega hbetaLow hbetaHigh t u

theorem norm_lemmaSixMellinErrorIntegrand_le
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    {D S : Finset ℕ} {z2 R : ℕ}
    (hDcard : D.card ≤ z2) (hDpos : ∀ d ∈ D, 0 < d)
    (hxi : ∀ d ∈ D, ‖xi d‖ ≤ 1)
    (hS : S ⊆ Finset.Icc 1 R)
    (hrsq : ∀ r ∈ S, Squarefree r)
    (hrcop : ∀ r ∈ S, r.Coprime q)
    {beta t X u : ℝ} (hX : 0 < X) :
    ‖lemmaSixMellinErrorIntegrand chi xi D S beta t X u‖ ≤
      (Real.rpow X (-beta) *
        ((z2 : ℝ) * (R : ℝ) * (harmonic R : ℝ) ^ 4)) *
          lemmaSixGammaLNorm chi beta t u := by
  have hM := norm_jutilaMWeightedSum_le
    chi xi hDcard hDpos hxi hS hrsq hrcop (t + u)
  have hXnorm : ‖(X : ℂ) ^ ((-beta : ℝ) + (u : ℂ) * I)‖ =
      Real.rpow X (-beta) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
    congr 1
    simp
  unfold lemmaSixMellinErrorIntegrand
  simp only [norm_mul, hXnorm]
  unfold lemmaSixGammaLNorm
  have hGamma0 : 0 ≤ ‖Complex.Gamma ((-beta : ℝ) + (u : ℂ) * I)‖ :=
    norm_nonneg _
  have hL0 : 0 ≤
      ‖DirichletCharacter.LFunction chi (((t + u : ℝ) : ℂ) * I)‖ :=
    norm_nonneg _
  have hX0 : 0 ≤ Real.rpow X (-beta) := Real.rpow_nonneg hX.le _
  calc
    ‖Complex.Gamma ((-beta : ℝ) + (u : ℂ) * I)‖ *
        ‖DirichletCharacter.LFunction chi (((t + u : ℝ) : ℂ) * I)‖ *
        Real.rpow X (-beta) * ‖jutilaMWeightedSum chi xi D S (t + u)‖ ≤
      ‖Complex.Gamma ((-beta : ℝ) + (u : ℂ) * I)‖ *
        ‖DirichletCharacter.LFunction chi (((t + u : ℝ) : ℂ) * I)‖ *
        Real.rpow X (-beta) *
          ((z2 : ℝ) * (R : ℝ) * (harmonic R : ℝ) ^ 4) := by
      gcongr
    _ = (Real.rpow X (-beta) *
          ((z2 : ℝ) * (R : ℝ) * (harmonic R : ℝ) ^ 4)) *
        (‖Complex.Gamma ((-beta : ℝ) + (u : ℂ) * I)‖ *
          ‖DirichletCharacter.LFunction chi (((t + u : ℝ) : ℂ) * I)‖) := by
      ring

/-- Complete absolute integral estimate for the right side of (2.11). -/
theorem integral_norm_lemmaSixMellinErrorIntegrand_le
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    (xi : ℕ → ℂ) {D S : Finset ℕ} {z2 R : ℕ}
    (hDcard : D.card ≤ z2) (hDpos : ∀ d ∈ D, 0 < d)
    (hxi : ∀ d ∈ D, ‖xi d‖ ≤ 1)
    (hS : S ⊆ Finset.Icc 1 R)
    (hrsq : ∀ r ∈ S, Squarefree r)
    (hrcop : ∀ r ∈ S, r.Coprime q)
    {beta omega t X : ℝ} (homega : 0 < omega)
    (hbetaLow : 4 / 5 ≤ beta) (hbetaHigh : beta ≤ 1 - omega)
    (hX : 0 < X) :
    (∫ u : ℝ, ‖lemmaSixMellinErrorIntegrand chi xi D S beta t X u‖) ≤
      (Real.rpow X (-beta) *
        ((z2 : ℝ) * (R : ℝ) * (harmonic R : ℝ) ^ 4)) *
      (2 * Real.pi * lemmaSixGammaSqConstant omega *
        p48ConvexityConstant *
          Real.rpow ((q : ℝ) * (1 + |t|)) p48HeightExponent) := by
  let C : ℝ := Real.rpow X (-beta) *
    ((z2 : ℝ) * (R : ℝ) * (harmonic R : ℝ) ^ 4)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hGammaInt := integrable_lemmaSixGammaLNorm chi hprim hchi
    homega hbetaLow hbetaHigh t
  have hmajor : Integrable
      (fun u : ℝ => C * lemmaSixGammaLNorm chi beta t u) :=
    hGammaInt.const_mul C
  calc
    (∫ u : ℝ, ‖lemmaSixMellinErrorIntegrand chi xi D S beta t X u‖) ≤
        ∫ u : ℝ, C * lemmaSixGammaLNorm chi beta t u :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        hmajor
        (Filter.Eventually.of_forall fun u => by
          simpa only [C] using norm_lemmaSixMellinErrorIntegrand_le
            chi xi hDcard hDpos hxi hS hrsq hrcop hX)
    _ = C * ∫ u : ℝ, lemmaSixGammaLNorm chi beta t u := by
      rw [integral_const_mul]
    _ ≤ C * (2 * Real.pi * lemmaSixGammaSqConstant omega *
          p48ConvexityConstant *
            Real.rpow ((q : ℝ) * (1 + |t|)) p48HeightExponent) :=
      mul_le_mul_of_nonneg_left
        (integral_lemmaSixGammaLNorm_le_sharp chi hprim hchi
          homega hbetaLow hbetaHigh t) hC
    _ = (Real.rpow X (-beta) *
          ((z2 : ℝ) * (R : ℝ) * (harmonic R : ℝ) ^ 4)) *
        (2 * Real.pi * lemmaSixGammaSqConstant omega *
          p48ConvexityConstant *
            Real.rpow ((q : ℝ) * (1 + |t|)) p48HeightExponent) := by rfl

end

end MAPJutilaLemma6ErrorBound

#print axioms MAPJutilaLemma6ErrorBound.norm_jutilaMWeightedSum_le
#print axioms MAPJutilaLemma6ErrorBound.not_all_Icc_squarefree_of_four_le
#print axioms MAPJutilaLemma6ErrorBound.integrable_lemmaSixGammaLNorm
#print axioms MAPJutilaLemma6ErrorBound.integral_norm_lemmaSixMellinErrorIntegrand_le
