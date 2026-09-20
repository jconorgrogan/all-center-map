import MRTCorollary25Interface
import SharpFinitePerronStep
import PrimitiveTruncatedExplicitFormulaBridge

/-!
# First-principles Perron core for MRT Corollary 2.5

This file proves only exact finite identities.  It does not assume the
published cutoff-removal estimate.
-/

namespace MAPMRTCorollary25PerronCore

open scoped BigOperators
open MAPMRTCorollary25 MixedMeanFrontend
open PrimitiveTruncatedExplicitFormulaBridge

noncomputable section

def rawPrefixOn (S : Finset ℕ) (N : ℕ) (f : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, if n ≤ N then f n * mellinPhase n t else 0

def kernelPrefixOn (S : Finset ℕ) (N : ℕ) (f : ℕ → ℂ)
    (t c T : ℝ) : ℂ :=
  ∑ n ∈ S, (f n * mellinPhase n t) *
    PerronKernel.kernel
      (halfIntegerPoint N / n) c T

theorem halfInteger_ratio_gt_one_iff
    {N n : ℕ} (hn : 1 ≤ n) :
    1 < halfIntegerPoint N / (n : ℝ) ↔
      n ≤ N := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [one_lt_div hnpos]
  unfold halfIntegerPoint
  constructor
  · intro h
    by_contra hnot
    have hNn : N + 1 ≤ n := Nat.add_one_le_iff.mpr (Nat.lt_of_not_ge hnot)
    have hcast : (N : ℝ) + 1 ≤ n := by exact_mod_cast hNn
    linarith
  · intro h
    have hcast : (n : ℝ) ≤ N := by exact_mod_cast h
    linarith

theorem kernelPrefixOn_eq_integral
    (S : Finset ℕ) (N : ℕ) (f : ℕ → ℂ) (t : ℝ)
    {c T : ℝ} (hc : 0 < c) :
    kernelPrefixOn S N f t c T =
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        ∫ u in (-T)..T,
          PerronKernel.finitePerronPolynomial S
            (fun n => f n * mellinPhase n t)
            (fun n =>
              halfIntegerPoint N / n)
            c u := by
  symm
  exact PerronKernel.kernel_finset_sum S
    (fun n => f n * mellinPhase n t)
    (fun n => halfIntegerPoint N / n) hc

def finiteHalfLinePolynomial
    (S : Finset ℕ) (f : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, (f n / (Real.sqrt (n : ℝ) : ℂ)) * mellinPhase n t

theorem verticalPower_half_div_nat
    {x : ℝ} {n : ℕ} (hx : 0 < x) (hn : 1 ≤ n) (u : ℝ) :
    PerronKernel.verticalPower (x / n) (1 / 2 : ℝ) u =
      PerronKernel.verticalPower x (1 / 2 : ℝ) u *
        (Real.sqrt (n : ℝ) : ℂ)⁻¹ *
        Complex.exp (-((u * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hdiv : 0 < x / (n : ℝ) := div_pos hx hnpos
  unfold PerronKernel.verticalPower
  rw [Real.div_rpow hx.le hnpos.le]
  rw [Real.log_div hx.ne' hnpos.ne']
  rw [show (n : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt n by
    simpa [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num] using
      (Real.sqrt_eq_rpow (n : ℝ)).symm]
  have hexp : Complex.exp
      (Complex.I * ((u : ℂ) *
        ((Real.log x - Real.log (n : ℝ) : ℝ) : ℂ))) =
        Complex.exp (Complex.I * ((u : ℂ) * (Real.log x : ℂ))) *
          Complex.exp (-((u * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp]
  push_cast
  field_simp [ne_of_gt (Real.sqrt_pos.2 hnpos)]

theorem mellinPhase_mul_frequency
    (n : ℕ) (t u : ℝ) :
    mellinPhase n t *
        Complex.exp (-((u * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I) =
      mellinPhase n (t + u) := by
  unfold mellinPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact factorization of the raw Perron polynomial into the critical-line
Dirichlet polynomial and the scalar Perron carrier. -/
theorem finitePerronPolynomial_eq_carrier_mul
    (S : Finset ℕ) (f : ℕ → ℂ) (t u : ℝ)
    {x : ℝ} (hx : 0 < x) (hS : ∀ n ∈ S, 1 ≤ n) :
    PerronKernel.finitePerronPolynomial S
        (fun n => f n * mellinPhase n t) (fun n => x / n)
        (1 / 2 : ℝ) u =
      (PerronKernel.verticalPower x (1 / 2 : ℝ) u /
          (((1 / 2 : ℝ) : ℂ) + Complex.I * u)) *
        finiteHalfLinePolynomial S f (t + u) := by
  unfold PerronKernel.finitePerronPolynomial finiteHalfLinePolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hnmem
  unfold PerronKernel.verticalIntegrand
  rw [verticalPower_half_div_nat hx (hS n hnmem) u]
  have hphase := mellinPhase_mul_frequency n t u
  rw [show (f n * mellinPhase n t) *
        (PerronKernel.verticalPower x (1 / 2 : ℝ) u *
          (Real.sqrt (n : ℝ) : ℂ)⁻¹ *
          Complex.exp (-((u * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I) /
          (((1 / 2 : ℝ) : ℂ) + Complex.I * u)) =
      (PerronKernel.verticalPower x (1 / 2 : ℝ) u /
          (((1 / 2 : ℝ) : ℂ) + Complex.I * u)) *
        (f n / (Real.sqrt (n : ℝ) : ℂ)) *
        (mellinPhase n t *
          Complex.exp (-((u * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I)) by ring]
  rw [hphase]
  ring

/-- Exact step extracted from the sharp kernel representation. -/
theorem rawPrefixOn_eq_stepSum
    (S : Finset ℕ) (N : ℕ) (f : ℕ → ℂ) (t : ℝ)
    (hS : ∀ n ∈ S, 1 ≤ n) :
    rawPrefixOn S N f t =
      ∑ n ∈ S, (f n * mellinPhase n t) *
        (if 1 < halfIntegerPoint N / n
          then (1 : ℂ) else 0) := by
  unfold rawPrefixOn
  apply Finset.sum_congr rfl
  intro n hn
  have hiff := halfInteger_ratio_gt_one_iff (N := N) (hS n hn)
  by_cases h : n ≤ N <;> simp [h, hiff]

/-- Exact finite coefficientwise Perron error before any harmonic summation. -/
theorem norm_rawPrefixOn_sub_kernelPrefixOn_le
    (S : Finset ℕ) (N : ℕ) (f : ℕ → ℂ) (t : ℝ)
    {c T : ℝ} (hc : 0 < c) (hT : 0 < T)
    (hS : ∀ n ∈ S, 1 ≤ n) :
    ‖rawPrefixOn S N f t - kernelPrefixOn S N f t c T‖ ≤
      ∑ n ∈ S, ‖f n‖ *
        ((halfIntegerPoint N / n) ^ c /
          (Real.pi * T *
            |Real.log
              (halfIntegerPoint N / n)|)) := by
  rw [rawPrefixOn_eq_stepSum S N f t hS]
  unfold kernelPrefixOn
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ n ∈ S,
        ((f n * mellinPhase n t) *
            (if 1 < halfIntegerPoint N / n
              then (1 : ℂ) else 0) -
          (f n * mellinPhase n t) *
            PerronKernel.kernel
              (halfIntegerPoint N / n) c T)‖
        ≤ ∑ n ∈ S, ‖(f n * mellinPhase n t) *
            ((if 1 < halfIntegerPoint N / n
              then (1 : ℂ) else 0) -
              PerronKernel.kernel
                (halfIntegerPoint N / n) c T)‖ := by
          simpa only [mul_sub] using
            (norm_sum_le S (fun n => (f n * mellinPhase n t) *
              ((if 1 < halfIntegerPoint N / n then (1 : ℂ) else 0) -
                PerronKernel.kernel (halfIntegerPoint N / n) c T)))
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hS n hn
      have hxpos : 0 < halfIntegerPoint N :=
        halfIntegerPoint_pos N
      have hyratio : 0 <
          halfIntegerPoint N / (n : ℝ) :=
        div_pos hxpos hnpos
      have hyratioNe :
          halfIntegerPoint N / (n : ℝ) ≠ 1 := by
        intro heq
        have heq' : halfIntegerPoint N = (n : ℝ) := by
          calc
            halfIntegerPoint N = 1 * (n : ℝ) :=
              (div_eq_iff hnpos.ne').mp (by simpa using heq)
            _ = (n : ℝ) := one_mul _
        unfold halfIntegerPoint at heq'
        have : ((N : ℝ) + 1 / 2) ≠ (n : ℝ) := by
          intro h
          have htwo : (2 : ℝ) * (N : ℝ) + 1 = 2 * (n : ℝ) := by linarith
          have hodd : (2 * N + 1 : ℕ) = 2 * n := by exact_mod_cast htwo
          omega
        exact this heq'
      have hk := SharpFinitePerronStep.norm_kernel_sub_step_le
        hyratio hc hT hyratioNe
      rw [norm_mul, norm_mul]
      have hphase : ‖mellinPhase n t‖ = 1 := by
        unfold mellinPhase
        rw [Complex.norm_exp]
        have hre :
            ((-((t * Real.log (n : ℝ) : ℝ) : ℂ)) * Complex.I).re = 0 := by
          simp only [Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
            Complex.I_re, Complex.I_im]
          ring
        rw [hre, Real.exp_zero]
      rw [hphase, mul_one]
      have hflip :
          ‖(if 1 < halfIntegerPoint N / (n : ℝ)
              then (1 : ℂ) else 0) -
              PerronKernel.kernel
                (halfIntegerPoint N / n) c T‖ =
            ‖PerronKernel.kernel
                (halfIntegerPoint N / n) c T -
              (if 1 < halfIntegerPoint N / (n : ℝ)
                then (1 : ℂ) else 0)‖ := by
        rw [← norm_neg]
        congr 1
        ring
      rw [hflip]
      exact mul_le_mul_of_nonneg_left hk (norm_nonneg _)

end
end MAPMRTCorollary25PerronCore

#print axioms MAPMRTCorollary25PerronCore.kernelPrefixOn_eq_integral
#print axioms MAPMRTCorollary25PerronCore.verticalPower_half_div_nat
#print axioms MAPMRTCorollary25PerronCore.finitePerronPolynomial_eq_carrier_mul
#print axioms MAPMRTCorollary25PerronCore.norm_rawPrefixOn_sub_kernelPrefixOn_le
