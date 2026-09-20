import GoldfeldPolyaVinogradovKernel
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The finite Abel-summation part of Koukoulopoulos, Lemma 11.2

This module separates the arithmetic Pólya--Vinogradov input from the analytic
continuation issue.  The first theorem packages the bound for initial
character sums.  The second is the exact finite summation-by-parts estimate
used on the tail of the differentiated Dirichlet series.
-/

namespace MAPGoldfeldSiegel

open Complex Set
open scoped BigOperators

noncomputable section

/-- Initial sums are a special case of the interval Pólya--Vinogradov bound. -/
theorem primitive_quadratic_initialSum_norm_le
    {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (chi : DirichletCharacter ℂ N)
    (hprim : chi.IsPrimitive) (hreal : chi ^ 2 = 1) (M : ℕ) :
    ‖∑ n ∈ Finset.range M, chi (n : ZMod N)‖ ≤
      Real.sqrt N * (1 + Real.log N) := by
  simpa using primitive_quadratic_polyaVinogradov hN chi hprim hreal 0 M

/-- Finite Abel summation with a nonnegative decreasing real weight.  This is
the exact deterministic estimate behind the tail in Lemma 11.2. -/
theorem norm_sum_Ioc_mul_le_two_mul_of_antitone
    (c : ℕ → ℂ) (w : ℕ → ℝ) {K M : ℕ} {P : ℝ}
    (hKM : K < M)
    (hpartial : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, c i‖ ≤ P)
    (hw_nonneg : ∀ n, K < n → n ≤ M → 0 ≤ w n)
    (hw_anti : ∀ i, K < i → i < M → w (i + 1) ≤ w i) :
    ‖∑ n ∈ Finset.Ioc K M, (w n : ℂ) * c n‖ ≤
      2 * P * w (K + 1) := by
  have hparts := Finset.sum_Ioc_by_parts (fun n => (w n : ℂ)) c hKM
  simp only [smul_eq_mul] at hparts
  rw [hparts]
  have hKM1 : K + 1 ≤ M := Nat.succ_le_iff.mpr hKM
  have hwK : 0 ≤ w (K + 1) := hw_nonneg (K + 1) (Nat.lt_succ_self K) hKM1
  have hwM : 0 ≤ w M := hw_nonneg M hKM le_rfl
  have hdiff_nonneg : ∀ i ∈ Finset.Ioc K (M - 1), 0 ≤ w i - w (i + 1) := by
    intro i hi
    have hi' := Finset.mem_Ioc.mp hi
    exact sub_nonneg.mpr (hw_anti i hi'.1 (by omega))
  have htel :
      (∑ i ∈ Finset.Ioc K (M - 1), (w i - w (i + 1))) =
        w (K + 1) - w M := by
    rw [← Finset.Ico_add_one_add_one_eq_Ioc]
    have hsub : M - 1 + 1 = M := Nat.sub_add_cancel (Nat.one_le_of_lt hKM)
    rw [hsub]
    have hshift :
        (∑ i ∈ Finset.Ico (K + 1) M, (w i - w (i + 1))) =
          (∑ j ∈ Finset.range (M - (K + 1)),
            (w (j + (K + 1)) - w (j + (K + 1) + 1))) := by
      rw [Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      congr 2 <;> omega
    rw [hshift]
    have htel' := Finset.sum_range_sub'
      (fun j => w (j + (K + 1))) (M - (K + 1))
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      Nat.sub_add_cancel hKM1] using htel'
  calc
    ‖(w M : ℂ) * (∑ i ∈ Finset.range (M + 1), c i) -
          (w (K + 1) : ℂ) * (∑ i ∈ Finset.range (K + 1), c i) -
          ∑ i ∈ Finset.Ioc K (M - 1),
            ((w (i + 1) : ℂ) - (w i : ℂ)) *
              ∑ j ∈ Finset.range (i + 1), c j‖
        ≤ ‖(w M : ℂ) * (∑ i ∈ Finset.range (M + 1), c i)‖ +
            ‖(w (K + 1) : ℂ) * (∑ i ∈ Finset.range (K + 1), c i)‖ +
            ‖∑ i ∈ Finset.Ioc K (M - 1),
              ((w (i + 1) : ℂ) - (w i : ℂ)) *
                ∑ j ∈ Finset.range (i + 1), c j‖ := by
          exact (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ ≤ w M * P + w (K + 1) * P +
          ∑ i ∈ Finset.Ioc K (M - 1), (w i - w (i + 1)) * P := by
      gcongr
      · simpa [norm_mul, Real.norm_eq_abs, abs_of_nonneg hwM] using
          mul_le_mul_of_nonneg_left (hpartial (M + 1)) hwM
      · simpa [norm_mul, Real.norm_eq_abs, abs_of_nonneg hwK] using
          mul_le_mul_of_nonneg_left (hpartial (K + 1)) hwK
      · calc
          ‖∑ i ∈ Finset.Ioc K (M - 1),
              ((w (i + 1) : ℂ) - (w i : ℂ)) *
                ∑ j ∈ Finset.range (i + 1), c j‖
              ≤ ∑ i ∈ Finset.Ioc K (M - 1),
                  ‖((w (i + 1) : ℂ) - (w i : ℂ)) *
                    ∑ j ∈ Finset.range (i + 1), c j‖ := norm_sum_le _ _
          _ ≤ ∑ i ∈ Finset.Ioc K (M - 1), (w i - w (i + 1)) * P := by
            apply Finset.sum_le_sum
            intro i hi
            have hd := hdiff_nonneg i hi
            rw [norm_mul, ← ofReal_sub, norm_real, Real.norm_eq_abs,
              abs_of_nonpos (by linarith)]
            simpa [abs_of_nonneg hd] using
              mul_le_mul_of_nonneg_left (hpartial (i + 1)) hd
    _ = 2 * P * w (K + 1) := by
      rw [← Finset.sum_mul, htel]
      ring

/-- Positive real weight occurring in the first derivative of a Dirichlet
series on the real axis. -/
def firstDerivativeWeight (sigma : ℝ) (n : ℕ) : ℝ :=
  Real.log n / (n : ℝ) ^ sigma

theorem firstDerivativeWeight_nonneg {sigma : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ firstDerivativeWeight sigma n := by
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hn))
    (Real.rpow_nonneg (Nat.cast_nonneg n) sigma)

/-- For `sigma ≥ 1/2`, the differentiated-series weight decreases from the
explicit integer point `9` onward. -/
theorem firstDerivativeWeight_antitone_of_nine_le
    {sigma : ℝ} (hsigma : 1 / 2 ≤ sigma) {m n : ℕ}
    (hm : 9 ≤ m) (hmn : m ≤ n) :
    firstDerivativeWeight sigma n ≤ firstDerivativeWeight sigma m := by
  have hsigmaPos : 0 < sigma := lt_of_lt_of_le (by norm_num) hsigma
  have hinv : sigma⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hsigmaPos (by norm_num : (0 : ℝ) < 2)]
    norm_num
    exact hsigma
  have hexpTwo : Real.exp 2 < 9 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  have hexp : Real.exp sigma⁻¹ ≤ (m : ℝ) := by
    calc
      Real.exp sigma⁻¹ ≤ Real.exp 2 := Real.exp_le_exp.mpr hinv
      _ ≤ (9 : ℝ) := hexpTwo.le
      _ ≤ (m : ℝ) := by exact_mod_cast hm
  have hexpN : Real.exp sigma⁻¹ ≤ (n : ℝ) :=
    hexp.trans (by exact_mod_cast hmn)
  exact Real.log_div_self_rpow_antitoneOn hsigmaPos
    (by simpa using hexp) (by simpa using hexpN) (by exact_mod_cast hmn)

/-- The finite tail estimate in the `j = 1`, `t = 0` case of Lemma 11.2. -/
theorem primitive_quadratic_firstDerivative_tail_finite
    {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (chi : DirichletCharacter ℂ N)
    (hprim : chi.IsPrimitive) (hreal : chi ^ 2 = 1)
    {sigma : ℝ} (hsigma : 1 / 2 ≤ sigma)
    {K M : ℕ} (hK : 9 ≤ K) (hKM : K < M) :
    ‖∑ n ∈ Finset.Ioc K M,
        (firstDerivativeWeight sigma n : ℂ) * chi (n : ZMod N)‖ ≤
      2 * (Real.sqrt N * (1 + Real.log N)) *
        firstDerivativeWeight sigma (K + 1) := by
  apply norm_sum_Ioc_mul_le_two_mul_of_antitone
  · exact hKM
  · intro n
    exact primitive_quadratic_initialSum_norm_le hN chi hprim hreal n
  · intro n hKn hnM
    exact firstDerivativeWeight_nonneg (by omega)
  · intro i hKi hiM
    exact firstDerivativeWeight_antitone_of_nine_le hsigma (by omega)
      (Nat.le_succ i)

/-- Passing the uniform finite-tail estimate to any certified ordered-series
limit.  The continuation identification supplying `hlim` is deliberately not
hidden in this deterministic lemma. -/
theorem primitive_quadratic_firstDerivative_tail_limit
    {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (chi : DirichletCharacter ℂ N)
    (hprim : chi.IsPrimitive) (hreal : chi ^ 2 = 1)
    {sigma : ℝ} (hsigma : 1 / 2 ≤ sigma)
    {K : ℕ} (hK : 9 ≤ K) {z : ℂ}
    (hlim : Filter.Tendsto
      (fun M => ∑ n ∈ Finset.Ioc K M,
        (firstDerivativeWeight sigma n : ℂ) * chi (n : ZMod N))
      Filter.atTop (nhds z)) :
    ‖z‖ ≤ 2 * (Real.sqrt N * (1 + Real.log N)) *
      firstDerivativeWeight sigma (K + 1) := by
  apply le_of_tendsto hlim.norm
  filter_upwards [Filter.eventually_gt_atTop K] with M hKM
  exact primitive_quadratic_firstDerivative_tail_finite hN chi hprim hreal
    hsigma hK hKM

end
end MAPGoldfeldSiegel

#print axioms MAPGoldfeldSiegel.primitive_quadratic_initialSum_norm_le
#print axioms MAPGoldfeldSiegel.norm_sum_Ioc_mul_le_two_mul_of_antitone
#print axioms MAPGoldfeldSiegel.firstDerivativeWeight_antitone_of_nine_le
#print axioms MAPGoldfeldSiegel.primitive_quadratic_firstDerivative_tail_finite
#print axioms MAPGoldfeldSiegel.primitive_quadratic_firstDerivative_tail_limit
