import TwistedMangoldtPerron
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The actual logarithmic derivative on the Perron line

This file replaces the finite Dirichlet-polynomial surrogate by the genuine
negative logarithmic derivative on `Re s = c > 1`.  Absolute convergence is
used to commute the whole twisted Mangoldt series through a finite vertical
integral, and the omitted coefficients are retained as a literal, bounded
remainder.
-/

namespace TruncatedTwistedPerron

open Set MeasureTheory Metric TopologicalSpace PerronKernel PrimitiveExplicitFormulaSpine
open scoped BigOperators Interval ArithmeticFunction LSeries.notation

noncomputable section

/-- The `n`th absolutely convergent Perron-line summand. -/
def perronTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (x c : ℝ)
    (n : ℕ) (t : ℝ) : ℂ :=
  LSeries.term (twistedMangoldtCoeff χ)
      ((c : ℂ) + Complex.I * t) n *
    verticalPower x c t / ((c : ℂ) + Complex.I * t)

/-- The actual Perron integrand containing `-L'/L`, not a finite polynomial. -/
def logDerivPerronIntegrand {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (x c : ℝ) (t : ℝ) : ℂ :=
  (-logDeriv (DirichletCharacter.LFunction χ)
      ((c : ℂ) + Complex.I * t)) *
    verticalPower x c t / ((c : ℂ) + Complex.I * t)

/-- The normalized finite vertical integral of the actual logarithmic derivative. -/
def rightLineIntegral {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (x c T : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ t in (-T)..T, logDerivPerronIntegrand χ x c t

/-- Every individual Perron summand is continuous on the real parameter line. -/
theorem continuous_perronTerm {q : ℕ} (χ : DirichletCharacter ℂ q)
    {x c : ℝ} (_hx : 0 < x) (hc : 0 < c) (n : ℕ) :
    Continuous (perronTerm χ x c n) := by
  unfold perronTerm verticalPower
  apply Continuous.div
  · apply Continuous.mul
    · exact continuous_iff_continuousAt.mpr fun t => by
        have houter := (LSeries.hasDerivAt_term (twistedMangoldtCoeff χ) n
          ((c : ℂ) + Complex.I * t)).continuousAt
        have hinner : ContinuousAt (fun u : ℝ =>
            (c : ℂ) + Complex.I * (u : ℂ)) t := by fun_prop
        have hcomp : ContinuousAt
            ((fun z : ℂ => LSeries.term (twistedMangoldtCoeff χ) z n) ∘
              (fun u : ℝ => (c : ℂ) + Complex.I * (u : ℂ))) t :=
          ContinuousAt.comp_of_eq (f := fun u : ℝ =>
              (c : ℂ) + Complex.I * (u : ℂ))
            (g := fun z : ℂ => LSeries.term (twistedMangoldtCoeff χ) z n)
            houter hinner rfl
        simpa only [Function.comp_apply] using hcomp
    · fun_prop
  · fun_prop
  · exact fun t => denominator_ne_zero hc

/-- The norm of a Perron summand is controlled by the corresponding absolute
Dirichlet-series term on the real point `c`, uniformly in height. -/
theorem norm_perronTerm_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    {x c : ℝ} (hx : 0 < x) (hc : 0 < c) (n : ℕ) (t : ℝ) :
    ‖perronTerm χ x c n t‖ ≤
      ‖LSeries.term (twistedMangoldtCoeff χ) (c : ℂ) n‖ * (x ^ c / c) := by
  rw [perronTerm, norm_div, norm_mul, norm_verticalPower hx]
  have hterm :
      ‖LSeries.term (twistedMangoldtCoeff χ)
          ((c : ℂ) + Complex.I * t) n‖ =
        ‖LSeries.term (twistedMangoldtCoeff χ) (c : ℂ) n‖ := by
    simp only [LSeries.norm_term_eq, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, add_zero]
  rw [hterm]
  have hden := c_le_norm_denominator (t := t) hc.le
  have hxc : 0 ≤ x ^ c := Real.rpow_nonneg hx.le c
  calc
    ‖LSeries.term (twistedMangoldtCoeff χ) (c : ℂ) n‖ * x ^ c /
          ‖(c : ℂ) + Complex.I * (t : ℂ)‖
        ≤ ‖LSeries.term (twistedMangoldtCoeff χ) (c : ℂ) n‖ * x ^ c / c := by
          exact div_le_div_of_nonneg_left
            (mul_nonneg (norm_nonneg _) hxc) hc hden
    _ = ‖LSeries.term (twistedMangoldtCoeff χ) (c : ℂ) n‖ *
          (x ^ c / c) := by ring

/-- Positive-base exponent algebra identifying the L-series term with the
`x/n` Perron kernel.  This is the branch-sensitive step that connects the
actual logarithmic derivative to `PerronKernel.kernel`. -/
theorem verticalPower_div_nat_cpow
    {x c t : ℝ} {n : ℕ} (hx : 0 < x) (hn : n ≠ 0) :
    verticalPower x c t /
        (n : ℂ) ^ ((c : ℂ) + Complex.I * t) =
      verticalPower (x / n) c t := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [verticalPower_eq_exp hx, verticalPower_eq_exp (div_pos hx hnpos)]
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn)]
  rw [← Complex.natCast_log]
  rw [div_eq_mul_inv, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  rw [Real.log_div hx.ne' hnpos.ne']
  push_cast
  ring

/-- Every nonzero-index Perron-line summand is exactly the twisted Mangoldt
coefficient times the existing positive-base kernel integrand. -/
theorem perronTerm_eq_coeff_mul_verticalIntegrand
    {q : ℕ} (χ : DirichletCharacter ℂ q) {x c : ℝ}
    (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    perronTerm χ x c n t =
      twistedMangoldtCoeff χ n * verticalIntegrand (x / n) c t := by
  rw [perronTerm, LSeries.term_of_ne_zero hn, verticalIntegrand,
    ← verticalPower_div_nat_cpow hx hn]
  ring

/-- The normalized integral of one nonzero coefficient is exactly that
coefficient times the finite-height Perron kernel. -/
theorem normalized_integral_perronTerm_eq_coeff_mul_kernel
    {q : ℕ} (χ : DirichletCharacter ℂ q) {x c T : ℝ}
    (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t in (-T)..T, perronTerm χ x c n t =
      twistedMangoldtCoeff χ n * kernel (x / n) c T := by
  simp_rw [perronTerm_eq_coeff_mul_verticalIntegrand χ hx hn]
  rw [intervalIntegral.integral_const_mul, kernel]
  ring

/-- The whole family of Perron summands is summable in the uniform norm on
any finite height interval. -/
theorem summable_restricted_perronTerm {q : ℕ} (χ : DirichletCharacter ℂ q)
    {x c T : ℝ} (hx : 0 < x) (hc1 : 1 < c) :
    Summable fun n : ℕ =>
      ‖(ContinuousMap.mk (perronTerm χ x c n)
          (continuous_perronTerm χ hx (lt_trans zero_lt_one hc1) n)).restrict
        (⟨uIcc (-T) T, isCompact_uIcc⟩ : Compacts ℝ)‖ := by
  let b : ℕ → ℝ := fun n =>
    ‖LSeries.term (twistedMangoldtCoeff χ) (c : ℂ) n‖ * (x ^ c / c)
  have hs : LSeriesSummable (twistedMangoldtCoeff χ) (c : ℂ) := by
    simpa only [twistedMangoldtCoeff, Pi.mul_apply] using
      (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ
        (by simpa using hc1))
  have hb : Summable b := by
    exact (summable_norm_iff.mpr hs).mul_right (x ^ c / c)
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hb
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  exact norm_perronTerm_le χ hx (lt_trans zero_lt_one hc1) n t

/-- On the absolute-convergence half-plane, the Perron summands sum pointwise
to the actual negative-logarithmic-derivative integrand. -/
theorem tsum_perronTerm_eq_logDerivPerronIntegrand
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x c : ℝ} (hc1 : 1 < c) (t : ℝ) :
    (∑' n : ℕ, perronTerm χ x c n t) =
      logDerivPerronIntegrand χ x c t := by
  rw [logDerivPerronIntegrand,
    ← LSeries_twistedMangoldtCoeff_eq_neg_logDeriv_LFunction χ (by simpa using hc1)]
  unfold perronTerm LSeries
  simp only [div_eq_mul_inv, mul_assoc]
  rw [tsum_mul_right]

/-- Exact countable-sum/finite-vertical-integral interchange for the actual
negative logarithmic derivative. -/
theorem rightLineIntegral_eq_tsum_integrals
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x c T : ℝ} (hx : 0 < x) (hc1 : 1 < c) :
    rightLineIntegral χ x c T =
      ∑' n : ℕ,
        ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
          ∫ t in (-T)..T, perronTerm χ x c n t := by
  let F : ℕ → C(ℝ, ℂ) := fun n =>
    ContinuousMap.mk (perronTerm χ x c n)
      (continuous_perronTerm χ hx (lt_trans zero_lt_one hc1) n)
  have hsum : Summable fun n : ℕ =>
      ‖(F n).restrict (⟨uIcc (-T) T, isCompact_uIcc⟩ : Compacts ℝ)‖ := by
    simpa only [F] using summable_restricted_perronTerm χ hx hc1 (T := T)
  rw [rightLineIntegral, tsum_mul_left]
  congr 1
  calc
    (∫ t in (-T)..T, logDerivPerronIntegrand χ x c t) =
        ∫ t in (-T)..T, ∑' n : ℕ, F n t := by
      apply intervalIntegral.integral_congr
      intro t ht
      change logDerivPerronIntegrand χ x c t =
        ∑' n : ℕ, perronTerm χ x c n t
      exact (tsum_perronTerm_eq_logDerivPerronIntegrand χ hc1 t).symm
    _ = ∑' n : ℕ, ∫ t in (-T)..T, F n t :=
      (intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hsum).symm
    _ = ∑' n : ℕ, ∫ t in (-T)..T, perronTerm χ x c n t := by
      rfl

/-- The actual Perron integral is the infinite sum of the literal
finite-height kernels.  The zero term vanishes and is stated separately so
there is no hidden division by zero. -/
theorem rightLineIntegral_eq_tsum_kernels
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x c T : ℝ} (hx : 0 < x) (hc1 : 1 < c) :
    rightLineIntegral χ x c T =
      ∑' n : ℕ, twistedMangoldtCoeff χ n * kernel (x / n) c T := by
  rw [rightLineIntegral_eq_tsum_integrals χ hx hc1]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [twistedMangoldtCoeff, perronTerm]
  · exact normalized_integral_perronTerm_eq_coeff_mul_kernel χ hx hn

/-- Literal omitted-coefficient remainder after cutting the absolutely
convergent Perron series at a finite set. -/
def coefficientTail {q : ℕ} (χ : DirichletCharacter ℂ q)
    (x c T : ℝ) (S : Finset ℕ) : ℂ :=
  ∑' n : {n // n ∉ S},
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ t in (-T)..T, perronTerm χ x c n t

/-- Exact finite-plus-tail decomposition of the actual Perron line. -/
theorem rightLineIntegral_eq_finset_add_tail
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x c T : ℝ} (hx : 0 < x) (hc1 : 1 < c) (S : Finset ℕ) :
    rightLineIntegral χ x c T =
      (∑ n ∈ S,
        ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
          ∫ t in (-T)..T, perronTerm χ x c n t) +
        coefficientTail χ x c T S := by
  rw [rightLineIntegral_eq_tsum_integrals χ hx hc1]
  let f : ℕ → ℂ := fun n =>
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ t in (-T)..T, perronTerm χ x c n t
  have hsummable : Summable f := by
    let F : ℕ → C(ℝ, ℂ) := fun n =>
      ContinuousMap.mk (perronTerm χ x c n)
        (continuous_perronTerm χ hx (lt_trans zero_lt_one hc1) n)
    have hsup : Summable fun n : ℕ =>
        ‖(F n).restrict (⟨uIcc (-T) T, isCompact_uIcc⟩ : Compacts ℝ)‖ := by
      simpa only [F] using summable_restricted_perronTerm χ hx hc1 (T := T)
    have hint : Summable fun n : ℕ => ∫ t in (-T)..T, F n t :=
      (intervalIntegral.hasSum_intervalIntegral_of_summable_norm hsup).summable
    exact (hint.mul_left (((2 * Real.pi : ℝ) : ℂ)⁻¹)).congr
      (fun n => by simp only [f, F, ContinuousMap.coe_mk])
  rw [← hsummable.sum_add_tsum_subtype_compl S]
  rfl

/-- Direct truncated Perron identity for the actual logarithmic derivative:
the main piece is the concrete kernel sum over `1 ≤ n ≤ N`, and the remainder
is the literal omitted-coefficient integral. -/
theorem rightLineIntegral_eq_Icc_kernel_sum_add_tail
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x c T : ℝ} (hx : 0 < x) (hc1 : 1 < c) (N : ℕ) :
    rightLineIntegral χ x c T =
      (∑ n ∈ Finset.Icc 1 N,
        twistedMangoldtCoeff χ n * kernel (x / n) c T) +
      coefficientTail χ x c T (Finset.Icc 1 N) := by
  rw [rightLineIntegral_eq_finset_add_tail χ hx hc1 (Finset.Icc 1 N)]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact normalized_integral_perronTerm_eq_coeff_mul_kernel χ hx
    (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)

/-- Explicit absolute bound for the omitted-coefficient remainder.  Nothing is
hidden in Big-O notation; the right side is the literal absolute Dirichlet
series tail on `Re s = c`. -/
theorem norm_coefficientTail_le
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    {x c T : ℝ} (hx : 0 < x) (hc1 : 1 < c) (hT : 0 ≤ T)
    (S : Finset ℕ) :
    ‖coefficientTail χ x c T S‖ ≤
      (T / Real.pi) * (x ^ c / c) *
        ∑' n : {n // n ∉ S},
          ‖LSeries.term (twistedMangoldtCoeff χ) (c : ℂ) n‖ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  let f : {n // n ∉ S} → ℂ := fun n =>
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ t in (-T)..T, perronTerm χ x c n t
  have htermSummable : Summable fun n : ℕ =>
      ‖LSeries.term (twistedMangoldtCoeff χ) (c : ℂ) n‖ := by
    apply summable_norm_iff.mpr
    simpa only [twistedMangoldtCoeff, Pi.mul_apply] using
      (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ
        (by simpa using hc1))
  have htailSummable : Summable fun n : {n // n ∉ S} =>
      ‖LSeries.term (twistedMangoldtCoeff χ) (c : ℂ) n‖ :=
    htermSummable.subtype _
  have hfbound (n : {n // n ∉ S}) :
      ‖f n‖ ≤ (T / Real.pi) * (x ^ c / c) *
        ‖LSeries.term (twistedMangoldtCoeff χ) (c : ℂ) n‖ := by
    dsimp only [f]
    rw [norm_mul]
    have hconst : ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ = (2 * Real.pi)⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (mul_pos (by norm_num) hpi)]
    rw [hconst]
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -T) (b := T)
      (fun t ht => norm_perronTerm_le χ hx (lt_trans zero_lt_one hc1) n t)
    have habs : |T - (-T)| = 2 * T := by
      rw [sub_neg_eq_add, ← two_mul, abs_of_nonneg (mul_nonneg (by norm_num) hT)]
    calc
      (2 * Real.pi)⁻¹ * ‖∫ t in (-T)..T, perronTerm χ x c n t‖
          ≤ (2 * Real.pi)⁻¹ *
              ((‖LSeries.term (twistedMangoldtCoeff χ) (c : ℂ) n‖ *
                (x ^ c / c)) * |T - (-T)|) :=
            mul_le_mul_of_nonneg_left hint
              (inv_nonneg.mpr (mul_nonneg (by norm_num) hpi.le))
      _ = (T / Real.pi) * (x ^ c / c) *
          ‖LSeries.term (twistedMangoldtCoeff χ) (c : ℂ) n‖ := by
            rw [habs]
            field_simp [ne_of_gt hpi]
  have hfsummable : Summable f := by
    exact Summable.of_norm_bounded
      ((htailSummable.mul_left ((T / Real.pi) * (x ^ c / c))))
      (fun n => hfbound n)
  rw [coefficientTail]
  change ‖∑' n, f n‖ ≤ _
  calc
    ‖∑' n, f n‖ ≤ ∑' n, ‖f n‖ :=
      norm_tsum_le_tsum_norm (hfsummable.norm)
    _ ≤ ∑' n : {n // n ∉ S}, (T / Real.pi) * (x ^ c / c) *
        ‖LSeries.term (twistedMangoldtCoeff χ) (c : ℂ) n‖ := by
          exact hfsummable.norm.tsum_le_tsum hfbound
            (htailSummable.mul_left ((T / Real.pi) * (x ^ c / c)))
    _ = (T / Real.pi) * (x ^ c / c) *
        ∑' n : {n // n ∉ S},
          ‖LSeries.term (twistedMangoldtCoeff χ) (c : ℂ) n‖ := by
          rw [tsum_mul_left]

/-- The absolute twisted term is bounded coefficientwise by the ordinary
von Mangoldt Dirichlet-series term. -/
theorem norm_twisted_LSeries_term_le_vonMangoldt_term
    {q : ℕ} (χ : DirichletCharacter ℂ q) {c : ℝ} (n : ℕ) :
    ‖LSeries.term (twistedMangoldtCoeff χ) (c : ℂ) n‖ ≤
      ‖LSeries.term (fun k : ℕ =>
        (ArithmeticFunction.vonMangoldt k : ℂ)) (c : ℂ) n‖ := by
  apply LSeries.norm_term_le (c : ℂ)
  simpa [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] using
      (norm_twistedMangoldtCoeff_le χ n)

/-- Character-uniform version of the explicit coefficient-tail bound.  Its
right side contains only the ordinary von Mangoldt Dirichlet series. -/
theorem norm_coefficientTail_le_vonMangoldt_series
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    {x c T : ℝ} (hx : 0 < x) (hc1 : 1 < c) (hT : 0 ≤ T)
    (S : Finset ℕ) :
    ‖coefficientTail χ x c T S‖ ≤
      (T / Real.pi) * (x ^ c / c) *
        ∑' n : {n // n ∉ S},
          ‖LSeries.term (fun k : ℕ =>
            (ArithmeticFunction.vonMangoldt k : ℂ)) (c : ℂ) n‖ := by
  have hχ := norm_coefficientTail_le χ hx hc1 hT S
  have htwistedBase : Summable fun n : ℕ =>
      ‖LSeries.term (twistedMangoldtCoeff χ) (c : ℂ) n‖ := by
    apply summable_norm_iff.mpr
    simpa only [twistedMangoldtCoeff, Pi.mul_apply] using
      (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ
        (by simpa using hc1))
  have htwisted : Summable fun n : {n // n ∉ S} =>
      ‖LSeries.term (twistedMangoldtCoeff χ) (c : ℂ) n‖ := by
    simpa only [Function.comp_apply] using
      htwistedBase.subtype {n : ℕ | n ∉ S}
  have hplainBase : Summable fun n : ℕ =>
      ‖LSeries.term (fun k : ℕ =>
        (ArithmeticFunction.vonMangoldt k : ℂ)) (c : ℂ) n‖ := by
    apply summable_norm_iff.mpr
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc1)
  have hplain : Summable fun n : {n // n ∉ S} =>
      ‖LSeries.term (fun k : ℕ =>
        (ArithmeticFunction.vonMangoldt k : ℂ)) (c : ℂ) n‖ := by
    simpa only [Function.comp_apply] using
      hplainBase.subtype {n : ℕ | n ∉ S}
  have hsum :
      (∑' n : {n // n ∉ S},
        ‖LSeries.term (twistedMangoldtCoeff χ) (c : ℂ) n‖) ≤
      ∑' n : {n // n ∉ S},
        ‖LSeries.term (fun k : ℕ =>
          (ArithmeticFunction.vonMangoldt k : ℂ)) (c : ℂ) n‖ :=
    htwisted.tsum_le_tsum
      (fun n => norm_twisted_LSeries_term_le_vonMangoldt_term χ n)
      hplain
  exact hχ.trans (mul_le_mul_of_nonneg_left hsum (by positivity))

end
end TruncatedTwistedPerron
