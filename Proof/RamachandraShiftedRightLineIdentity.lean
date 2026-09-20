import RamachandraPrimitiveShiftedContourReduction
import GammaMellinInversion

/-!
# The exact right-line identities in Ramachandra Lemma 3

This module verifies two algebraic/Mellin ingredients preceding the contour
shift:

* the coefficient `chi(n)d(n)` is exactly the Dirichlet-convolution square
  of the character coefficient sequence, hence its L-series is `L(s,chi)^2`
  in `Re s > 1`;
* each smoothed coefficient has the literal Gamma inverse-Mellin
  representation used on the starting line.

The remaining Lemma 3 work is therefore the complex contour displacement,
functional-equation substitution, and residue/tail control, not either of
these right-line identities.
-/

namespace RamachandraShiftedRightLineIdentity

open scoped BigOperators ArithmeticFunction.zeta LSeries.notation
open ArithmeticFunction Complex MeasureTheory
open CGLProofDAG
open BHPRamachandraMeanValueFromDyadicAFE

noncomputable section

/-- Exact arithmetic-function identity behind the coefficient
`chi(n)d(n)` of `L(s,chi)^2`. -/
theorem characterArithmeticFunction_sq_apply
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (n : ℕ) :
    ((toArithmeticFunction (chi ·)) ^ 2) n =
      ramachandraDivisorCoeff chi n := by
  rw [pow_two, ArithmeticFunction.mul_apply]
  unfold ramachandraDivisorCoeff orderedDivisorCount
  rw [pow_two, ArithmeticFunction.mul_apply]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hmem := Nat.mem_divisorsAntidiagonal.mp hx
  have hprod : x.1 * x.2 = n := hmem.1
  have hx1 : x.1 ≠ 0 := by
    intro h
    apply hmem.2
    simp [h] at hprod
    exact hprod.symm
  have hx2 : x.2 ≠ 0 := by
    intro h
    apply hmem.2
    simp [h] at hprod
    exact hprod.symm
  rw [← DirichletCharacter.apply_eq_toArithmeticFunction_apply chi hx1,
    ← DirichletCharacter.apply_eq_toArithmeticFunction_apply chi hx2]
  calc
    chi (x.1 : ZMod q) * chi (x.2 : ZMod q) =
        chi ((x.1 : ZMod q) * (x.2 : ZMod q)) :=
      (map_mul chi _ _).symm
    _ = chi (n : ZMod q) := by rw [← Nat.cast_mul, hprod]
    _ = chi (n : ZMod q) *
        (((ArithmeticFunction.zeta x.1 : ℕ) : ℂ) *
          ((ArithmeticFunction.zeta x.2 : ℕ) : ℂ)) := by
      simp [ArithmeticFunction.zeta_apply, hx1, hx2]

/-- In the absolute-convergence half-plane, the literal coefficient series
in Lemma 3 is exactly the square of the Dirichlet L-function. -/
theorem LSeries_ramachandraDivisorCoeff_eq_LFunction_sq
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (ramachandraDivisorCoeff chi) s =
      DirichletCharacter.LFunction chi s ^ 2 := by
  let f : ArithmeticFunction ℂ := toArithmeticFunction (chi ·)
  have hcoeff : (ramachandraDivisorCoeff chi) =
      (fun n ↦ (f * f) n) := by
    funext n
    simpa [pow_two] using (characterArithmeticFunction_sq_apply chi n).symm
  have hf : LSeriesSummable (fun n ↦ f n) s := by
    apply (LSeriesSummable_congr s (fun {n} hn ↦
      (DirichletCharacter.apply_eq_toArithmeticFunction_apply chi hn).symm)).mpr
    exact DirichletCharacter.LSeriesSummable_of_one_lt_re chi hs
  have hLf : LSeries (fun n ↦ f n) s =
      LSeries (fun n ↦ chi (n : ZMod q)) s :=
    LSeries_congr (fun {n} hn ↦
      (DirichletCharacter.apply_eq_toArithmeticFunction_apply chi hn).symm) s
  rw [hcoeff, ArithmeticFunction.LSeries_mul' hf hf, hLf,
    ← DirichletCharacter.LFunction_eq_LSeries chi hs]
  ring

/-- Coefficientwise inverse Mellin formula on every positive starting line.
This is the exact detector used before interchanging the sum and integral in
the first displayed equation of the proof of Lemma 3. -/
theorem smoothed_ramachandraTerm_eq_gamma_right_line
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {c X : ℝ} (hc : 0 < c) (hX : 0 < X)
    {n : ℕ} (hn : 0 < n) (s : ℂ) :
    LSeries.term (ramachandraDivisorCoeff chi) s n *
        (Real.exp (-((n : ℝ) / X)) : ℂ) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          LSeries.term (ramachandraDivisorCoeff chi) s n *
            (Complex.Gamma ((c : ℂ) + v * I) *
              ((X / n : ℝ) : ℂ) ^ ((c : ℂ) + v * I))) := by
  rw [MAPGammaMellinInversion.exp_neg_nat_div_eq_detector_right_line
    hc hX hn]
  rw [MeasureTheory.integral_const_mul]
  ring

/-- Moving the Mellin factor into the Dirichlet-series exponent is exact for
positive `n` and `X`. -/
theorem term_mul_ratio_cpow_eq_shiftedTerm_mul_scale
    (f : ℕ → ℂ) (s w : ℂ) {X : ℝ} (hX : 0 < X)
    {n : ℕ} (hn : 0 < n) :
    LSeries.term f s n * ((X / n : ℝ) : ℂ) ^ w =
      LSeries.term f (s + w) n * (X : ℂ) ^ w := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  have hratio : 0 ≤ X / (n : ℝ) :=
    (div_pos hX (by exact_mod_cast hn)).le
  have hfactor : (((X / n : ℝ) : ℂ) ^ w) * ((n : ℂ) ^ w) =
      (X : ℂ) ^ w := by
    calc
      (((X / n : ℝ) : ℂ) ^ w) * ((n : ℂ) ^ w) =
          ((((X / n : ℝ) : ℂ) * (n : ℂ)) ^ w) :=
        (Complex.mul_cpow_ofReal_nonneg hratio (Nat.cast_nonneg n) w).symm
      _ = (X : ℂ) ^ w := by
        congr 1
        push_cast
        field_simp
  rw [Complex.cpow_add _ _ hnC]
  have hns : (n : ℂ) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
  have hnw : (n : ℂ) ^ w ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
  field_simp [hns, hnw]
  calc
    f n * ((X / n : ℝ) : ℂ) ^ w * (n : ℂ) ^ w =
        f n * ((((X / n : ℝ) : ℂ) ^ w) * (n : ℂ) ^ w) := by ring
    _ = f n * (X : ℂ) ^ w := by rw [hfactor]

/-- Coefficientwise form matching the literal starting integrand
`L(s+w,chi)^2 Gamma(w) X^w` in Lemma 3. -/
theorem smoothed_ramachandraTerm_eq_shifted_gamma_right_line
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {c X : ℝ} (hc : 0 < c) (hX : 0 < X)
    {n : ℕ} (hn : 0 < n) (s : ℂ) :
    LSeries.term (ramachandraDivisorCoeff chi) s n *
        (Real.exp (-((n : ℝ) / X)) : ℂ) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          Complex.Gamma ((c : ℂ) + v * I) *
            LSeries.term (ramachandraDivisorCoeff chi)
              (s + ((c : ℂ) + v * I)) n *
            (X : ℂ) ^ ((c : ℂ) + v * I)) := by
  rw [smoothed_ramachandraTerm_eq_gamma_right_line chi hc hX hn s]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with v
  have hterm := term_mul_ratio_cpow_eq_shiftedTerm_mul_scale
    (ramachandraDivisorCoeff chi) s ((c : ℂ) + v * I) hX hn
  calc
    LSeries.term (ramachandraDivisorCoeff chi) s n *
        (Complex.Gamma ((c : ℂ) + v * I) *
          ((X / n : ℝ) : ℂ) ^ ((c : ℂ) + v * I)) =
      Complex.Gamma ((c : ℂ) + v * I) *
        (LSeries.term (ramachandraDivisorCoeff chi) s n *
          ((X / n : ℝ) : ℂ) ^ ((c : ℂ) + v * I)) := by ring
    _ = Complex.Gamma ((c : ℂ) + v * I) *
        (LSeries.term (ramachandraDivisorCoeff chi)
          (s + ((c : ℂ) + v * I)) n *
            (X : ℂ) ^ ((c : ℂ) + v * I)) := by rw [hterm]
    _ = _ := by ring

/-! ## Sum--integral weld on the starting line -/

/-- The literal coefficient integrand on the initial positive line. -/
def ramachanandraRightLineTerm {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (X : ℝ) (s : ℂ)
    (c v : ℝ) (n : ℕ) : ℂ :=
  Complex.Gamma ((c : ℂ) + v * I) *
    LSeries.term (ramachandraDivisorCoeff chi)
      (s + ((c : ℂ) + v * I)) n *
    (X : ℂ) ^ ((c : ℂ) + v * I)

/-- Once absolute Fubini is supplied, the coefficientwise inverse-Mellin
formula sums to the exact starting-line integral with `L(s+w,chi)^2`.
The hypotheses mention only integrability of the explicit coefficient
integrands; they contain no moment estimate. -/
theorem smoothedSeries_eq_LFunctionSq_gamma_rightLine
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {c X : ℝ} (hc : 0 < c) (hX : 0 < X)
    (s : ℂ) (hhalfplane : 1 < s.re + c)
    (hInt : ∀ n : ℕ,
      Integrable (fun v : ℝ ↦
        ramachanandraRightLineTerm chi X s c v n))
    (hSum : Summable (fun n : ℕ ↦
      ∫ v : ℝ, ‖ramachanandraRightLineTerm chi X s c v n‖)) :
    (∑' n : ℕ,
      LSeries.term (ramachandraDivisorCoeff chi) s n *
        (Real.exp (-((n : ℝ) / X)) : ℂ)) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          DirichletCharacter.LFunction chi
              (s + ((c : ℂ) + v * I)) ^ 2 *
            Complex.Gamma ((c : ℂ) + v * I) *
            (X : ℂ) ^ ((c : ℂ) + v * I)) := by
  let A : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hcoeff (n : ℕ) :
      LSeries.term (ramachandraDivisorCoeff chi) s n *
          (Real.exp (-((n : ℝ) / X)) : ℂ) =
        A * ∫ v : ℝ, ramachanandraRightLineTerm chi X s c v n := by
    by_cases hn : n = 0
    · subst n
      simp [ramachanandraRightLineTerm, A, LSeries.term_zero]
    · simpa [ramachanandraRightLineTerm, A] using
        (smoothed_ramachandraTerm_eq_shifted_gamma_right_line
          chi hc hX (Nat.pos_of_ne_zero hn) s)
  calc
    (∑' n : ℕ,
        LSeries.term (ramachandraDivisorCoeff chi) s n *
          (Real.exp (-((n : ℝ) / X)) : ℂ)) =
        ∑' n : ℕ, A *
          ∫ v : ℝ, ramachanandraRightLineTerm chi X s c v n := by
      apply tsum_congr
      intro n
      exact hcoeff n
    _ = A * ∑' n : ℕ,
          ∫ v : ℝ, ramachanandraRightLineTerm chi X s c v n :=
      tsum_mul_left
    _ = A * ∫ v : ℝ,
          ∑' n : ℕ, ramachanandraRightLineTerm chi X s c v n := by
      rw [MeasureTheory.integral_tsum_of_summable_integral_norm hInt hSum]
    _ = A * ∫ v : ℝ,
          DirichletCharacter.LFunction chi
              (s + ((c : ℂ) + v * I)) ^ 2 *
            Complex.Gamma ((c : ℂ) + v * I) *
            (X : ℂ) ^ ((c : ℂ) + v * I) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with v
      have hsline : 1 < (s + ((c : ℂ) + v * I)).re := by
        simpa using hhalfplane
      have hL := LSeries_ramachandraDivisorCoeff_eq_LFunction_sq chi hsline
      unfold ramachanandraRightLineTerm
      calc
        (∑' n : ℕ,
            Complex.Gamma ((c : ℂ) + v * I) *
              LSeries.term (ramachandraDivisorCoeff chi)
                (s + ((c : ℂ) + v * I)) n *
              (X : ℂ) ^ ((c : ℂ) + v * I)) =
          ∑' n : ℕ,
            Complex.Gamma ((c : ℂ) + v * I) *
              (LSeries.term (ramachandraDivisorCoeff chi)
                (s + ((c : ℂ) + v * I)) n *
                (X : ℂ) ^ ((c : ℂ) + v * I)) := by
            apply tsum_congr
            intro n
            ring
        _ = Complex.Gamma ((c : ℂ) + v * I) *
            ∑' n : ℕ,
              LSeries.term (ramachandraDivisorCoeff chi)
                (s + ((c : ℂ) + v * I)) n *
                (X : ℂ) ^ ((c : ℂ) + v * I) := tsum_mul_left
        _ = Complex.Gamma ((c : ℂ) + v * I) *
            (LSeries (ramachandraDivisorCoeff chi)
                (s + ((c : ℂ) + v * I)) *
              (X : ℂ) ^ ((c : ℂ) + v * I)) := by
            rw [tsum_mul_right]
            rfl
        _ = _ := by rw [hL]; ring
    _ = _ := by rfl

/-! ## Premise-free absolute Fubini on the starting line -/

theorem LSeriesSummable_ramachandraDivisorCoeff
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {z : ℂ} (hz : 1 < z.re) :
    LSeriesSummable (ramachandraDivisorCoeff chi) z := by
  let f : ArithmeticFunction ℂ := toArithmeticFunction (chi ·)
  have hcoeff : (ramachandraDivisorCoeff chi) =
      (fun n ↦ (f * f) n) := by
    funext n
    simpa [pow_two] using
      (characterArithmeticFunction_sq_apply chi n).symm
  have hf : LSeriesSummable (fun n ↦ f n) z := by
    apply (LSeriesSummable_congr z (fun {n} hn ↦
      (DirichletCharacter.apply_eq_toArithmeticFunction_apply chi hn).symm)).mpr
    exact DirichletCharacter.LSeriesSummable_of_one_lt_re chi hz
  rw [hcoeff]
  exact ArithmeticFunction.LSeriesSummable_mul hf hf

theorem norm_term_mul_ratio_rpow
    (f : ℕ → ℂ) (s : ℂ) {c X : ℝ} (hX : 0 < X) (n : ℕ) :
    ‖LSeries.term f s n‖ * (X / n) ^ c =
      X ^ c * ‖LSeries.term f (s + c) n‖ := by
  by_cases hn0 : n = 0
  · subst n
    simp [LSeries.term_zero]
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  simp only [hn0, if_false, Complex.add_re, Complex.ofReal_re]
  rw [Real.div_rpow hX.le (Nat.cast_nonneg n),
    Real.rpow_add (by exact_mod_cast hn)]
  have hns : (n : ℝ) ^ s.re ≠ 0 :=
    (Real.rpow_pos_of_pos (by exact_mod_cast hn) _).ne'
  have hnc : (n : ℝ) ^ c ≠ 0 :=
    (Real.rpow_pos_of_pos (by exact_mod_cast hn) _).ne'
  field_simp [hns, hnc]

theorem integrable_ramachanandraRightLineTerm
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {c X : ℝ} (hc : 0 < c) (hX : 0 < X) (s : ℂ) (n : ℕ) :
    Integrable (fun v : ℝ ↦
      ramachanandraRightLineTerm chi X s c v n) := by
  by_cases hn0 : n = 0
  · subst n
    simp [ramachanandraRightLineTerm, LSeries.term_zero]
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  let r : ℝ := X / n
  have hr : 0 < r := div_pos hX (by exact_mod_cast hn)
  let a : ℂ := LSeries.term (ramachandraDivisorCoeff chi) s n
  let phase : ℝ → ℂ :=
    fun v ↦ a * (r : ℂ) ^ ((c : ℂ) + v * I)
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  letI : NeZero (r : ℂ) := ⟨hrC⟩
  have hphase : Continuous phase := by
    dsimp [phase]
    exact continuous_const.mul
      (continuous_const_cpow (r : ℂ) |>.comp (by fun_prop))
  have hphaseBound : ∀ v : ℝ,
      ‖phase v‖ ≤ ‖a‖ * (r ^ c) := by
    intro v
    rw [show ‖phase v‖ = ‖a‖ *
        ‖(r : ℂ) ^ ((c : ℂ) + v * I)‖ by simp [phase]]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
    simp
  have hGamma := MAPGammaMellinInversion.verticalIntegrable_Gamma hc
  have hprod : Integrable (fun v : ℝ ↦
      phase v * Complex.Gamma ((c : ℂ) + v * I)) :=
    hGamma.bdd_mul hphase.aestronglyMeasurable
      (Filter.Eventually.of_forall hphaseBound)
  apply hprod.congr
  filter_upwards [] with v
  unfold ramachanandraRightLineTerm
  have hterm := term_mul_ratio_cpow_eq_shiftedTerm_mul_scale
    (ramachandraDivisorCoeff chi) s ((c : ℂ) + v * I) hX hn
  dsimp [phase, r, a]
  rw [hterm]
  ring

theorem integral_norm_ramachanandraRightLineTerm
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {c X : ℝ} (hX : 0 < X) (s : ℂ) (n : ℕ) :
    (∫ v : ℝ, ‖ramachanandraRightLineTerm chi X s c v n‖) =
      (‖LSeries.term (ramachandraDivisorCoeff chi) s n‖ *
        (X / n) ^ c) *
        ∫ v : ℝ, ‖Complex.Gamma ((c : ℂ) + v * I)‖ := by
  by_cases hn0 : n = 0
  · subst n
    simp [ramachanandraRightLineTerm, LSeries.term_zero]
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  let r : ℝ := X / n
  have hr : 0 < r := div_pos hX (by exact_mod_cast hn)
  let a : ℂ := LSeries.term (ramachandraDivisorCoeff chi) s n
  have hpoint (v : ℝ) :
      ‖ramachanandraRightLineTerm chi X s c v n‖ =
        (‖a‖ * r ^ c) *
          ‖Complex.Gamma ((c : ℂ) + v * I)‖ := by
    unfold ramachanandraRightLineTerm
    have hterm := term_mul_ratio_cpow_eq_shiftedTerm_mul_scale
      (ramachandraDivisorCoeff chi) s ((c : ℂ) + v * I) hX hn
    have heq : Complex.Gamma ((c : ℂ) + v * I) *
          LSeries.term (ramachandraDivisorCoeff chi)
            (s + ((c : ℂ) + v * I)) n *
          (X : ℂ) ^ ((c : ℂ) + v * I) =
        Complex.Gamma ((c : ℂ) + v * I) *
          (LSeries.term (ramachandraDivisorCoeff chi) s n *
            ((X / n : ℝ) : ℂ) ^ ((c : ℂ) + v * I)) := by
      rw [hterm]
      ring
    rw [heq, norm_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hr]
    simp [a, r]
    ring
  calc
    (∫ v : ℝ, ‖ramachanandraRightLineTerm chi X s c v n‖) =
        ∫ v : ℝ, (‖a‖ * r ^ c) *
          ‖Complex.Gamma ((c : ℂ) + v * I)‖ := by
      apply integral_congr_ae
      filter_upwards [] with v
      exact hpoint v
    _ = (‖a‖ * r ^ c) * ∫ v : ℝ,
        ‖Complex.Gamma ((c : ℂ) + v * I)‖ := by
      rw [MeasureTheory.integral_const_mul]
    _ = _ := by rfl

theorem summable_integral_norm_ramachanandraRightLineTerm
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {c X : ℝ} (_hc : 0 < c) (hX : 0 < X) (s : ℂ)
    (hhalfplane : 1 < s.re + c) :
    Summable (fun n : ℕ ↦
      ∫ v : ℝ, ‖ramachanandraRightLineTerm chi X s c v n‖) := by
  let G : ℝ := ∫ v : ℝ,
    ‖Complex.Gamma ((c : ℂ) + v * I)‖
  have hz : 1 < (s + (c : ℂ)).re := by simpa using hhalfplane
  have hLS := LSeriesSummable_ramachandraDivisorCoeff chi hz
  have hnorm : Summable (fun n ↦
      ‖LSeries.term (ramachandraDivisorCoeff chi) (s + c) n‖) :=
    summable_norm_iff.mpr hLS
  have hscaled : Summable (fun n ↦
      (X ^ c) *
        ‖LSeries.term (ramachandraDivisorCoeff chi) (s + c) n‖) :=
    hnorm.mul_left (X ^ c)
  have hscaled' : Summable (fun n ↦
      ‖LSeries.term (ramachandraDivisorCoeff chi) s n‖ *
        (X / n) ^ c) := by
    apply hscaled.congr
    intro n
    exact (norm_term_mul_ratio_rpow _ s hX n).symm
  have hfinal := hscaled'.mul_left G
  apply hfinal.congr
  intro n
  rw [integral_norm_ramachanandraRightLineTerm chi hX s n]
  dsimp [G]
  ring

/-- Fully premise-free starting-line identity.  The next unproved analytic
operation is now exactly the contour displacement, not Mellin inversion or
Fubini. -/
theorem smoothedSeries_eq_LFunctionSq_gamma_rightLine_unconditional
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {c X : ℝ} (hc : 0 < c) (hX : 0 < X)
    (s : ℂ) (hhalfplane : 1 < s.re + c) :
    (∑' n : ℕ,
      LSeries.term (ramachandraDivisorCoeff chi) s n *
        (Real.exp (-((n : ℝ) / X)) : ℂ)) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          DirichletCharacter.LFunction chi
              (s + ((c : ℂ) + v * I)) ^ 2 *
            Complex.Gamma ((c : ℂ) + v * I) *
            (X : ℂ) ^ ((c : ℂ) + v * I)) := by
  exact smoothedSeries_eq_LFunctionSq_gamma_rightLine chi hc hX s hhalfplane
    (integrable_ramachanandraRightLineTerm chi hc hX s)
    (summable_integral_norm_ramachanandraRightLineTerm
      chi hc hX s hhalfplane)

end
end RamachandraShiftedRightLineIdentity

#print axioms RamachandraShiftedRightLineIdentity.characterArithmeticFunction_sq_apply
#print axioms RamachandraShiftedRightLineIdentity.LSeries_ramachandraDivisorCoeff_eq_LFunction_sq
#print axioms RamachandraShiftedRightLineIdentity.smoothed_ramachandraTerm_eq_gamma_right_line
#print axioms RamachandraShiftedRightLineIdentity.term_mul_ratio_cpow_eq_shiftedTerm_mul_scale
#print axioms RamachandraShiftedRightLineIdentity.smoothed_ramachandraTerm_eq_shifted_gamma_right_line
#print axioms RamachandraShiftedRightLineIdentity.smoothedSeries_eq_LFunctionSq_gamma_rightLine
#print axioms RamachandraShiftedRightLineIdentity.integrable_ramachanandraRightLineTerm
#print axioms RamachandraShiftedRightLineIdentity.summable_integral_norm_ramachanandraRightLineTerm
#print axioms RamachandraShiftedRightLineIdentity.smoothedSeries_eq_LFunctionSq_gamma_rightLine_unconditional
