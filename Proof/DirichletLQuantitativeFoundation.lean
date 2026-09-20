import MellinDetectorLeaf
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Quantitative Dirichlet-L foundations for Appendices A.4 and A.5

This module develops explicit right-boundary and Jensen-center estimates and
starts the functional-equation boundary estimate needed for polynomial growth
on a fixed strip.
-/

open Complex LSeries
open scoped BigOperators

namespace MAPDirichletLQuantitative

noncomputable section

private def gammaImagPoint (t : ℝ) : ℂ := t * Complex.I
private def gammaOnePoint (t : ℝ) : ℂ := 1 + t * Complex.I
private def gammaTwoPoint (t : ℝ) : ℂ := 2 + t * Complex.I

private lemma gammaOnePoint_conj (t : ℝ) :
    (starRingEnd ℂ) (gammaOnePoint t) = gammaOnePoint (-t) := by
  apply Complex.ext <;> simp [gammaOnePoint]

private lemma one_sub_gammaImagPoint (t : ℝ) :
    1 - gammaImagPoint t = gammaOnePoint (-t) := by
  apply Complex.ext <;> simp [gammaImagPoint, gammaOnePoint]

private lemma sin_pi_mul_gammaImagPoint (t : ℝ) :
    Complex.sin ((Real.pi : ℂ) * gammaImagPoint t) =
      (Real.sinh (Real.pi * t) : ℂ) * Complex.I := by
  rw [show (Real.pi : ℂ) * gammaImagPoint t =
      (Real.pi * t : ℂ) * Complex.I by
    apply Complex.ext <;> simp [gammaImagPoint] <;> ring]
  rw [Complex.sin_mul_I]
  simp

private lemma gammaOnePoint_eq (t : ℝ) (ht : t ≠ 0) :
    Complex.Gamma (gammaOnePoint t) =
      gammaImagPoint t * Complex.Gamma (gammaImagPoint t) := by
  have hne : gammaImagPoint t ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [gammaImagPoint] at him
    exact ht him
  simpa [gammaOnePoint, gammaImagPoint, add_comm] using
    Complex.Gamma_add_one (gammaImagPoint t) hne

/-- Exact square norm on the line `Re(s)=1`. -/
theorem norm_Gamma_one_add_mul_I_sq (t : ℝ) (ht : t ≠ 0) :
    ‖Complex.Gamma (gammaOnePoint t)‖ ^ 2 =
      Real.pi * |t| / |Real.sinh (Real.pi * t)| := by
  have href := Complex.Gamma_mul_Gamma_one_sub (gammaImagPoint t)
  rw [one_sub_gammaImagPoint, sin_pi_mul_gammaImagPoint] at href
  have hnorm := congrArg norm href
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one] at hnorm
  have hconj :
      ‖Complex.Gamma (gammaOnePoint (-t))‖ =
        ‖Complex.Gamma (gammaOnePoint t)‖ := by
    rw [← gammaOnePoint_conj, Complex.Gamma_conj, RCLike.norm_conj]
  rw [hconj] at hnorm
  have hrec := congrArg norm (gammaOnePoint_eq t ht)
  rw [norm_mul] at hrec
  have himag : ‖gammaImagPoint t‖ = |t| := by
    simp [gammaImagPoint, Real.norm_eq_abs]
  rw [himag] at hrec
  calc
    ‖Complex.Gamma (gammaOnePoint t)‖ ^ 2 =
        |t| * (‖Complex.Gamma (gammaImagPoint t)‖ *
          ‖Complex.Gamma (gammaOnePoint t)‖) := by
      rw [hrec]
      ring
    _ = |t| * (Real.pi / |Real.sinh (Real.pi * t)|) := by rw [hnorm]
    _ = Real.pi * |t| / |Real.sinh (Real.pi * t)| := by ring

private lemma abs_sinh_pi_mul (t : ℝ) :
    |Real.sinh (Real.pi * t)| = Real.sinh (Real.pi * |t|) := by
  rw [Real.abs_sinh, abs_mul, abs_of_pos Real.pi_pos]

/-- Exponential upper bound on `Gamma(1+it)` with the sharp cancellation
rate `pi/2` needed by the Dirichlet functional equation. -/
theorem norm_Gamma_one_add_mul_I_le (t : ℝ) :
    ‖Complex.Gamma (gammaOnePoint t)‖ ≤
      9 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|) := by
  by_cases ht : t = 0
  · subst t
    simp [gammaOnePoint]
  · let u : ℝ := |t|
    have hu : 0 < u := by simpa [u] using abs_pos.mpr ht
    have hsq := norm_Gamma_one_add_mul_I_sq t ht
    rw [abs_sinh_pi_mul] at hsq
    change ‖Complex.Gamma (gammaOnePoint t)‖ ≤
      9 * (1 + u) * Real.exp (-(Real.pi / 2) * u)
    by_cases huone : u ≤ 1
    · have hsinh_lower : Real.pi * u ≤ Real.sinh (Real.pi * u) :=
        Real.self_le_sinh_iff.mpr (mul_nonneg Real.pi_pos.le hu.le)
      have hsinh_pos : 0 < Real.sinh (Real.pi * u) := by positivity
      have hsq_one : ‖Complex.Gamma (gammaOnePoint t)‖ ^ 2 ≤ 1 := by
        rw [hsq]
        exact (div_le_one hsinh_pos).2 hsinh_lower
      have hnorm_one : ‖Complex.Gamma (gammaOnePoint t)‖ ≤ 1 := by
        nlinarith [norm_nonneg (Complex.Gamma (gammaOnePoint t))]
      have hpiu : Real.pi / 2 * u ≤ 2 := by
        nlinarith [Real.pi_le_four]
      have hexp2 : Real.exp 2 ≤ 9 := by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
        nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
      have hone : 1 ≤ Real.exp (2 - Real.pi / 2 * u) :=
        Real.one_le_exp (by linarith)
      have hfactor :
          1 ≤ 9 * (1 + u) * Real.exp (-(Real.pi / 2) * u) := by
        calc
          1 ≤ Real.exp (2 - Real.pi / 2 * u) := hone
          _ = Real.exp 2 * Real.exp (-(Real.pi / 2) * u) := by
            rw [show 2 - Real.pi / 2 * u =
              2 + (-(Real.pi / 2) * u) by ring, Real.exp_add]
          _ ≤ 9 * (1 + u) * Real.exp (-(Real.pi / 2) * u) := by
            have he : 0 ≤ Real.exp (-(Real.pi / 2) * u) := (Real.exp_pos _).le
            have hbase : Real.exp 2 ≤ 9 * (1 + u) := by nlinarith
            exact mul_le_mul_of_nonneg_right hbase he
      exact hnorm_one.trans hfactor
    · have huone' : 1 < u := lt_of_not_ge huone
      let x : ℝ := Real.pi * u
      have hx : 0 < x := mul_pos Real.pi_pos hu
      have hx4 : 4 ≤ Real.exp x := by
        calc
          4 ≤ x + 1 := by dsimp [x]; nlinarith [Real.pi_gt_three]
          _ ≤ Real.exp x := Real.add_one_le_exp x
      have hneg_le_one : Real.exp (-x) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith)
      have hsinh_lower : Real.exp x / 4 ≤ Real.sinh x := by
        rw [Real.sinh_eq]
        nlinarith
      have hsinh_pos : 0 < Real.sinh x := by positivity
      have hexp_pos : 0 < Real.exp x := Real.exp_pos x
      have hsq_exp :
          ‖Complex.Gamma (gammaOnePoint t)‖ ^ 2 ≤
            4 * Real.pi * u * Real.exp (-x) := by
        rw [hsq]
        change Real.pi * u / Real.sinh x ≤ _
        have hdiv : Real.pi * u / Real.sinh x ≤
            Real.pi * u / (Real.exp x / 4) := by
          exact div_le_div_of_nonneg_left (mul_nonneg Real.pi_pos.le hu.le)
            (by positivity) hsinh_lower
        calc
          Real.pi * u / Real.sinh x ≤
              Real.pi * u / (Real.exp x / 4) := hdiv
          _ = 4 * Real.pi * u * Real.exp (-x) := by
            rw [Real.exp_neg]
            field_simp
      have hsq_final :
          ‖Complex.Gamma (gammaOnePoint t)‖ ^ 2 ≤
            (4 * (1 + u) * Real.exp (-(Real.pi / 2) * u)) ^ 2 := by
        calc
          ‖Complex.Gamma (gammaOnePoint t)‖ ^ 2 ≤
              4 * Real.pi * u * Real.exp (-x) := hsq_exp
          _ ≤ 16 * (1 + u) ^ 2 * Real.exp (-x) := by
            have : 4 * Real.pi * u ≤ 16 * (1 + u) ^ 2 := by
              nlinarith [Real.pi_le_four]
            gcongr
          _ = (4 * (1 + u) * Real.exp (-(Real.pi / 2) * u)) ^ 2 := by
            dsimp [x]
            rw [show -(Real.pi * u) =
              (-(Real.pi / 2) * u) + (-(Real.pi / 2) * u) by ring,
              Real.exp_add]
            ring
      have hfour_nonneg :
          0 ≤ 4 * (1 + u) * Real.exp (-(Real.pi / 2) * u) := by positivity
      have hfour :
          ‖Complex.Gamma (gammaOnePoint t)‖ ≤
            4 * (1 + u) * Real.exp (-(Real.pi / 2) * u) :=
        (sq_le_sq₀ (norm_nonneg _) hfour_nonneg).mp hsq_final
      exact hfour.trans (by
        have : 0 ≤ (1 + u) * Real.exp (-(Real.pi / 2) * u) := by positivity
        nlinarith)


private lemma gammaTwoPoint_eq (t : ℝ) :
    Complex.Gamma (gammaTwoPoint t) =
      gammaOnePoint t * Complex.Gamma (gammaOnePoint t) := by
  have hne : gammaOnePoint t ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [gammaOnePoint] at hre
  convert Complex.Gamma_add_one (gammaOnePoint t) hne using 1 <;>
    simp [gammaTwoPoint, gammaOnePoint] <;> ring

private lemma norm_gammaOnePoint_le_one_add_abs (t : ℝ) :
    ‖gammaOnePoint t‖ ≤ 1 + |t| := by
  calc
    ‖gammaOnePoint t‖ ≤ |(gammaOnePoint t).re| + |(gammaOnePoint t).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = 1 + |t| := by simp [gammaOnePoint]

/-- Sharp-enough exponential bound on `Gamma(2+it)`. -/
theorem norm_Gamma_two_add_mul_I_le (t : ℝ) :
    ‖Complex.Gamma (gammaTwoPoint t)‖ ≤
      9 * (1 + |t|) ^ 2 * Real.exp (-(Real.pi / 2) * |t|) := by
  rw [gammaTwoPoint_eq, norm_mul]
  calc
    ‖gammaOnePoint t‖ * ‖Complex.Gamma (gammaOnePoint t)‖ ≤
        (1 + |t|) *
          (9 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) := by
      exact mul_le_mul (norm_gammaOnePoint_le_one_add_abs t)
        (norm_Gamma_one_add_mul_I_le t) (norm_nonneg _) (by positivity)
    _ = 9 * (1 + |t|) ^ 2 * Real.exp (-(Real.pi / 2) * |t|) := by ring

/-- A bounded Dirichlet series on `Re(s)=2`, with the constant made linear
in the coefficient bound. -/
theorem norm_LSeries_two_add_mul_I_le
    (f : ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ n ≠ 0, ‖f n‖ ≤ B) (y : ℝ) :
    ‖LSeries f (2 + Complex.I * y)‖ ≤ B * (Real.pi ^ 2 / 6) := by
  have hs : 1 < (2 + Complex.I * y : ℂ).re := by simp
  have hsum : Summable (LSeries.term f (2 + Complex.I * y)) :=
    LSeriesSummable_of_bounded_of_one_lt_re hf hs
  have htarget : Summable (fun n : ℕ => B * ((1 : ℝ) / (n : ℝ) ^ 2)) :=
    hasSum_zeta_two.summable.mul_left B
  unfold LSeries
  calc
    ‖∑' n : ℕ, LSeries.term f (2 + Complex.I * y) n‖ ≤
        ∑' n : ℕ, ‖LSeries.term f (2 + Complex.I * y) n‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ, B * ((1 : ℝ) / (n : ℝ) ^ 2) := by
      apply Summable.tsum_le_tsum _ hsum.norm htarget
      intro n
      rw [LSeries.norm_term_eq]
      rw [show (2 + Complex.I * y : ℂ).re = 2 by simp]
      split_ifs with hn
      · simp [hn, hB]
      · have hden : 0 ≤ (n : ℝ) ^ (2 : ℝ) := by positivity
        calc
          ‖f n‖ / (n : ℝ) ^ (2 : ℝ) ≤ B / (n : ℝ) ^ (2 : ℝ) :=
            div_le_div_of_nonneg_right (hf n hn) hden
          _ = B * ((1 : ℝ) / (n : ℝ) ^ 2) := by
            norm_num [div_eq_mul_inv]
    _ = B * (Real.pi ^ 2 / 6) := by
      rw [tsum_mul_left, hasSum_zeta_two.tsum_eq]

variable {N : ℕ} [NeZero N]

/-- The unnormalized finite Fourier transform of a function bounded by
one has norm at most the cardinality of `ZMod N`. -/
theorem norm_dft_le_level
    (Φ : ZMod N → ℂ) (hΦ : ∀ a, ‖Φ a‖ ≤ 1) (a : ZMod N) :
    ‖ZMod.dft Φ a‖ ≤ N := by
  rw [ZMod.dft_apply]
  calc
    ‖∑ j : ZMod N, ZMod.stdAddChar (-(j * a)) • Φ j‖ ≤
        ∑ j : ZMod N, ‖ZMod.stdAddChar (-(j * a)) • Φ j‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : ZMod N, (1 : ℝ) := by
      gcongr with j
      rw [norm_smul, AddChar.norm_apply, one_mul]
      exact hΦ j
    _ = N := by simp [ZMod.card]

/-- The unnormalized Fourier transform of a Dirichlet character has norm at
most its level. -/
theorem norm_dft_dirichletCharacter_le
    (χ : DirichletCharacter ℂ N) (a : ZMod N) :
    ‖ZMod.dft (fun x : ZMod N => χ x) a‖ ≤ N :=
  norm_dft_le_level _ χ.norm_le_one a

/-- A Fourier-transformed bounded periodic function has an `N*zeta(2)`
right-boundary estimate. -/
theorem norm_dft_LFunction_two_add_mul_I_le_of_norm_le_one
    (Φ : ZMod N → ℂ) (hΦ : ∀ a, ‖Φ a‖ ≤ 1) (y : ℝ) :
    ‖ZMod.LFunction (ZMod.dft Φ) (2 + Complex.I * y)‖ ≤
      (N : ℝ) * (Real.pi ^ 2 / 6) := by
  have hs : 1 < (2 + Complex.I * y : ℂ).re := by simp
  rw [ZMod.LFunction_eq_LSeries _ hs]
  apply norm_LSeries_two_add_mul_I_le _ N (Nat.cast_nonneg N)
  intro n hn
  exact norm_dft_le_level Φ hΦ n

/-- Consequently the Fourier-transformed character L-function is bounded on
the right boundary by `N*zeta(2)`. -/
theorem norm_dft_LFunction_two_add_mul_I_le
    (χ : DirichletCharacter ℂ N) (y : ℝ) :
    ‖ZMod.LFunction (ZMod.dft (fun x : ZMod N => χ x))
        (2 + Complex.I * y)‖ ≤ (N : ℝ) * (Real.pi ^ 2 / 6) :=
  norm_dft_LFunction_two_add_mul_I_le_of_norm_le_one _ χ.norm_le_one y

/-- Uniform right-boundary bound for an ordinary Dirichlet L-function. -/
theorem norm_LFunction_two_add_mul_I_le_zeta_two
    (χ : DirichletCharacter ℂ N) (y : ℝ) :
    ‖DirichletCharacter.LFunction χ (2 + Complex.I * y)‖ ≤
      Real.pi ^ 2 / 6 := by
  have hs : 1 < (2 + Complex.I * y : ℂ).re := by simp
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  simpa using (norm_LSeries_two_add_mul_I_le
    (fun n : ℕ => χ n) 1 zero_le_one
    (fun n _ => χ.norm_le_one n) y)

/-- A completely explicit lower bound at the Jensen center `2+it`.  This
uses the exact Dirichlet-series inverse, not compactness or nonvanishing. -/
theorem one_third_le_norm_LFunction_two_add_mul_I
    (χ : DirichletCharacter ℂ N) (y : ℝ) :
    (1 / 3 : ℝ) ≤ ‖DirichletCharacter.LFunction χ (2 + Complex.I * y)‖ := by
  have hs : 1 < (2 + Complex.I * y : ℂ).re := by simp
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  let g : ℕ → ℂ := (fun n : ℕ => χ n) *
    (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ))
  have hginv : LSeries (fun n : ℕ => χ n) (2 + Complex.I * y) *
      LSeries g (2 + Complex.I * y) = 1 := by
    simpa [g] using DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hgcoeff : ∀ n ≠ 0, ‖g n‖ ≤ 1 := by
    intro n hn
    simp only [g, Pi.mul_apply, norm_mul, norm_intCast]
    have hχ := χ.norm_le_one n
    have hμ := ArithmeticFunction.abs_moebius_le_one (n := n)
    have hμR : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by exact_mod_cast hμ
    exact mul_le_one₀ hχ (abs_nonneg _) hμR
  have hg : ‖LSeries g (2 + Complex.I * y)‖ ≤ 3 := by
    have hzeta := norm_LSeries_two_add_mul_I_le g 1 zero_le_one hgcoeff y
    have hpi : Real.pi ^ 2 / 6 < 3 := by
      nlinarith [Real.pi_pos.le, Real.pi_lt_four]
    have hpi' : 1 * (Real.pi ^ 2 / 6) ≤ 3 := by simpa using hpi.le
    exact hzeta.trans hpi'
  have hone : 1 ≤ 3 * ‖LSeries (fun n : ℕ => χ n) (2 + Complex.I * y)‖ := by
    calc
      1 = ‖LSeries (fun n : ℕ => χ n) (2 + Complex.I * y) *
          LSeries g (2 + Complex.I * y)‖ := by rw [hginv, norm_one]
      _ = ‖LSeries g (2 + Complex.I * y)‖ *
          ‖LSeries (fun n : ℕ => χ n) (2 + Complex.I * y)‖ := by
        rw [norm_mul, mul_comm]
      _ ≤ 3 * ‖LSeries (fun n : ℕ => χ n) (2 + Complex.I * y)‖ := by
        gcongr
  linarith


private def functionalEquationPoint (t : ℝ) : ℂ := 2 - Complex.I * t

private lemma functionalEquationPoint_re (t : ℝ) :
    (functionalEquationPoint t).re = 2 := by simp [functionalEquationPoint]

private lemma functionalEquationPoint_ne_neg_nat (t : ℝ) (n : ℕ) :
    functionalEquationPoint t ≠ -(n : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp [functionalEquationPoint] at hre
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

private lemma functionalEquationPoint_ne_one (t : ℝ) :
    functionalEquationPoint t ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  simp [functionalEquationPoint] at hre

private lemma one_sub_functionalEquationPoint (t : ℝ) :
    1 - functionalEquationPoint t = -1 + Complex.I * t := by
  simp [functionalEquationPoint]
  ring

private lemma functionalEquationPoint_eq_two_add (t : ℝ) :
    functionalEquationPoint t = 2 + Complex.I * (-t) := by
  simp [functionalEquationPoint]
  ring

private lemma norm_functional_exp_pos_le (t : ℝ) :
    ‖Complex.exp ((Real.pi : ℂ) * Complex.I *
        functionalEquationPoint t / 2)‖ ≤
      Real.exp ((Real.pi / 2) * |t|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  rw [show ((Real.pi : ℂ) * Complex.I *
      functionalEquationPoint t / 2).re = Real.pi * t / 2 by
    simp [functionalEquationPoint]]
  calc
    Real.pi * t / 2 ≤ Real.pi * |t| / 2 := by
      gcongr
      exact le_abs_self t
    _ = Real.pi / 2 * |t| := by ring

private lemma norm_functional_exp_neg_le (t : ℝ) :
    ‖Complex.exp (-(Real.pi : ℂ) * Complex.I *
        functionalEquationPoint t / 2)‖ ≤
      Real.exp ((Real.pi / 2) * |t|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  rw [show (-(Real.pi : ℂ) * Complex.I *
      functionalEquationPoint t / 2).re = -(Real.pi * t / 2) by
    simp [functionalEquationPoint]
    ring]
  calc
    -(Real.pi * t / 2) ≤ Real.pi * |t| / 2 := by
      have := neg_le_abs t
      nlinarith [Real.pi_pos]
    _ = Real.pi / 2 * |t| := by ring

private lemma norm_nat_cpow_functionalEquationPoint_sub_one (t : ℝ) :
    ‖(N : ℂ) ^ (functionalEquationPoint t - 1)‖ = N := by
  rw [Complex.norm_natCast_cpow_of_pos (NeZero.pos N)]
  norm_num [functionalEquationPoint, Real.rpow_one]

private lemma norm_two_pi_cpow_neg_functionalEquationPoint_le_one (t : ℝ) :
    ‖((2 * Real.pi : ℝ) : ℂ) ^ (-functionalEquationPoint t)‖ ≤ 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  have hbase : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hexp : (-functionalEquationPoint t).re = -2 := by
    simp [functionalEquationPoint]
  rw [hexp]
  exact Real.rpow_le_one_of_one_le_of_nonpos hbase (by norm_num)

/-- The left boundary `Re(s)=-1` has a conductor/height polynomial bound.
The deliberately coarse constant is uniform and is enough for a subsequent
Phragmen--Lindelof normalization.  Primitivity is not needed for this bound. -/
theorem norm_LFunction_neg_one_add_mul_I_le
    (χ : DirichletCharacter ℂ N) (t : ℝ) :
    ‖DirichletCharacter.LFunction χ (-1 + Complex.I * t)‖ ≤
      100 * (N : ℝ) ^ 2 * (1 + |t|) ^ 2 := by
  let s : ℂ := functionalEquationPoint t
  have hfe := ZMod.LFunction_one_sub (fun x : ZMod N => χ x)
    (s := s) (fun n => functionalEquationPoint_ne_neg_nat t n)
    (Or.inr (functionalEquationPoint_ne_one t))
  have hleft : 1 - s = -1 + Complex.I * t := one_sub_functionalEquationPoint t
  have hsright : s = 2 + Complex.I * (-t) := functionalEquationPoint_eq_two_add t
  have hchiNeg : ∀ a : ZMod N, ‖χ (-a)‖ ≤ 1 := fun a => χ.norm_le_one (-a)
  have hL₁ := norm_dft_LFunction_two_add_mul_I_le_of_norm_le_one
    (N := N) (fun x : ZMod N => χ x) χ.norm_le_one (-t)
  have hL₂ := norm_dft_LFunction_two_add_mul_I_le_of_norm_le_one
    (N := N) (fun x : ZMod N => χ (-x)) hchiNeg (-t)
  have hgamma :
      ‖Complex.Gamma s‖ ≤
        9 * (1 + |t|) ^ 2 * Real.exp (-(Real.pi / 2) * |t|) := by
    rw [hsright]
    convert norm_Gamma_two_add_mul_I_le (-t) using 1 <;>
      simp [gammaTwoPoint, abs_neg] <;> ring
  have hexp₁ :
      ‖Complex.exp ((Real.pi : ℂ) * Complex.I * s / 2)‖ ≤
        Real.exp ((Real.pi / 2) * |t|) := by
    simpa [s] using norm_functional_exp_pos_le t
  have hexp₂ :
      ‖Complex.exp (-(Real.pi : ℂ) * Complex.I * s / 2)‖ ≤
        Real.exp ((Real.pi / 2) * |t|) := by
    simpa [s] using norm_functional_exp_neg_le t
  have hbracket :
      ‖Complex.exp ((Real.pi : ℂ) * Complex.I * s / 2) *
          ZMod.LFunction (ZMod.dft (fun x : ZMod N => χ x)) s +
        Complex.exp (-(Real.pi : ℂ) * Complex.I * s / 2) *
          ZMod.LFunction (ZMod.dft (fun x : ZMod N => χ (-x))) s‖ ≤
        2 * Real.exp ((Real.pi / 2) * |t|) *
          ((N : ℝ) * (Real.pi ^ 2 / 6)) := by
    calc
      ‖Complex.exp ((Real.pi : ℂ) * Complex.I * s / 2) *
          ZMod.LFunction (ZMod.dft (fun x : ZMod N => χ x)) s +
        Complex.exp (-(Real.pi : ℂ) * Complex.I * s / 2) *
          ZMod.LFunction (ZMod.dft (fun x : ZMod N => χ (-x))) s‖ ≤
        ‖Complex.exp ((Real.pi : ℂ) * Complex.I * s / 2)‖ *
            ‖ZMod.LFunction (ZMod.dft (fun x : ZMod N => χ x)) s‖ +
          ‖Complex.exp (-(Real.pi : ℂ) * Complex.I * s / 2)‖ *
            ‖ZMod.LFunction (ZMod.dft (fun x : ZMod N => χ (-x))) s‖ := by
          simpa [norm_mul] using norm_add_le
            (Complex.exp ((Real.pi : ℂ) * Complex.I * s / 2) *
              ZMod.LFunction (ZMod.dft (fun x : ZMod N => χ x)) s)
            (Complex.exp (-(Real.pi : ℂ) * Complex.I * s / 2) *
              ZMod.LFunction (ZMod.dft (fun x : ZMod N => χ (-x))) s)
      _ ≤ Real.exp ((Real.pi / 2) * |t|) *
            ((N : ℝ) * (Real.pi ^ 2 / 6)) +
          Real.exp ((Real.pi / 2) * |t|) *
            ((N : ℝ) * (Real.pi ^ 2 / 6)) := by
        have hL₁s : ‖ZMod.LFunction
            (ZMod.dft (fun x : ZMod N => χ x)) s‖ ≤
            (N : ℝ) * (Real.pi ^ 2 / 6) := by
          rw [hsright]
          rw [show ((-t : ℝ) : ℂ) = -(t : ℂ) by norm_num] at hL₁
          exact hL₁
        have hL₂s : ‖ZMod.LFunction
            (ZMod.dft (fun x : ZMod N => χ (-x))) s‖ ≤
            (N : ℝ) * (Real.pi ^ 2 / 6) := by
          rw [hsright]
          rw [show ((-t : ℝ) : ℂ) = -(t : ℂ) by norm_num] at hL₂
          exact hL₂
        exact add_le_add
          (mul_le_mul hexp₁ hL₁s (norm_nonneg _) (Real.exp_pos _).le)
          (mul_le_mul hexp₂ hL₂s (norm_nonneg _) (Real.exp_pos _).le)
      _ = 2 * Real.exp ((Real.pi / 2) * |t|) *
          ((N : ℝ) * (Real.pi ^ 2 / 6)) := by ring
  have hNpow : ‖(N : ℂ) ^ (s - 1)‖ = N := by
    simpa [s] using norm_nat_cpow_functionalEquationPoint_sub_one (N := N) t
  have htwopi : ‖(2 * (Real.pi : ℂ)) ^ (-s)‖ ≤ 1 := by
    convert norm_two_pi_cpow_neg_functionalEquationPoint_le_one t using 1 <;>
      simp [s]
  change ‖ZMod.LFunction (fun x : ZMod N => χ x)
      (-1 + Complex.I * t)‖ ≤ _
  rw [← hleft, hfe]
  rw [norm_mul, norm_mul, norm_mul]
  calc
    ‖(N : ℂ) ^ (s - 1)‖ *
        ‖(2 * (Real.pi : ℂ)) ^ (-s)‖ * ‖Complex.Gamma s‖ *
        ‖Complex.exp ((Real.pi : ℂ) * Complex.I * s / 2) *
            ZMod.LFunction (ZMod.dft (fun x : ZMod N => χ x)) s +
          Complex.exp (-(Real.pi : ℂ) * Complex.I * s / 2) *
            ZMod.LFunction (ZMod.dft (fun x : ZMod N => χ (-x))) s‖ ≤
      (N : ℝ) * 1 *
        (9 * (1 + |t|) ^ 2 * Real.exp (-(Real.pi / 2) * |t|)) *
        (2 * Real.exp ((Real.pi / 2) * |t|) *
          ((N : ℝ) * (Real.pi ^ 2 / 6))) := by
      rw [hNpow]
      gcongr
    _ ≤ 100 * (N : ℝ) ^ 2 * (1 + |t|) ^ 2 := by
      have hcancel : Real.exp (-(Real.pi / 2) * |t|) *
          Real.exp ((Real.pi / 2) * |t|) = 1 := by
        rw [← Real.exp_add]
        simp
      rw [show (N : ℝ) * 1 *
          (9 * (1 + |t|) ^ 2 * Real.exp (-(Real.pi / 2) * |t|)) *
          (2 * Real.exp ((Real.pi / 2) * |t|) *
            ((N : ℝ) * (Real.pi ^ 2 / 6))) =
          3 * Real.pi ^ 2 * (N : ℝ) ^ 2 * (1 + |t|) ^ 2 *
            (Real.exp (-(Real.pi / 2) * |t|) *
              Real.exp ((Real.pi / 2) * |t|)) by ring,
        hcancel, mul_one]
      have hpi : 3 * Real.pi ^ 2 ≤ 100 := by
        nlinarith [Real.pi_pos.le, Real.pi_lt_four]
      gcongr

end
end MAPDirichletLQuantitative

#print axioms MAPDirichletLQuantitative.norm_Gamma_one_add_mul_I_sq
#print axioms MAPDirichletLQuantitative.norm_Gamma_one_add_mul_I_le
#print axioms MAPDirichletLQuantitative.norm_Gamma_two_add_mul_I_le
#print axioms MAPDirichletLQuantitative.norm_LSeries_two_add_mul_I_le
#print axioms MAPDirichletLQuantitative.norm_LFunction_two_add_mul_I_le_zeta_two
#print axioms MAPDirichletLQuantitative.one_third_le_norm_LFunction_two_add_mul_I
#print axioms MAPDirichletLQuantitative.norm_LFunction_neg_one_add_mul_I_le
