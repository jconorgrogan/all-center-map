import CGLProofDAG
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Finite reduction of the Dirichlet-polynomial mean square

Everything in this file is finite or an elementary integral.  The goal is to
expose the precise Montgomery--Vaughan/Hilbert off-diagonal inequality rather
than packaging it inside a general mean-value premise.
-/

namespace MontgomeryVaughanFiniteReduction

open scoped BigOperators ComplexConjugate
open MeasureTheory CGLProofDAG

noncomputable section

def dyadicSupport (N : ℕ) : Finset ℕ := Finset.Ioc N (2 * N)

def phase (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (((t * Real.log n : ℝ) : ℂ) * Complex.I)

def pairTerm (b : ℕ → ℂ) (n m : ℕ) (t : ℝ) : ℂ :=
  (b n * phase n t) * star (b m * phase m t)

def offDiagonalAt (b : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ dyadicSupport N, ∑ m ∈ (dyadicSupport N).erase n,
    pairTerm b n m t

def coefficientEnergy (b : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ n ∈ dyadicSupport N, ‖b n‖ ^ 2

theorem dirichletPolynomial_eq
    (b : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    dirichletPolynomial b N t =
      ∑ n ∈ dyadicSupport N, b n * phase n t := by
  unfold dirichletPolynomial dyadicSupport phase
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Complex.ofReal_mul, mul_comm Complex.I]

theorem finite_square_expansion
    (s : Finset ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ s, f n) * star (∑ m ∈ s, f m) =
      ∑ n ∈ s, ∑ m ∈ s, f n * star (f m) := by
  rw [star_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]

theorem pairTerm_self
    (b : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    pairTerm b n n t = (‖b n‖ ^ 2 : ℝ) := by
  rw [pairTerm]
  have hphase : phase n t * star (phase n t) = 1 := by
    change phase n t * (starRingEnd ℂ) (phase n t) = 1
    have hnorm : ‖phase n t‖ = 1 := by
      unfold phase
      exact Complex.norm_exp_ofReal_mul_I _
    rw [Complex.mul_conj, ← Complex.sq_norm, hnorm]
    norm_num
  rw [star_mul]
  calc
    (b n * phase n t) * (star (phase n t) * star (b n)) =
        (b n * star (b n)) * (phase n t * star (phase n t)) := by ring
    _ = b n * star (b n) := by rw [hphase, mul_one]
    _ = (‖b n‖ ^ 2 : ℝ) := by
      change b n * (starRingEnd ℂ) (b n) = (‖b n‖ ^ 2 : ℝ)
      rw [Complex.mul_conj, ← Complex.sq_norm]

theorem square_eq_diagonal_add_offDiagonal
    (b : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    dirichletPolynomial b N t * star (dirichletPolynomial b N t) =
      (coefficientEnergy b N : ℂ) + offDiagonalAt b N t := by
  rw [dirichletPolynomial_eq, finite_square_expansion]
  unfold coefficientEnergy offDiagonalAt
  calc
    (∑ n ∈ dyadicSupport N, ∑ m ∈ dyadicSupport N,
        b n * phase n t * star (b m * phase m t)) =
      ∑ n ∈ dyadicSupport N,
        (pairTerm b n n t +
          ∑ m ∈ (dyadicSupport N).erase n, pairTerm b n m t) := by
      apply Finset.sum_congr rfl
      intro n hn
      have herase := Finset.sum_erase_add (dyadicSupport N)
        (fun m => pairTerm b n m t) hn
      rw [add_comm] at herase
      exact herase.symm
    _ = ∑ n ∈ dyadicSupport N,
        ((‖b n‖ ^ 2 : ℝ) +
          ∑ m ∈ (dyadicSupport N).erase n, pairTerm b n m t) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [pairTerm_self]
    _ = (↑(∑ n ∈ dyadicSupport N, ‖b n‖ ^ 2) : ℂ) +
        ∑ n ∈ dyadicSupport N,
          ∑ m ∈ (dyadicSupport N).erase n, pairTerm b n m t := by
      rw [Finset.sum_add_distrib]
      push_cast
      rfl

theorem intervalIntegrable_pairTerm
    (b : ℕ → ℂ) (n m : ℕ) (a c : ℝ) :
    IntervalIntegrable (pairTerm b n m) volume a c := by
  apply Continuous.intervalIntegrable
  unfold pairTerm phase
  fun_prop

theorem intervalIntegrable_offDiagonalAt
    (b : ℕ → ℂ) (N : ℕ) (a c : ℝ) :
    IntervalIntegrable (offDiagonalAt b N) volume a c := by
  apply Continuous.intervalIntegrable
  unfold offDiagonalAt pairTerm phase
  fun_prop

def integratedOffDiagonal (b : ℕ → ℂ) (N : ℕ) (T : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..T, offDiagonalAt b N t

/-- Exact continuous finite expansion: diagonal plus one explicit
off-diagonal integral. -/
theorem integral_square_eq_diagonal_add_offDiagonal
    (b : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    (∫ t in (0 : ℝ)..T,
      dirichletPolynomial b N t * star (dirichletPolynomial b N t)) =
      (T : ℂ) * coefficientEnergy b N + integratedOffDiagonal b N T := by
  calc
    (∫ t in (0 : ℝ)..T,
      dirichletPolynomial b N t * star (dirichletPolynomial b N t)) =
        ∫ t in (0 : ℝ)..T,
          ((coefficientEnergy b N : ℂ) + offDiagonalAt b N t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact square_eq_diagonal_add_offDiagonal b N t
    _ = (∫ _t in (0 : ℝ)..T, (coefficientEnergy b N : ℂ)) +
          ∫ t in (0 : ℝ)..T, offDiagonalAt b N t := by
      rw [intervalIntegral.integral_add]
      · exact (continuous_const.intervalIntegrable _ _)
      · exact intervalIntegrable_offDiagonalAt b N 0 T
    _ = (T : ℂ) * coefficientEnergy b N + integratedOffDiagonal b N T := by
      rw [intervalIntegral.integral_const]
      simp [integratedOffDiagonal]

/-- Literal logarithmic frequency gap. -/
def logGap (n m : ℕ) : ℝ := Real.log n - Real.log m

theorem logGap_ne_zero
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hne : n ≠ m) :
    logGap n m ≠ 0 := by
  intro h
  have hlog : Real.log n = Real.log m := sub_eq_zero.mp h
  have : (n : ℝ) = m := Real.strictMonoOn_log.injOn
    (Set.mem_Ioi.mpr (by exact_mod_cast hn))
    (Set.mem_Ioi.mpr (by exact_mod_cast hm)) hlog
  exact hne (by exact_mod_cast this)

theorem pairTerm_frequency_form
    (b : ℕ → ℂ) (n m : ℕ) (t : ℝ) :
    pairTerm b n m t =
      (b n * star (b m)) *
        Complex.exp
          (Complex.I * (((t * logGap n m : ℝ) : ℂ))) := by
  unfold pairTerm phase logGap
  rw [star_mul]
  have hstar :
      star (Complex.exp (((t * Real.log m : ℝ) : ℂ) * Complex.I)) =
        Complex.exp (-(((t * Real.log m : ℝ) : ℂ) * Complex.I)) := by
    change (starRingEnd ℂ)
      (Complex.exp (((t * Real.log m : ℝ) : ℂ) * Complex.I)) = _
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hstar]
  calc
    (b n * Complex.exp (((t * Real.log n : ℝ) : ℂ) * Complex.I)) *
        (Complex.exp (-(((t * Real.log m : ℝ) : ℂ) * Complex.I)) * star (b m)) =
      (b n * star (b m)) *
        (Complex.exp (((t * Real.log n : ℝ) : ℂ) * Complex.I) *
          Complex.exp (-(((t * Real.log m : ℝ) : ℂ) * Complex.I))) := by ring
    _ = (b n * star (b m)) *
        Complex.exp
          ((((t * Real.log n : ℝ) : ℂ) * Complex.I) +
            -(((t * Real.log m : ℝ) : ℂ) * Complex.I)) := by
      rw [Complex.exp_add]
    _ = (b n * star (b m)) *
        Complex.exp
          (Complex.I *
            ((((t * (Real.log n - Real.log m) : ℝ)) : ℂ))) := by
      push_cast
      ring

/-- The exact elementary oscillatory integral on every off-diagonal pair. -/
theorem integral_pairTerm_offDiagonal
    (b : ℕ → ℂ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hne : n ≠ m) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, pairTerm b n m t) =
      (b n * star (b m)) *
        ((Complex.exp
          (Complex.I * (((T * logGap n m : ℝ) : ℂ))) - 1) /
          (Complex.I * logGap n m)) := by
  rw [intervalIntegral.integral_congr (fun t _ => pairTerm_frequency_form b n m t)]
  rw [intervalIntegral.integral_const_mul]
  have hgap : (Complex.I * (logGap n m : ℂ)) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero
      (Complex.ofReal_ne_zero.mpr (logGap_ne_zero hn hm hne))
  have hexp := integral_exp_mul_complex (a := (0 : ℝ)) (b := T) hgap
  have hform :
      (fun t : ℝ => Complex.exp
        (Complex.I * (((t * logGap n m : ℝ) : ℂ)))) =
        fun t : ℝ => Complex.exp ((Complex.I * logGap n m) * (t : ℂ)) := by
    funext t
    congr 1
    push_cast
    ring
  congr 1
  rw [hform, hexp]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  congr 2
  congr 1
  push_cast
  ring

/-- Finite sum/integral interchange for the entire off-diagonal sector. -/
theorem integratedOffDiagonal_eq_sum_integrals
    (b : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    integratedOffDiagonal b N T =
      ∑ n ∈ dyadicSupport N,
        ∑ m ∈ (dyadicSupport N).erase n,
          ∫ t in (0 : ℝ)..T, pairTerm b n m t := by
  unfold integratedOffDiagonal offDiagonalAt
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [intervalIntegral.integral_finsetSum]
    intro m hm
    exact intervalIntegrable_pairTerm b n m 0 T
  · intro n hn
    apply Continuous.intervalIntegrable
    simp only [pairTerm, phase]
    fun_prop

/-- The exact explicit off-diagonal kernel obtained after finite expansion and
elementary integration.  No estimate has yet been used. -/
theorem integratedOffDiagonal_eq_explicitKernel
    (b : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    integratedOffDiagonal b N T =
      ∑ n ∈ dyadicSupport N,
        ∑ m ∈ (dyadicSupport N).erase n,
          (b n * star (b m)) *
            ((Complex.exp
              (Complex.I * (((T * logGap n m : ℝ) : ℂ))) - 1) /
              (Complex.I * logGap n m)) := by
  rw [integratedOffDiagonal_eq_sum_integrals]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  have hnpos : 0 < n := by
    have := (Finset.mem_Ioc.mp hn).1
    omega
  have hmSupport : m ∈ dyadicSupport N := (Finset.mem_erase.mp hm).2
  have hmpos : 0 < m := by
    have := (Finset.mem_Ioc.mp hmSupport).1
    omega
  have hne : n ≠ m := by
    exact fun h => (Finset.mem_erase.mp hm).1 h.symm
  exact integral_pairTerm_offDiagonal b hnpos hmpos hne T

/-- The elementary lower bound `1 - x⁻¹ ≤ log x`, rewritten for a
positive quotient. -/
theorem sub_div_le_log_div
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (y - x) / y ≤ Real.log y - Real.log x := by
  have hquot : 0 < y / x := div_pos hy hx
  have hlog := Real.one_sub_inv_le_log_of_pos hquot
  have hrewrite : 1 - (y / x)⁻¹ = (y - x) / y := by
    rw [inv_div]
    field_simp [hx.ne', hy.ne']
  calc
    (y - x) / y = 1 - (y / x)⁻¹ := hrewrite.symm
    _ ≤ Real.log (y / x) := hlog
    _ = Real.log y - Real.log x := Real.log_div hy.ne' hx.ne'

/-- Distinct natural logarithmic frequencies in `(N,2N]` are separated by
at least `1/(2N)`.  The statement is symmetric and keeps the literal
logarithmic kernel used by the finite expansion. -/
theorem dyadic_logGap_separated
    {N n m : ℕ} (hN : 1 ≤ N)
    (hn : n ∈ dyadicSupport N) (hm : m ∈ dyadicSupport N)
    (hne : n ≠ m) :
    (1 : ℝ) / (2 * N) ≤ |logGap n m| := by
  have hNpos : 0 < N := Nat.zero_lt_of_lt hN
  have hnIoc := Finset.mem_Ioc.mp hn
  have hmIoc := Finset.mem_Ioc.mp hm
  have hnpos : 0 < n := lt_of_lt_of_le hNpos hnIoc.1.le
  have hmpos : 0 < m := lt_of_lt_of_le hNpos hmIoc.1.le
  have hnupper : (n : ℝ) ≤ 2 * N := by exact_mod_cast hnIoc.2
  have hmupper : (m : ℝ) ≤ 2 * N := by exact_mod_cast hmIoc.2
  have hdenpos : (0 : ℝ) < 2 * N := by positivity
  rcases lt_or_gt_of_ne hne with hnm | hmn
  · have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hnm.le
    have hdiffReal : (1 : ℝ) ≤ (m : ℝ) - n := by
      have : (n : ℝ) + 1 ≤ m := by exact_mod_cast hnm
      linarith
    have hfrac : (1 : ℝ) / (2 * N) ≤ ((m : ℝ) - n) / m := by
      apply (div_le_div_iff₀ hdenpos (by exact_mod_cast hmpos)).2
      nlinarith
    have hlog : ((m : ℝ) - n) / m ≤ Real.log m - Real.log n :=
      sub_div_le_log_div (by exact_mod_cast hnpos) (by exact_mod_cast hmpos)
    rw [logGap, abs_of_nonpos]
    · linarith
    · exact sub_nonpos.mpr (Real.log_le_log (by exact_mod_cast hnpos) hnmR)
  · have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn.le
    have hdiffReal : (1 : ℝ) ≤ (n : ℝ) - m := by
      have : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn
      linarith
    have hfrac : (1 : ℝ) / (2 * N) ≤ ((n : ℝ) - m) / n := by
      apply (div_le_div_iff₀ hdenpos (by exact_mod_cast hnpos)).2
      nlinarith
    have hlog : ((n : ℝ) - m) / n ≤ Real.log n - Real.log m :=
      sub_div_le_log_div (by exact_mod_cast hmpos) (by exact_mod_cast hnpos)
    rw [logGap, abs_of_nonneg]
    · exact hfrac.trans hlog
    · exact sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast hmpos) hmnR)

/-- The one remaining analytic kernel theorem in the continuous mean-square
route.  It is the finite Montgomery--Vaughan Hilbert inequality specialized
to logarithmic frequencies on `(N,2N]`.  It is deliberately not asserted. -/
def FiniteLogHilbertInequality : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (a : ℕ → ℂ), 1 ≤ N →
      ‖∑ n ∈ dyadicSupport N,
          ∑ m ∈ (dyadicSupport N).erase n,
            (a n * star (a m)) / (logGap n m : ℂ)‖ ≤
        C * N * coefficientEnergy a N

/-- The exact separated-frequency Hilbert theorem specializes to the finite
logarithmic Hilbert inequality with the explicit witness `3 * pi`.  The
hypothesis is intentionally written out rather than hidden behind another
project proposition: this finite classical inequality is the remaining
analytic leaf in the pinned environment. -/
theorem finiteLogHilbertInequality_of_separated
    (hHilbert :
      ∀ (s : Finset ℕ) (lam : ℕ → ℝ) (z : ℕ → ℂ) (delta : ℝ),
        0 < delta →
        (∀ m ∈ s, ∀ n ∈ s, m ≠ n →
          delta ≤ |lam m - lam n|) →
        ‖∑ m ∈ s, ∑ n ∈ s.erase m,
            (z m * star (z n)) / ((lam m - lam n : ℝ) : ℂ)‖ ≤
          (3 * Real.pi / (2 * delta)) * ∑ n ∈ s, ‖z n‖ ^ 2) :
    FiniteLogHilbertInequality := by
  refine ⟨3 * Real.pi, mul_pos (by norm_num) Real.pi_pos, ?_⟩
  intro N a hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hdelta : (0 : ℝ) < 1 / (2 * N) := by positivity
  have hbound := hHilbert (dyadicSupport N) (fun n => Real.log n) a (1 / (2 * N))
    hdelta (fun m hm n hn hne => dyadic_logGap_separated hN hm hn hne)
  change ‖∑ n ∈ dyadicSupport N,
      ∑ m ∈ (dyadicSupport N).erase n,
        (a n * star (a m)) / (logGap n m : ℂ)‖ ≤
    3 * Real.pi * N * coefficientEnergy a N
  rw [show (3 * Real.pi / (2 * (1 / (2 * (N : ℝ))))) =
      3 * Real.pi * N by field_simp] at hbound
  simpa [logGap, coefficientEnergy] using hbound

def modulatedCoefficient (b : ℕ → ℂ) (T : ℝ) (n : ℕ) : ℂ :=
  b n * phase n T

def hilbertPair (a : ℕ → ℂ) (n m : ℕ) : ℂ :=
  (a n * star (a m)) / (logGap n m : ℂ)

def hilbertForm (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ dyadicSupport N,
    ∑ m ∈ (dyadicSupport N).erase n, hilbertPair a n m

theorem coefficientEnergy_modulated
    (b : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    coefficientEnergy (modulatedCoefficient b T) N =
      coefficientEnergy b N := by
  unfold coefficientEnergy modulatedCoefficient
  apply Finset.sum_congr rfl
  intro n hn
  rw [norm_mul]
  have hnorm : ‖phase n T‖ = 1 := by
    unfold phase
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hnorm, mul_one]

/-- Pointwise algebra splitting the integrated numerator into two finite
Hilbert kernels, one with phase-modulated coefficients and one unmodulated. -/
theorem explicitKernelPair_eq_hilbertDifference
    (b : ℕ → ℂ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hne : n ≠ m) (T : ℝ) :
    (b n * star (b m)) *
        ((Complex.exp
          (Complex.I * (((T * logGap n m : ℝ) : ℂ))) - 1) /
          (Complex.I * logGap n m)) =
      -Complex.I *
        (hilbertPair (modulatedCoefficient b T) n m -
          hilbertPair b n m) := by
  have hfreq :
      modulatedCoefficient b T n * star (modulatedCoefficient b T m) =
        (b n * star (b m)) *
          Complex.exp
            (Complex.I * (((T * logGap n m : ℝ) : ℂ))) := by
    simpa [pairTerm, modulatedCoefficient] using
      (pairTerm_frequency_form b n m T)
  have hgap : (logGap n m : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (logGap_ne_zero hn hm hne)
  unfold hilbertPair
  rw [hfreq]
  field_simp [hgap, Complex.I_ne_zero]
  rw [Complex.I_sq]
  ring

theorem integratedOffDiagonal_eq_hilbertDifference
    (b : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    integratedOffDiagonal b N T =
      -Complex.I *
        (hilbertForm (modulatedCoefficient b T) N - hilbertForm b N) := by
  rw [integratedOffDiagonal_eq_explicitKernel]
  unfold hilbertForm
  rw [mul_sub, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  have hnpos : 0 < n := by
    have := (Finset.mem_Ioc.mp hn).1
    omega
  have hmSupport : m ∈ dyadicSupport N := (Finset.mem_erase.mp hm).2
  have hmpos : 0 < m := by
    have := (Finset.mem_Ioc.mp hmSupport).1
    omega
  have hne : n ≠ m := fun h => (Finset.mem_erase.mp hm).1 h.symm
  simpa [mul_sub] using
    (explicitKernelPair_eq_hilbertDifference b hnpos hmpos hne T)

/-- Once the one finite logarithmic Hilbert inequality is supplied, the full
continuous off-diagonal energy is bounded with no further analytic input. -/
theorem norm_integratedOffDiagonal_le_of_hilbert
    (hHilbert : FiniteLogHilbertInequality)
    (b : ℕ → ℂ) (N : ℕ) (T : ℝ) (hN : 1 ≤ N) :
    ‖integratedOffDiagonal b N T‖ ≤
      2 * Classical.choose hHilbert * N * coefficientEnergy b N := by
  let C : ℝ := Classical.choose hHilbert
  have hCspec := Classical.choose_spec hHilbert
  have hmod := hCspec.2 N (modulatedCoefficient b T) hN
  have hbase := hCspec.2 N b hN
  rw [integratedOffDiagonal_eq_hilbertDifference, norm_mul,
    norm_neg, Complex.norm_I, one_mul]
  calc
    ‖hilbertForm (modulatedCoefficient b T) N - hilbertForm b N‖ ≤
        ‖hilbertForm (modulatedCoefficient b T) N‖ + ‖hilbertForm b N‖ :=
      norm_sub_le _ _
    _ ≤ C * N * coefficientEnergy (modulatedCoefficient b T) N +
        C * N * coefficientEnergy b N := add_le_add hmod hbase
    _ = 2 * C * N * coefficientEnergy b N := by
      rw [coefficientEnergy_modulated]
      ring

end
end MontgomeryVaughanFiniteReduction

#print axioms MontgomeryVaughanFiniteReduction.finite_square_expansion
#print axioms MontgomeryVaughanFiniteReduction.pairTerm_self
#print axioms MontgomeryVaughanFiniteReduction.square_eq_diagonal_add_offDiagonal
#print axioms MontgomeryVaughanFiniteReduction.integral_square_eq_diagonal_add_offDiagonal
#print axioms MontgomeryVaughanFiniteReduction.integral_pairTerm_offDiagonal
#print axioms MontgomeryVaughanFiniteReduction.integratedOffDiagonal_eq_sum_integrals
#print axioms MontgomeryVaughanFiniteReduction.integratedOffDiagonal_eq_explicitKernel
#print axioms MontgomeryVaughanFiniteReduction.sub_div_le_log_div
#print axioms MontgomeryVaughanFiniteReduction.dyadic_logGap_separated
#print axioms MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_of_separated
#print axioms MontgomeryVaughanFiniteReduction.coefficientEnergy_modulated
#print axioms MontgomeryVaughanFiniteReduction.integratedOffDiagonal_eq_hilbertDifference
#print axioms MontgomeryVaughanFiniteReduction.norm_integratedOffDiagonal_le_of_hilbert
