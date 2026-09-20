import GuthMaynardHeathBrownInterface

/-!
# The coefficient-majorant descent in Heath--Brown's difference-set theorem

This file proves the finite algebraic step at the start of the published
Heath--Brown argument: the difference-set quadratic form is monotone under
pointwise majorization of the coefficient norms.  It is Lemma 2.1 in Seth
Hardy's 2025 Warwick notes on Heath--Brown's theorem and is the identity
described by Heath--Brown as the majorant step.

The proof expands the quadratic form into its coefficient Gram kernel.  It
does not invoke `HeathBrownTheorem16` and introduces no analytic premise.
-/

namespace GuthMaynardHeathBrownMajorant

open scoped BigOperators
open GuthMaynardHeathBrownInterface

noncomputable section

/-! ## A generic finite Gram-majorant identity -/

def gramPolynomial {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (a : ι → ℂ) (z : ι → κ → ℂ) (t u : κ) : ℂ :=
  ∑ n ∈ S, a n * z n t * star (z n u)

def gramKernel {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (W : Finset κ) (z : ι → κ → ℂ) (n m : ι) : ℂ :=
  ∑ t ∈ W, z n t * star (z m t)

def complexGramQuadratic {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (W : Finset κ) (a : ι → ℂ)
    (z : ι → κ → ℂ) : ℂ :=
  ∑ t ∈ W, ∑ u ∈ W,
    gramPolynomial S a z t u * star (gramPolynomial S a z t u)

def expandedGramQuadratic {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (W : Finset κ) (a : ι → ℂ)
    (z : ι → κ → ℂ) : ℂ :=
  ∑ n ∈ S, ∑ m ∈ S,
    a n * star (a m) *
      (gramKernel W z n m * star (gramKernel W z n m))

def realGramQuadratic {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (W : Finset κ) (a : ι → ℂ)
    (z : ι → κ → ℂ) : ℝ :=
  ∑ t ∈ W, ∑ u ∈ W, ‖gramPolynomial S a z t u‖ ^ 2

def absoluteCoefficientMajorant {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (W : Finset κ) (a : ι → ℂ)
    (z : ι → κ → ℂ) : ℝ :=
  ∑ n ∈ S, ∑ m ∈ S,
    ‖a n‖ * ‖a m‖ * ‖gramKernel W z n m‖ ^ 2

theorem sum_four_swap {ι κ M : Type*}
    [DecidableEq ι] [DecidableEq κ] [AddCommMonoid M]
    (S : Finset ι) (W : Finset κ)
    (f : κ → κ → ι → ι → M) :
    (∑ t ∈ W, ∑ u ∈ W, ∑ n ∈ S, ∑ m ∈ S, f t u n m) =
      ∑ n ∈ S, ∑ m ∈ S, ∑ t ∈ W, ∑ u ∈ W, f t u n m := by
  calc
    (∑ t ∈ W, ∑ u ∈ W, ∑ n ∈ S, ∑ m ∈ S, f t u n m) =
        ∑ t ∈ W, ∑ n ∈ S, ∑ u ∈ W, ∑ m ∈ S, f t u n m := by
      apply Finset.sum_congr rfl
      intro t ht
      exact Finset.sum_comm
    _ = ∑ n ∈ S, ∑ t ∈ W, ∑ u ∈ W, ∑ m ∈ S, f t u n m :=
      Finset.sum_comm
    _ = ∑ n ∈ S, ∑ t ∈ W, ∑ m ∈ S, ∑ u ∈ W, f t u n m := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro t ht
      exact Finset.sum_comm
    _ = ∑ n ∈ S, ∑ m ∈ S, ∑ t ∈ W, ∑ u ∈ W, f t u n m := by
      apply Finset.sum_congr rfl
      intro n hn
      exact Finset.sum_comm

set_option maxHeartbeats 800000 in
/-- Exact four-fold expansion of the difference-set Gram form. -/
theorem complexGramQuadratic_eq_expanded
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (W : Finset κ) (a : ι → ℂ)
    (z : ι → κ → ℂ) :
    complexGramQuadratic S W a z = expandedGramQuadratic S W a z := by
  simp only [complexGramQuadratic, expandedGramQuadratic, gramPolynomial,
    gramKernel, star_sum, star_mul]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [sum_four_swap, Finset.sum_comm]
  simp only [star_star]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  ring

theorem complexGramQuadratic_eq_coe_real
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (W : Finset κ) (a : ι → ℂ)
    (z : ι → κ → ℂ) :
    complexGramQuadratic S W a z = (realGramQuadratic S W a z : ℂ) := by
  unfold complexGramQuadratic realGramQuadratic
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [show star (gramPolynomial S a z t u) =
      (starRingEnd ℂ) (gramPolynomial S a z t u) by rfl]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

set_option maxHeartbeats 800000 in
theorem realGramQuadratic_le_absoluteCoefficientMajorant
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (W : Finset κ) (a : ι → ℂ)
    (z : ι → κ → ℂ) :
    realGramQuadratic S W a z ≤ absoluteCoefficientMajorant S W a z := by
  have hcomplex : (realGramQuadratic S W a z : ℂ) =
      expandedGramQuadratic S W a z := by
    rw [← complexGramQuadratic_eq_coe_real]
    exact complexGramQuadratic_eq_expanded S W a z
  have hreal := congrArg Complex.re hcomplex
  simp only [Complex.ofReal_re] at hreal
  rw [hreal]
  unfold expandedGramQuadratic absoluteCoefficientMajorant
  calc
    (∑ n ∈ S, ∑ m ∈ S,
      a n * star (a m) *
        (gramKernel W z n m * star (gramKernel W z n m))).re =
        ∑ n ∈ S, ∑ m ∈ S,
          (a n * star (a m) *
            (gramKernel W z n m * star (gramKernel W z n m))).re := by
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Complex.re_sum]
    _ ≤ ∑ n ∈ S, ∑ m ∈ S,
          ‖a n * star (a m) *
            (gramKernel W z n m * star (gramKernel W z n m))‖ := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      exact Complex.re_le_norm _
    _ = ∑ n ∈ S, ∑ m ∈ S,
          ‖a n‖ * ‖a m‖ * ‖gramKernel W z n m‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      rw [norm_mul, norm_mul, norm_star, norm_mul, norm_star]
      ring

theorem absoluteCoefficientMajorant_real_nonnegative_eq
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (W : Finset κ) (b : ι → ℝ)
    (z : ι → κ → ℂ) (hb : ∀ n ∈ S, 0 ≤ b n) :
    absoluteCoefficientMajorant S W (fun n => (b n : ℂ)) z =
      realGramQuadratic S W (fun n => (b n : ℂ)) z := by
  apply Complex.ofReal_injective
  rw [← complexGramQuadratic_eq_coe_real,
    complexGramQuadratic_eq_expanded]
  unfold absoluteCoefficientMajorant expandedGramQuadratic
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hbn := hb n hn
  have hbm := hb m hm
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hbn,
    abs_of_nonneg hbm, Complex.ofReal_mul, Complex.ofReal_pow]
  rw [← Complex.ofReal_pow]
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  rw [show star (b m : ℂ) = (b m : ℂ) by simp]
  rw [show star (gramKernel W z n m) =
      (starRingEnd ℂ) (gramKernel W z n m) by rfl]

set_option maxHeartbeats 800000 in
/-- Generic finite majorant principle.  No spacing or interval assumption is
needed for this algebraic step. -/
theorem gram_majorant_principle
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (W : Finset κ) (a : ι → ℂ) (b : ι → ℝ)
    (z : ι → κ → ℂ) (hb : ∀ n ∈ S, ‖a n‖ ≤ b n) :
    realGramQuadratic S W a z ≤
      realGramQuadratic S W (fun n => (b n : ℂ)) z := by
  calc
    realGramQuadratic S W a z ≤
        absoluteCoefficientMajorant S W a z :=
      realGramQuadratic_le_absoluteCoefficientMajorant S W a z
    _ ≤ absoluteCoefficientMajorant S W (fun n => (b n : ℂ)) z := by
      unfold absoluteCoefficientMajorant
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      have hbn : 0 ≤ b n := (norm_nonneg _).trans (hb n hn)
      have hbm : 0 ≤ b m := (norm_nonneg _).trans (hb m hm)
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hbn,
        abs_of_nonneg hbm]
      gcongr
      · exact hb n hn
      · exact hb m hm
    _ = realGramQuadratic S W (fun n => (b n : ℂ)) z :=
      absoluteCoefficientMajorant_real_nonnegative_eq S W b z
        (fun n hn => (norm_nonneg (a n)).trans (hb n hn))

/-! ## Literal Dirichlet-polynomial specialization -/

def dirichletPhase (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp ((((t * Real.log n : ℝ) : ℂ) * Complex.I))

theorem dirichletPhase_difference (n : ℕ) (t u : ℝ) :
    dirichletPhase n t * star (dirichletPhase n u) =
      Complex.exp (Complex.I * ((t - u) * Real.log n)) := by
  unfold dirichletPhase
  have hstar :
      star (((((u * Real.log n) : ℝ) : ℂ) * Complex.I)) =
        (((-(u * Real.log n) : ℝ) : ℂ) * Complex.I) := by
    change (starRingEnd ℂ) (((((u * Real.log n) : ℝ) : ℂ) * Complex.I)) = _
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [show star
        (Complex.exp (((((u * Real.log n) : ℝ) : ℂ) * Complex.I))) =
      Complex.exp
        (star (((((u * Real.log n) : ℝ) : ℂ) * Complex.I))) by
    exact (Complex.exp_conj _).symm]
  rw [hstar, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem gramPolynomial_dirichletPhase_eq_differencePolynomial
    (a : ℕ → ℂ) (M : ℕ) (t u : ℝ) :
    gramPolynomial (Finset.Icc M (2 * M)) a dirichletPhase t u =
      differencePolynomial a M t u := by
  unfold gramPolynomial differencePolynomial
  unfold GuthMaynardSource.displayedDirichletPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  calc
    a n * dirichletPhase n t * star (dirichletPhase n u) =
        a n * (dirichletPhase n t * star (dirichletPhase n u)) := by ring
    _ = a n * Complex.exp
        (Complex.I * (((t : ℂ) - (u : ℂ)) * (Real.log n : ℂ))) :=
      congrArg (fun z : ℂ => a n * z) (dirichletPhase_difference n t u)
    _ = a n * Complex.exp
        (Complex.I * ((((t - u : ℝ) : ℂ)) * (Real.log n : ℂ))) := by
      rw [Complex.ofReal_sub]

theorem realGramQuadratic_dirichletPhase_eq
    (a : ℕ → ℂ) (M : ℕ) (W : Finset ℝ) :
    realGramQuadratic (Finset.Icc M (2 * M)) W a dirichletPhase =
      differenceQuadraticForm a M W := by
  unfold realGramQuadratic differenceQuadraticForm
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro u hu
  rw [gramPolynomial_dirichletPhase_eq_differencePolynomial]

/-- Literal Heath--Brown coefficient majorant, with the displayed closed
dyadic interval and exact difference polynomial. -/
theorem differenceQuadraticForm_majorant
    {a : ℕ → ℂ} {b : ℕ → ℝ} (M : ℕ) (W : Finset ℝ)
    (hb : ∀ n ∈ Finset.Icc M (2 * M), ‖a n‖ ≤ b n) :
    differenceQuadraticForm a M W ≤
      differenceQuadraticForm (fun n => (b n : ℂ)) M W := by
  rw [← realGramQuadratic_dirichletPhase_eq,
    ← realGramQuadratic_dirichletPhase_eq]
  exact gram_majorant_principle
    (Finset.Icc M (2 * M)) W a b dirichletPhase hb

/-- In particular, every unit-bounded coefficient sequence is dominated by
the coefficient-one difference-set form.  This is the first completed descent
below `HeathBrownTheorem16`. -/
theorem differenceQuadraticForm_le_oneCoefficient
    {a : ℕ → ℂ} (M : ℕ) (W : Finset ℝ)
    (ha : ∀ n ∈ Finset.Icc M (2 * M), ‖a n‖ ≤ 1) :
    differenceQuadraticForm a M W ≤
      differenceQuadraticForm (fun _ => (1 : ℂ)) M W := by
  exact differenceQuadraticForm_majorant M W (b := fun _ => 1) ha

/-! ## Exact constant scaling and the coefficient-one core -/

theorem differencePolynomial_const_mul
    (c : ℂ) (a : ℕ → ℂ) (M : ℕ) (t u : ℝ) :
    differencePolynomial (fun n => c * a n) M t u =
      c * differencePolynomial a M t u := by
  unfold differencePolynomial GuthMaynardSource.displayedDirichletPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem differenceQuadraticForm_const_mul
    (c : ℂ) (a : ℕ → ℂ) (M : ℕ) (W : Finset ℝ) :
    differenceQuadraticForm (fun n => c * a n) M W =
      ‖c‖ ^ 2 * differenceQuadraticForm a M W := by
  unfold differenceQuadraticForm
  simp_rw [differencePolynomial_const_mul, norm_mul]
  calc
    (∑ t ∈ W, ∑ u ∈ W,
        (‖c‖ * ‖differencePolynomial a M t u‖) ^ 2) =
        ∑ t ∈ W, ∑ u ∈ W,
          ‖c‖ ^ 2 * ‖differencePolynomial a M t u‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro u hu
      ring
    _ = ‖c‖ ^ 2 *
        ∑ t ∈ W, ∑ u ∈ W, ‖differencePolynomial a M t u‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mul_sum]

theorem differenceQuadraticForm_constant
    (c : ℂ) (M : ℕ) (W : Finset ℝ) :
    differenceQuadraticForm (fun _ => c) M W =
      ‖c‖ ^ 2 * differenceQuadraticForm (fun _ => (1 : ℂ)) M W := by
  simpa only [mul_one] using
    differenceQuadraticForm_const_mul c (fun _ => (1 : ℂ)) M W

/-- The right side of Heath--Brown Theorem 1.6 before its epsilon factor. -/
def heathBrownShape (T : ℝ) (M : ℕ) (W : Finset ℝ) : ℝ :=
  (W.card : ℝ) ^ 2 * M +
    (W.card : ℝ) * (M : ℝ) ^ 2 +
    Real.rpow (W.card : ℝ) (5 / 4 : ℝ) *
      Real.rpow T (1 / 2 : ℝ) * M

theorem heathBrownShape_nonneg
    {T : ℝ} (hT : 0 ≤ T) (M : ℕ) (W : Finset ℝ) :
    0 ≤ heathBrownShape T M W := by
  unfold heathBrownShape
  have hcard : 0 ≤ (W.card : ℝ) := Nat.cast_nonneg _
  have hM : 0 ≤ (M : ℝ) := Nat.cast_nonneg _
  have hcardPow : 0 ≤ Real.rpow (W.card : ℝ) (5 / 4 : ℝ) :=
    Real.rpow_nonneg hcard _
  have hTPow : 0 ≤ Real.rpow T (1 / 2 : ℝ) :=
    Real.rpow_nonneg hT _
  nlinarith [sq_nonneg (W.card : ℝ), sq_nonneg (M : ℝ),
    mul_nonneg hcardPow (mul_nonneg hTPow hM)]

/-- Exact remaining analytic core after coefficient majorization: prove the
published bound only for the coefficient-one polynomial.  The next source
steps are smoothing, reflection, and Heath--Brown's length-comparison lemma. -/
def HeathBrownOneCoefficientCore : Prop :=
  ∀ eta : ℝ, 0 < eta →
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (M : ℕ) (W : Finset ℝ),
        T₀ ≤ T → 1 ≤ M →
        CGLProofDAG.OneSeparated W →
        ContainedInIntervalOfLength W T →
        differenceQuadraticForm (fun _ => (1 : ℂ)) M W ≤
          C * Real.rpow T eta * heathBrownShape T M W

/-- Unit-bounded Heath--Brown follows from the coefficient-one analytic core.
This is the exact form quoted inside Guth--Maynard Section 6. -/
theorem unitCoefficient_differenceMeanSquare_of_oneCoefficientCore
    (hcore : HeathBrownOneCoefficientCore) {eta : ℝ} (heta : 0 < eta) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (M : ℕ) (a : ℕ → ℂ) (W : Finset ℝ),
        T₀ ≤ T → 1 ≤ M →
        (∀ n ∈ Finset.Icc M (2 * M), ‖a n‖ ≤ 1) →
        CGLProofDAG.OneSeparated W →
        ContainedInIntervalOfLength W T →
        differenceQuadraticForm a M W ≤
          C * Real.rpow T eta * heathBrownShape T M W := by
  obtain ⟨C, T₀, hC, hT₀, hbound⟩ := hcore eta heta
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T M a W hT hM ha hsep hinterval
  exact (differenceQuadraticForm_le_oneCoefficient M W ha).trans
    (hbound T M W hT hM hsep hinterval)

/-- The coefficient-one core implies the full `T^{o(1)}`-coefficient form of
the published theorem.  Choosing the input coefficient budget `eta/4` pays
exactly `eta/2` after squaring; the remaining `eta/2` is assigned to the
coefficient-one analytic estimate. -/
theorem heathBrownTheorem16_of_oneCoefficientCore
    (hcore : HeathBrownOneCoefficientCore) : HeathBrownTheorem16 := by
  intro eta heta
  have hetaHalf : 0 < eta / 2 := by positivity
  obtain ⟨C, T₀, hC, hT₀, hbound⟩ := hcore (eta / 2) hetaHalf
  refine ⟨eta / 4, C, T₀, by positivity, hC, hT₀, ?_⟩
  intro T M a W hT hM ha hsep hinterval
  have hTone : 1 ≤ T := by linarith
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hTone
  have hTnonneg : 0 ≤ T := le_trans (by norm_num) hTone
  have hscaleNonneg : 0 ≤ Real.rpow T (eta / 4) :=
    Real.rpow_nonneg hTnonneg _
  have hmajorant :
      differenceQuadraticForm a M W ≤
        differenceQuadraticForm
          (fun _ => (Real.rpow T (eta / 4) : ℂ)) M W :=
    differenceQuadraticForm_majorant M W ha
  have hone := hbound T M W hT hM hsep hinterval
  have hpowSquare :
      Real.rpow T (eta / 4) ^ 2 = Real.rpow T (eta / 2) := by
    calc
      Real.rpow T (eta / 4) ^ 2 =
          Real.rpow T ((eta / 4) * (2 : ℝ)) := by
        simpa using
          (Real.rpow_mul_natCast hTnonneg (eta / 4) 2).symm
      _ = Real.rpow T (eta / 2) := by ring_nf
  have hpowProduct :
      Real.rpow T (eta / 4) ^ 2 * Real.rpow T (eta / 2) =
        Real.rpow T eta := by
    calc
      Real.rpow T (eta / 4) ^ 2 * Real.rpow T (eta / 2) =
          Real.rpow T (eta / 2) * Real.rpow T (eta / 2) := by
        rw [hpowSquare]
      _ = Real.rpow T (eta / 2 + eta / 2) :=
        (Real.rpow_add hTpos (eta / 2) (eta / 2)).symm
      _ = Real.rpow T eta := by ring_nf
  calc
    differenceQuadraticForm a M W ≤
        differenceQuadraticForm
          (fun _ => (Real.rpow T (eta / 4) : ℂ)) M W := hmajorant
    _ = Real.rpow T (eta / 4) ^ 2 *
        differenceQuadraticForm (fun _ => (1 : ℂ)) M W := by
      rw [differenceQuadraticForm_constant]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hscaleNonneg]
    _ ≤ Real.rpow T (eta / 4) ^ 2 *
        (C * Real.rpow T (eta / 2) * heathBrownShape T M W) := by
      exact mul_le_mul_of_nonneg_left hone (sq_nonneg _)
    _ = C * Real.rpow T eta * heathBrownShape T M W := by
      rw [← hpowProduct]
      ring
    _ = C * Real.rpow T eta *
        ((W.card : ℝ) ^ 2 * M +
          (W.card : ℝ) * (M : ℝ) ^ 2 +
          Real.rpow (W.card : ℝ) (5 / 4 : ℝ) *
            Real.rpow T (1 / 2 : ℝ) * M) := by
      rfl

end

end GuthMaynardHeathBrownMajorant

#print axioms GuthMaynardHeathBrownMajorant.complexGramQuadratic_eq_expanded
#print axioms GuthMaynardHeathBrownMajorant.gram_majorant_principle
#print axioms GuthMaynardHeathBrownMajorant.dirichletPhase_difference
#print axioms GuthMaynardHeathBrownMajorant.differenceQuadraticForm_majorant
#print axioms GuthMaynardHeathBrownMajorant.differenceQuadraticForm_le_oneCoefficient
#print axioms GuthMaynardHeathBrownMajorant.differenceQuadraticForm_const_mul
#print axioms GuthMaynardHeathBrownMajorant.unitCoefficient_differenceMeanSquare_of_oneCoefficientCore
#print axioms GuthMaynardHeathBrownMajorant.heathBrownTheorem16_of_oneCoefficientCore
