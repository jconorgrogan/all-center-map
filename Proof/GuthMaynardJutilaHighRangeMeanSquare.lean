import RecenteredSampling
import GuthMaynardLengthComparison

/-!
# The classical high-length branch of Jutila's second moment

For a fixed second ordinate, Jutila's weighted difference polynomial is an
ordinary Dirichlet polynomial with coefficient energy at most one.  The
already-certified finite Hilbert inequality therefore gives the classical
`R(T+M)` bound.  In the range `T ≤ M` this is `O(RM)`, which is the high/base
branch of Lemma 29.10.  The low/intermediate range is deliberately not claimed
here; it is where the reflection and powering argument is essential.
-/

namespace GuthMaynardJutilaHighRangeMeanSquare

open scoped BigOperators
open CGLProofDAG
open DiscreteMeanValueSourceLeaf
open GuthMaynardHeathBrownMajorant
open GuthMaynardLengthComparison

noncomputable section

def fixedRightCoefficient (u : ℝ) (n : ℕ) : ℂ :=
  (inverseSqrtWeight n : ℂ) * star (dirichletPhase n u)

theorem norm_fixedRightCoefficient (u : ℝ) (n : ℕ) :
    ‖fixedRightCoefficient u n‖ = inverseSqrtWeight n := by
  unfold fixedRightCoefficient dirichletPhase
  rw [norm_mul, norm_star, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, Real.exp_zero,
    mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (inverseSqrtWeight_nonneg n)

theorem inverseSqrtWeight_sq_eq_inv_natCast
    {n : ℕ} (hn : 0 < n) :
    inverseSqrtWeight n ^ 2 = ((n : ℝ))⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold inverseSqrtWeight
  rw [inv_pow, Real.sq_sqrt hnR.le]

theorem coefficientEnergy_fixedRight_le_one
    (M : ℕ) (hM : 1 ≤ M) (u : ℝ) :
    coefficientEnergy (fixedRightCoefficient u) M ≤ 1 := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  unfold coefficientEnergy
  calc
    (∑ n ∈ Finset.Ioc M (2 * M), ‖fixedRightCoefficient u n‖ ^ 2) ≤
        ∑ _n ∈ Finset.Ioc M (2 * M), ((M : ℝ))⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnM : M < n := (Finset.mem_Ioc.mp hn).1
      have hnpos : 0 < n := by omega
      rw [norm_fixedRightCoefficient, inverseSqrtWeight_sq_eq_inv_natCast hnpos]
      exact inv_anti₀ hMpos (by exact_mod_cast hnM.le)
    _ = (Finset.Ioc M (2 * M)).card * ((M : ℝ))⁻¹ := by simp
    _ = 1 := by
      rw [show (Finset.Ioc M (2 * M)).card = M by simp; omega]
      push_cast
      exact mul_inv_cancel₀ hMpos.ne'

theorem differenceGram_eq_dirichletPolynomial
    (M : ℕ) (t u : ℝ) :
    gramPolynomial (Finset.Ioc M (2 * M))
        (fun n => (inverseSqrtWeight n : ℂ)) dirichletPhase t u =
      dirichletPolynomial (fixedRightCoefficient u) M t := by
  unfold gramPolynomial dirichletPolynomial fixedRightCoefficient
  apply Finset.sum_congr rfl
  intro n hn
  have hphase :
      Complex.exp (Complex.I * ((t : ℂ) * (Real.log n : ℂ))) =
        dirichletPhase n t := by
    unfold dirichletPhase
    congr 1
    push_cast
    ring
  rw [hphase]
  ring

/-- The exact high-range estimate, with the finite Hilbert constant visible.
This theorem is assumption-free. -/
theorem jutilaSecondMoment_natCast_le_classical
    (T : ℝ) (M : ℕ) (W : Finset ℝ)
    (hT : 0 ≤ T) (hM : 1 ≤ M)
    (hsep : OneSeparated W)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T) :
    jutilaSecondMoment (M : ℝ) W ≤
      (W.card : ℝ) *
        (3 * (T + 1 +
          2 * Classical.choose
            MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert *
              (M : ℝ))) := by
  let hHilbert :=
    MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert
  have hmean (u : ℝ) := RecenteredSampling.discrete_meanSquare_raw_of_hilbert
    hHilbert T M (fixedRightCoefficient u) W hT hM hsep hheight
  have henergy (u : ℝ) := coefficientEnergy_fixedRight_le_one M hM u
  have hfactor0 : 0 ≤
      3 * (T + 1 + 2 * Classical.choose hHilbert * (M : ℝ)) := by
    have hC : 0 < Classical.choose hHilbert :=
      (Classical.choose_spec hHilbert).1
    positivity
  unfold jutilaSecondMoment realGramQuadratic
  rw [realDyadicIoc_natCast]
  calc
    (∑ t ∈ W, ∑ u ∈ W,
        ‖gramPolynomial (Finset.Ioc M (2 * M))
          (fun n => (inverseSqrtWeight n : ℂ)) dirichletPhase t u‖ ^ 2) =
      ∑ u ∈ W, ∑ t ∈ W,
        ‖dirichletPolynomial (fixedRightCoefficient u) M t‖ ^ 2 := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro u hu
          apply Finset.sum_congr rfl
          intro t ht
          rw [differenceGram_eq_dirichletPolynomial]
    _ ≤ ∑ _u ∈ W,
        3 * (T + 1 + 2 * Classical.choose hHilbert * (M : ℝ)) := by
      apply Finset.sum_le_sum
      intro u hu
      exact (hmean u).trans
        (mul_le_of_le_one_right hfactor0 (henergy u))
    _ = (W.card : ℝ) *
        (3 * (T + 1 + 2 * Classical.choose hHilbert * (M : ℝ))) := by simp

/-- Once the polynomial length dominates the aperture, the classical branch
has the source size `O(RM)`. -/
theorem jutilaSecondMoment_natCast_le_highRange
    (T : ℝ) (M : ℕ) (W : Finset ℝ)
    (hT : 0 ≤ T) (hM : 1 ≤ M) (hTM : T ≤ M)
    (hsep : OneSeparated W)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T) :
    jutilaSecondMoment (M : ℝ) W ≤
      (6 + 6 * Classical.choose
        MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert) *
        (W.card : ℝ) * M := by
  let hHilbert :=
    MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert
  have hC : 0 < Classical.choose hHilbert :=
    (Classical.choose_spec hHilbert).1
  have hbase := jutilaSecondMoment_natCast_le_classical T M W hT hM hsep hheight
  have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hinner :
      3 * (T + 1 + 2 * Classical.choose hHilbert * (M : ℝ)) ≤
        (6 + 6 * Classical.choose hHilbert) * (M : ℝ) := by
    nlinarith
  calc
    jutilaSecondMoment (M : ℝ) W ≤
        (W.card : ℝ) *
          (3 * (T + 1 + 2 * Classical.choose hHilbert * (M : ℝ))) := hbase
    _ ≤ (W.card : ℝ) *
          ((6 + 6 * Classical.choose hHilbert) * (M : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg _)
    _ = (6 + 6 * Classical.choose hHilbert) * (W.card : ℝ) * M := by ring

end

end GuthMaynardJutilaHighRangeMeanSquare

#print axioms GuthMaynardJutilaHighRangeMeanSquare.coefficientEnergy_fixedRight_le_one
#print axioms GuthMaynardJutilaHighRangeMeanSquare.jutilaSecondMoment_natCast_le_classical
#print axioms GuthMaynardJutilaHighRangeMeanSquare.jutilaSecondMoment_natCast_le_highRange
