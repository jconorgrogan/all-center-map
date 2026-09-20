import GuthMaynardLemma62NegativeNonstationary

/-!
# Infinite far-tail closure for Guth--Maynard Lemma 6.2

The finite source estimate already has a tail bound independent of the upper
cutoff.  This file proves absolute summability of the literal positive and
negative tails and passes to their `tsum`s.  Thus no informal
"let the truncation tend to infinity" step remains in Lemma 6.2.
-/

namespace GuthMaynardLemma62InfiniteTail

open Real Complex Set MeasureTheory
open scoped BigOperators
open GuthMaynardLemma62FarTail
open GuthMaynardLemma62NegativeNonstationary
open GuthMaynardSectionThreeCutoffDerivativeBudget
open GuthMaynardLemma62AbsoluteMellinTail

noncomputable section

def positiveFourierTail (t N : ℝ) (M i : ℕ) : ℂ :=
  sectionThreeFourierCoefficient t
    (((M + (i + 1 : ℕ) : ℕ) : ℝ) * N)

def negativeFourierTail (t N : ℝ) (M i : ℕ) : ℂ :=
  sectionThreeFourierCoefficient t
    (-(((M + (i + 1 : ℕ) : ℕ) : ℝ) * N))

theorem summable_norm_positiveFourierTail
    (t : ℝ) {N : ℝ} (hN : 0 < N) {M j : ℕ}
    (hM : 1 ≤ M) (hj : 2 ≤ j) :
    Summable (fun i => ‖positiveFourierTail t N M i‖) := by
  apply summable_of_sum_range_le (fun i => norm_nonneg _)
  intro K
  simpa [positiveFourierTail] using
    (finite_signed_fourier_tail_le t hN (M := M) (K := K) hM hj 1 (by simp))

theorem summable_norm_negativeFourierTail
    (t : ℝ) {N : ℝ} (hN : 0 < N) {M j : ℕ}
    (hM : 1 ≤ M) (hj : 2 ≤ j) :
    Summable (fun i => ‖negativeFourierTail t N M i‖) := by
  apply summable_of_sum_range_le (fun i => norm_nonneg _)
  intro K
  have h := finite_signed_fourier_tail_le
    t hN (M := M) (K := K) hM hj (-1) (by simp)
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  unfold negativeFourierTail
  congr 3
  ring

theorem summable_positiveFourierTail
    (t : ℝ) {N : ℝ} (hN : 0 < N) {M j : ℕ}
    (hM : 1 ≤ M) (hj : 2 ≤ j) :
    Summable (positiveFourierTail t N M) :=
  (summable_norm_positiveFourierTail t hN hM hj).of_norm

theorem summable_negativeFourierTail
    (t : ℝ) {N : ℝ} (hN : 0 < N) {M j : ℕ}
    (hM : 1 ≤ M) (hj : 2 ≤ j) :
    Summable (negativeFourierTail t N M) :=
  (summable_norm_negativeFourierTail t hN hM hj).of_norm

theorem norm_tsum_positiveFourierTail_le
    (t : ℝ) {N : ℝ} (hN : 0 < N) {M j : ℕ}
    (hM : 1 ≤ M) (hj : 2 ≤ j) :
    ‖∑' i, positiveFourierTail t N M i‖ ≤
      (lemma43DerivativeConstant j * (1 + |t|) ^ j *
          N ^ (-(j : ℝ))) *
        ((M : ℝ) ^ (1 - (j : ℝ)) / ((j : ℝ) - 1)) := by
  have hnorm := summable_norm_positiveFourierTail t hN hM hj
  refine (norm_tsum_le_tsum_norm hnorm).trans ?_
  apply Real.tsum_le_of_sum_range_le (fun i => norm_nonneg _)
  intro K
  simpa [positiveFourierTail] using
    (finite_signed_fourier_tail_le t hN (M := M) (K := K) hM hj 1 (by simp))

theorem norm_tsum_negativeFourierTail_le
    (t : ℝ) {N : ℝ} (hN : 0 < N) {M j : ℕ}
    (hM : 1 ≤ M) (hj : 2 ≤ j) :
    ‖∑' i, negativeFourierTail t N M i‖ ≤
      (lemma43DerivativeConstant j * (1 + |t|) ^ j *
          N ^ (-(j : ℝ))) *
        ((M : ℝ) ^ (1 - (j : ℝ)) / ((j : ℝ) - 1)) := by
  have hnorm := summable_norm_negativeFourierTail t hN hM hj
  refine (norm_tsum_le_tsum_norm hnorm).trans ?_
  apply Real.tsum_le_of_sum_range_le (fun i => norm_nonneg _)
  intro K
  have h := finite_signed_fourier_tail_le
    t hN (M := M) (K := K) hM hj (-1) (by simp)
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  unfold negativeFourierTail
  congr 3
  ring

/-- Infinite source-facing form of Guth--Maynard Lemma 6.2.  Both signs and
the complete absolutely summable far tail are present. -/
theorem norm_infinite_twoSided_coefficients_le_reflectedPolynomialIntegral
    (t : ℝ) {N R : ℝ} (hN : 0 < N) (hR : 0 < R) (htR : R < t)
    (J k ell : ℕ) (hk : 2 ≤ k) (hell : 2 ≤ ell) :
    ‖((∑ m ∈ Finset.Icc (1 : ℕ) (2 ^ J),
          sectionThreeFourierCoefficient t ((m : ℝ) * N)) +
        (∑ m ∈ Finset.Icc (1 : ℕ) (2 ^ J),
          sectionThreeFourierCoefficient t (-((m : ℝ) * N))) +
        (∑' i, positiveFourierTail t N (2 ^ J) i) +
        (∑' i, negativeFourierTail t N (2 ^ J) i))‖ ≤
      (∫ r : ℝ in Set.Ioc (-R) R,
        ((1 / (2 * Real.pi)) *
          ((J + 1) * (20 * Real.sqrt (8 * Real.pi) /
            Real.sqrt (t - R)))) *
          (‖mellin GuthMaynardSectionThreeCutoff.sectionThreeCutoff
              ((1 : ℂ) + r * Complex.I)‖ *
            ‖GuthMaynardLemma62FiniteFactorization.reflectedDirichletPolynomial
              (2 ^ J) (t - r)‖)) +
      ((1 / (2 * Real.pi)) *
          Real.log (2 * ((2 ^ J : ℕ) : ℝ)) * ((2 ^ J : ℕ) : ℝ)) *
        (2 * (((2 * Real.pi) ^ k *
          GuthMaynardLemma62AbsoluteMellinTail.sectionThreeMellinSeminorm k) *
          (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)))) +
      ((2 ^ J : ℕ) : ℝ) * (negativeSectorConstant / t) +
      2 * ((lemma43DerivativeConstant ell * (1 + |t|) ^ ell *
          N ^ (-(ell : ℝ))) *
        (((2 ^ J : ℕ) : ℝ) ^ (1 - (ell : ℝ)) /
          ((ell : ℝ) - 1))) := by
  let Base : ℂ :=
    (∑ m ∈ Finset.Icc (1 : ℕ) (2 ^ J),
      sectionThreeFourierCoefficient t ((m : ℝ) * N)) +
    (∑ m ∈ Finset.Icc (1 : ℕ) (2 ^ J),
      sectionThreeFourierCoefficient t (-((m : ℝ) * N)))
  let B : ℝ :=
    (lemma43DerivativeConstant ell * (1 + |t|) ^ ell *
      N ^ (-(ell : ℝ))) *
      (((2 ^ J : ℕ) : ℝ) ^ (1 - (ell : ℝ)) / ((ell : ℝ) - 1))
  have hM : 1 ≤ (2 ^ J : ℕ) := Nat.one_le_pow J 2 (by norm_num)
  have hbase :=
    norm_finite_twoSided_coefficients_le_reflectedPolynomialIntegral
      t hN hR htR J k hk
  have hpos := norm_tsum_positiveFourierTail_le
    t hN hM hell
  have hneg := norm_tsum_negativeFourierTail_le
    t hN hM hell
  have htri :
      ‖Base + (∑' i, positiveFourierTail t N (2 ^ J) i) +
          (∑' i, negativeFourierTail t N (2 ^ J) i)‖ ≤
        ‖Base‖ +
          ‖∑' i, positiveFourierTail t N (2 ^ J) i‖ +
          ‖∑' i, negativeFourierTail t N (2 ^ J) i‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  exact htri.trans (by
    calc
      ‖Base‖ + ‖∑' i, positiveFourierTail t N (2 ^ J) i‖ +
          ‖∑' i, negativeFourierTail t N (2 ^ J) i‖ ≤
        ((∫ r : ℝ in Set.Ioc (-R) R,
          ((1 / (2 * Real.pi)) *
            ((J + 1) * (20 * Real.sqrt (8 * Real.pi) /
              Real.sqrt (t - R)))) *
            (‖mellin GuthMaynardSectionThreeCutoff.sectionThreeCutoff
                ((1 : ℂ) + r * Complex.I)‖ *
              ‖GuthMaynardLemma62FiniteFactorization.reflectedDirichletPolynomial
                (2 ^ J) (t - r)‖)) +
        ((1 / (2 * Real.pi)) *
            Real.log (2 * ((2 ^ J : ℕ) : ℝ)) * ((2 ^ J : ℕ) : ℝ)) *
          (2 * (((2 * Real.pi) ^ k *
            GuthMaynardLemma62AbsoluteMellinTail.sectionThreeMellinSeminorm k) *
            (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)))) +
        ((2 ^ J : ℕ) : ℝ) * (negativeSectorConstant / t)) + B + B :=
          add_le_add (add_le_add hbase hpos) hneg
      _ = _ := by ring)

end

end GuthMaynardLemma62InfiniteTail

#print axioms GuthMaynardLemma62InfiniteTail.summable_positiveFourierTail
#print axioms GuthMaynardLemma62InfiniteTail.summable_negativeFourierTail
#print axioms GuthMaynardLemma62InfiniteTail.norm_infinite_twoSided_coefficients_le_reflectedPolynomialIntegral
