import JutilaLemma6PrefixMainTail
import JutilaP53CoefficientQuotient
import JutilaLemma6LowerWeld

/-! Exact identification of the common p.53 polynomial with the Lemma 6
finite detector, including removal of zero pseudocharacter columns. The
signed main-term identity is derived from the literal convergent series. -/
namespace MAPJutilaLemma6DetectorIdentity
open scoped BigOperators
open MAPJutilaLemma6PrefixMainTail MAPJutilaLemma6DirectTail
open MAPJutilaP53CoefficientQuotient MAPJutilaP53AggregateCorrelationLeaf
open MAPJutilaP53PseudocharacterExactBridge
noncomputable section

def detectorColumns (z1 : ℝ) (S : Finset ℕ) (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun n =>
    z1 < (n : ℝ) ∧ jutilaP53PseudoReal S n ≠ 0

theorem detectedCoefficient_mul_phase {q : ℕ}
    (row : JutilaP53Row q) (z1 z2 alpha X : ℝ) (S : Finset ℕ)
    {n : ℕ} (hn : n ≠ 0) :
    jutilaP53DetectedCoefficient z1 z2 alpha X S n *
        jutilaP53Phase alpha row n =
      jutilaLemmaSixDirectTerm row.character z1 z2 S row.zero X n := by
  have hpseudo : jutilaWeightedPseudocharacter S n =
      (jutilaP53PseudoReal S n : ℂ) :=
    jutilaP53WeightedPseudocharacter_eq_ofReal S n
  have hpow : (n : ℂ) ^ (-row.zero) =
      (n : ℂ) ^ (-(alpha : ℂ)) *
        (n : ℂ) ^ (-(row.zero - (alpha : ℂ))) := by
    rw [← Complex.cpow_add _ _ (by exact_mod_cast hn)]
    congr 1
    ring
  have hrpow : (Real.rpow (n : ℝ) (-alpha) : ℂ) = (n : ℂ) ^ (-(alpha : ℂ)) := by
    simpa using (Complex.ofReal_cpow (Nat.cast_nonneg n) (-alpha))
  unfold jutilaP53DetectedCoefficient jutilaP53DetectedCoefficientReal
    jutilaP53Phase jutilaLemmaSixDirectTerm
  simp only [hn, ↓reduceIte, Complex.ofReal_mul,
    hrpow, hpseudo, hpow]
  ring

theorem polynomial_eq_finiteDetector {q : ℕ}
    (row : JutilaP53Row q) {z1 : ℝ} (hz1 : 0 ≤ z1)
    (z2 alpha X : ℝ) (S : Finset ℕ) (x : ℕ) :
    (∑ n ∈ detectorColumns z1 S x,
      jutilaP53DetectedCoefficient z1 z2 alpha X S n *
        jutilaP53Phase alpha row n) =
      jutilaLemmaSixFiniteDetector row.character z1 z2 S row.zero X x := by
  classical
  unfold detectorColumns jutilaLemmaSixFiniteDetector
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hz : z1 < (n : ℝ)
  · have hn0 : n ≠ 0 := by intro h; subst n; norm_num at hz; linarith
    by_cases hp : jutilaP53PseudoReal S n = 0
    · have hzero : jutilaWeightedPseudocharacter S n = 0 := by
        rw [show jutilaWeightedPseudocharacter S n =
          (jutilaP53PseudoReal S n : ℂ) from
          jutilaP53WeightedPseudocharacter_eq_ofReal S n, hp]
        rfl
      simp [hz, hp, jutilaLemmaSixDirectTerm, hzero]
    · simp only [hz, Ne, hp, not_false_eq_true, and_self, ↓reduceIte]
      exact detectedCoefficient_mul_phase row z1 z2 alpha X S hn0
  · simp [hz]

/-- The main term has a minus sign for the unnegated source polynomial.
This is an unconditional algebraic identity, not an assumed detector formula. -/
theorem polynomial_eq_neg_main_add_series_sub_tail {q : ℕ}
    (row : JutilaP53Row q) {z1 z2 : ℝ}
    (hz1 : 1 < z1) (hz12 : z1 < z2)
    (alpha : ℝ) {S : Finset ℕ} {R : ℕ} (hS : S ⊆ Finset.Icc 1 R)
    (hrho : 0 ≤ row.zero.re) {X : ℝ} (hX : 0 < X)
    {x : ℕ} (hx : 1 ≤ x) :
    (∑ n ∈ detectorColumns z1 S x,
      jutilaP53DetectedCoefficient z1 z2 alpha X S n *
        jutilaP53Phase alpha row n) =
      -((Real.exp (-(1 / X)) : ℂ) * ∑ r ∈ S, (r : ℂ)⁻¹) +
      ((∑' n : ℕ, jutilaLemmaSixDirectTerm row.character z1 z2 S row.zero X n) -
       ∑' k : ℕ, jutilaLemmaSixDirectTerm row.character z1 z2 S row.zero X
         (k + (x + 1))) := by
  rw [polynomial_eq_finiteDetector row (by linarith) z2 alpha X S x,
    jutilaLemmaSixDirectSeries_eq_main_add_detector_add_tail
      row.character hz1 hz12 hS hrho hX hx]
  ring

/-- Canonical positive-main identity, with the necessary global minus sign
made explicit. Negation preserves the Halasz polynomial's norm. -/
theorem neg_canonical_polynomial_eq_main_add_error {q : ℕ}
    (row : JutilaP53Row q) {z1 z2 : ℝ}
    (hz1 : 1 < z1) (hz12 : z1 < z2)
    (alpha : ℝ) (R : ℕ) (hrho : 0 ≤ row.zero.re)
    {X : ℝ} (hX : 0 < X) {x : ℕ} (hx : 1 ≤ x) :
    -(∑ n ∈ detectorColumns z1
        (MAPJutilaPseudocharacterHarmonicLower.jutilaPrimedRSet q R) x,
      jutilaP53DetectedCoefficient z1 z2 alpha X
        (MAPJutilaPseudocharacterHarmonicLower.jutilaPrimedRSet q R) n *
      jutilaP53Phase alpha row n) =
      (MAPJutilaLemma6LowerWeld.lemmaSixMain X q R : ℂ) +
      ((∑' k : ℕ, jutilaLemmaSixDirectTerm row.character z1 z2
          (MAPJutilaPseudocharacterHarmonicLower.jutilaPrimedRSet q R)
          row.zero X (k + (x + 1))) -
       ∑' n : ℕ, jutilaLemmaSixDirectTerm row.character z1 z2
          (MAPJutilaPseudocharacterHarmonicLower.jutilaPrimedRSet q R)
          row.zero X n) := by
  rw [polynomial_eq_finiteDetector row (by linarith) z2 alpha X,
    jutilaCanonicalDirectSeries_eq_main_add_detector_add_tail
      row.character hz1 hz12 R hrho hX hx]
  simp only [MAPJutilaLemma6LowerWeld.lemmaSixMain, Complex.ofReal_mul]
  ring

end
end MAPJutilaLemma6DetectorIdentity
#print axioms MAPJutilaLemma6DetectorIdentity.polynomial_eq_neg_main_add_series_sub_tail
