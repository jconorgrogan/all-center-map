import MontgomeryPoweredSourceExponentLedger

/-!
# Mixed fourth/second moment route with a full-scale mollifier

Source: Montgomery--Vaughan, Multiplicative Number Theory III, §28.4.1,
pp. 195--197, author-hosted Vol3.pdf. Their choice K=H removes the short
shell obstruction. This is a different parameter choice from Montgomery
1971 p.110. The finite inequality below retains the mollifier second
moment instead of replacing its norm by its pointwise square-root bound.
No zero-density theorem is assumed or asserted here.
-/
namespace MAPMontgomeryMixedMomentLowStrip
open scoped BigOperators
open MAPMontgomeryPoweredSourceExponentLedger MAPMontgomeryLowStrip

/-- The mixed-moment counting inequality behind the source's Holder 4/3
step. It follows from two Cauchy inequalities and retains both moments. -/
theorem finite_mixed_fourth_second_count
    {ι : Type*} (S : Finset ι) (L M : ι → ℝ) {V : ℝ}
    (hV : 0 ≤ V) (hL : ∀ i ∈ S, 0 ≤ L i)
    (hM : ∀ i ∈ S, 0 ≤ M i)
    (hlarge : ∀ i ∈ S, V ≤ L i * M i) :
    (S.card : ℝ)^3 * V^4 ≤
      (∑ i ∈ S, L i ^ 4) * (∑ i ∈ S, M i ^ 2)^2 := by
  have hc : 0 ≤ (S.card : ℝ) := by positivity
  have hA : 0 ≤ ∑ i ∈ S, L i ^ 2 := Finset.sum_nonneg fun i hi => sq_nonneg _
  have hB : 0 ≤ ∑ i ∈ S, M i ^ 2 := Finset.sum_nonneg fun i hi => sq_nonneg _
  have hsum : (S.card : ℝ) * V ≤ ∑ i ∈ S, L i * M i := by
    simpa using Finset.sum_le_sum hlarge
  have hsum0 : 0 ≤ ∑ i ∈ S, L i * M i :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hL i hi) (hM i hi)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S L M
  have hcs2 := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ))
    (fun i => L i ^ 2)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
    ← pow_mul] at hcs2
  have hfirst : ((S.card : ℝ) * V)^2 ≤
      (∑ i ∈ S, L i ^ 2) * (∑ i ∈ S, M i ^ 2) := by
    exact (pow_le_pow_left₀ (mul_nonneg hc hV) hsum 2).trans hcs
  have hsquare := pow_le_pow_left₀ (sq_nonneg ((S.card : ℝ) * V)) hfirst 2
  have hmul := mul_le_mul_of_nonneg_right hcs2 (sq_nonneg (∑ i ∈ S, M i ^ 2))
  by_cases hz : (S.card : ℝ) = 0
  · simp [hz]; positivity
  · have hpos : 0 < (S.card : ℝ) := lt_of_le_of_ne hc (Ne.symm hz)
    apply (mul_le_mul_iff_right₀ hpos).mp
    nlinarith only [hsquare, hmul]

/-- Taking X=qT puts every extracted Type-I shell above scale exponent 1;
ordinary hybrid mean square now handles both terms without powering. -/
theorem fullScale_typeI_hybrid_exponent_le
    {sigma d : ℝ} (ht : sigma ≤ 1)
    (hd : 1 ≤ d) (hY : d ≤ sourceYExponent sigma) :
    1 + d * (1 - 2 * sigma) ≤ inghamExponent sigma ∧
      d * (2 * (1 - sigma)) ≤ inghamExponent sigma := by
  have hterminal := powered_length_exponent_eq_ingham (by linarith : sigma < 2)
  constructor
  · have hcompare : 1 + d * (1 - 2 * sigma) ≤ d * (2 * (1-sigma)) := by
      nlinarith
    apply hcompare.trans
    rw [← hterminal]
    exact mul_le_mul_of_nonneg_right hY (by linarith)
  · rw [← hterminal]
    exact mul_le_mul_of_nonneg_right hY (by linarith)

/-- With mollifier length X=qT, fourth moment scale qT and mollifier
second moment scale qT, the cubic count budget has exactly three times
the Ingham exponent. -/
theorem fullScale_typeII_cubic_exponent_eq
    {sigma : ℝ} (hs : sigma < 2) :
    sourceYExponent sigma * (2 - 4 * sigma) + 3 =
      3 * inghamExponent sigma := by
  rw [inghamExponent_eq]
  unfold sourceYExponent
  have h : 2-sigma ≠ 0 := by linarith
  field_simp
  <;> ring
/-- Literal power normalization of the optimized cubic count budget. -/
theorem fullScale_typeII_power_balance
    {S sigma : ℝ} (hS : 0 < S) (hsigma : sigma < 2) :
    Real.rpow (Real.rpow S (sourceYExponent sigma)) (2-4*sigma) * S^3 =
      (Real.rpow S (inghamExponent sigma))^3 := by
  calc
    _ = Real.rpow S (sourceYExponent sigma * (2-4*sigma)) * Real.rpow S 3 := by
      exact congrArg₂ (· * ·)
        (Real.rpow_mul hS.le (sourceYExponent sigma) (2-4*sigma)).symm
        (Real.rpow_natCast S 3).symm
    _ = Real.rpow S (sourceYExponent sigma * (2-4*sigma)+3) :=
      (Real.rpow_add hS _ _).symm
    _ = Real.rpow S (3*inghamExponent sigma) := by
      rw [fullScale_typeII_cubic_exponent_eq hsigma]
    _ = Real.rpow S (inghamExponent sigma*3) := by congr 1; ring
    _ = (Real.rpow S (inghamExponent sigma))^3 := by
      exact Real.rpow_mul_natCast hS.le (inghamExponent sigma) 3

end MAPMontgomeryMixedMomentLowStrip
#print axioms MAPMontgomeryMixedMomentLowStrip.finite_mixed_fourth_second_count
#print axioms MAPMontgomeryMixedMomentLowStrip.fullScale_typeI_hybrid_exponent_le
#print axioms MAPMontgomeryMixedMomentLowStrip.fullScale_typeII_cubic_exponent_eq

#print axioms MAPMontgomeryMixedMomentLowStrip.fullScale_typeII_power_balance
