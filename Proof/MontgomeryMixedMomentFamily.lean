import MontgomeryMixedMomentIntegral
namespace MAPMontgomeryMixedMomentFamily
open scoped BigOperators
open MeasureTheory
open MAPMontgomeryMixedMomentIntegral MAPMRTCorollary25Minkowski
noncomputable section

theorem finite_count_of_mixed_products
    {ι : Type*} (S : Finset ι) (A B C : ι → ℝ) {V W : ℝ}
    (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hA : ∀ i ∈ S, 0 ≤ A i) (hB : ∀ i ∈ S, 0 ≤ B i)
    (hlarge : ∀ i ∈ S, V^2 ≤ A i * B i)
    (hfourth : ∀ i ∈ S, A i^2 ≤ W * C i) :
    (S.card : ℝ)^3 * V^4 ≤ W * (∑ i ∈ S, C i) * (∑ i ∈ S, B i)^2 := by
  have hc : 0 ≤ (S.card : ℝ) := by positivity
  have hsum : (S.card : ℝ) * V ≤ ∑ i ∈ S, Real.sqrt (A i) * Real.sqrt (B i) := by
    have hpoint : ∀ i ∈ S, V ≤ Real.sqrt (A i) * Real.sqrt (B i) := by
      intro i hi
      have hs : (Real.sqrt (A i) * Real.sqrt (B i))^2 = A i * B i := by
        rw [mul_pow, Real.sq_sqrt (hA i hi), Real.sq_sqrt (hB i hi)]
      have hn : 0 ≤ Real.sqrt (A i) * Real.sqrt (B i) := by positivity
      nlinarith [hlarge i hi]
    simpa using Finset.sum_le_sum hpoint
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S
    (fun i => Real.sqrt (A i)) (fun i => Real.sqrt (B i))
  have hAe : (∑ i ∈ S, Real.sqrt (A i)^2) = ∑ i ∈ S, A i :=
    Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (hA i hi))
  have hBe : (∑ i ∈ S, Real.sqrt (B i)^2) = ∑ i ∈ S, B i :=
    Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (hB i hi))
  rw [hAe,hBe] at hcs
  have hfirst := (pow_le_pow_left₀ (mul_nonneg hc hV) hsum 2).trans hcs
  have hfirstSq := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
  have hcs2 := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) A
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs2
  have hsum4 : (∑ i ∈ S, A i^2) ≤ W * ∑ i ∈ S, C i := by
    simpa only [Finset.mul_sum] using Finset.sum_le_sum hfourth
  have hsecond := hcs2.trans (mul_le_mul_of_nonneg_left hsum4 hc)
  have hmul := mul_le_mul_of_nonneg_right hsecond (sq_nonneg (∑ i ∈ S, B i))
  by_cases hz : (S.card : ℝ) = 0
  · have he : S = ∅ := Finset.card_eq_zero.mp (by exact_mod_cast hz)
    simp [he]
  · apply (mul_le_mul_iff_right₀ (lt_of_le_of_ne hc (Ne.symm hz))).mp
    nlinarith only [hfirstSq, hmul]

/-- Family-level retained-integral counting bound. The same weight is used
on every row, and the actual L-fourth and mollifier-second integrals are
summed before any global moment budget is applied. -/
theorem integral_family_mixed_count
    {ι : Type*} (S : Finset ι) (w : ℝ → ℝ) (L M : ι → ℝ → ℝ)
    (hw : Continuous w) (hL : ∀ i ∈ S, Continuous (L i))
    (hM : ∀ i ∈ S, Continuous (M i))
    {a b V : ℝ} (hab : a ≤ b) (hV : 0 ≤ V) (hw0 : ∀ u, 0 ≤ w u)
    (hW : 0 < ∫ u in a..b, w u)
    (hlarge : ∀ i ∈ S, V ≤ ∫ u in a..b, w u * (L i u * M i u)) :
    (S.card : ℝ)^3 * V^4 ≤
      (∫ u in a..b, w u) *
      (∑ i ∈ S, ∫ u in a..b, w u * L i u^4) *
      (∑ i ∈ S, ∫ u in a..b, w u * M i u^2)^2 := by
  apply finite_count_of_mixed_products S
    (fun i => ∫ u in a..b, w u * L i u^2)
    (fun i => ∫ u in a..b, w u * M i u^2)
    (fun i => ∫ u in a..b, w u * L i u^4) hV hW.le
  · intro i hi
    exact intervalIntegral.integral_nonneg hab (fun u hu => mul_nonneg (hw0 u) (sq_nonneg _))
  · intro i hi
    exact intervalIntegral.integral_nonneg hab (fun u hu => mul_nonneg (hw0 u) (sq_nonneg _))
  · intro i hi
    exact (pow_le_pow_left₀ hV (hlarge i hi) 2).trans
      (intervalIntegral_weighted_product_sq_le hw (hL i hi) (hM i hi) hab hw0)
  · intro i hi
    simpa only [Pi.pow_apply, ← pow_mul] using
      intervalIntegral_weighted_sq_le hw ((hL i hi).pow 2) hab hw0 hW
/-- Uniform detector normalization can be retained outside the mixed moments. -/
theorem integral_family_mixed_count_scaled
    {ι : Type*} (S : Finset ι) (w : ℝ → ℝ) (L M : ι → ℝ → ℝ)
    (hw : Continuous w) (hL : ∀ i ∈ S, Continuous (L i))
    (hM : ∀ i ∈ S, Continuous (M i))
    {a b V C : ℝ} (hab : a ≤ b) (hV : 0 ≤ V) (hw0 : ∀ u, 0 ≤ w u)
    (hW : 0 < ∫ u in a..b, w u)
    (hlarge : ∀ i ∈ S, V ≤ C * ∫ u in a..b, w u * (L i u * M i u)) :
    (S.card : ℝ)^3 * V^4 ≤ C^4 *
      (∫ u in a..b, w u) *
      (∑ i ∈ S, ∫ u in a..b, w u * L i u^4) *
      (∑ i ∈ S, ∫ u in a..b, w u * M i u^2)^2 := by
  have h := integral_family_mixed_count S w (fun i u => C * L i u) M hw
    (fun i hi => (hL i hi).const_mul C) hM hab hV hw0 hW
    (by
      intro i hi
      have heq : (fun u => w u * ((C * L i u) * M i u)) =
          (fun u => C * (w u * (L i u * M i u))) := by funext u; ring
      rw [heq, intervalIntegral.integral_const_mul]
      exact hlarge i hi)
  have heq : (∑ i ∈ S, ∫ u in a..b, w u * (C * L i u)^4) =
      C^4 * ∑ i ∈ S, ∫ u in a..b, w u * L i u^4 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have heq : (fun u => w u * (C * L i u)^4) =
        (fun u => C^4 * (w u * L i u^4)) := by funext u; ring
    rw [heq, intervalIntegral.integral_const_mul]
  rw [heq] at h
  nlinarith only [h]

end
end MAPMontgomeryMixedMomentFamily
#print axioms MAPMontgomeryMixedMomentFamily.integral_family_mixed_count
