import GuthMaynardLemma118FractionPackingWeld
import GuthMaynardRatioKernelIdentity

/-!
# Energy packing in Guth--Maynard Lemma 11.8

This file proves the measure-theoretic step after local constancy and rational
separation.  A nonnegative field sampled on a separated finite family is
controlled by its continuous mass, with exactly the interval-packing
multiplicity.  This is the source-faithful bridge used in Lemma 11.8 before
the final Cauchy--Schwarz estimate.
-/

open scoped BigOperators
open MeasureTheory Set

namespace GuthMaynardLemma118

noncomputable section

/-- The collar of radius `r` around a sample location. -/
def sampleCollar {ι : Type*} (x : ι → ℝ) (r : ℝ) (i : ι) : Set ℝ :=
  {v | |x i - v| ≤ r}

/-- At a fixed point, the sum of collar indicators is the number of sample
locations whose collars contain that point. -/
theorem sum_indicator_sampleCollar_eq_card_filter
    {ι : Type*} [DecidableEq ι] (P : Finset ι) (x : ι → ℝ)
    (r v : ℝ) (F : ℝ → ℝ) :
    (∑ i ∈ P, (sampleCollar x r i).indicator F v) =
      ((P.filter fun i => |x i - v| ≤ r).card : ℝ) * F v := by
  classical
  simp only [sampleCollar, Set.mem_setOf_eq, Set.indicator_apply]
  calc
    (∑ i ∈ P, if |x i - v| ≤ r then F v else 0) =
        ∑ i ∈ P, (if |x i-v| ≤ r then (1:ℝ) else 0) * F v := by
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> ring
    _ = (∑ i ∈ P, if |x i-v| ≤ r then (1:ℝ) else 0) * F v := by
      rw [Finset.sum_mul]
    _ = ((P.filter fun i => |x i-v| ≤ r).card : ℝ) * F v := by
      rw [Finset.sum_boole]

/-- The exact finite-overlap estimate supplied by one-dimensional packing.
The hypotheses isolate only the already-certified separation geometry. -/
theorem sum_indicator_sampleCollar_le
    {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (x : ι → ℝ) {r δ : ℝ}
    (hr : 0 ≤ r) (hδ : 0 < δ)
    (hsep : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → δ ≤ |x i - x j|)
    (F : ℝ → ℝ) (hF : ∀ v, 0 ≤ F v) (v : ℝ) :
    (∑ i ∈ P, (sampleCollar x r i).indicator F v) ≤
      ((⌊(2 * r) / δ⌋₊ + 1 : ℕ) : ℝ) * F v := by
  classical
  let Q := P.filter fun i => |x i - v| ≤ r
  have hQmem : ∀ i ∈ Q, v - r ≤ x i ∧ x i ≤ v - r + 2 * r := by
    intro i hi
    have hiP := (Finset.mem_filter.mp hi).1
    have hic := abs_le.mp (Finset.mem_filter.mp hi).2
    constructor <;> linarith
  have hQsep : ∀ i ∈ Q, ∀ j ∈ Q, i ≠ j → δ ≤ |x i - x j| := by
    intro i hi j hj hij
    exact hsep i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hij
  have hcard : Q.card ≤ ⌊(2 * r) / δ⌋₊ + 1 :=
    card_le_natFloor_div_add_one_of_injective_map Q x (v-r) (2*r) δ
      hδ (by positivity) (by
        intro i hi j hj heq
        by_contra hij
        have hs := hQsep i hi j hj hij
        rw [heq, sub_self, abs_zero] at hs
        exact (not_le_of_gt hδ) hs) hQmem hQsep
  rw [sum_indicator_sampleCollar_eq_card_filter]
  change (Q.card : ℝ) * F v ≤ _
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hF v)

/-- Finite collar overlap can be integrated without losing anything beyond
the exact packing multiplicity. -/
theorem sum_integral_sampleCollar_le
    {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (x : ι → ℝ) {r δ : ℝ}
    (hr : 0 ≤ r) (hδ : 0 < δ)
    (hsep : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → δ ≤ |x i - x j|)
    (F : ℝ → ℝ) (hFint : Integrable F) (hF : ∀ v, 0 ≤ F v) :
    (∑ i ∈ P, ∫ v, (sampleCollar x r i).indicator F v) ≤
      ((⌊(2 * r) / δ⌋₊ + 1 : ℕ) : ℝ) * ∫ v, F v := by
  classical
  rw [← integral_finset_sum P]
  · calc
      (∫ v, ∑ i ∈ P, (sampleCollar x r i).indicator F v) ≤
          ∫ v, (((⌊(2*r)/δ⌋₊+1 : ℕ) : ℝ) * F v) := by
        apply integral_mono
        · exact integrable_finset_sum P (fun i _ =>
            hFint.indicator (measurableSet_le
              (continuous_abs.comp (continuous_const.sub continuous_id)).measurable
              measurable_const))
        · exact hFint.const_mul _
        · intro v
          exact sum_indicator_sampleCollar_le P x hr hδ hsep F hF v
      _ = ((⌊(2 * r) / δ⌋₊ + 1 : ℕ) : ℝ) * ∫ v, F v :=
        integral_const_mul _ _
  · intro i hi
    exact hFint.indicator (measurableSet_le
      (continuous_abs.comp (continuous_const.sub continuous_id)).measurable
      measurable_const)

/-- Local constancy plus separated collar packing.  This is the precise
analytic/geometric core of the first display in Lemma 11.8: the only remaining
input is the pointwise local-constancy inequality itself. -/
theorem sum_samples_le_packing_mul_integral
    {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (x : ι → ℝ) {r δ C : ℝ}
    (hr : 0 ≤ r) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hsep : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → δ ≤ |x i - x j|)
    (F : ℝ → ℝ) (hFint : Integrable F) (hF : ∀ v, 0 ≤ F v)
    (hlocal : ∀ i ∈ P,
      F (x i) ≤ C * ∫ v, (sampleCollar x r i).indicator F v) :
    (∑ i ∈ P, F (x i)) ≤
      C * ((⌊(2 * r) / δ⌋₊ + 1 : ℕ) : ℝ) * ∫ v, F v := by
  calc
    (∑ i ∈ P, F (x i)) ≤
        ∑ i ∈ P, C * ∫ v, (sampleCollar x r i).indicator F v := by
      exact Finset.sum_le_sum fun i hi => hlocal i hi
    _ = C * (∑ i ∈ P, ∫ v, (sampleCollar x r i).indicator F v) := by
      rw [Finset.mul_sum]
    _ ≤ C * (((⌊(2 * r) / δ⌋₊ + 1 : ℕ) : ℝ) * ∫ v, F v) :=
      mul_le_mul_of_nonneg_left
        (sum_integral_sampleCollar_le P x hr hδ hsep F hFint hF) hC
    _ = C * ((⌊(2 * r) / δ⌋₊ + 1 : ℕ) : ℝ) * ∫ v, F v := by ring

/-- Rational specialization of the packing-energy bridge.  The denominator
box and cross-product hypotheses are exactly the reduced-fraction data used
in Guth--Maynard Lemma 11.8. -/
theorem sum_rational_samples_le_packing_mul_integral
    (P : Finset (ℕ × ℕ)) {B r C : ℝ}
    (hB : 0 < B) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hden : ∀ p ∈ P, 0 < p.2 ∧ (p.2 : ℝ) ≤ B)
    (hcross : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      p.1 * q.2 ≠ q.1 * p.2)
    (F : ℝ → ℝ) (hFint : Integrable F) (hF : ∀ v, 0 ≤ F v)
    (hlocal : ∀ p ∈ P,
      F ((p.1 : ℝ) / (p.2 : ℝ)) ≤
        C * ∫ v, (sampleCollar
          (fun z : ℕ × ℕ => (z.1 : ℝ) / (z.2 : ℝ)) r p).indicator F v) :
    (∑ p ∈ P, F ((p.1 : ℝ) / (p.2 : ℝ))) ≤
      C * ((⌊(2 * r) * B ^ 2⌋₊ + 1 : ℕ) : ℝ) * ∫ v, F v := by
  let x : ℕ × ℕ → ℝ := fun p => (p.1 : ℝ) / (p.2 : ℝ)
  have hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      (1 : ℝ) / B ^ 2 ≤ |x p - x q| := by
    intro p hp q hq hpq
    exact GuthMaynardS3Source.distinct_nat_fraction_separation_of_denominator_le
      (hden p hp).1 (hden q hq).1 hB (hden p hp).2 (hden q hq).2
        (hcross p hp q hq hpq)
  have hδ : 0 < (1 : ℝ) / B ^ 2 := by positivity
  have hmain := sum_samples_le_packing_mul_integral P x hr hδ hC hsep
    F hFint hF hlocal
  have hscale : (2 * r) / ((1 : ℝ) / B ^ 2) = (2 * r) * B ^ 2 := by
    field_simp
  simpa [x, hscale] using hmain

/-- The continuous Cauchy--Schwarz step printed at the end of Lemma 11.8:
the cubic mass is bounded by the geometric mean of the second and fourth
moments. -/
theorem integral_cube_le_sqrt_mul_sqrt
    (F : ℝ → ℝ) (hFmeas : AEStronglyMeasurable F)
    (hF2 : Integrable (fun v => F v ^ 2))
    (hF4 : Integrable (fun v => F v ^ 4))
    (hF : ∀ v, 0 ≤ F v) :
    (∫ v, F v ^ 3) ≤
      Real.sqrt (∫ v, F v ^ 2) * Real.sqrt (∫ v, F v ^ 4) := by
  have hFm : MemLp F 2 volume :=
    (memLp_two_iff_integrable_sq hFmeas).2 hF2
  have hF2meas : AEStronglyMeasurable (fun v => F v ^ 2) := hFmeas.pow 2
  have hF2m : MemLp (fun v => F v ^ 2) 2 volume := by
    apply (memLp_two_iff_integrable_sq hF2meas).2
    convert hF4 using 1
    funext v
    ring
  have hpq : Real.HolderConjugate 2 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) hpq
    (Filter.Eventually.of_forall hF)
    (Filter.Eventually.of_forall fun v => sq_nonneg (F v))
    (by simpa using hFm) (by simpa using hF2m)
  simp only [Real.rpow_two, one_div] at hh
  have hrpow (x : ℝ) : x ^ (2 : ℝ)⁻¹ = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    norm_num
  rw [hrpow, hrpow] at hh
  have hcube : (fun v => F v * F v ^ 2) = (fun v => F v ^ 3) := by
    funext v
    ring
  have hfour : (fun v => (F v ^ 2) ^ 2) = (fun v => F v ^ 4) := by
    funext v
    ring
  rw [hcube, hfour] at hh
  exact hh

/-! ## The factored moment step in Lemma 11.9 -/

/-- Literal dyadic `p`-th moment of the ratio kernel. -/
def ratioKernelMoment (p M : ℕ) (W : Finset ℝ) : ℝ :=
  ∑ z ∈ (Finset.Icc M (2*M)).product (Finset.Icc M (2*M)),
    ‖GuthMaynardRatioKernelIdentity.ratioDirichletKernel W
      ((z.1 : ℝ) / (z.2 : ℝ))‖ ^ p

/-- The first displayed inequality in Lemma 11.9, before the second and
fourth moments are estimated.  This is finite Cauchy--Schwarz on the literal
ratio kernel, so no analytic premise is present. -/
theorem ratioKernelMoment_three_le_geometricMean
    (M : ℕ) (W : Finset ℝ) :
    ratioKernelMoment 3 M W ≤
      Real.sqrt (ratioKernelMoment 2 M W) *
        Real.sqrt (ratioKernelMoment 4 M W) := by
  let I := Finset.Icc M (2*M)
  let P := I.product I
  let K : ℕ × ℕ → ℝ := fun z =>
    ‖GuthMaynardRatioKernelIdentity.ratioDirichletKernel W
      ((z.1 : ℝ) / (z.2 : ℝ))‖
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt P K (fun z => K z ^ 2)
  have hthree (z : ℕ × ℕ) : K z * K z ^ 2 = K z ^ 3 := by ring
  have hfour (z : ℕ × ℕ) : (K z ^ 2) ^ 2 = K z ^ 4 := by ring
  simp_rw [hthree, hfour] at hcs
  dsimp only [P] at hcs
  dsimp only [I, K] at hcs
  simpa only [ratioKernelMoment] using hcs

/-- The second factor in the preceding geometric mean is the only new
fourth-moment object: the first factor is exactly Heath--Brown's
coefficient-one quadratic form. -/
theorem ratioKernelMoment_three_le_heathBrownFactor
    (M : ℕ) (W : Finset ℝ) (hM : 1 ≤ M) :
    ratioKernelMoment 3 M W ≤
      Real.sqrt
          (GuthMaynardHeathBrownInterface.differenceQuadraticForm
            (fun _ => (1 : ℂ)) M W) *
        Real.sqrt (ratioKernelMoment 4 M W) := by
  have heq :
      GuthMaynardHeathBrownInterface.differenceQuadraticForm
          (fun _ => (1 : ℂ)) M W = ratioKernelMoment 2 M W := by
    rw [GuthMaynardRatioKernelIdentity.differenceQuadraticForm_one_eq_ratioKernelSecondMoment
      M W hM]
    unfold ratioKernelMoment
    exact (Finset.sum_product (Finset.Icc M (2*M)) (Finset.Icc M (2*M))
      (fun z : ℕ × ℕ =>
        ‖GuthMaynardRatioKernelIdentity.ratioDirichletKernel W
          ((z.1 : ℝ) / (z.2 : ℝ))‖ ^ 2)).symm
  rw [heq]
  exact ratioKernelMoment_three_le_geometricMean M W

/-! ## The summation over gcd scales in Lemma 11.8 -/

/-- Elementary reciprocal-square budget used when summing the packing loss
`T + N²/d²` over `d ≤ D`.  The explicit constant `2` is more than enough for
the source's Vinogradov notation. -/
theorem sum_range_succ_inverse_square_le_two (D : ℕ) :
    (∑ k ∈ Finset.range D, (1 : ℝ) / ((k+1 : ℕ) : ℝ) ^ 2) ≤ 2 := by
  by_cases hD : D = 0
  · simp [hD]
  have hstrong : ∀ n : ℕ, 1 ≤ n →
      (∑ k ∈ Finset.range n, (1 : ℝ) / ((k+1 : ℕ) : ℝ) ^ 2) ≤
        2 - 1 / (n : ℝ) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
        rw [Finset.sum_range_succ]
        have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
        have hspos : (0 : ℝ) < n+1 := by positivity
        have hstep :
            (1 : ℝ) / ((n+1 : ℕ) : ℝ) ^ 2 ≤
              1 / (n : ℝ) - 1 / ((n+1 : ℕ) : ℝ) := by
          push_cast
          have hprodpos : 0 < (n:ℝ) * (n+1) := mul_pos hnpos hspos
          have hden : (n:ℝ) * (n+1) ≤ (n+1)^2 := by nlinarith
          calc
            (1:ℝ)/(n+1)^2 ≤ 1/((n:ℝ)*(n+1)) :=
              one_div_le_one_div_of_le hprodpos hden
            _ = 1/(n:ℝ)-1/(n+1) := by
              field_simp [hnpos.ne', hspos.ne']
              ring
        calc
          (∑ k ∈ Finset.range n, (1 : ℝ) / ((k+1 : ℕ) : ℝ) ^ 2) +
              1 / ((n+1 : ℕ) : ℝ) ^ 2 ≤
              (2 - 1/(n:ℝ)) + (1/(n:ℝ)-1/((n+1:ℕ):ℝ)) :=
            add_le_add ih hstep
          _ = 2 - 1/((n+1:ℕ):ℝ) := by ring
  have hDone := hstrong D (Nat.one_le_iff_ne_zero.mpr hD)
  have hnonneg : 0 ≤ 1 / (D : ℝ) := by positivity
  exact hDone.trans (by linarith)

/-- Exact summation of the per-`d` packing cost.  This is the quantitative
source step turning `Σ_{d≤D}(T+N²/d²)` into `D*T+O(N²)`. -/
theorem sum_gcd_scale_cost_le
    (D : ℕ) (A : ℕ → ℝ) {C T N I : ℝ}
    (hC : 0 ≤ C) (hI : 0 ≤ I)
    (hA : ∀ k ∈ Finset.range D,
      A (k+1) ≤ C * (T + N^2 / ((k+1 : ℕ) : ℝ)^2) * I) :
    (∑ k ∈ Finset.range D, A (k+1)) ≤
      C * ((D : ℝ) * T + 2 * N^2) * I := by
  let S : ℝ := ∑ k ∈ Finset.range D, (1:ℝ)/((k+1:ℕ):ℝ)^2
  have hsum :
      (∑ k ∈ Finset.range D,
          C * (T + N^2 / ((k+1 : ℕ) : ℝ)^2) * I) =
        C * ((D:ℝ)*T + N^2*S) * I := by
    dsimp [S]
    calc
      (∑ k ∈ Finset.range D,
          C * (T + N^2 / ((k+1 : ℕ) : ℝ)^2) * I) =
          (∑ k ∈ Finset.range D,
            C * (T + N^2 / ((k+1 : ℕ) : ℝ)^2)) * I := by
        exact (Finset.sum_mul (Finset.range D)
          (fun k => C * (T + N^2 / ((k+1 : ℕ) : ℝ)^2)) I).symm
      _ = C * (∑ k ∈ Finset.range D,
            (T + N^2 / ((k+1 : ℕ) : ℝ)^2)) * I := by
        rw [Finset.mul_sum]
      _ = C * ((∑ _k ∈ Finset.range D, T) +
            ∑ k ∈ Finset.range D, N^2 / ((k+1 : ℕ) : ℝ)^2) * I := by
        rw [Finset.sum_add_distrib]
      _ = C * ((D:ℝ)*T + N^2 *
            ∑ k ∈ Finset.range D, (1:ℝ)/((k+1:ℕ):ℝ)^2) * I := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [Finset.mul_sum]
        apply congrArg (fun x : ℝ => C * (↑D * T + x) * I)
        apply Finset.sum_congr rfl
        intro k hk
        ring
  have hS : S ≤ 2 := sum_range_succ_inverse_square_le_two D
  have hinside : (D:ℝ)*T + N^2*S ≤ (D:ℝ)*T + 2*N^2 := by
    have hmul : N^2*S ≤ N^2*2 :=
      mul_le_mul_of_nonneg_left hS (sq_nonneg N)
    nlinarith
  calc
    (∑ k ∈ Finset.range D, A (k+1)) ≤
        ∑ k ∈ Finset.range D,
          C * (T + N^2 / ((k+1 : ℕ) : ℝ)^2) * I :=
      Finset.sum_le_sum fun k hk => hA k hk
    _ = C * ((D:ℝ)*T + N^2*S) * I := hsum
    _ ≤ C * ((D:ℝ)*T + 2*N^2) * I := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinside hC) hI

end
end GuthMaynardLemma118

#print axioms GuthMaynardLemma118.sum_indicator_sampleCollar_eq_card_filter
#print axioms GuthMaynardLemma118.sum_indicator_sampleCollar_le
#print axioms GuthMaynardLemma118.sum_integral_sampleCollar_le
#print axioms GuthMaynardLemma118.sum_samples_le_packing_mul_integral
#print axioms GuthMaynardLemma118.sum_rational_samples_le_packing_mul_integral
#print axioms GuthMaynardLemma118.integral_cube_le_sqrt_mul_sqrt
#print axioms GuthMaynardLemma118.ratioKernelMoment_three_le_geometricMean
#print axioms GuthMaynardLemma118.ratioKernelMoment_three_le_heathBrownFactor
#print axioms GuthMaynardLemma118.sum_range_succ_inverse_square_le_two
#print axioms GuthMaynardLemma118.sum_gcd_scale_cost_le
