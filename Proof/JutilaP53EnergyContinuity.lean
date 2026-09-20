import JutilaP53KernelExpansion
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Continuity of the literal p.53 smooth energy

The integrated p.53 source leaf must not exploit the convention that a
Bochner integral of a non-integrable function is zero.  This module proves
continuity of the actual infinite correlation energy on every legal compact
rectangle of logarithmic smoothing scales.  Interval integrability then
follows without an additional analytic assumption.
-/

namespace MAPJutilaP53EnergyContinuity

open scoped BigOperators
open Set
open MeasureTheory
open MAPJutilaP53AggregateCorrelationLeaf

noncomputable section

set_option maxHeartbeats 800000 in
theorem continuousOn_jutilaP53CorrelationEnergy_logScales
    {q R : ℕ} (rows : Finset (JutilaP53Row q))
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 R)
    {alpha xiLo xiHi upsLo upsHi : ℝ} (hcross : xiHi < upsLo)
    (eta : JutilaP53Row q → ℂ)
    (hrow : ∀ row ∈ rows, alpha ≤ row.zero.re)
    (heta : ∀ row ∈ rows, ‖eta row‖ = 1) :
    ContinuousOn
      (fun p : ℝ × ℝ =>
        jutilaP53CorrelationEnergy rows S alpha
          (Real.exp p.1) (Real.exp p.2) eta)
      (Icc xiLo xiHi ×ˢ Icc upsLo upsHi) := by
  let J : ℝ := rows.card
  let r : ℝ := Real.exp (-(1 / Real.exp upsHi))
  let u : ℕ → ℝ := fun n => (R : ℝ) ^ 2 * J ^ 2 * r ^ n
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrlt : r < 1 := by
    dsimp [r]
    have hinv : 0 < 1 / Real.exp upsHi := one_div_pos.mpr (Real.exp_pos _)
    have hneg : -(1 / Real.exp upsHi) < 0 := by linarith
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hneg
  have husum : Summable u := by
    have hgeo : Summable (fun n : ℕ => r ^ n) :=
      summable_geometric_of_norm_lt_one
        (show ‖r‖ < 1 by
          simpa [Real.norm_eq_abs, abs_of_pos hrpos] using hrlt)
    have hscaled := hgeo.mul_left ((R : ℝ) ^ 2 * J ^ 2)
    simpa [u, mul_assoc] using hscaled
  unfold jutilaP53CorrelationEnergy
  apply continuousOn_tsum
  · intro n
    apply Continuous.continuousOn
    unfold jutilaP53CorrelationWeight
    unfold MAPJutilaHalaszLargeValueFront.jutilaCorrelationWeight
    have hdivN : Continuous (fun p : ℝ × ℝ =>
        (n : ℝ) / Real.exp p.2) :=
      continuous_const.div
        (Real.continuous_exp.comp continuous_snd)
        (fun p => (Real.exp_pos p.2).ne')
    have hdivM : Continuous (fun p : ℝ × ℝ =>
        (n : ℝ) / Real.exp p.1) :=
      continuous_const.div
        (Real.continuous_exp.comp continuous_fst)
        (fun p => (Real.exp_pos p.1).ne')
    have hN : Continuous (fun p : ℝ × ℝ =>
        Real.exp (-((n : ℝ) / Real.exp p.2))) :=
      Real.continuous_exp.comp hdivN.neg
    have hMcont : Continuous (fun p : ℝ × ℝ =>
        Real.exp (-((n : ℝ) / Real.exp p.1))) :=
      Real.continuous_exp.comp hdivM.neg
    exact (continuous_const.mul (hN.sub hMcont)).mul continuous_const
  · exact husum
  · intro n p hp
    rcases hp with ⟨hxi, hups⟩
    have hpCross : p.1 < p.2 := hxi.2.trans_lt (hcross.trans_le hups.1)
    have hM : 0 < Real.exp p.1 := Real.exp_pos _
    have hMN : Real.exp p.1 < Real.exp p.2 := Real.exp_lt_exp.mpr hpCross
    have hw0 := jutilaP53CorrelationWeight_nonneg S hM hMN n
    have hw := jutilaP53CorrelationWeight_le_geometric
      (n := n) hS hM hMN
    have hexpBase : Real.exp (-(1 / Real.exp p.2)) ≤ r := by
      have hden : Real.exp p.2 ≤ Real.exp upsHi :=
        Real.exp_le_exp.mpr hups.2
      have hinv : 1 / Real.exp upsHi ≤ 1 / Real.exp p.2 := by
        exact one_div_le_one_div_of_le (Real.exp_pos p.2) hden
      dsimp [r]
      exact Real.exp_le_exp.mpr (by linarith)
    have hpow : (Real.exp (-(1 / Real.exp p.2))) ^ n ≤ r ^ n :=
      pow_le_pow_left₀ (Real.exp_nonneg _) hexpBase n
    have hsum : ‖∑ row ∈ rows,
        eta row * jutilaP53Phase alpha row n‖ ≤ J := by
      calc
        ‖∑ row ∈ rows, eta row * jutilaP53Phase alpha row n‖ ≤
            ∑ row ∈ rows,
              ‖eta row * jutilaP53Phase alpha row n‖ := norm_sum_le _ _
        _ ≤ ∑ _row ∈ rows, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro row hr
          rw [norm_mul, heta row hr, one_mul]
          exact norm_jutilaP53Phase_le_one (hrow row hr) n
        _ = J := by simp [J]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hsum 2
    have hterm0 : 0 ≤ jutilaP53CorrelationWeight S
        (Real.exp p.1) (Real.exp p.2) n *
          ‖∑ row ∈ rows,
            eta row * jutilaP53Phase alpha row n‖ ^ 2 :=
      mul_nonneg hw0 (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hterm0]
    calc
      jutilaP53CorrelationWeight S (Real.exp p.1) (Real.exp p.2) n *
            ‖∑ row ∈ rows,
              eta row * jutilaP53Phase alpha row n‖ ^ 2 ≤
          ((R : ℝ) ^ 2 *
            (Real.exp (-(1 / Real.exp p.2))) ^ n) * J ^ 2 :=
        mul_le_mul hw hsq (sq_nonneg _) (by positivity)
      _ ≤ ((R : ℝ) ^ 2 * r ^ n) * J ^ 2 := by
        gcongr
      _ = u n := by dsimp [u]; ring

set_option maxHeartbeats 800000 in
/-- Every inner smoothing-scale integral in the literal p.53 double average
is a genuine interval integral. -/
theorem intervalIntegrable_jutilaP53CorrelationEnergy_inner
    {q R : ℕ} (rows : Finset (JutilaP53Row q))
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 R)
    {alpha xiLo xiHi upsLo upsHi xi : ℝ}
    (hupsOrder : upsLo ≤ upsHi)
    (hcross : xiHi < upsLo) (hxi : xi ∈ Icc xiLo xiHi)
    (eta : JutilaP53Row q → ℂ)
    (hrow : ∀ row ∈ rows, alpha ≤ row.zero.re)
    (heta : ∀ row ∈ rows, ‖eta row‖ = 1) :
    IntervalIntegrable
      (fun upsilon : ℝ =>
        jutilaP53CorrelationEnergy rows S alpha
          (Real.exp xi) (Real.exp upsilon) eta)
      volume upsLo upsHi := by
  let F : ℝ × ℝ → ℝ := fun p =>
    jutilaP53CorrelationEnergy rows S alpha
      (Real.exp p.1) (Real.exp p.2) eta
  have hcont : ContinuousOn F (Icc xiLo xiHi ×ˢ Icc upsLo upsHi) := by
    exact continuousOn_jutilaP53CorrelationEnergy_logScales
      (xiLo := xiLo) (upsHi := upsHi) rows hS hcross eta hrow heta
  have hslice : ContinuousOn
      (fun upsilon : ℝ =>
        jutilaP53CorrelationEnergy rows S alpha
          (Real.exp xi) (Real.exp upsilon) eta)
      (Icc upsLo upsHi) := by
    change ContinuousOn (fun upsilon : ℝ => F (xi, upsilon))
      (Icc upsLo upsHi)
    exact ContinuousOn.comp hcont
      (continuous_const.prodMk continuous_id).continuousOn
      (fun upsilon hups => ⟨hxi, hups⟩)
  exact hslice.intervalIntegrable_of_Icc hupsOrder

set_option maxHeartbeats 800000 in
/-- The outer integral of the literal nested p.53 average is also genuine.
This closes the possible Bochner-`0` loophole in the analytic source leaf. -/
theorem intervalIntegrable_jutilaP53IntegratedCorrelationEnergy_outer
    {q R : ℕ} (rows : Finset (JutilaP53Row q))
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 R)
    {alpha xiLo xiHi upsLo upsHi : ℝ}
    (hxiOrder : xiLo ≤ xiHi) (hupsOrder : upsLo ≤ upsHi)
    (hcross : xiHi < upsLo)
    (eta : JutilaP53Row q → ℂ)
    (hrow : ∀ row ∈ rows, alpha ≤ row.zero.re)
    (heta : ∀ row ∈ rows, ‖eta row‖ = 1) :
    IntervalIntegrable
      (fun xi : ℝ =>
        ∫ upsilon in upsLo..upsHi,
          jutilaP53CorrelationEnergy rows S alpha
            (Real.exp xi) (Real.exp upsilon) eta)
      volume xiLo xiHi := by
  let F : ℝ × ℝ → ℝ := fun p =>
    jutilaP53CorrelationEnergy rows S alpha
      (Real.exp p.1) (Real.exp p.2) eta
  let K : Set (ℝ × ℝ) := Icc xiLo xiHi ×ˢ Icc upsLo upsHi
  have hcont : ContinuousOn F K := by
    exact continuousOn_jutilaP53CorrelationEnergy_logScales
      (xiLo := xiLo) (upsHi := upsHi) rows hS hcross eta hrow heta
  have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKmeas : MeasurableSet K := hKcompact.measurableSet
  have hG : Integrable (K.indicator F) volume :=
    (hcont.integrableOn_compact hKcompact).integrable_indicator hKmeas
  have houter : Integrable
      (fun xi : ℝ => ∫ upsilon : ℝ, K.indicator F (xi, upsilon))
      volume := by
    exact hG.integral_prod_left
  apply houter.intervalIntegrable.congr
  intro xi hxiU
  have hxi : xi ∈ Icc xiLo xiHi := by
    rw [uIoc_of_le hxiOrder] at hxiU
    exact Ioc_subset_Icc_self hxiU
  change (∫ upsilon : ℝ, K.indicator F (xi, upsilon)) =
    ∫ upsilon in upsLo..upsHi, F (xi, upsilon)
  rw [intervalIntegral.integral_of_le hupsOrder]
  rw [← integral_Icc_eq_integral_Ioc]
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with upsilon
  by_cases hups : upsilon ∈ Icc upsLo upsHi
  · have hp : (xi, upsilon) ∈ K := by
      change (xi, upsilon) ∈ Icc xiLo xiHi ×ˢ Icc upsLo upsHi
      exact ⟨hxi, hups⟩
    rw [Set.indicator_of_mem hp, Set.indicator_of_mem hups]
  · have hp : (xi, upsilon) ∉ K := by
      intro hp
      change (xi, upsilon) ∈ Icc xiLo xiHi ×ˢ Icc upsLo upsHi at hp
      exact hups hp.2
    rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hups]

/-- Direct specialization to Jutila's source ranges (3.4)--(3.5). -/
theorem intervalIntegrable_jutilaP53IntegratedCorrelationEnergy_sourceRanges
    {q R : ℕ} (rows : Finset (JutilaP53Row q))
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 R)
    {alpha epsilon z1 x : ℝ}
    (hepsilon : 0 ≤ epsilon) (hz1 : 1 ≤ z1) (hz1x : z1 < x)
    (eta : JutilaP53Row q → ℂ)
    (hrow : ∀ row ∈ rows, alpha ≤ row.zero.re)
    (heta : ∀ row ∈ rows, ‖eta row‖ = 1) :
    IntervalIntegrable
      (fun xi : ℝ =>
        ∫ upsilon in Real.log x..(1 + epsilon) * Real.log x,
          jutilaP53CorrelationEnergy rows S alpha
            (Real.exp xi) (Real.exp upsilon) eta)
      volume ((1 - epsilon) * Real.log z1) (Real.log z1) := by
  have hz1pos : 0 < z1 := zero_lt_one.trans_le hz1
  have hxpos : 0 < x := hz1pos.trans hz1x
  have hlogz1 : 0 ≤ Real.log z1 := Real.log_nonneg hz1
  have hxone : 1 ≤ x := hz1.trans hz1x.le
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hxone
  have hxiOrder : (1 - epsilon) * Real.log z1 ≤ Real.log z1 := by
    nlinarith
  have hupsOrder : Real.log x ≤ (1 + epsilon) * Real.log x := by
    nlinarith
  have hcross : Real.log z1 < Real.log x :=
    Real.strictMonoOn_log hz1pos hxpos hz1x
  exact intervalIntegrable_jutilaP53IntegratedCorrelationEnergy_outer
    rows hS hxiOrder hupsOrder hcross eta hrow heta

end

end MAPJutilaP53EnergyContinuity

#print axioms MAPJutilaP53EnergyContinuity.continuousOn_jutilaP53CorrelationEnergy_logScales
#print axioms MAPJutilaP53EnergyContinuity.intervalIntegrable_jutilaP53CorrelationEnergy_inner
#print axioms MAPJutilaP53EnergyContinuity.intervalIntegrable_jutilaP53IntegratedCorrelationEnergy_outer
#print axioms MAPJutilaP53EnergyContinuity.intervalIntegrable_jutilaP53IntegratedCorrelationEnergy_sourceRanges
