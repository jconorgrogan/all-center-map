import JutilaP53PairSectorAggregation
import JutilaP53EnergyContinuity
import JutilaP53SourceScaleIntegration

/-!
# Exact source-rectangle adapter for the aggregated p.53 pair sectors
-/

namespace MAPJutilaP53IntegratedPairSectorAdapter

open MeasureTheory Set
open CGLProofDAG
open MAPJutilaP53AggregateCorrelationLeaf
open MAPJutilaP53PairSectorAggregation
open MAPJutilaP53EnergyContinuity
open MAPJutilaP53SourceScaleIntegration
open MAPJutilaP53PrincipalRResidueAggregation
open MAPJutilaOneSeparatedExponentialPacking

noncomputable section

/-- A uniform source-rectangle envelope for the two explicit outputs of the
pair-sector theorem yields the precise integrated `F #rows + E #rows^2`
statement.  The rectangle area is retained exactly in both coefficients. -/
theorem integratedCorrelationEstimateAt_of_pairSectorEnvelopes
    {q R : ℕ} [NeZero q] (rows : Finset (JutilaP53Row q))
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 R)
    (hSq : ∀ r ∈ S, Squarefree r)
    {alpha epsilon z1 x F E : ℝ}
    (heps0 : 0 ≤ epsilon) (hepsHi : epsilon ≤ 1 / 8)
    (hz1 : 1 ≤ z1) (hz1x : z1 < x)
    (hrows : ∀ row ∈ rows,
      alpha ≤ row.zero.re ∧ row.zero.re ≤ alpha + epsilon)
    (hfiberSep : ∀ chi : DirichletCharacter ℂ q,
      OneSeparated ((rows.filter (fun row => row.character = chi)).image
        (fun row => row.zero.im)))
    (hfiberCard : ∀ chi : DirichletCharacter ℂ q,
      ((rows.filter (fun row => row.character = chi)).image
        (fun row => row.zero.im)).card =
      (rows.filter (fun row => row.character = chi)).card)
    (hscale : ∀ xi ∈ Set.Icc ((1 - epsilon) * Real.log z1) (Real.log z1),
      ∀ r ∈ S, ∀ r' ∈ S, ((r.lcm r' : ℕ) : ℝ) ≤ Real.exp xi)
    (hResidue : ∀ xi ∈ Set.Icc ((1 - epsilon) * Real.log z1) (Real.log z1),
      ∀ upsilon ∈ Set.Icc (Real.log x) ((1 + epsilon) * Real.log x),
        (12 * (upsilon - xi) +
            48 * Real.exp 1 * integerExponentialMass) *
          p53NormalizedEulerMass S ≤ F)
    (hAnalytic : ∀ xi ∈ Set.Icc ((1 - epsilon) * Real.log z1) (Real.log z1),
      ∀ upsilon ∈ Set.Icc (Real.log x) ((1 + epsilon) * Real.log x),
        (∑ i ∈ rows, ∑ j ∈ rows,
          p53AnalyticPairBudget S alpha (Real.exp xi) (Real.exp upsilon) i j) ≤
          E * (rows.card : ℝ) ^ 2) :
    JutilaP53IntegratedCorrelationEstimateAt rows S alpha epsilon z1 x
      (epsilon ^ 2 * Real.log z1 * Real.log x * F)
      (epsilon ^ 2 * Real.log z1 * Real.log x * E) := by
  intro eta heta
  have hx : 1 ≤ x := hz1.trans hz1x.le
  have hOuterInt :=
    intervalIntegrable_jutilaP53IntegratedCorrelationEnergy_sourceRanges
      rows hS heps0 hz1 hz1x eta (fun row hr => (hrows row hr).1) heta
  have hlogCross : Real.log z1 < Real.log x := by
    exact Real.strictMonoOn_log (zero_lt_one.trans_le hz1)
      ((zero_lt_one.trans_le hz1).trans hz1x) hz1x
  have hxiOrder : (1 - epsilon) * Real.log z1 ≤ Real.log z1 := by
    have := Real.log_nonneg hz1
    nlinarith
  have hupsOrder : Real.log x ≤ (1 + epsilon) * Real.log x := by
    have := Real.log_nonneg hx
    nlinarith
  have hInnerInt : ∀ xi ∈ Set.Icc ((1 - epsilon) * Real.log z1) (Real.log z1),
      IntervalIntegrable
        (fun upsilon => jutilaP53CorrelationEnergy rows S alpha
          (Real.exp xi) (Real.exp upsilon) eta)
        volume (Real.log x) ((1 + epsilon) * Real.log x) := by
    intro xi hxi
    exact intervalIntegrable_jutilaP53CorrelationEnergy_inner rows hS
      hupsOrder hlogCross hxi eta (fun row hr => (hrows row hr).1) heta
  have hPoint : ∀ xi ∈ Set.Icc ((1 - epsilon) * Real.log z1) (Real.log z1),
      ∀ upsilon ∈ Set.Icc (Real.log x) ((1 + epsilon) * Real.log x),
        jutilaP53CorrelationEnergy rows S alpha
          (Real.exp xi) (Real.exp upsilon) eta ≤
          F * (rows.card : ℝ) + E * (rows.card : ℝ) ^ 2 := by
    intro xi hxi upsilon hups
    have hMNlog : xi < upsilon := hxi.2.trans_lt (hlogCross.trans_le hups.1)
    have hpair := jutilaP53CorrelationEnergy_le_pairSectors rows hS hSq
      hepsHi (Real.exp_pos xi) (Real.exp_lt_exp.mpr hMNlog)
      (hscale xi hxi) hrows hfiberSep hfiberCard eta heta
    calc
      _ ≤ (∑ i ∈ rows, ∑ j ∈ rows,
          p53AnalyticPairBudget S alpha (Real.exp xi) (Real.exp upsilon) i j) +
        (rows.card : ℝ) *
          ((12 * (Real.log (Real.exp upsilon) - Real.log (Real.exp xi)) +
              48 * Real.exp 1 * integerExponentialMass) *
            p53NormalizedEulerMass S) := hpair
      _ = (∑ i ∈ rows, ∑ j ∈ rows,
          p53AnalyticPairBudget S alpha (Real.exp xi) (Real.exp upsilon) i j) +
        (rows.card : ℝ) *
          ((12 * (upsilon - xi) +
              48 * Real.exp 1 * integerExponentialMass) *
            p53NormalizedEulerMass S) := by rw [Real.log_exp, Real.log_exp]
      _ ≤ E * (rows.card : ℝ) ^ 2 + (rows.card : ℝ) * F := by
        exact add_le_add (hAnalytic xi hxi upsilon hups)
          (mul_le_mul_of_nonneg_left (hResidue xi hxi upsilon hups)
            (Nat.cast_nonneg _))
      _ = F * (rows.card : ℝ) + E * (rows.card : ℝ) ^ 2 := by ring
  have hint := sourceRectangle_integral_le_const heps0 hz1 hx hOuterInt
    hInnerInt hPoint
  unfold jutilaP53IntegratedCorrelationEnergy
  calc
    _ ≤ epsilon ^ 2 * Real.log z1 * Real.log x *
        (F * (rows.card : ℝ) + E * (rows.card : ℝ) ^ 2) := hint
    _ = (epsilon ^ 2 * Real.log z1 * Real.log x * F) * (rows.card : ℝ) +
        (epsilon ^ 2 * Real.log z1 * Real.log x * E) *
          (rows.card : ℝ) ^ 2 := by ring

end
end MAPJutilaP53IntegratedPairSectorAdapter

#print axioms MAPJutilaP53IntegratedPairSectorAdapter.integratedCorrelationEstimateAt_of_pairSectorEnvelopes
