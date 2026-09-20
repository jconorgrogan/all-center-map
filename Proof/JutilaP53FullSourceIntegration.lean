import JutilaP53SourcePairEnergy
import JutilaP53SourceRectangleBudget
import JutilaP53EnergyContinuity
import JutilaP53SourceScaleIntegration

/-! # Complete source-rectangle correlation estimate

The source-line analytic coefficient and signed residue coefficient are both
proved here, uniformly over all row systems and ambient moduli. -/
namespace MAPJutilaP53FullSourceIntegration
open scoped BigOperators
open MeasureTheory
open MAPJutilaP53AggregateCorrelationLeaf MAPJutilaP53SourcePairEnergy
open MAPJutilaP53SourceRectangleBudget MAPJutilaP53EnergyContinuity
open MAPJutilaP53SourceScaleIntegration MAPJutilaP53SourceScaleEnvelopes
open MAPJutilaP53NormalizedEulerMassBound MAPJutilaP53PrincipalRResidueAggregation
open MAPJutilaP53SourceDivisorMass MAPJutilaOneSeparatedExponentialPacking
noncomputable section

/-- All analytic and arithmetic envelopes on the literal logarithmic
rectangle, including the source endpoint exponent `-(1-epsilon)^2`. -/
theorem exists_integratedCorrelationEstimateAt_fullSourceBudgets
    {epsilon : ℝ} (heps : 0 < epsilon) (hepsHi : epsilon ≤ 1/8) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q R : ℕ) [NeZero q]
      (rows : Finset (JutilaP53Row q)) (S : Finset ℕ) (alpha z1 x T : ℝ),
      S ⊆ Finset.Icc 1 R → (∀ r ∈ S, Squarefree r) → (∀ r ∈ S, r.Coprime q) →
      1 ≤ z1 → z1 < x → 0 ≤ T →
      (∀ row ∈ rows, |row.zero.im| ≤ T) →
      (∀ row ∈ rows, alpha ≤ row.zero.re ∧ row.zero.re ≤ alpha + epsilon) →
      (∀ chi : DirichletCharacter ℂ q, CGLProofDAG.OneSeparated
        ((rows.filter (fun row => row.character = chi)).image (fun row => row.zero.im))) →
      (∀ chi : DirichletCharacter ℂ q,
        ((rows.filter (fun row => row.character = chi)).image (fun row => row.zero.im)).card =
        (rows.filter (fun row => row.character = chi)).card) →
      JutilaP53IntegratedCorrelationEstimateAt rows S alpha epsilon z1 x
        (epsilon^2 * Real.log z1 * Real.log x * sourceSharpResidueBudget R epsilon z1 x)
        (epsilon^2 * Real.log z1 * Real.log x *
          (K * Real.rpow ((q : ℝ)*(1+2*T)) (1/2) *
            (2*Real.exp (-((1-epsilon)^2)*Real.log z1)) *
            ((R : ℝ)^2 * (harmonic R : ℝ)^8))) := by
  obtain ⟨K,hK,henergy⟩ := exists_sourcePair_energy_le heps hepsHi
  refine ⟨K,hK,?_⟩
  intro q R _inst rows S alpha z1 x T hS hSq hcop hz1 hz1x hT hrowsT hrows hsep hcard
  intro eta heta
  let E := K * Real.rpow ((q : ℝ)*(1+2*T)) (1/2) *
    (2*Real.exp (-((1-epsilon)^2)*Real.log z1)) * ((R : ℝ)^2*(harmonic R : ℝ)^8)
  let F := sourceSharpResidueBudget R epsilon z1 x
  have hzpos : 0 < z1 := zero_lt_one.trans_le hz1
  have hx : 1 ≤ x := hz1.trans hz1x.le
  have hlog : Real.log z1 < Real.log x :=
    Real.strictMonoOn_log hzpos (hzpos.trans hz1x) hz1x
  have hlo : (1-epsilon)*Real.log z1 ≤ Real.log z1 := by
    have := Real.log_nonneg hz1
    nlinarith
  have hOuterInt := intervalIntegrable_jutilaP53IntegratedCorrelationEnergy_sourceRanges
    rows hS heps.le hz1 hz1x eta (fun row hr => (hrows row hr).1) heta
  have hupsOrder : Real.log x ≤ (1+epsilon)*Real.log x := by
    have := Real.log_nonneg hx
    nlinarith
  have hInnerInt : ∀ xi ∈ Set.Icc ((1-epsilon)*Real.log z1) (Real.log z1),
      IntervalIntegrable (fun upsilon => jutilaP53CorrelationEnergy rows S alpha
        (Real.exp xi) (Real.exp upsilon) eta) volume (Real.log x) ((1+epsilon)*Real.log x) := by
    intro xi hxi
    exact intervalIntegrable_jutilaP53CorrelationEnergy_inner rows hS hupsOrder hlog hxi eta
      (fun row hr => (hrows row hr).1) heta
  have hmass := p53NormalizedEulerMass_le_R_sq_mul_harmonic_pow_eight hS hSq
  have hH : 0 ≤ (harmonic R : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    exact Finset.sum_nonneg fun r hr => by positivity
  have hPoint : ∀ xi ∈ Set.Icc ((1-epsilon)*Real.log z1) (Real.log z1),
      ∀ upsilon ∈ Set.Icc (Real.log x) ((1+epsilon)*Real.log x),
      jutilaP53CorrelationEnergy rows S alpha (Real.exp xi) (Real.exp upsilon) eta ≤
        F * (rows.card : ℝ) + E * (rows.card : ℝ)^2 := by
    intro xi hxi upsilon hups
    have hxi0 : 0 ≤ xi := (mul_nonneg (by linarith) (Real.log_nonneg hz1)).trans hxi.1
    have hM : 1 ≤ Real.exp xi := by simpa using Real.exp_le_exp.mpr hxi0
    have hMN : Real.exp xi < Real.exp upsilon :=
      Real.exp_lt_exp.mpr (hxi.2.trans_lt (hlog.trans_le hups.1))
    have hp := henergy q R rows S alpha (Real.exp xi) (Real.exp upsilon) T
      hS hSq hcop hM hMN hT hrowsT hrows hsep hcard eta heta
    have hEnd := sourceEndpoint_exp_le heps.le (by linarith : epsilon ≤ 1)
      hxi.1 (hlo.trans (hlog.le.trans hups.1))
    have hAnalytic : K * Real.rpow ((q : ℝ)*(1+2*T)) (1/2) *
        sourceEndpoint (Real.exp upsilon) (Real.exp xi) epsilon * p53NormalizedEulerMass S ≤ E := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hEnd
          (mul_nonneg hK.le (Real.rpow_nonneg (by positivity) _))) hmass
        (p53NormalizedEulerMass_nonneg S) (by dsimp; positivity)
    have hResidue : (12*(Real.log (Real.exp upsilon)-Real.log (Real.exp xi)) +
        48*Real.exp 1*integerExponentialMass)*(harmonic R : ℝ) ≤ F := by
      dsimp [F, sourceSharpResidueBudget]
      rw [Real.log_exp, Real.log_exp]
      exact mul_le_mul_of_nonneg_right (by linarith [hxi.1,hups.2]) hH
    calc
      _ ≤ (K * Real.rpow ((q : ℝ)*(1+2*T)) (1/2) *
          sourceEndpoint (Real.exp upsilon) (Real.exp xi) epsilon * p53NormalizedEulerMass S) *
          (rows.card : ℝ)^2 + (rows.card : ℝ)*
          ((12*(Real.log (Real.exp upsilon)-Real.log (Real.exp xi)) +
            48*Real.exp 1*integerExponentialMass)*(harmonic R : ℝ)) := hp
      _ ≤ E * (rows.card : ℝ)^2 + (rows.card : ℝ)*F :=
        add_le_add (mul_le_mul_of_nonneg_right hAnalytic (sq_nonneg _))
          (mul_le_mul_of_nonneg_left hResidue (Nat.cast_nonneg _))
      _ = _ := by ring
  have hint := sourceRectangle_integral_le_const heps.le hz1 hx hOuterInt hInnerInt hPoint
  unfold jutilaP53IntegratedCorrelationEnergy
  calc
    _ ≤ epsilon^2 * Real.log z1 * Real.log x *
        (F*(rows.card : ℝ)+E*(rows.card : ℝ)^2) := hint
    _ = _ := by dsimp [F,E]; ring
end
end MAPJutilaP53FullSourceIntegration
#print axioms MAPJutilaP53FullSourceIntegration.exists_integratedCorrelationEstimateAt_fullSourceBudgets
