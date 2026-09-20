import JutilaP53FullSourceIntegration
import JutilaLemma6CanonicalLower
import JutilaP53IntegratedHalaszWeld

/-! # Canonical detector and the complete source correlation estimate

The only remaining analytic hypotheses concern the two literal detector
errors. The common coefficients, pseudocharacter set, quotient estimate,
source integration, and cancellation of the positive rectangle area are proved.
-/
namespace MAPJutilaP53CanonicalHalaszSource
open scoped BigOperators
open Complex MeasureTheory
open MAPJutilaP53AggregateCorrelationLeaf MAPJutilaP53FullSourceIntegration
open MAPJutilaLemma6CanonicalLower MAPJutilaLemma6DetectorIdentity
open MAPJutilaLemma6DirectTail MAPJutilaPseudocharacterHarmonicLower
open MAPJutilaP53CoefficientQuotient MAPJutilaP53IntegratedHalaszWeld
open MAPJutilaDeterministicCore MAPJutilaP53SourceScaleEnvelopes
noncomputable section

set_option maxHeartbeats 1200000 in
theorem exists_canonical_halasz_source_quadratic
    {epsilon : ℝ} (heps : 0 < epsilon) (hepsHi : epsilon ≤ 1/8) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q R x : ℕ) [NeZero q]
      (rows : Finset (JutilaP53Row q)) (z1 z2 X alpha T : ℝ),
      1 ≤ R → 1 ≤ x → 1 < z1 → z1 < z2 → 2 ≤ X →
      4*z1 ≤ (x : ℝ) → 0 ≤ alpha → alpha ≤ 1 → 0 ≤ T →
      (∀ row ∈ rows, |row.zero.im| ≤ T) →
      (∀ row ∈ rows, alpha ≤ row.zero.re ∧ row.zero.re ≤ alpha+epsilon) →
      (∀ chi : DirichletCharacter ℂ q, CGLProofDAG.OneSeparated
        ((rows.filter (fun row => row.character = chi)).image (fun row => row.zero.im))) →
      (∀ chi : DirichletCharacter ℂ q,
        ((rows.filter (fun row => row.character = chi)).image (fun row => row.zero.im)).card =
        (rows.filter (fun row => row.character = chi)).card) →
      (4 ≤ (1/8:ℝ)*((Nat.totient q : ℝ)/(q : ℝ))*Real.log (R : ℝ)) →
      (∀ row ∈ rows, ‖∑' n : ℕ, jutilaLemmaSixDirectTerm row.character z1 z2
        (jutilaPrimedRSet q R) row.zero X n‖ ≤ 1) →
      (∀ row ∈ rows, ‖∑' k : ℕ, jutilaLemmaSixDirectTerm row.character z1 z2
        (jutilaPrimedRSet q R) row.zero X (k+(x+1))‖ ≤ 1) →
      ((1/16:ℝ)*((Nat.totient q : ℝ)/(q : ℝ))*Real.log (R : ℝ))^2 *
        (rows.card : ℝ)^2 ≤
      (10*Real.rpow (x : ℝ) (2-2*alpha)*(1+Real.log (x : ℝ))^4) *
        (sourceSharpResidueBudget R epsilon z1 (x : ℝ)*(rows.card : ℝ) +
          (K*Real.rpow ((q : ℝ)*(1+2*T)) (1/2)*
            (2*Real.exp (-((1-epsilon)^2)*Real.log z1))*
            ((R : ℝ)^2*(harmonic R : ℝ)^8))*(rows.card : ℝ)^2) := by
  obtain ⟨K,hK,hfull⟩ := exists_integratedCorrelationEstimateAt_fullSourceBudgets heps hepsHi
  refine ⟨K,hK,?_⟩
  intro q R x _inst rows z1 z2 X alpha T hR hx hz1 hz12 hX hsep halpha0 halpha1 hT
    hrowsT hrows hfiberSep hfiberCard hsize hseries htail
  let S := jutilaPrimedRSet q R
  let cols := detectorColumns z1 S x
  let a := jutilaP53DetectedCoefficient z1 z2 alpha X S
  let V : ℝ := (1/16:ℝ)*((Nat.totient q : ℝ)/(q : ℝ))*Real.log (R : ℝ)
  let Q : ℝ := 10*Real.rpow (x : ℝ) (2-2*alpha)*(1+Real.log (x : ℝ))^4
  let F : ℝ := sourceSharpResidueBudget R epsilon z1 (x : ℝ)
  let E : ℝ := K*Real.rpow ((q : ℝ)*(1+2*T)) (1/2)*
    (2*Real.exp (-((1-epsilon)^2)*Real.log z1))*((R : ℝ)^2*(harmonic R : ℝ)^8)
  let A : ℝ := epsilon^2*Real.log z1*Real.log (x : ℝ)
  have hzx : z1 < (x : ℝ) := by linarith
  have hzpos : 0 < z1 := by linarith
  have hlogCross : Real.log z1 < Real.log (x : ℝ) :=
    Real.strictMonoOn_log hzpos (hzpos.trans hzx) hzx
  have hlogZ : 0 < Real.log z1 := Real.log_pos hz1
  have hlogX : 0 < Real.log (x : ℝ) := hlogZ.trans hlogCross
  have hA : 0 < A := by dsimp [A]; positivity
  have hV : 0 ≤ V := by
    have hlogR : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg (by exact_mod_cast hR)
    dsimp [V]
    positivity
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg x) _)) (pow_nonneg (by linarith) _)
  have hS : S ⊆ Finset.Icc 1 R := jutilaPrimedRSet_subset_Icc q R
  have hcols : cols ⊆ Finset.Icc 1 x := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hnpos : 0 < n := by
      have hzN := hn'.2.1
      have hnR : (0:ℝ) < n := hzpos.trans hzN
      exact Nat.cast_pos.mp hnR
    exact Finset.mem_Icc.mpr ⟨hnpos, Nat.le_of_lt_succ (Finset.mem_range.mp hn'.1)⟩
  have hzcols : ∀ n ∈ cols, z1 < (n : ℝ) := fun n hn => (Finset.mem_filter.mp hn).2.1
  have hP : ∀ n ∈ cols, jutilaP53PseudoReal S n ≠ 0 := fun n hn => (Finset.mem_filter.mp hn).2.2
  have hlarge : ∀ row ∈ rows, V ≤ ‖finitePolynomial cols a (jutilaP53Phase alpha) row‖ := by
    intro row hr
    exact canonical_polynomial_lower_of_series_tail_le_one row (NeZero.pos q)
      hz1 hz12 alpha hR (halpha0.trans (hrows row hr).1) hX hx
      (hseries row hr) (htail row hr) hsize
  have hxiOrder : (1-epsilon)*Real.log z1 ≤ Real.log z1 := by nlinarith
  have hupsOrder : Real.log (x : ℝ) ≤ (1+epsilon)*Real.log (x : ℝ) := by nlinarith
  have hquotient : ∀ xi ∈ Set.Icc ((1-epsilon)*Real.log z1) (Real.log z1),
      ∀ upsilon ∈ Set.Icc (Real.log (x : ℝ)) ((1+epsilon)*Real.log (x : ℝ)),
      (∑ n ∈ cols, ‖a n‖^2 / jutilaP53CorrelationWeight S (Real.exp xi) (Real.exp upsilon) n) ≤ Q := by
    intro xi hxi upsilon hups
    have hMz : Real.exp xi ≤ z1 := by
      rw [← Real.exp_log hzpos]
      exact Real.exp_le_exp.mpr hxi.2
    have hxN : (x : ℝ) ≤ Real.exp upsilon := by
      rw [← Real.exp_log (show (0:ℝ)<x by exact_mod_cast hx)]
      exact Real.exp_le_exp.mpr hups.1
    exact sum_detectedCoefficient_div_correlationWeight_le_logPow hz1 hz12 halpha1 hx
      (by linarith) (Real.exp_pos _) hMz hsep hxN hcols hzcols hP
  obtain ⟨eta,heta,hhalasz⟩ := exists_common_phase_integrated_halasz rows cols a hS
    hxiOrder hupsOrder hlogCross hV hQ (fun row hr => (hrows row hr).1) hlarge
    (fun n hn => (Finset.mem_Icc.mp (hcols hn)).1) hP hquotient
  have hint := hfull q R rows S alpha z1 (x : ℝ) T hS
    (fun r hr => squarefree_of_mem_jutilaPrimedRSet hr)
    (fun r hr => coprime_of_mem_jutilaPrimedRSet hr)
    hz1.le hzx hT hrowsT hrows hfiberSep hfiberCard eta heta
  have harea : (Real.log z1-(1-epsilon)*Real.log z1)*
      ((1+epsilon)*Real.log (x : ℝ)-Real.log (x : ℝ)) = A := by dsimp [A]; ring
  rw [harea] at hhalasz
  have hcombined : A*((rows.card : ℝ)*V)^2 ≤ Q*((A*F)*(rows.card : ℝ)+(A*E)*(rows.card : ℝ)^2) :=
    hhalasz.trans (mul_le_mul_of_nonneg_left hint hQ)
  have hcancel : A*(V^2*(rows.card : ℝ)^2) ≤ A*(Q*(F*(rows.card : ℝ)+E*(rows.card : ℝ)^2)) := by
    nlinarith [hcombined]
  exact le_of_mul_le_mul_left hcancel hA
end
end MAPJutilaP53CanonicalHalaszSource
#print axioms MAPJutilaP53CanonicalHalaszSource.exists_canonical_halasz_source_quadratic
