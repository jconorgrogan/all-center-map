import JutilaP53IntegratedPairSectorAdapter
import JutilaP53SharpIntegratedPairSectorAdapter
import JutilaP53NormalizedEulerMassBound

/-!
# Elementary source-scale envelopes for the p.53 pair estimate
-/

namespace MAPJutilaP53SourceScaleEnvelopes

open scoped BigOperators
open MAPJutilaP53AggregateCorrelationLeaf
open MAPJutilaP53KernelSourceForm
open MAPJutilaP53LeftLineEstimate
open MAPJutilaP53PrincipalLeftLineEstimate
open MAPJutilaP53ShiftedContourBound
open MAPJutilaP53PrincipalShiftedContourBound
open MAPJutilaP53PrincipalRResidueAggregation
open MAPJutilaP53PairSectorAggregation

noncomputable section

/-- The lcm of two selected pseudocharacter moduli is at most the square of
the selection endpoint. -/
theorem cast_lcm_le_R_sq
    {S : Finset ℕ} {R r r' : ℕ} (hS : S ⊆ Finset.Icc 1 R)
    (hr : r ∈ S) (hr' : r' ∈ S) :
    ((r.lcm r' : ℕ) : ℝ) ≤ (R : ℝ) ^ 2 := by
  have hrI := Finset.mem_Icc.mp (hS hr)
  have hr'I := Finset.mem_Icc.mp (hS hr')
  have hprodPos : 0 < r * r' := Nat.mul_pos (by omega) (by omega)
  have hlcmNat : r.lcm r' ≤ r * r' :=
    Nat.le_of_dvd hprodPos (Nat.lcm_dvd_mul r r')
  have h := hlcmNat.trans (Nat.mul_le_mul hrI.2 hr'I.2)
  exact_mod_cast (show r.lcm r' ≤ R ^ 2 by simpa [pow_two] using h)

/-- Uniform lcm legality over the complete logarithmic source interval. -/
theorem source_lcm_le_exp
    {S : Finset ℕ} {R : ℕ} {epsilon z1 : ℝ}
    (hS : S ⊆ Finset.Icc 1 R)
    (hR : (R : ℝ) ^ 2 ≤ Real.exp ((1 - epsilon) * Real.log z1)) :
    ∀ xi ∈ Set.Icc ((1 - epsilon) * Real.log z1) (Real.log z1),
      ∀ r ∈ S, ∀ r' ∈ S, ((r.lcm r' : ℕ) : ℝ) ≤ Real.exp xi := by
  intro xi hxi r hr r' hr'
  exact (cast_lcm_le_R_sq hS hr hr').trans
    (hR.trans (Real.exp_le_exp.mpr hxi.1))

/-- Pair shifts of rows from an ordinate window `[-T,T]` have height at most
`2T`. -/
theorem abs_pairShift_im_le_two_mul
    {q : ℕ} {alpha T : ℝ} {i j : JutilaP53Row q}
    (hi : |i.zero.im| ≤ T) (hj : |j.zero.im| ≤ T) :
    |(jutilaP53PairShift alpha i j).im| ≤ 2 * T := by
  rw [pairShift_im]
  calc
    |j.zero.im - i.zero.im| ≤ |j.zero.im| + |i.zero.im| := abs_sub _ _
    _ ≤ T + T := add_le_add hj hi
    _ = 2 * T := by ring

/-- Exact negative-half endpoint envelope on the source rectangle. -/
theorem p53CpowEndpointBound_source_le
    {epsilon z1 xi upsilon : ℝ} (hz1 : 0 < z1)
    (hxi : (1 - epsilon) * Real.log z1 ≤ xi)
    (hups : (1 - epsilon) * Real.log z1 ≤ upsilon) :
    p53CpowEndpointBound (Real.exp upsilon) (Real.exp xi)
        (-(1 / 2)) (-(1 / 2)) ≤
      2 * Real.exp (-((1 - epsilon) * Real.log z1) / 2) := by
  have hU : Real.rpow (Real.exp upsilon) (-(1 / 2)) ≤
      Real.exp (-((1 - epsilon) * Real.log z1) / 2) := by
    calc
      Real.rpow (Real.exp upsilon) (-(1 / 2)) =
          Real.exp (Real.log (Real.exp upsilon) * (-(1 / 2))) :=
        Real.rpow_def_of_pos (Real.exp_pos upsilon) _
      _ = Real.exp (upsilon * (-(1 / 2))) := by rw [Real.log_exp]
      _ ≤ Real.exp (-((1 - epsilon) * Real.log z1) / 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith
  have hV : Real.rpow (Real.exp xi) (-(1 / 2)) ≤
      Real.exp (-((1 - epsilon) * Real.log z1) / 2) := by
    calc
      Real.rpow (Real.exp xi) (-(1 / 2)) =
          Real.exp (Real.log (Real.exp xi) * (-(1 / 2))) :=
        Real.rpow_def_of_pos (Real.exp_pos xi) _
      _ = Real.exp (xi * (-(1 / 2))) := by rw [Real.log_exp]
      _ ≤ Real.exp (-((1 - epsilon) * Real.log z1) / 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith
  unfold p53CpowEndpointBound
  simp only [max_self]
  exact (add_le_add hU hV).trans_eq (by ring)

/-- Uniform analytic-pair sum.  It displays all modulus, ordinate, endpoint,
and normalized Euler-mass costs before parameter absorption. -/
theorem sum_p53AnalyticPairBudget_source_le
    {q R : ℕ} (rows : Finset (JutilaP53Row q))
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 R)
    (hSq : ∀ r ∈ S, Squarefree r)
    {alpha epsilon z1 xi upsilon T : ℝ}
    (hz1 : 0 < z1)
    (hxi : (1 - epsilon) * Real.log z1 ≤ xi)
    (hups : (1 - epsilon) * Real.log z1 ≤ upsilon)
    (hT : 0 ≤ T)
    (hrowsT : ∀ row ∈ rows, |row.zero.im| ≤ T) :
    (∑ i ∈ rows, ∑ j ∈ rows,
      p53AnalyticPairBudget S alpha (Real.exp xi) (Real.exp upsilon) i j) ≤
      ((4800 * (q : ℝ) ^ 2 * (5 + 2 * T) ^ 2 * p53UniversalVerticalMass +
          153600 * (2 : ℝ) ^ q.primeFactors.card * (5 + 2 * T) ^ 6 *
            p53PrincipalUniversalVerticalMass) *
        (2 * Real.exp (-((1 - epsilon) * Real.log z1) / 2)) *
        ((R : ℝ) ^ 2 * (harmonic R : ℝ) ^ 8)) *
      (rows.card : ℝ) ^ 2 := by
  let K := (4800 * (q : ℝ) ^ 2 * (5 + 2 * T) ^ 2 * p53UniversalVerticalMass +
      153600 * (2 : ℝ) ^ q.primeFactors.card * (5 + 2 * T) ^ 6 *
        p53PrincipalUniversalVerticalMass) *
    (2 * Real.exp (-((1 - epsilon) * Real.log z1) / 2)) *
    ((R : ℝ) ^ 2 * (harmonic R : ℝ) ^ 8)
  have hmass :=
    MAPJutilaP53NormalizedEulerMassBound.p53NormalizedEulerMass_le_R_sq_mul_harmonic_pow_eight
      hS hSq
  have hend := p53CpowEndpointBound_source_le hz1 hxi hups
  have hVM0 : 0 ≤ p53UniversalVerticalMass := by
    unfold p53UniversalVerticalMass
    exact MeasureTheory.integral_nonneg fun t =>
      mul_nonneg (pow_nonneg (by positivity) 6) (Real.exp_pos _).le
  have hPVM0 : 0 ≤ p53PrincipalUniversalVerticalMass := by
    unfold p53PrincipalUniversalVerticalMass
    exact MeasureTheory.integral_nonneg fun t =>
      mul_nonneg (pow_nonneg (by positivity) 7) (Real.exp_pos _).le
  have hmass0 : 0 ≤ p53NormalizedEulerMass S :=
    p53NormalizedEulerMass_nonneg S
  have hend0 : 0 ≤ p53CpowEndpointBound (Real.exp upsilon) (Real.exp xi)
      (-(1 / 2)) (-(1 / 2)) :=
    p53CpowEndpointBound_nonneg (Real.exp_pos _) (Real.exp_pos _) _ _
  have hpoint : ∀ i ∈ rows, ∀ j ∈ rows,
      p53AnalyticPairBudget S alpha (Real.exp xi) (Real.exp upsilon) i j ≤ K := by
    intro i hi j hj
    have him := abs_pairShift_im_le_two_mul (alpha := alpha)
      (hrowsT i hi) (hrowsT j hj)
    have hbase : 0 ≤ 5 + 2 * T := by linarith
    have hoff : p53ShiftedAnalyticFactor q (jutilaP53PairShift alpha i j) ≤
        4800 * (q : ℝ) ^ 2 * (5 + 2 * T) ^ 2 * p53UniversalVerticalMass := by
      unfold p53ShiftedAnalyticFactor
      have : 5 + |(jutilaP53PairShift alpha i j).im| ≤ 5 + 2 * T := by linarith
      gcongr
    have hprin : p53PrincipalShiftedAnalyticFactor q
          (jutilaP53PairShift alpha i j) ≤
        153600 * (2 : ℝ) ^ q.primeFactors.card * (5 + 2 * T) ^ 6 *
          p53PrincipalUniversalVerticalMass := by
      unfold p53PrincipalShiftedAnalyticFactor
      have : 5 + |(jutilaP53PairShift alpha i j).im| ≤ 5 + 2 * T := by linarith
      gcongr
    unfold p53AnalyticPairBudget
    split_ifs with hc
    · calc
        _ ≤ (153600 * (2 : ℝ) ^ q.primeFactors.card * (5 + 2 * T) ^ 6 *
              p53PrincipalUniversalVerticalMass) *
            (2 * Real.exp (-((1 - epsilon) * Real.log z1) / 2)) *
            ((R : ℝ) ^ 2 * (harmonic R : ℝ) ^ 8) := by
          gcongr
        _ ≤ K := by
          dsimp [K]
          have hoff0 := p53ShiftedAnalyticFactor_nonneg q
            (jutilaP53PairShift alpha i j)
          have hA0 : 0 ≤ 2 * Real.exp (-((1 - epsilon) * Real.log z1) / 2) := by positivity
          have hR0 : 0 ≤ (R : ℝ) ^ 2 * (harmonic R : ℝ) ^ 8 := by positivity
          have hprincipal0 : 0 ≤ 153600 * (2 : ℝ) ^ q.primeFactors.card *
              (5 + 2 * T) ^ 6 * p53PrincipalUniversalVerticalMass := by
            exact hprin.trans' (p53PrincipalShiftedAnalyticFactor_nonneg q _)
          have hoffBound0 : 0 ≤ 4800 * (q : ℝ) ^ 2 * (5 + 2 * T) ^ 2 *
              p53UniversalVerticalMass := by
            exact hoff.trans' (p53ShiftedAnalyticFactor_nonneg q _)
          nlinarith [mul_nonneg hA0 hR0,
            mul_nonneg hoffBound0 (mul_nonneg hA0 hR0)]
    · calc
        _ ≤ (4800 * (q : ℝ) ^ 2 * (5 + 2 * T) ^ 2 *
              p53UniversalVerticalMass) *
            (2 * Real.exp (-((1 - epsilon) * Real.log z1) / 2)) *
            ((R : ℝ) ^ 2 * (harmonic R : ℝ) ^ 8) := by
          gcongr
        _ ≤ K := by
          dsimp [K]
          have hA0 : 0 ≤ 2 * Real.exp (-((1 - epsilon) * Real.log z1) / 2) := by positivity
          have hR0 : 0 ≤ (R : ℝ) ^ 2 * (harmonic R : ℝ) ^ 8 := by positivity
          have hprincipal0 : 0 ≤ 153600 * (2 : ℝ) ^ q.primeFactors.card *
              (5 + 2 * T) ^ 6 * p53PrincipalUniversalVerticalMass := by
            exact hprin.trans' (p53PrincipalShiftedAnalyticFactor_nonneg q _)
          nlinarith [mul_nonneg hA0 hR0,
            mul_nonneg hprincipal0 (mul_nonneg hA0 hR0)]
  calc
    _ ≤ ∑ _i ∈ rows, ∑ _j ∈ rows, K := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.sum_le_sum (hpoint i hi)
    _ = K * (rows.card : ℝ) ^ 2 := by simp [pow_two, K]; ring

/-- Explicit linear residue coefficient on the complete source rectangle. -/
def sourceResidueBudget (R : ℕ) (epsilon z1 x : ℝ) : ℝ :=
  (12 * ((1 + epsilon) * Real.log x - (1 - epsilon) * Real.log z1) +
    48 * Real.exp 1 * MAPJutilaOneSeparatedExponentialPacking.integerExponentialMass) *
      ((R : ℝ) ^ 2 * (harmonic R : ℝ) ^ 8)

/-- Explicit quadratic shifted-contour coefficient on the source rectangle. -/
def sourceAnalyticBudget (q R : ℕ) (epsilon z1 T : ℝ) : ℝ :=
  (4800 * (q : ℝ) ^ 2 * (5 + 2 * T) ^ 2 * p53UniversalVerticalMass +
    153600 * (2 : ℝ) ^ q.primeFactors.card * (5 + 2 * T) ^ 6 *
      p53PrincipalUniversalVerticalMass) *
    (2 * Real.exp (-((1 - epsilon) * Real.log z1) / 2)) *
    ((R : ℝ) ^ 2 * (harmonic R : ℝ) ^ 8)

theorem residueBudget_source_le
    {S : Finset ℕ} {R : ℕ} (hS : S ⊆ Finset.Icc 1 R)
    (hSq : ∀ r ∈ S, Squarefree r)
    {epsilon z1 x xi upsilon : ℝ}
    (hxi : (1 - epsilon) * Real.log z1 ≤ xi)
    (hups : upsilon ≤ (1 + epsilon) * Real.log x)
    (hcross : xi ≤ upsilon) :
    (12 * (upsilon - xi) + 48 * Real.exp 1 *
      MAPJutilaOneSeparatedExponentialPacking.integerExponentialMass) *
        p53NormalizedEulerMass S ≤ sourceResidueBudget R epsilon z1 x := by
  have hm := MAPJutilaP53NormalizedEulerMassBound.p53NormalizedEulerMass_le_R_sq_mul_harmonic_pow_eight hS hSq
  have he : 0 ≤ MAPJutilaOneSeparatedExponentialPacking.integerExponentialMass :=
    tsum_nonneg fun k => (Real.exp_pos _).le
  have hcoef : 0 ≤ 12 * (upsilon - xi) + 48 * Real.exp 1 *
      MAPJutilaOneSeparatedExponentialPacking.integerExponentialMass := by positivity
  unfold sourceResidueBudget
  exact (mul_le_mul_of_nonneg_left hm hcoef).trans
    (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

/-- The actual integrated pair-sector estimate with no envelope premises.
Its explicit coefficients still require source-parameter absorption. -/
theorem integratedCorrelationEstimateAt_sourceBudgets
    {q R : ℕ} [NeZero q] (rows : Finset (JutilaP53Row q))
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 R)
    (hSq : ∀ r ∈ S, Squarefree r)
    {alpha epsilon z1 x T : ℝ}
    (heps0 : 0 ≤ epsilon) (hepsHi : epsilon ≤ 1 / 8)
    (hz1 : 1 ≤ z1) (hz1x : z1 < x) (hT : 0 ≤ T)
    (hrowsT : ∀ row ∈ rows, |row.zero.im| ≤ T)
    (hrows : ∀ row ∈ rows,
      alpha ≤ row.zero.re ∧ row.zero.re ≤ alpha + epsilon)
    (hfiberSep : ∀ chi : DirichletCharacter ℂ q,
      CGLProofDAG.OneSeparated ((rows.filter (fun row => row.character = chi)).image
        (fun row => row.zero.im)))
    (hfiberCard : ∀ chi : DirichletCharacter ℂ q,
      ((rows.filter (fun row => row.character = chi)).image
        (fun row => row.zero.im)).card =
      (rows.filter (fun row => row.character = chi)).card)
    (hR : (R : ℝ) ^ 2 ≤ Real.exp ((1 - epsilon) * Real.log z1)) :
    JutilaP53IntegratedCorrelationEstimateAt rows S alpha epsilon z1 x
      (epsilon ^ 2 * Real.log z1 * Real.log x * sourceResidueBudget R epsilon z1 x)
      (epsilon ^ 2 * Real.log z1 * Real.log x * sourceAnalyticBudget q R epsilon z1 T) := by
  have hzpos : 0 < z1 := zero_lt_one.trans_le hz1
  have hlog : Real.log z1 < Real.log x :=
    Real.strictMonoOn_log hzpos (hzpos.trans hz1x) hz1x
  have hlo : (1 - epsilon) * Real.log z1 ≤ Real.log z1 := by
    have := Real.log_nonneg hz1
    nlinarith
  apply MAPJutilaP53IntegratedPairSectorAdapter.integratedCorrelationEstimateAt_of_pairSectorEnvelopes rows hS hSq
      heps0 hepsHi hz1 hz1x hrows hfiberSep hfiberCard (source_lcm_le_exp hS hR)
  · intro xi hxi upsilon hups
    exact residueBudget_source_le hS hSq hxi.1 hups.2
      (hxi.2.trans (hlog.le.trans hups.1))
  · intro xi hxi upsilon hups
    exact sum_p53AnalyticPairBudget_source_le rows hS hSq hzpos hxi.1
      (hlo.trans (hlog.le.trans hups.1)) hT hrowsT

/-- The signed residue budget; unlike its absolute-mass precursor, this
retains the exact orthogonality in the primed pseudocharacter sum. -/
def sourceSharpResidueBudget (R : ℕ) (epsilon z1 x : ℝ) : ℝ :=
  (12 * ((1 + epsilon) * Real.log x - (1 - epsilon) * Real.log z1) +
    48 * Real.exp 1 * MAPJutilaOneSeparatedExponentialPacking.integerExponentialMass) *
      (harmonic R : ℝ)

/-- Explicit integrated source estimate with the signed residue cancellation
fully discharged. The half-line analytic coefficient remains visible. -/
theorem integratedCorrelationEstimateAt_sharpSourceBudgets
    {q R : ℕ} [NeZero q] (rows : Finset (JutilaP53Row q))
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 R)
    (hSq : ∀ r ∈ S, Squarefree r) (hcop : ∀ r ∈ S, r.Coprime q)
    {alpha epsilon z1 x T : ℝ}
    (heps0 : 0 ≤ epsilon) (hepsHi : epsilon ≤ 1 / 8)
    (hz1 : 1 ≤ z1) (hz1x : z1 < x) (hT : 0 ≤ T)
    (hrowsT : ∀ row ∈ rows, |row.zero.im| ≤ T)
    (hrows : ∀ row ∈ rows,
      alpha ≤ row.zero.re ∧ row.zero.re ≤ alpha + epsilon)
    (hfiberSep : ∀ chi : DirichletCharacter ℂ q,
      CGLProofDAG.OneSeparated ((rows.filter (fun row => row.character = chi)).image
        (fun row => row.zero.im)))
    (hfiberCard : ∀ chi : DirichletCharacter ℂ q,
      ((rows.filter (fun row => row.character = chi)).image
        (fun row => row.zero.im)).card =
      (rows.filter (fun row => row.character = chi)).card) :
    JutilaP53IntegratedCorrelationEstimateAt rows S alpha epsilon z1 x
      (epsilon ^ 2 * Real.log z1 * Real.log x * sourceSharpResidueBudget R epsilon z1 x)
      (epsilon ^ 2 * Real.log z1 * Real.log x * sourceAnalyticBudget q R epsilon z1 T) := by
  have hzpos : 0 < z1 := zero_lt_one.trans_le hz1
  have hlog : Real.log z1 < Real.log x :=
    Real.strictMonoOn_log hzpos (hzpos.trans hz1x) hz1x
  have hlo : (1 - epsilon) * Real.log z1 ≤ Real.log z1 := by
    have := Real.log_nonneg hz1
    nlinarith
  apply MAPJutilaP53SharpIntegratedPairSectorAdapter.integratedCorrelationEstimateAt_of_sharpPairSectorEnvelopes
      rows hS hSq hcop heps0 hepsHi hz1 hz1x hrows hfiberSep hfiberCard
  · intro xi hxi upsilon hups
    unfold sourceSharpResidueBudget
    apply mul_le_mul_of_nonneg_right
    · linarith [hxi.1, hups.2]
    · have hmass := MAPJutilaP53SignedDivisorMass.sum_totient_div_sq_le_harmonic hS
      exact (Finset.sum_nonneg (fun r hr =>
        div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))).trans hmass
  · intro xi hxi upsilon hups
    exact sum_p53AnalyticPairBudget_source_le rows hS hSq hzpos hxi.1
      (hlo.trans (hlog.le.trans hups.1)) hT hrowsT

end
end MAPJutilaP53SourceScaleEnvelopes

#print axioms MAPJutilaP53SourceScaleEnvelopes.cast_lcm_le_R_sq
#print axioms MAPJutilaP53SourceScaleEnvelopes.source_lcm_le_exp
#print axioms MAPJutilaP53SourceScaleEnvelopes.p53CpowEndpointBound_source_le
#print axioms MAPJutilaP53SourceScaleEnvelopes.sum_p53AnalyticPairBudget_source_le

#print axioms MAPJutilaP53SourceScaleEnvelopes.integratedCorrelationEstimateAt_sourceBudgets

#print axioms MAPJutilaP53SourceScaleEnvelopes.integratedCorrelationEstimateAt_sharpSourceBudgets
