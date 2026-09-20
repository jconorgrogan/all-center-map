import JutilaP53SourceDivisorMass

/-! # Endpoint and exponent bookkeeping on the p.53 source rectangle

The page 52 image `tmp_jutila_page08.png` gives the literal choices
`R = D^epsilon`, `z1 = D^(1/2+7*epsilon)`, `z2 = D^(1/2+8*epsilon)`,
and `X = D^(1+12*epsilon)`. The separate `+6*epsilon` calculation below
is labeled a diagnostic; it is not attributed to the source.
-/
namespace MAPJutilaP53SourceRectangleBudget
open MAPJutilaP53SourceDivisorMass
noncomputable section

/-- Both scale endpoints decay at the same negative power uniformly over
the logarithmic source rectangle. -/
theorem sourceEndpoint_exp_le
    {epsilon z1 xi upsilon : ℝ} (heps0 : 0 ≤ epsilon) (heps1 : epsilon ≤ 1)
    (hxi : (1 - epsilon) * Real.log z1 ≤ xi)
    (hups : (1 - epsilon) * Real.log z1 ≤ upsilon) :
    sourceEndpoint (Real.exp upsilon) (Real.exp xi) epsilon ≤
      2 * Real.exp (-((1 - epsilon)^2) * Real.log z1) := by
  have hpoint (u : ℝ) (hu : (1 - epsilon) * Real.log z1 ≤ u) :
      Real.rpow (Real.exp u) (-1 + epsilon) ≤
        Real.exp (-((1 - epsilon)^2) * Real.log z1) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonpos_right hu (show -1 + epsilon ≤ 0 by linarith)
    nlinarith [h]
  exact (add_le_add (hpoint upsilon hups) (hpoint xi hxi)).trans_eq (by ring)

/-- Row-pair heights in `[-T,T]` cost at most a universal square-root factor
relative to the fixed-modulus height `q*T`. -/
theorem sqrt_pairHeight_le_sqrt_three_scale
    {q T : ℝ} (hq : 0 ≤ q) (hT : 1 ≤ T) :
    Real.sqrt (q * (1 + 2*T)) ≤ Real.sqrt (3*q*T) := by
  apply Real.sqrt_le_sqrt
  nlinarith [mul_nonneg hq (show 0 ≤ T-1 by linarith)]

/-- Diagnostic ledger for the smaller trial scale `z1=D^(1/2+6*epsilon)`.
This is not the published page 52 choice. -/
theorem trial_six_epsilon_ledger
    {epsilon : ℝ} (heps0 : 0 ≤ epsilon) (hepsHi : epsilon ≤ 1/100) :
    (1/2:ℝ) + 2*epsilon - (1-epsilon)^2*(1/2+6*epsilon) +
      2*epsilon*(1+12*epsilon) ≤ -epsilon/2 := by
  have hsq : epsilon^2 ≤ epsilon/100 := by
    nlinarith [mul_nonneg heps0 (show 0 ≤ 1/100-epsilon by linarith)]
  have hcube : 0 ≤ epsilon^3 := pow_nonneg heps0 _
  nlinarith

/-- Literal page 52 scale ledger. The `+7*epsilon` choice leaves a full
additional epsilon of reserve compared with the `+6*epsilon` diagnostic. -/
theorem source_seven_epsilon_ledger
    {epsilon : ℝ} (heps0 : 0 ≤ epsilon) (hepsHi : epsilon ≤ 1/100) :
    (1/2:ℝ) + 2*epsilon - (1-epsilon)^2*(1/2+7*epsilon) +
      2*epsilon*(1+12*epsilon) ≤ -(3/2)*epsilon := by
  have hsq : epsilon^2 ≤ epsilon/100 := by
    nlinarith [mul_nonneg heps0 (show 0 ≤ 1/100-epsilon by linarith)]
  have hcube : 0 ≤ epsilon^3 := pow_nonneg heps0 _
  nlinarith

/-- Keep the actual detector exponent `2-2*alpha` until the collar lower
bound on `alpha` is applied. -/
theorem source_seven_epsilon_ledger_of_alpha
    {epsilon alpha : ℝ} (heps0 : 0 ≤ epsilon) (hepsHi : epsilon ≤ 1/100)
    (halpha : 1-epsilon ≤ alpha) :
    (1/2:ℝ) + 2*epsilon - (1-epsilon)^2*(1/2+7*epsilon) +
      (2-2*alpha)*(1+12*epsilon) ≤ -(3/2)*epsilon := by
  have hdet : (2-2*alpha)*(1+12*epsilon) ≤ 2*epsilon*(1+12*epsilon) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  linarith [source_seven_epsilon_ledger heps0 hepsHi]
end
end MAPJutilaP53SourceRectangleBudget
#print axioms MAPJutilaP53SourceRectangleBudget.sourceEndpoint_exp_le
#print axioms MAPJutilaP53SourceRectangleBudget.source_seven_epsilon_ledger_of_alpha
