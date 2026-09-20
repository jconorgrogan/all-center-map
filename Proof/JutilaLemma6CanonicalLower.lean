import JutilaLemma6DetectorIdentity
namespace MAPJutilaLemma6CanonicalLower
open scoped BigOperators
open MAPJutilaPseudocharacterHarmonicLower MAPJutilaLemma6LowerWeld
open MAPJutilaLemma6DetectorIdentity MAPJutilaLemma6DirectTail
open MAPJutilaP53CoefficientQuotient MAPJutilaP53AggregateCorrelationLeaf
noncomputable section

theorem norm_detector_ge_of_error_two
    {X : ℝ} {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) (hX : 2 ≤ X)
    {g error : ℂ}
    (hidentity : g = (lemmaSixMain X q R : ℂ) + error)
    (herror : ‖error‖ ≤ 2)
    (hsize : 4 ≤ (1 / 8 : ℝ) *
      ((Nat.totient q : ℝ) / (q : ℝ)) * Real.log (R : ℝ)) :
    (1 / 16 : ℝ) * ((Nat.totient q : ℝ) / (q : ℝ)) *
        Real.log (R : ℝ) ≤ ‖g‖ := by
  have hXpos : 0 < X := by linarith
  have hinv : 1 / X ≤ 1 / 2 := by
    apply (div_le_iff₀ hXpos).2
    nlinarith
  have hhalfExp : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
    nlinarith [Real.add_one_le_exp (-(1 / 2 : ℝ))]
  have hexpMono : Real.exp (-(1 / 2 : ℝ)) ≤ Real.exp (-(1 / X)) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hexpHalf : (1 / 2 : ℝ) ≤ Real.exp (-(1 / X)) :=
    hhalfExp.trans hexpMono
  have hlog0 : 0 ≤ Real.log (R : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hR
  have hratio0 : 0 ≤ (Nat.totient q : ℝ) / (q : ℝ) := by positivity
  have hlowerCore0 : 0 ≤
      (1 / 4 : ℝ) * ((Nat.totient q : ℝ) / (q : ℝ)) *
        Real.log (R : ℝ) := by positivity
  let lower : ℝ :=
    (1 / 8 : ℝ) * ((Nat.totient q : ℝ) / (q : ℝ)) *
      Real.log (R : ℝ)
  have hmainLower : lower ≤ lemmaSixMain X q R := by
    have hharmonic := quarter_totientRatio_log_le_jutilaPrimedHarmonic
      (q := q) (R := R) hq
    unfold lower lemmaSixMain
    calc
      (1 / 8 : ℝ) * ((Nat.totient q : ℝ) / (q : ℝ)) *
          Real.log (R : ℝ) =
        (1 / 2 : ℝ) *
          ((1 / 4 : ℝ) * ((Nat.totient q : ℝ) / (q : ℝ)) *
            Real.log (R : ℝ)) := by ring
      _ ≤ Real.exp (-(1 / X)) * jutilaPrimedHarmonic q R :=
        mul_le_mul hexpHalf hharmonic hlowerCore0 (Real.exp_pos _).le
  have hmain0 : 0 ≤ lemmaSixMain X q R := lemmaSixMain_nonneg X q R
  have hmainNorm : ‖(lemmaSixMain X q R : ℂ)‖ = lemmaSixMain X q R := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hmain0]
  have hreverse : lemmaSixMain X q R ≤ ‖g‖ + ‖error‖ := by
    calc
      lemmaSixMain X q R = ‖(lemmaSixMain X q R : ℂ)‖ := hmainNorm.symm
      _ = ‖g - error‖ := by rw [hidentity]; ring_nf
      _ ≤ ‖g‖ + ‖error‖ := norm_sub_le _ _
  have hlowerNorm : lower - 2 ≤ ‖g‖ := by linarith
  have hhalf : lower / 2 ≤ lower - 2 := by
    dsimp [lower] at hsize ⊢
    linarith
  have htarget :
      (1 / 16 : ℝ) * ((Nat.totient q : ℝ) / (q : ℝ)) *
          Real.log (R : ℝ) =
        lower / 2 := by
    dsimp [lower]
    ring
  rw [htarget]
  exact hhalf.trans hlowerNorm


/-- Actual common polynomial lower bound. The two literal analytic errors
are charged separately; the exact detector identity is proved, not assumed. -/
theorem canonical_polynomial_lower_of_series_tail_le_one
    {q : ℕ} (row : JutilaP53Row q) (hq : 0 < q)
    {z1 z2 : ℝ} (hz1 : 1 < z1) (hz12 : z1 < z2)
    (alpha : ℝ) {R : ℕ} (hR : 1 ≤ R)
    (hrho : 0 ≤ row.zero.re) {X : ℝ} (hX : 2 ≤ X)
    {x : ℕ} (hx : 1 ≤ x)
    (hseries : ‖∑' n : ℕ, jutilaLemmaSixDirectTerm row.character z1 z2
      (jutilaPrimedRSet q R) row.zero X n‖ ≤ 1)
    (htail : ‖∑' k : ℕ, jutilaLemmaSixDirectTerm row.character z1 z2
      (jutilaPrimedRSet q R) row.zero X (k + (x + 1))‖ ≤ 1)
    (hsize : 4 ≤ (1 / 8 : ℝ) *
      ((Nat.totient q : ℝ) / (q : ℝ)) * Real.log (R : ℝ)) :
    (1 / 16 : ℝ) * ((Nat.totient q : ℝ) / (q : ℝ)) * Real.log (R : ℝ) ≤
      ‖∑ n ∈ detectorColumns z1 (jutilaPrimedRSet q R) x,
        jutilaP53DetectedCoefficient z1 z2 alpha X (jutilaPrimedRSet q R) n *
          jutilaP53Phase alpha row n‖ := by
  have hid := neg_canonical_polynomial_eq_main_add_error row hz1 hz12
    alpha R hrho (show 0 < X by linarith) hx
  have herr : ‖(∑' k : ℕ, jutilaLemmaSixDirectTerm row.character z1 z2
      (jutilaPrimedRSet q R) row.zero X (k + (x + 1))) -
      ∑' n : ℕ, jutilaLemmaSixDirectTerm row.character z1 z2
      (jutilaPrimedRSet q R) row.zero X n‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by linarith)
  simpa only [norm_neg] using norm_detector_ge_of_error_two hq hR hX hid herr hsize

end
end MAPJutilaLemma6CanonicalLower
#print axioms MAPJutilaLemma6CanonicalLower.canonical_polynomial_lower_of_series_tail_le_one
