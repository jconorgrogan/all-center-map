import MajorArcPrimePairWeld
import ContinuousKernelOverlap

/-!
# Integrated pointwise-error weld for one MAP rational arc

The only analytic premise in the final specialization is the published
pointwise approximation to the prime polynomial.  Squaring, Fourier phase,
interval length, and integration are proved here.
-/

namespace MAPMajorArcIntegratedError

open AddCircle MeasureTheory Metric Set
open MAPMajorArcWeld MAPContinuousOverlap

noncomputable section

/-- A generic interval error lemma for squared magnitudes carrying a unit
complex phase. -/
theorem norm_interval_normSq_phase_sub_le
    {R E M : ℝ} (hR : 0 ≤ R) {actual model phase : ℝ → ℂ}
    (hactual : Continuous actual) (hmodel : Continuous model)
    (hphase : Continuous phase) (hphaseNorm : ∀ β, ‖phase β‖ = 1)
    (happrox : ∀ β ∈ Set.uIcc (-R) R, ‖actual β - model β‖ ≤ E)
    (hmodelBound : ∀ β ∈ Set.uIcc (-R) R, ‖model β‖ ≤ M) :
    ‖(∫ β in -R..R, ((‖actual β‖ ^ 2 : ℝ) : ℂ) * phase β) -
      ∫ β in -R..R, ((‖model β‖ ^ 2 : ℝ) : ℂ) * phase β‖ ≤
        2 * R * (E * (2 * M + E)) := by
  have hactualInt : IntervalIntegrable
      (fun β => ((‖actual β‖ ^ 2 : ℝ) : ℂ) * phase β) volume (-R) R :=
    ((Complex.continuous_ofReal.comp (hactual.norm.pow 2)).mul hphase).intervalIntegrable _ _
  have hmodelInt : IntervalIntegrable
      (fun β => ((‖model β‖ ^ 2 : ℝ) : ℂ) * phase β) volume (-R) R :=
    ((Complex.continuous_ofReal.comp (hmodel.norm.pow 2)).mul hphase).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub hactualInt hmodelInt]
  calc
    ‖∫ β in -R..R,
        ((‖actual β‖ ^ 2 : ℝ) : ℂ) * phase β -
          ((‖model β‖ ^ 2 : ℝ) : ℂ) * phase β‖ ≤
        (E * (2 * M + E)) * |R - (-R)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro β hβ
      rw [← sub_mul, norm_mul, hphaseNorm, mul_one]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have hsq := abs_normSq_sub_normSq_le_of_error
        (happrox β (Set.uIoc_subset_uIcc hβ))
      have hEnonneg : 0 ≤ E :=
        (norm_nonneg _).trans (happrox β (Set.uIoc_subset_uIcc hβ))
      calc
        |‖actual β‖ ^ 2 - ‖model β‖ ^ 2| ≤
            E * (2 * ‖model β‖ + E) := hsq
        _ ≤ E * (2 * M + E) := by
          gcongr
          exact hmodelBound β (Set.uIoc_subset_uIcc hβ)
    _ = 2 * R * (E * (2 * M + E)) := by
      rw [show R - -R = 2 * R by ring, abs_of_nonneg (by positivity)]
      ring

/-- The actual prime-polynomial contribution of one lifted rational arc. -/
def actualLiftedRationalArc
    (X R : ℝ) (q a : ℕ) (h : ℤ) : ℂ :=
  ∫ β in -R..R,
    ((‖PrimePairEndpoints.primeExponentialSum X
      (rationalCenter q a + (β : UnitAddCircle))‖ ^ 2 : ℝ) : ℂ) *
      fourier (-h) (rationalCenter q a + (β : UnitAddCircle))

theorem continuous_primePolynomial_lift (X : ℝ) (q a : ℕ) :
    Continuous (fun β : ℝ => PrimePairEndpoints.primeExponentialSum X
      (rationalCenter q a + (β : UnitAddCircle))) := by
  unfold PrimePairEndpoints.primeExponentialSum
  fun_prop

/-- One-arc integrated consequence of the published pointwise major-arc
approximation.  No integrated estimate is assumed. -/
theorem norm_actualLiftedRationalArc_sub_modeled_le
    {X R E : ℝ} {q a : ℕ} {h : ℤ} (hX : 0 ≤ X) (hR : 0 ≤ R)
    (happrox : ∀ β ∈ Set.uIcc (-R) R,
      ‖PrimePairEndpoints.primeExponentialSum X
          (rationalCenter q a + (β : UnitAddCircle)) -
        primeMajorCoefficient q * dyadicAmplitude X β‖ ≤ E) :
    ‖actualLiftedRationalArc X R q a h -
        modeledRationalArc (dyadicContinuousAmplitude X) R q a h‖ ≤
      2 * R *
        (E * (2 * (‖primeMajorCoefficient q‖ * X) + E)) := by
  unfold actualLiftedRationalArc modeledRationalArc
  apply norm_interval_normSq_phase_sub_le hR
  · exact continuous_primePolynomial_lift X q a
  · exact continuous_const.mul (by
      simpa only [dyadicContinuousAmplitude] using continuous_dyadicAmplitude X)
  · fun_prop
  · intro β
    rw [fourier_apply, Circle.norm_coe]
  · intro β hβ
    simpa only [dyadicContinuousAmplitude, dyadicAmplitude] using happrox β hβ
  · intro β hβ
    change ‖primeMajorCoefficient q * dyadicAmplitude X β‖ ≤
      ‖primeMajorCoefficient q‖ * X
    rw [norm_mul]
    gcongr
    exact norm_dyadicAmplitude_le_length hX

/-! ## Finite summation over every reduced rational arc -/

/-- The actual lifted contribution of all reduced rational arcs with
`1 ≤ q ≤ Q`.  Disjointness is deliberately not built into this definition:
that geometric fact is proved separately for the manuscript's literal mask. -/
def actualLiftedMajorContribution
    (X R : ℝ) (Q : ℕ) (h : ℤ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 Q,
    ∑ a ∈ reducedResidues q, actualLiftedRationalArc X R q a h

/-- MAP-owned integration and finite-summation weld.  A uniform pointwise
prime-polynomial approximation on the legal lifted arcs is converted into the
error for the complete modeled major-arc sum; no integrated estimate is
assumed. -/
theorem norm_actualLiftedMajorContribution_sub_modeled_le
    {X R E : ℝ} {Q : ℕ} {h : ℤ} (hX : 0 ≤ X) (hR : 0 ≤ R)
    (happrox : ∀ q ∈ Finset.Icc 1 Q, ∀ a ∈ reducedResidues q,
      ∀ β ∈ Set.uIcc (-R) R,
        ‖PrimePairEndpoints.primeExponentialSum X
            (rationalCenter q a + (β : UnitAddCircle)) -
          primeMajorCoefficient q * dyadicAmplitude X β‖ ≤ E) :
    ‖actualLiftedMajorContribution X R Q h -
        modeledDyadicMajorContribution X R Q h‖ ≤
      ∑ q ∈ Finset.Icc 1 Q,
        ∑ _a ∈ reducedResidues q,
          2 * R * (E * (2 * (‖primeMajorCoefficient q‖ * X) + E)) := by
  unfold actualLiftedMajorContribution modeledDyadicMajorContribution
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ q ∈ Finset.Icc 1 Q,
        ((∑ a ∈ reducedResidues q, actualLiftedRationalArc X R q a h) -
          ∑ a ∈ reducedResidues q,
            modeledRationalArc (dyadicContinuousAmplitude X) R q a h)‖ ≤
        ∑ q ∈ Finset.Icc 1 Q,
          ‖(∑ a ∈ reducedResidues q, actualLiftedRationalArc X R q a h) -
            ∑ a ∈ reducedResidues q,
              modeledRationalArc (dyadicContinuousAmplitude X) R q a h‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.Icc 1 Q,
        ∑ a ∈ reducedResidues q,
          ‖actualLiftedRationalArc X R q a h -
            modeledRationalArc (dyadicContinuousAmplitude X) R q a h‖ := by
      gcongr with q hq
      rw [← Finset.sum_sub_distrib]
      exact norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.Icc 1 Q,
        ∑ _a ∈ reducedResidues q,
          2 * R * (E * (2 * (‖primeMajorCoefficient q‖ * X) + E)) := by
      gcongr with q hq a ha
      exact norm_actualLiftedRationalArc_sub_modeled_le hX hR
        (happrox q hq a ha)

/-- Actual contribution at the manuscript's literal polylogarithmic cutoffs. -/
def actualLiftedPaperMajorContribution
    (X : ℝ) (B D : ℕ) (h : ℤ) : ℂ :=
  actualLiftedMajorContribution X (paperArcRadius X D)
    (paperDenominatorCutoff X B) h

/-- Literal-cutoff specialization of the integration weld.  Its sole
analytic premise has exactly the legal range of MRT Proposition 4.1: reduced
`a/q`, denominator at most `(log X)^B`, and
`|β| ≤ (log X)^D / X`. -/
theorem norm_actualLiftedPaperMajorContribution_sub_modeled_le
    {X E : ℝ} {B D : ℕ} {h : ℤ} (hX : 1 ≤ X)
    (hpointwise : ∀ q a : ℕ, ∀ β : ℝ,
      1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B →
      a < q → a.Coprime q →
      |β| ≤ paperArcRadius X D →
      ‖PrimePairEndpoints.primeExponentialSum X
          (rationalCenter q a + (β : UnitAddCircle)) -
        primeMajorCoefficient q * dyadicAmplitude X β‖ ≤ E) :
    ‖actualLiftedPaperMajorContribution X B D h -
        modeledPaperMajorContribution X B D h‖ ≤
      ∑ q ∈ Finset.Icc 1 (paperDenominatorCutoff X B),
        ∑ _a ∈ reducedResidues q,
          2 * paperArcRadius X D *
            (E * (2 * (‖primeMajorCoefficient q‖ * X) + E)) := by
  have hX0 : 0 ≤ X := le_trans (by norm_num) hX
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  have hR : 0 ≤ paperArcRadius X D := by
    unfold paperArcRadius
    positivity
  unfold actualLiftedPaperMajorContribution modeledPaperMajorContribution
  apply norm_actualLiftedMajorContribution_sub_modeled_le hX0 hR
  intro q hq a ha β hβ
  have hqIcc : 1 ≤ q ∧ q ≤ paperDenominatorCutoff X B :=
    Finset.mem_Icc.mp hq
  have haq := mem_reducedResidues.mp ha
  have hqReal : (q : ℝ) ≤ (Real.log X) ^ B := by
    exact (Nat.le_floor_iff (pow_nonneg hlog B)).mp hqIcc.2
  have hβabs : |β| ≤ paperArcRadius X D := by
    rw [abs_le]
    simpa [Set.uIcc_of_le (neg_le_self hR)] using hβ
  exact hpointwise q a β hqIcc.1 hqReal haq.1 haq.2 hβabs

/-! ## Elementary parameter cost of the finite rational-arc family -/

theorem norm_primeMajorCoefficient_le_one {q : ℕ} (hq : 1 ≤ q) :
    ‖primeMajorCoefficient q‖ ≤ (1 : ℝ) := by
  unfold primeMajorCoefficient
  rw [norm_div]
  simp only [Complex.norm_intCast, Complex.norm_natCast]
  have hmu : |ArithmeticFunction.moebius q| ≤ 1 :=
    ArithmeticFunction.abs_moebius_le_one
  have hphiNat : 1 ≤ q.totient := Nat.totient_pos.mpr (by omega)
  have hphi : (1 : ℝ) ≤ q.totient := by exact_mod_cast hphiNat
  apply (div_le_one (by positivity)).2
  exact le_trans (by exact_mod_cast hmu) hphi

theorem card_reducedResidues_le (q : ℕ) :
    (reducedResidues q).card ≤ q := by
  unfold reducedResidues
  simpa using Finset.card_le_card
    (Finset.filter_subset (fun a => a.Coprime q) (Finset.range q))

/-- There are at most `Q²` legal reduced pairs with `1 ≤ q ≤ Q`.
This is the exact elementary counting loss used to choose the pointwise
logarithmic saving. -/
theorem sum_reducedResidues_const_le_sq
    {Q : ℕ} {C : ℝ} (hC : 0 ≤ C) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ _a ∈ reducedResidues q, C) ≤
      (Q : ℝ) ^ 2 * C := by
  calc
    (∑ q ∈ Finset.Icc 1 Q, ∑ _a ∈ reducedResidues q, C) ≤
        ∑ _q ∈ Finset.Icc 1 Q, (Q : ℝ) * C := by
      gcongr with q hq
      rw [Finset.sum_const, nsmul_eq_mul]
      have hqIcc := Finset.mem_Icc.mp hq
      have hc : ((reducedResidues q).card : ℝ) ≤ Q := by
        exact_mod_cast (le_trans (card_reducedResidues_le q) hqIcc.2)
      exact mul_le_mul_of_nonneg_right hc hC
    _ = (Q : ℝ) ^ 2 * C := by
      rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
      simp
      ring

/-- Fully elementary coarse parameter weld.  It turns the pointwise MRT error
`E` into at most `Q² · 2R · E(2X+E)` at the manuscript's cutoffs. -/
theorem norm_actualLiftedPaperMajorContribution_sub_modeled_le_coarse
    {X E : ℝ} {B D : ℕ} {h : ℤ} (hX : 1 ≤ X) (hE : 0 ≤ E)
    (hpointwise : ∀ q a : ℕ, ∀ β : ℝ,
      1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B →
      a < q → a.Coprime q →
      |β| ≤ paperArcRadius X D →
      ‖PrimePairEndpoints.primeExponentialSum X
          (rationalCenter q a + (β : UnitAddCircle)) -
        primeMajorCoefficient q * dyadicAmplitude X β‖ ≤ E) :
    ‖actualLiftedPaperMajorContribution X B D h -
        modeledPaperMajorContribution X B D h‖ ≤
      ((paperDenominatorCutoff X B : ℕ) : ℝ) ^ 2 *
        (2 * paperArcRadius X D * (E * (2 * X + E))) := by
  have hR : 0 ≤ paperArcRadius X D := by
    unfold paperArcRadius
    have hlog := Real.log_nonneg hX
    positivity
  calc
    ‖actualLiftedPaperMajorContribution X B D h -
        modeledPaperMajorContribution X B D h‖ ≤
      ∑ q ∈ Finset.Icc 1 (paperDenominatorCutoff X B),
        ∑ _a ∈ reducedResidues q,
          2 * paperArcRadius X D *
            (E * (2 * (‖primeMajorCoefficient q‖ * X) + E)) :=
      norm_actualLiftedPaperMajorContribution_sub_modeled_le hX hpointwise
    _ ≤ ∑ _q ∈ Finset.Icc 1 (paperDenominatorCutoff X B),
        ∑ _a ∈ reducedResidues _q,
          2 * paperArcRadius X D * (E * (2 * X + E)) := by
      gcongr with q hq a ha
      have hqIcc := Finset.mem_Icc.mp hq
      have hcoeff := norm_primeMajorCoefficient_le_one hqIcc.1
      nlinarith [norm_nonneg (primeMajorCoefficient q)]
    _ ≤ ((paperDenominatorCutoff X B : ℕ) : ℝ) ^ 2 *
        (2 * paperArcRadius X D * (E * (2 * X + E))) := by
      apply sum_reducedResidues_const_le_sq
      positivity

end

end MAPMajorArcIntegratedError
