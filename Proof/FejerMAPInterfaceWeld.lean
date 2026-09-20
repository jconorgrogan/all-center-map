import HarmonicInterfaces

/-!
# Fejer--MAP elementary interface weld

This module proves only elementary set, measure, and quantifier interfaces
adjacent to the all-center local MAP declaration.  It introduces no analytic
estimate and no proposition-valued replacement for one.
-/

namespace FejerMAPInterfaceWeld

open AddCircle MeasureTheory Set
open scoped BigOperators ArithmeticFunction

noncomputable section

open PrimePairEndpoints MAPHarmonicEndpoint

/-- Restricting `minorWeight` to an arc is definitionally the same as
restricting the raw norm-square density to the intersection of that arc with
the minor arcs. -/
theorem integral_minorWeight_centeredArc
    (X H : ℝ) (B D : ℕ) (center : UnitAddCircle) :
    (∫ α in centeredArc H center,
        minorWeight X B D α ∂AddCircle.haarAddCircle) =
      ∫ α in centeredArc H center ∩ minorArcs X B D,
        ‖primeExponentialSum X α‖ ^ 2
          ∂AddCircle.haarAddCircle := by
  unfold minorWeight
  rw [MeasureTheory.setIntegral_indicator (measurableSet_minorArcs X B D)]

/-- Increasing both logarithmic cutoff exponents enlarges the major arcs.
The positivity of `X` is the analytic scale hypothesis needed to preserve the
direction of the width inequality; `1 ≤ log X` is needed for monotonicity of
the natural powers. -/
theorem majorArcs_mono_cutoffs
    {X : ℝ} {B₁ B₂ D₁ D₂ : ℕ}
    (hX : 0 < X) (hlog : 1 ≤ Real.log X)
    (hB : B₁ ≤ B₂) (hD : D₁ ≤ D₂) :
    majorArcs X B₁ D₁ ⊆ majorArcs X B₂ D₂ := by
  intro α hα
  rcases hα with ⟨q, a, hq1, hqB, haq, hcop, hdist⟩
  refine ⟨q, a, hq1, ?_, haq, hcop, ?_⟩
  · exact hqB.trans (pow_le_pow_right₀ hlog hB)
  · exact hdist.trans
      (div_le_div_of_nonneg_right (pow_le_pow_right₀ hlog hD) hX.le)

theorem majorArcs_mono_firstExponent
    {X : ℝ} {B₁ B₂ D : ℕ}
    (hX : 0 < X) (hlog : 1 ≤ Real.log X) (hB : B₁ ≤ B₂) :
    majorArcs X B₁ D ⊆ majorArcs X B₂ D := by
  exact majorArcs_mono_cutoffs hX hlog hB le_rfl

theorem majorArcs_mono_secondExponent
    {X : ℝ} {B D₁ D₂ : ℕ}
    (hX : 0 < X) (hlog : 1 ≤ Real.log X) (hD : D₁ ≤ D₂) :
    majorArcs X B D₁ ⊆ majorArcs X B D₂ := by
  exact majorArcs_mono_cutoffs hX hlog le_rfl hD

/-- Enlarging the major-arc cutoffs shrinks the minor arcs. -/
theorem minorArcs_anti_cutoffs
    {X : ℝ} {B₁ B₂ D₁ D₂ : ℕ}
    (hX : 0 < X) (hlog : 1 ≤ Real.log X)
    (hB : B₁ ≤ B₂) (hD : D₁ ≤ D₂) :
    minorArcs X B₂ D₂ ⊆ minorArcs X B₁ D₁ := by
  exact Set.compl_subset_compl.mpr
    (majorArcs_mono_cutoffs hX hlog hB hD)

/-- Pointwise version of preservation of minor-arc mass after the major arcs
are enlarged. -/
theorem minorWeight_anti_cutoffs
    {X : ℝ} {B₁ B₂ D₁ D₂ : ℕ}
    (hX : 0 < X) (hlog : 1 ≤ Real.log X)
    (hB : B₁ ≤ B₂) (hD : D₁ ≤ D₂)
    (a : UnitAddCircle) :
    minorWeight X B₂ D₂ a ≤ minorWeight X B₁ D₁ a := by
  have hminor := minorArcs_anti_cutoffs hX hlog hB hD
  by_cases ha : a ∈ minorArcs X B₂ D₂
  · have ha' : a ∈ minorArcs X B₁ D₁ := hminor ha
    simp [minorWeight, ha, ha']
  · simp only [minorWeight, Set.indicator_of_notMem ha]
    exact minorWeight_nonneg X B₁ D₁ a

/-- Every centered-arc minor mass decreases when the major-arc cutoffs are
enlarged. -/
theorem integral_minorWeight_anti_cutoffs
    {X H : ℝ} {B₁ B₂ D₁ D₂ : ℕ}
    (hX : 0 < X) (hlog : 1 ≤ Real.log X)
    (hB : B₁ ≤ B₂) (hD : D₁ ≤ D₂)
    (center : UnitAddCircle) :
    (∫ a in centeredArc H center, minorWeight X B₂ D₂ a
        ∂AddCircle.haarAddCircle) ≤
      ∫ a in centeredArc H center, minorWeight X B₁ D₁ a
        ∂AddCircle.haarAddCircle := by
  apply MeasureTheory.integral_mono_ae
  · exact (minorWeight_integrable X B₂ D₂).integrableOn
  · exact (minorWeight_integrable X B₁ D₁).integrableOn
  · exact Filter.Eventually.of_forall
      (minorWeight_anti_cutoffs hX hlog hB hD)

/-- A uniform local mass bound survives enlargement of both cutoffs. -/
theorem localMassBound_preserved_of_enlarge_cutoffs
    {X H M : ℝ} {B₁ B₂ D₁ D₂ : ℕ}
    (hX : 0 < X) (hlog : 1 ≤ Real.log X)
    (hB : B₁ ≤ B₂) (hD : D₁ ≤ D₂)
    (hbound : ∀ center : UnitAddCircle,
      (∫ a in centeredArc H center, minorWeight X B₁ D₁ a
          ∂AddCircle.haarAddCircle) ≤ M) :
    ∀ center : UnitAddCircle,
      (∫ a in centeredArc H center, minorWeight X B₂ D₂ a
          ∂AddCircle.haarAddCircle) ≤ M := by
  intro center
  exact (integral_minorWeight_anti_cutoffs hX hlog hB hD center).trans
    (hbound center)

/-- Exact paper-facing specialization of `AllCenterLocalMAP`.  The mask
exponents remain outside, and therefore uniform in, `X`, `H`, and `center`. -/
theorem allCenterLocalMAP_minorWeight
    (hMAP : AllCenterLocalMAP) :
    ∀ A ε : ℝ, 0 < A → 0 < ε →
      ∃ B D : ℕ, ∃ C X₀ : ℝ,
        0 < C ∧ 2 ≤ X₀ ∧
        ∀ X H : ℝ, X₀ ≤ X →
          Real.rpow X (2 / 15 + ε) ≤ H →
          ∀ center : UnitAddCircle,
            (∫ α in centeredArc H center,
                minorWeight X B D α ∂AddCircle.haarAddCircle) ≤
              C * X * Real.rpow (Real.log X) (-A) := by
  intro A ε hA hε
  rcases hMAP A ε hA hε with ⟨B, D, C, X₀, hC, hX₀, hlocal⟩
  refine ⟨B, D, C, X₀, hC, hX₀, ?_⟩
  intro X H hXX₀ hH center
  rw [integral_minorWeight_centeredArc]
  exact hlocal X H hXX₀ hH center

/-- Elementary global `L²` bound.  This uses only the exact Parseval identity
and `vonMangoldt n ≤ log n`; it deliberately does not use the prime number
theorem and therefore pays `log²` rather than the manuscript's `log`. -/
theorem integral_normSq_primeExponentialSum_le_log_sq
    {X : ℝ} (hX : 1 ≤ X) :
    (∫ α : UnitAddCircle,
        ‖primeExponentialSum X α‖ ^ 2
          ∂AddCircle.haarAddCircle) ≤
      2 * X * (Real.log (2 * X)) ^ 2 := by
  rw [integral_normSq_primeExponentialSum]
  let s := Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊
  have h2X0 : 0 ≤ 2 * X := by positivity
  have hlog2X0 : 0 ≤ Real.log (2 * X) := by
    apply Real.log_nonneg
    nlinarith
  have hpoint : ∀ n ∈ s,
      (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 ≤
        (Real.log (2 * X)) ^ 2 := by
    intro n hn
    have hnIoc : n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ := hn
    have hn_bounds := Finset.mem_Ioc.mp hnIoc
    have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le ⌊X⌋₊) hn_bounds.1
    have hncastpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos
    have hncast_le_floor : (n : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by
      exact_mod_cast hn_bounds.2
    have hncast_le : (n : ℝ) ≤ 2 * X :=
      hncast_le_floor.trans (Nat.floor_le h2X0)
    have hlogn_le : Real.log (n : ℝ) ≤ Real.log (2 * X) :=
      Real.log_le_log hncastpos hncast_le
    have hvm_le : ArithmeticFunction.vonMangoldt n ≤ Real.log (2 * X) :=
      ArithmeticFunction.vonMangoldt_le_log.trans hlogn_le
    exact (sq_le_sq₀ ArithmeticFunction.vonMangoldt_nonneg hlog2X0).2 hvm_le
  have hsum :
      (∑ n ∈ s, (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2) ≤
        (s.card : ℝ) * (Real.log (2 * X)) ^ 2 := by
    calc
      (∑ n ∈ s, (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2) ≤
          ∑ _n ∈ s, (Real.log (2 * X)) ^ 2 := by
            exact Finset.sum_le_sum hpoint
      _ = (s.card : ℝ) * (Real.log (2 * X)) ^ 2 := by simp
  have hcardNat : s.card ≤ ⌊2 * X⌋₊ := by
    simpa only [s, Nat.card_Ioc] using Nat.sub_le ⌊2 * X⌋₊ ⌊X⌋₊
  have hcardFloor : (s.card : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by
    exact_mod_cast hcardNat
  have hcard : (s.card : ℝ) ≤ 2 * X :=
    hcardFloor.trans (Nat.floor_le h2X0)
  have hmul := mul_le_mul_of_nonneg_right hcard (sq_nonneg (Real.log (2 * X)))
  change (∑ n ∈ s, (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2) ≤
    2 * X * (Real.log (2 * X)) ^ 2
  exact hsum.trans hmul

end

end FejerMAPInterfaceWeld
