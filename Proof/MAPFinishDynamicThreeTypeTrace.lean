import MRTLemma215DynamicTypeIIFactorizationV3

/-!
# Source-exact traces for the three dynamic low types

This file closes the remaining purely finite classifier-to-polynomial seams.
In particular, Type-d1 and Type-d2 are identified with the literal masked
preliminary component, and every Type-d component is regrouped at the exact
factor selected by the classifier.  No analytic moment estimate is asserted.
-/

namespace MAPFinishDynamicThreeTypeTrace

set_option maxHeartbeats 1200000

open scoped ArithmeticFunction BigOperators
open ArithmeticFunction
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicPreliminaryV3 MRTLemma215DynamicSupportV3
open MRTLemma215DynamicFactorExtractionV3 MRTLemma215ScaleClassifierV3
open MRTLemma215DynamicOutcomeWeldV3 MRTLemma215DynamicRegroupingV3
open MRTLemma215DynamicClassificationV3
open HBPerronPacketIndexedSourceV2
open MAPMRTCorollary53Source

noncomputable section

/-! ## Exact removal of the already-enforced source mask -/

/-- The literal critical Dirichlet polynomial already sums only over
`X < n ≤ 2X`; applying the same sharp mask to its coefficients changes
nothing. -/
theorem criticalDirichletPolynomial_sourceBlockMask_eq
    (X : ℝ) (q₀ q₁ : ℕ) (f : ℕ → ℂ)
    (hfSupport : ∀ m, m ∉ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ → f m = 0)
    (chi : DirichletCharacter ℂ q₁) (t : ℝ) :
    criticalDirichletPolynomial X q₀ q₁
        (fun n ↦ if n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ then f n else 0)
        chi t =
      criticalDirichletPolynomial X q₀ q₁ f chi t := by
  unfold criticalDirichletPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hm : q₀ * n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊
  · simp [hm]
  · rw [hfSupport (q₀ * n) hm]
    simp [hm]

theorem componentIntegral_sourceBlockMask_eq
    (X H : ℝ) (q₀ q₁ : ℕ) (f : ℕ → ℂ) (beta eta : ℝ)
    (hfSupport : ∀ m, m ∉ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ → f m = 0)
    (component : OuterComponent) :
    componentIntegral X H q₀ q₁
        (fun n ↦ if n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ then f n else 0)
        beta eta component =
      componentIntegral X H q₀ q₁ f beta eta component := by
  unfold componentIntegral characterWindow
  simp_rw [criticalDirichletPolynomial_sourceBlockMask_eq
    X q₀ q₁ f hfSupport]

/-- Type-d1 is literally the source-masked preliminary component. -/
theorem dynamicComponentRemainderV3_typeD1_eq_masked
    {X delta H₀ : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (j : Fin 8) (hj : (j : ℕ) = 1)
    (houtcome : dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag =
      .typeD j) (n : ℕ) :
    dynamicComponentRemainderV3 (delta := delta) (H₀ := H₀)
        logIndex zbag mbag .typeD1 n =
      maskedDynamicComponentV3 logIndex zbag mbag n := by
  unfold dynamicComponentRemainderV3
  rw [houtcome]
  simp [hj]

/-- Type-d2 is literally the source-masked preliminary component. -/
theorem dynamicComponentRemainderV3_typeD2_eq_masked
    {X delta H₀ : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (j : Fin 8) (hj : (j : ℕ) = 2)
    (houtcome : dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag =
      .typeD j) (n : ℕ) :
    dynamicComponentRemainderV3 (delta := delta) (H₀ := H₀)
        logIndex zbag mbag .typeD2 n =
      maskedDynamicComponentV3 logIndex zbag mbag n := by
  unfold dynamicComponentRemainderV3
  rw [houtcome]
  have hj1 : (j : ℕ) ≠ 1 := by omega
  simp [hj, hj1]

/-- Exact factor selected by any Type-d outcome, including the two low
outcomes.  The equality `j = factors.length - s` is retained because it is the
datum distinguishing Type-d1 from Type-d2 in the published argument. -/
theorem typeD_regrouping_geometry
    {X delta H₀ : ℝ} {K k m : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (j : Fin m)
    (houtcome : dynamicComponentOutcome m delta H₀ logIndex zbag mbag =
      .typeD j) :
    let factors := sortedComponentFactorList logIndex zbag mbag
    let scales := dynamicPreliminaryScaleList (some logIndex) zbag mbag
    let s := largestSmallPrefix scales (Real.rpow X delta)
    ∃ hs : s < factors.length,
      (j : ℕ) = factors.length - s ∧
        factorConvolution (dynamicComponentFactorList logIndex zbag mbag) =
          factors[s].coeff *
            factorConvolution (complementFactorList factors s) := by
  dsimp only
  let factors := sortedComponentFactorList logIndex zbag mbag
  let scales := dynamicPreliminaryScaleList (some logIndex) zbag mbag
  let s := largestSmallPrefix scales (Real.rpow X delta)
  have hdata := typeD_outcome_data logIndex zbag mbag j houtcome
  dsimp only at hdata
  have hlengths := sortedComponent_realLengths_eq_scaleList
    logIndex zbag mbag
  have hlenEq : factors.length = scales.length := by
    have h := congrArg List.length hlengths
    simpa [factors, scales] using h
  have hs : s < factors.length := by
    rw [hlenEq]
    simpa [s, scales] using hdata.1
  refine ⟨hs, ?_, ?_⟩
  · rw [hlenEq]
    simpa [s, scales] using hdata.2.2.1
  · rw [← factorConvolution_sortedComponentFactorList
      logIndex zbag mbag]
    exact factorConvolution_regroup_at factors hs

/-- The literal masked component has the classifier-selected two-factor
regrouping.  This is the coefficient identity needed before any Type-d1/d2
Cauchy or fourth-moment estimate can be applied. -/
theorem maskedDynamicComponentV3_eq_typeD_regrouping
    {X delta H₀ : ℝ} (hX : 1 ≤ X) {K k : ℕ} (hK : 1 ≤ K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (j : Fin 8)
    (houtcome : dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag =
      .typeD j) (n : ℕ) :
    let factors := sortedComponentFactorList logIndex zbag mbag
    let scales := dynamicPreliminaryScaleList (some logIndex) zbag mbag
    let s := largestSmallPrefix scales (Real.rpow X delta)
    ∃ hs : s < factors.length,
      maskedDynamicComponentV3 logIndex zbag mbag n =
        if n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ then
          (dynamicComponentScalar zbag mbag *
            ((factors[s]'hs).coeff *
              factorConvolution (complementFactorList factors s))) n
        else 0 := by
  dsimp only
  let factors := sortedComponentFactorList logIndex zbag mbag
  let scales := dynamicPreliminaryScaleList (some logIndex) zbag mbag
  let s := largestSmallPrefix scales (Real.rpow X delta)
  obtain ⟨hs, hj, hregroup⟩ :=
    typeD_regrouping_geometry logIndex zbag mbag j houtcome
  refine ⟨hs, ?_⟩
  unfold maskedDynamicComponentV3
  split_ifs with hn
  · rw [dynamicPreliminaryComponent_some_eq_factorConvolution hX hK]
    rw [hregroup]
  · rfl

/-- Every classified low component retains the sharp source support. -/
theorem dynamicComponentRemainderV3_eq_zero_off_sourceBlock
    {X delta H₀ : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (kind : HBRemainderKind) {n : ℕ}
    (hn : n ∉ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊) :
    dynamicComponentRemainderV3 (delta := delta) (H₀ := H₀)
        logIndex zbag mbag kind n = 0 := by
  unfold dynamicComponentRemainderV3
  cases h : dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag with
  | typeII =>
      simp [h, maskedDynamicComponentV3, hn]
  | typeD j =>
      simp [h, maskedDynamicComponentV3, hn]
  | vanishing =>
      simp [h]

/-- The branch aggregate for each genuine kind has exactly the same sharp
source support; no later analytic estimate may silently enlarge it. -/
theorem dynamicRawBranchRemainderCoeffV3_eq_zero_off_sourceBlock
    (X delta H₀ : ℝ) {K : ℕ} (branch : Fin K)
    (kind : HBRemainderKind) {n : ℕ}
    (hn : n ∉ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊) :
    dynamicRawBranchRemainderCoeffV3 X delta H₀ branch kind n = 0 := by
  unfold dynamicRawBranchRemainderCoeffV3
  simp_rw [dynamicComponentRemainderV3_eq_zero_off_sourceBlock
    (delta := delta) (H₀ := H₀) (kind := kind)
    (logIndex := _) (zbag := _) (mbag := _) hn]
  simp

/-! ## Exact component-level Cauchy ledger -/

def dynamicLowZBagSetV3 (X : ℝ) (branch : ℕ) :=
  (Finset.univ : Finset
    (Option (Fin (sourceDyadicCount (hbFactorCutoff X))))).sym branch

def dynamicLowMBagSetV3 (X : ℝ) (K branch : ℕ) :=
  (Finset.univ : Finset
    (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊)))).sym
      (branch + 1)

/-- Exact number of preliminary components summed into one raw low-type
coefficient of one HB branch. -/
def dynamicLowComponentMultiplicityV3
    (X : ℝ) (K branch : ℕ) : ℕ :=
  sourceDyadicCount (hbFactorCutoff X) *
    (dynamicLowZBagSetV3 X branch).card *
      (dynamicLowMBagSetV3 X K branch).card

/-- Sum of the individual preliminary-component masses before the Cauchy
loss introduced by collecting them into a raw branch. -/
def dynamicRawLowComponentMassV3
    (p : MAPMRTCorollary53Source.Corollary53Input)
    (delta H₀ : ℝ) {K : ℕ} (branch : Fin K)
    (kind : HBRemainderKind)
    (component : OuterComponent) : ℝ :=
  ∑ logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)),
    ∑ zbag ∈ dynamicLowZBagSetV3 p.X (branch : ℕ),
      ∑ mbag ∈ dynamicLowMBagSetV3 p.X K (branch : ℕ),
        componentIntegral p.X p.H 1 p.q
          (dynamicComponentRemainderV3 (delta := delta) (H₀ := H₀)
            logIndex zbag mbag kind) p.beta p.eta component

/-- Push the branch-level coefficient collection through `componentIntegral`.
The multiplier is the literal product of the three finite index cardinalities,
not an asymptotic replacement. -/
theorem componentIntegral_dynamicRawBranchRemainderCoeffV3_le_components
    {p : MAPMRTCorollary53Source.Corollary53Input}
    (hp : MAPMRTCorollary53Source.Corollary53Admissible 1 1 p)
    {delta H₀ : ℝ} {K : ℕ} (branch : Fin K)
    (kind : HBRemainderKind)
    (component : OuterComponent) :
    componentIntegral p.X p.H 1 p.q
        (dynamicRawBranchRemainderCoeffV3 p.X delta H₀ branch kind)
        p.beta p.eta component ≤
      (dynamicLowComponentMultiplicityV3 p.X K (branch : ℕ) : ℝ) *
        dynamicRawLowComponentMassV3 p delta H₀ branch kind component := by
  rcases hp with ⟨hHone, _, _, _, heta, hetaOne, _⟩
  have hX0 : 0 ≤ p.X := by linarith
  have hH0 : 0 ≤ p.H := by linarith
  let Z := dynamicLowZBagSetV3 p.X (branch : ℕ)
  let M := dynamicLowMBagSetV3 p.X K (branch : ℕ)
  let F := fun
      (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
      (zbag : Sym
        (Option (Fin (sourceDyadicCount (hbFactorCutoff p.X)))) (branch : ℕ))
      (mbag : Sym
        (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff p.X K⌋₊)))
          ((branch : ℕ) + 1)) =>
      dynamicComponentRemainderV3 (delta := delta) (H₀ := H₀)
        logIndex zbag mbag kind
  have houter := componentIntegral_finset_sum_le
    (Finset.univ : Finset
      (Fin (sourceDyadicCount (hbFactorCutoff p.X))))
    (fun logIndex n => ∑ zbag ∈ Z, ∑ mbag ∈ M,
      F logIndex zbag mbag n)
    (beta := p.beta) (q₀ := 1) (q₁ := p.q)
    hX0 hH0 heta hetaOne component
  have hmiddle :
      (∑ logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)),
        componentIntegral p.X p.H 1 p.q
          (fun n => ∑ zbag ∈ Z, ∑ mbag ∈ M,
            F logIndex zbag mbag n) p.beta p.eta component) ≤
      (Z.card : ℝ) *
        ∑ logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)),
          ∑ zbag ∈ Z,
            componentIntegral p.X p.H 1 p.q
              (fun n => ∑ mbag ∈ M, F logIndex zbag mbag n)
              p.beta p.eta component := by
    calc
      _ ≤ ∑ logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)),
          (Z.card : ℝ) * ∑ zbag ∈ Z,
            componentIntegral p.X p.H 1 p.q
              (fun n => ∑ mbag ∈ M, F logIndex zbag mbag n)
              p.beta p.eta component := by
        apply Finset.sum_le_sum
        intro logIndex hlog
        exact componentIntegral_finset_sum_le Z
          (fun zbag n => ∑ mbag ∈ M, F logIndex zbag mbag n)
          (beta := p.beta) (q₀ := 1) (q₁ := p.q)
          hX0 hH0 heta hetaOne component
      _ = _ := by simp_rw [Finset.mul_sum]
  have hinner :
      (∑ logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)),
        ∑ zbag ∈ Z,
          componentIntegral p.X p.H 1 p.q
            (fun n => ∑ mbag ∈ M, F logIndex zbag mbag n)
            p.beta p.eta component) ≤
      (M.card : ℝ) *
        ∑ logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)),
          ∑ zbag ∈ Z, ∑ mbag ∈ M,
            componentIntegral p.X p.H 1 p.q
              (F logIndex zbag mbag) p.beta p.eta component := by
    calc
      _ ≤ ∑ logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)),
          ∑ zbag ∈ Z, (M.card : ℝ) * ∑ mbag ∈ M,
            componentIntegral p.X p.H 1 p.q
              (F logIndex zbag mbag) p.beta p.eta component := by
        apply Finset.sum_le_sum
        intro logIndex hlog
        apply Finset.sum_le_sum
        intro zbag hz
        exact componentIntegral_finset_sum_le M (F logIndex zbag)
          (beta := p.beta) (q₀ := 1) (q₁ := p.q)
          hX0 hH0 heta hetaOne component
      _ = _ := by
        simp_rw [Finset.mul_sum]
  have hlogCard :
      ((Finset.univ : Finset
        (Fin (sourceDyadicCount (hbFactorCutoff p.X)))).card : ℝ) =
        sourceDyadicCount (hbFactorCutoff p.X) := by simp
  unfold dynamicRawBranchRemainderCoeffV3
  change componentIntegral p.X p.H 1 p.q
      (fun n => ∑ logIndex, ∑ zbag ∈ Z, ∑ mbag ∈ M,
        F logIndex zbag mbag n) p.beta p.eta component ≤ _
  rw [hlogCard] at houter
  have hmiddle' := mul_le_mul_of_nonneg_left hmiddle
    (show 0 ≤ (sourceDyadicCount (hbFactorCutoff p.X) : ℝ) by positivity)
  have hinner' := mul_le_mul_of_nonneg_left hinner
    (show 0 ≤ (sourceDyadicCount (hbFactorCutoff p.X) : ℝ) * Z.card by
      positivity)
  unfold dynamicLowComponentMultiplicityV3 dynamicRawLowComponentMassV3
  dsimp [Z, M, F] at houter hmiddle' hinner' ⊢
  calc
    _ ≤ (sourceDyadicCount (hbFactorCutoff p.X) : ℝ) *
        ∑ logIndex, componentIntegral p.X p.H 1 p.q
          (fun n => ∑ zbag ∈ dynamicLowZBagSetV3 p.X (branch : ℕ),
            ∑ mbag ∈ dynamicLowMBagSetV3 p.X K (branch : ℕ),
              dynamicComponentRemainderV3 (delta := delta) (H₀ := H₀)
                logIndex zbag mbag kind n) p.beta p.eta component := houter
    _ ≤ (sourceDyadicCount (hbFactorCutoff p.X) : ℝ) *
        ((dynamicLowZBagSetV3 p.X (branch : ℕ)).card : ℝ) *
        ∑ logIndex, ∑ zbag ∈ dynamicLowZBagSetV3 p.X (branch : ℕ),
          componentIntegral p.X p.H 1 p.q
            (fun n => ∑ mbag ∈ dynamicLowMBagSetV3 p.X K (branch : ℕ),
              dynamicComponentRemainderV3 (delta := delta) (H₀ := H₀)
                logIndex zbag mbag kind n) p.beta p.eta component := by
      simpa [mul_assoc] using hmiddle'
    _ ≤ (sourceDyadicCount (hbFactorCutoff p.X) : ℝ) *
        ((dynamicLowZBagSetV3 p.X (branch : ℕ)).card : ℝ) *
        ((dynamicLowMBagSetV3 p.X K (branch : ℕ)).card : ℝ) *
        ∑ logIndex, ∑ zbag ∈ dynamicLowZBagSetV3 p.X (branch : ℕ),
          ∑ mbag ∈ dynamicLowMBagSetV3 p.X K (branch : ℕ),
            componentIntegral p.X p.H 1 p.q
              (dynamicComponentRemainderV3 (delta := delta) (H₀ := H₀)
                logIndex zbag mbag kind) p.beta p.eta component := by
      simpa [mul_assoc] using hinner'
    _ = _ := by
      push_cast
      ring

end
end MAPFinishDynamicThreeTypeTrace

#print axioms MAPFinishDynamicThreeTypeTrace.dynamicComponentRemainderV3_typeD1_eq_masked
#print axioms MAPFinishDynamicThreeTypeTrace.dynamicComponentRemainderV3_typeD2_eq_masked
#print axioms MAPFinishDynamicThreeTypeTrace.typeD_regrouping_geometry
#print axioms MAPFinishDynamicThreeTypeTrace.maskedDynamicComponentV3_eq_typeD_regrouping
#print axioms MAPFinishDynamicThreeTypeTrace.dynamicComponentRemainderV3_eq_zero_off_sourceBlock
#print axioms MAPFinishDynamicThreeTypeTrace.dynamicRawBranchRemainderCoeffV3_eq_zero_off_sourceBlock
