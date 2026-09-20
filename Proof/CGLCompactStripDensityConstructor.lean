import BudgetedSelectedPoweredBlockAssembly
import AppendixA4PostA5SetAdapter
import FixedCharacterReduction

/-!
# Canonical compact-strip density constructor

This module isolates the exact analytic handoff still required after the
certified Appendix A.4/A.5 detector dichotomy and the now-inhabited budgeted
powered large-value bridge.

The high-strip handoff is deliberately quantitative.  It must turn one
primitive nonprincipal zero count into a one-separated common polynomial
large-value set, losing at most `T^epsilon` in cardinality.  This is the
source-faithful endpoint of the remaining Fourier-L1, ordinate-crowding,
Type-II truncation, and multiplicity bookkeeping.  It is not replaced by an
existential assertion of the desired density bound.

The low-strip/principal field records the separate classical input which is
not supplied by the Guth--Maynard high-strip theorem or by the nonprincipal
Appendix A.4 detector.
-/

namespace CGLCompactStripDensityConstructor

open scoped BigOperators
open DirichletZeros ZeroDensityInterface MAPAPZeroDensityCert MAPGuthMaynard
open CGLProofDAG FixedCharacterPoweredBridge

noncomputable section

/-- The literal uniform polynomial large-value conclusion produced from the
budgeted powered bridge. -/
def UniformThirtyThirteenLargeValue : Prop :=
  ∀ κ η : ℝ, 0 < κ → 0 < η →
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T σ : ℝ) (N : ℕ) (b : ℕ → ℂ) (W : Finset ℝ),
        T₀ ≤ T → 7 / 10 ≤ σ → σ ≤ 4 / 5 →
        Real.rpow T κ ≤ N →
        (N : ℝ) ≤ Real.rpow T (1 / 2) * (Real.log T) ^ 2 →
        (∀ n, ‖b n‖ ≤ 1) →
        OneSeparated W →
        (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) →
        (∀ t ∈ W,
          Real.rpow N σ * Real.rpow T (-inputLoss κ (η / 2)) ≤
            ‖dirichletPolynomial b N t‖) →
        (W.card : ℝ) ≤
          C * Real.rpow T ((30 / 13) * (1 - σ) + η)

/-- The exact high-strip output expected from the remaining post-A.5
reduction.  The conclusion retains actual witnesses `N`, `b`, and `W`, all
hypotheses consumed by `UniformThirtyThirteenLargeValue`, and an explicit
`T^epsilon` crowding/Fourier loss.  The additive `1` permits finitely many
boundary or exceptional zeros without making the interface artificially
false when the selected large-value set is empty. -/
def PostA5HighStripLargeValueReduction : Prop :=
  ∀ K delta epsilon : ℝ, 0 < K → 0 < delta → 0 < epsilon →
    ∃ κ A T₀ : ℝ,
      0 < κ ∧ κ ≤ 1 / 2 ∧ 0 < A ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (Q : ℕ) (σ : ℝ), T₀ ≤ T →
        (Q : ℝ) ≤ Real.rpow (Real.log T) K →
        7 / 10 ≤ σ → σ ≤ 4 / 5 →
        ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r),
          χ.IsPrimitive → χ ≠ 1 → r ≤ Q →
          ∃ (N : ℕ) (b : ℕ → ℂ) (W : Finset ℝ),
            Real.rpow T κ ≤ N ∧
            (N : ℝ) ≤ Real.rpow T (1 / 2) * (Real.log T) ^ 2 ∧
            (∀ n, ‖b n‖ ≤ 1) ∧
            OneSeparated W ∧
            (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) ∧
            (∀ t ∈ W,
              Real.rpow N σ * Real.rpow T (-inputLoss κ (epsilon / 2)) ≤
                ‖dirichletPolynomial b N t‖) ∧
            (dirichletZeroCount χ σ T : ℝ) ≤
              A * Real.rpow T epsilon * (1 + (W.card : ℝ))

/-- The exact compact-strip part not furnished by the nonprincipal high-strip
detector: Ingham's low strip, together with conductor-one principal zeta on
the whole compact strip. -/
def FixedPrimitiveLowStripOrPrincipalDensity : Prop :=
  ∀ K delta η : ℝ, 0 < K → 0 < delta → 0 < η →
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (Q : ℕ) (σ : ℝ), T₀ ≤ T →
        (Q : ℝ) ≤ Real.rpow (Real.log T) K →
        1 / 2 + delta ≤ σ → σ ≤ 4 / 5 →
        ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r),
          χ.IsPrimitive → r ≤ Q → (σ ≤ 7 / 10 ∨ χ = 1) →
          (dirichletZeroCount χ σ T : ℝ) ≤
            C * Real.rpow T (densityCoeff * (1 - σ) + η)

/-- One named analytic surface for the remaining compact-strip work.  Its
first field is the precise post-A.5 large-value reduction; its second field is
the disjoint classical low-strip/principal input. -/
structure CompactStripAnalyticInput : Prop where
  postA5HighStrip : PostA5HighStripLargeValueReduction
  lowStripOrPrincipal : FixedPrimitiveLowStripOrPrincipalDensity

/-- The green selected-block assembly, followed by the existing powered-to-
uniform exponent conversion, inhabits the literal uniform large-value
proposition. -/
theorem uniformThirtyThirteenLargeValue_of_guthMaynard
    (hGM : GuthMaynardTheorem11) :
    UniformThirtyThirteenLargeValue :=
  CGLPoweredToUniformDensity.uniformThirtyThirteen_of_budgetedFixedCharacterPoweredBridge
    (BudgetedSelectedPoweredBlockAssembly.budgetedFixedCharacterPoweredLargeValueBridge
      hGM)

/-- High-strip fixed-primitive density obtained by composing the exact
post-A.5 reduction with the uniform polynomial large-value estimate. -/
theorem fixedPrimitiveHighStripDensity_of_reduction
    (hreduce : PostA5HighStripLargeValueReduction)
    (huniform : UniformThirtyThirteenLargeValue) :
    ∀ K delta η : ℝ, 0 < K → 0 < delta → 0 < η →
      ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
        ∀ (T : ℝ) (Q : ℕ) (σ : ℝ), T₀ ≤ T →
          (Q : ℝ) ≤ Real.rpow (Real.log T) K →
          7 / 10 ≤ σ → σ ≤ 4 / 5 →
          ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r),
            χ.IsPrimitive → χ ≠ 1 → r ≤ Q →
            (dirichletZeroCount χ σ T : ℝ) ≤
              C * Real.rpow T (densityCoeff * (1 - σ) + η) := by
  intro K delta η hK hdelta hη
  obtain ⟨κ, A, Tred, hκ, _hκhalf, hA, hTred, hreduce'⟩ :=
    hreduce K delta (η / 2) hK hdelta (half_pos hη)
  obtain ⟨C, Tlarge, hC, hTlarge, hlarge⟩ :=
    huniform κ (η / 2) hκ (half_pos hη)
  let Cfinal : ℝ := A * (1 + C)
  let T₀ : ℝ := max Tred Tlarge
  refine ⟨Cfinal, T₀, ?_, ?_, ?_⟩
  · dsimp [Cfinal]
    positivity
  · exact hTred.trans (le_max_left _ _)
  · intro T Q σ hT hQ hσlow hσhigh r _inst χ hprim hχ hlevel
    have hTred' : Tred ≤ T := (le_max_left _ _).trans hT
    have hTlarge' : Tlarge ≤ T := (le_max_right _ _).trans hT
    obtain ⟨N, b, W, hNlow, hNhigh, hb, hsep, hheight, hpoly, hcount⟩ :=
      hreduce' T Q σ hTred' hQ hσlow hσhigh r χ hprim hχ hlevel
    have hW := hlarge T σ N b W hTlarge' hσlow hσhigh
      hNlow hNhigh hb hsep hheight hpoly
    have hTone : 1 ≤ T := (by norm_num : (1 : ℝ) ≤ 2).trans
      (hTlarge.trans hTlarge')
    have hexp0 :
        0 ≤ (30 / 13 : ℝ) * (1 - σ) + η / 2 := by
      have : 0 ≤ 1 - σ := by linarith
      positivity
    have honePow :
        1 ≤ Real.rpow T ((30 / 13 : ℝ) * (1 - σ) + η / 2) :=
      Real.one_le_rpow hTone hexp0
    have honeCard :
        1 + (W.card : ℝ) ≤
          (1 + C) * Real.rpow T
            ((30 / 13 : ℝ) * (1 - σ) + η / 2) := by
      calc
        1 + (W.card : ℝ) ≤
            Real.rpow T ((30 / 13 : ℝ) * (1 - σ) + η / 2) +
              C * Real.rpow T
                ((30 / 13 : ℝ) * (1 - σ) + η / 2) :=
          add_le_add honePow hW
        _ = (1 + C) * Real.rpow T
              ((30 / 13 : ℝ) * (1 - σ) + η / 2) := by ring
    calc
      (dirichletZeroCount χ σ T : ℝ) ≤
          A * Real.rpow T (η / 2) * (1 + (W.card : ℝ)) := hcount
      _ ≤ A * Real.rpow T (η / 2) *
          ((1 + C) * Real.rpow T
            ((30 / 13 : ℝ) * (1 - σ) + η / 2)) := by
        exact mul_le_mul_of_nonneg_left honeCard
          (mul_nonneg hA.le (Real.rpow_nonneg (zero_le_one.trans hTone) _))
      _ = Cfinal * Real.rpow T (densityCoeff * (1 - σ) + η) := by
        dsimp [Cfinal, densityCoeff]
        change A * Real.rpow T (η / 2) *
              ((1 + C) * Real.rpow T
                ((30 / 13 : ℝ) * (1 - σ) + η / 2)) =
            A * (1 + C) *
              Real.rpow T ((30 / 13 : ℝ) * (1 - σ) + η)
        rw [show A * Real.rpow T (η / 2) *
              ((1 + C) * Real.rpow T
                ((30 / 13 : ℝ) * (1 - σ) + η / 2)) =
            A * (1 + C) *
              (Real.rpow T (η / 2) *
                Real.rpow T
                  ((30 / 13 : ℝ) * (1 - σ) + η / 2)) by ring]
        have hrpow :
            Real.rpow T (η / 2) *
                Real.rpow T ((30 / 13 : ℝ) * (1 - σ) + η / 2) =
              Real.rpow T
                (η / 2 + ((30 / 13 : ℝ) * (1 - σ) + η / 2)) :=
          (Real.rpow_add (zero_lt_one.trans_le hTone) _ _).symm
        rw [hrpow]
        congr 2
        ring

/-- Deterministic splice of the classical low-strip/principal input with the
post-A.5 nonprincipal high-strip estimate. -/
theorem fixedPrimitivePolylogDensity_of_components
    (hbase : FixedPrimitiveLowStripOrPrincipalDensity)
    (hhigh :
      ∀ K delta η : ℝ, 0 < K → 0 < delta → 0 < η →
        ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
          ∀ (T : ℝ) (Q : ℕ) (σ : ℝ), T₀ ≤ T →
            (Q : ℝ) ≤ Real.rpow (Real.log T) K →
            7 / 10 ≤ σ → σ ≤ 4 / 5 →
            ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r),
              χ.IsPrimitive → χ ≠ 1 → r ≤ Q →
              (dirichletZeroCount χ σ T : ℝ) ≤
                C * Real.rpow T (densityCoeff * (1 - σ) + η)) :
    CGLPolylogBypass.FixedPrimitivePolylogDensity := by
  intro K delta η hK hdelta hη
  obtain ⟨Cbase, Tbase, hCbase, hTbase, hbase'⟩ :=
    hbase K delta η hK hdelta hη
  obtain ⟨Chigh, Thigh, hChigh, hThigh, hhigh'⟩ :=
    hhigh K delta η hK hdelta hη
  let C : ℝ := max Cbase Chigh
  let T₀ : ℝ := max Tbase Thigh
  refine ⟨C, T₀, ?_, ?_, ?_⟩
  · exact hCbase.trans_le (le_max_left _ _)
  · exact hTbase.trans (le_max_left _ _)
  · intro T Q σ hT hQ hσcompact hσhigh r _inst χ hprim hlevel
    have hTbase' : Tbase ≤ T := (le_max_left _ _).trans hT
    have hThigh' : Thigh ≤ T := (le_max_right _ _).trans hT
    have hTnonneg : 0 ≤ T := by linarith [hTbase.trans hTbase']
    by_cases hcase : σ ≤ 7 / 10 ∨ χ = 1
    · have h := hbase' T Q σ hTbase' hQ hσcompact hσhigh
          r χ hprim hlevel hcase
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg hTnonneg _))
    · have hσseven : 7 / 10 ≤ σ := le_of_not_ge (fun h => hcase (Or.inl h))
      have hχne : χ ≠ 1 := fun h => hcase (Or.inr h)
      have h := hhigh' T Q σ hThigh' hQ hσseven hσhigh
        r χ hprim hχne hlevel
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg hTnonneg _))

/-- The shortest fixed-primitive constructor.  All deterministic arrows from
Guth--Maynard Theorem 1.1 through the budgeted powered bridge and uniform
`30/13` conversion are discharged here. -/
theorem fixedPrimitivePolylogDensity_of_guthMaynard
    (hanalytic : CompactStripAnalyticInput)
    (hGM : GuthMaynardTheorem11) :
    CGLPolylogBypass.FixedPrimitivePolylogDensity :=
  fixedPrimitivePolylogDensity_of_components
    hanalytic.lowStripOrPrincipal
    (fixedPrimitiveHighStripDensity_of_reduction
      hanalytic.postA5HighStrip
      (uniformThirtyThirteenLargeValue_of_guthMaynard hGM))

/-- Canonical project-facing compact-strip density constructor. -/
theorem polylogConductorDensity_of_guthMaynard
    (hanalytic : CompactStripAnalyticInput)
    (hGM : GuthMaynardTheorem11) :
    PolylogConductorDensity :=
  CGLPolylogBypass.fixedPrimitivePolylogDensity_to_project_target
    (fixedPrimitivePolylogDensity_of_guthMaynard hanalytic hGM)

end
end CGLCompactStripDensityConstructor

#print axioms CGLCompactStripDensityConstructor.uniformThirtyThirteenLargeValue_of_guthMaynard
#print axioms CGLCompactStripDensityConstructor.fixedPrimitiveHighStripDensity_of_reduction
#print axioms CGLCompactStripDensityConstructor.fixedPrimitivePolylogDensity_of_guthMaynard
#print axioms CGLCompactStripDensityConstructor.polylogConductorDensity_of_guthMaynard
