import MAPLiveEndpointWeld
import PrincipalZetaStructuredDensity

/-!
# Stable live-endpoint adapters for the low/principal density fields

These theorems return the exact aliases consumed by `MAPLiveEndpointWeld`.
They keep the principal structured-detector route and the direct CGL route
available without changing the endpoint record.
-/

namespace MAPLivePrincipalDensityAdapters

open CGLDetectorStructuredLargeValue
open MAPPrincipalZetaStructuredDensity

noncomputable section

/-- Legacy one-polynomial adapter.  The detector premise is stronger than the
certified A.4 output because it suppresses Type II. -/
theorem principalClosedHighStripSource_of_structured_detector
    (hDetector : PrincipalPoleRemovedStructuredDetectorReduction)
    (hStructured : DetectorStructuredThirtyThirteenLargeValue) :
    MAPLiveEndpointWeld.PrincipalClosedHighStripSource :=
  principal_zeta_high_strip_density_of_structured_detector
    hDetector hStructured

/-- Preferred exact adapter: the honest ZI/ZII principal split and the shared
structured large-value theorem inhabit the live principal source field. -/
theorem principalClosedHighStripSource_of_structured_split
    (hSplit : PrincipalPostA5StructuredSplitReduction)
    (hStructured : DetectorStructuredThirtyThirteenLargeValue) :
    MAPLiveEndpointWeld.PrincipalClosedHighStripSource :=
  principal_zeta_high_strip_density_of_structured_split
    hSplit hStructured

/-- Extract the exact live principal field from any low-strip/principal
density inhabitant. -/
theorem principalClosedHighStripSource_of_lowStripOrPrincipal
    (hbase :
      CGLCompactStripDensityConstructor.FixedPrimitiveLowStripOrPrincipalDensity) :
    MAPLiveEndpointWeld.PrincipalClosedHighStripSource := by
  intro eta heta
  obtain ⟨C, Tbase, hC, hTbase, hbound⟩ :=
    hbase 1 (1 / 10) eta (by norm_num) (by norm_num) heta
  let T0 : ℝ := max Tbase (Real.exp 1)
  refine ⟨C, T0, hC, hTbase.trans (le_max_left _ _), ?_⟩
  intro T sigma hT hsigmaLow hsigmaHigh
  have hTbase' : Tbase ≤ T := (le_max_left _ _).trans hT
  have hTexp : Real.exp 1 ≤ T := (le_max_right _ _).trans hT
  have hlog : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hTexp
  have hQ : (1 : ℝ) ≤ Real.rpow (Real.log T) 1 := by
    simpa using hlog
  have hQ' : ((1 : ℕ) : ℝ) ≤ Real.rpow (Real.log T) 1 := by
    simpa only [Nat.cast_one] using hQ
  have hsigmaCompact : 1 / 2 + (1 / 10 : ℝ) ≤ sigma := by
    linarith
  have hprimitive : (1 : DirichletCharacter ℂ 1).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def,
      DirichletCharacter.conductor_one]
  exact hbound T 1 sigma hTbase' hQ' hsigmaCompact hsigmaHigh 1
    (1 : DirichletCharacter ℂ 1) hprimitive (by omega) (Or.inr rfl)

/-- Once the CGL all-cases source is certified, its `q = 1` specialization
fills the exact live principal field with no independent zeta-density leaf. -/
theorem principalClosedHighStripSource_of_cgl_v2
    (hCGL : CGLMeshFormalization.CGLv2Theorem12AllCases) :
    MAPLiveEndpointWeld.PrincipalClosedHighStripSource :=
  principalClosedHighStripSource_of_lowStripOrPrincipal
    (fixedPrimitiveLowStripOrPrincipalDensity_of_cgl_v2 hCGL)

/-- Stable identity adapter for Montgomery's literal closed low-strip source.
Its purpose is to keep the exact live alias visible at integration sites. -/
theorem montgomeryClosedLowStripSource_of_literal
    (hMontgomery :
      ∃ Czero : ℝ, 0 < Czero ∧
        ∀ (r : ℕ) [NeZero r] (T sigma : ℝ),
          2 ≤ T → 1 / 2 ≤ sigma → sigma ≤ 4 / 5 →
            (MAPAPZeroDensityCert.ambientZeroCountAtLevel r sigma T : ℝ) ≤
              Czero * Real.rpow ((r : ℝ) * T)
                (MAPMontgomeryLowStrip.inghamExponent sigma) *
                (Real.log ((r : ℝ) * T)) ^ 9) :
    MAPLiveEndpointWeld.MontgomeryClosedLowStripSource :=
  hMontgomery

end
end MAPLivePrincipalDensityAdapters

#print axioms MAPLivePrincipalDensityAdapters.principalClosedHighStripSource_of_structured_detector
#print axioms MAPLivePrincipalDensityAdapters.principalClosedHighStripSource_of_lowStripOrPrincipal
#print axioms MAPLivePrincipalDensityAdapters.principalClosedHighStripSource_of_cgl_v2
#print axioms MAPLivePrincipalDensityAdapters.montgomeryClosedLowStripSource_of_literal
#print axioms MAPLivePrincipalDensityAdapters.principalClosedHighStripSource_of_structured_split
