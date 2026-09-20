import APRegularNearCGLGappedJutilaAppendixBAdapter
import JutilaGappedCollarSelectedP53Adapter

/-!
# Primary CGL endpoint with only the selected-system p.53 collar leaf

This is the submission-facing adapter.  The finite occupied-box aggregation,
principal/nonprincipal A.5 cap, ceiling, and exponent weld are all certified;
the collar premise is only Jutila's p.53 detector/correlation estimate for a
one-separated regular subsystem.
-/

namespace MAPAPRegularNearCGLSelectedP53AppendixBAdapter

open MAPAPRegularNearLogSaving MAPAPWeightedZeroMassIntegration
open MAPFixedScaleAPZeroRoute CGLMeshFormalization
open MAPKhaleAppendixBSource
open MAPAPRegularNearAppendixBAdapter
open MAPJutilaGappedCollarSelectedP53Adapter
open MAPAPRegularNearCGLGappedJutilaAppendixBAdapter

noncomputable section

theorem apRegularNearOneRangeMass_logSaving_of_cglv2_selectedP53_and_high_gap
    (hCGL : CGLv2Theorem12AllCases)
    (hP53 : JutilaGappedSelectedSystemP53Eventually)
    (hPrincipalP53 : JutilaGappedSelectedPrincipalP53Eventually)
    (hHighGap : PrimitiveRegularHighGap) :
    ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
        ∀ X : ℝ, X₀ ≤ X →
          apRegularNearOneRangeMass
              ⌊Real.rpow (Real.log X) K⌋₊ X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A) :=
  apRegularNearOneRangeMass_logSaving_of_cglv2_gappedCumulative_and_high_gap
    hCGL
      (primitiveRegularCumulativeCount_le_of_gappedSelectedP53
        hP53 hPrincipalP53)
      hHighGap

theorem apRegularNearOneRangeMass_logSaving_of_cglv2_selectedP53_appendixB104
    (hCGL : CGLv2Theorem12AllCases)
    (hP53 : JutilaGappedSelectedSystemP53Eventually)
    (hPrincipalP53 : JutilaGappedSelectedPrincipalP53Eventually)
    (hKhale104 : AppendixBCorollary104) :
    ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
        ∀ X : ℝ, X₀ ≤ X →
          apRegularNearOneRangeMass
              ⌊Real.rpow (Real.log X) K⌋₊ X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A) :=
  apRegularNearOneRangeMass_logSaving_of_cglv2_gappedCumulative_appendixB104
    hCGL
      (primitiveRegularCumulativeCount_le_of_gappedSelectedP53
        hP53 hPrincipalP53)
      hKhale104

/-- Exact equation-(2.7) weld from the primitive high-gap interface, without
re-expanding it to the stronger Appendix-B statement. -/
theorem apWeightedZeroMassLogSaving_of_compact_cglv2_selectedP53_and_high_gap
    (hCompact : ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
        ∀ X : ℝ, X₀ ≤ X →
          apCompactRangeMass ⌊Real.rpow (Real.log X) K⌋₊ epsilon X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A))
    (hCGL : CGLv2Theorem12AllCases)
    (hP53 : JutilaGappedSelectedSystemP53Eventually)
    (hPrincipalP53 : JutilaGappedSelectedPrincipalP53Eventually)
    (hHighGap : PrimitiveRegularHighGap) :
    APWeightedZeroMassLogSaving :=
  MAPAPExceptionalUnconditional.apWeightedZeroMassLogSaving_of_compact_regular
    hCompact
    (apRegularNearOneRangeMass_logSaving_of_cglv2_selectedP53_and_high_gap
      hCGL hP53 hPrincipalP53 hHighGap)

theorem apWeightedZeroMassLogSaving_of_compact_cglv2_selectedP53_appendixB104
    (hCompact : ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
      ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
        ∀ X : ℝ, X₀ ≤ X →
          apCompactRangeMass ⌊Real.rpow (Real.log X) K⌋₊ epsilon X
              (apZeroHeight epsilon X) ≤
            C * Real.rpow (Real.log X) (-A))
    (hCGL : CGLv2Theorem12AllCases)
    (hP53 : JutilaGappedSelectedSystemP53Eventually)
    (hPrincipalP53 : JutilaGappedSelectedPrincipalP53Eventually)
    (hKhale104 : AppendixBCorollary104) :
    APWeightedZeroMassLogSaving :=
  apWeightedZeroMassLogSaving_of_compact_cglv2_gappedCumulative_appendixB104
    hCompact hCGL
      (primitiveRegularCumulativeCount_le_of_gappedSelectedP53
        hP53 hPrincipalP53)
      hKhale104

end

end MAPAPRegularNearCGLSelectedP53AppendixBAdapter

#print axioms MAPAPRegularNearCGLSelectedP53AppendixBAdapter.apRegularNearOneRangeMass_logSaving_of_cglv2_selectedP53_and_high_gap
#print axioms MAPAPRegularNearCGLSelectedP53AppendixBAdapter.apWeightedZeroMassLogSaving_of_compact_cglv2_selectedP53_and_high_gap
#print axioms MAPAPRegularNearCGLSelectedP53AppendixBAdapter.apRegularNearOneRangeMass_logSaving_of_cglv2_selectedP53_appendixB104
#print axioms MAPAPRegularNearCGLSelectedP53AppendixBAdapter.apWeightedZeroMassLogSaving_of_compact_cglv2_selectedP53_appendixB104
