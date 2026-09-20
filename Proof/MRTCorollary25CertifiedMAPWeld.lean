import MRTCorollary25Certified
import MRTCorollary25MAPInstantiation

/-!
# Premise-free MRT cutoff removal on the first MAP HB branch

This is the first literal consumer weld: the externally named Corollary 2.5
premise is replaced by its certified source proof and the result is specialized
to the `typeD1` branch tag.
-/

namespace MAPMRTCorollary25CertifiedMAPWeld

open scoped BigOperators
open MAPMRTCorollary25 MAPMRTCorollary25Certified
open MAPMRTCorollary25Instantiation MixedMeanFrontend

noncomputable section

/-- Premise-free cutoff removal for one character-twisted coefficient. -/
theorem cutoffRemoval_characterTwist_certified
    {C : ℝ} (hC : 1 < C) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (X T X1 X2 t B : ℝ) (phase f : ℕ → ℂ),
        1 ≤ X → 1 ≤ T → 0 ≤ B →
        SupportedNear X C f →
        (∀ n, ‖phase n‖ ≤ 1) →
        (∀ n, ‖f n‖ ≤ B) →
        ‖halfLineDirichletPolynomial X C
            (intervalCutoff X1 X2 (characterTwist phase f)) t‖ ≤
          K * ((∫ u in (-T)..T,
              ‖halfLineDirichletPolynomial X C
                (characterTwist phase f) (t + u)‖ / (1 + |u|)) +
            B * Real.sqrt X * Real.log (2 + T) / T) := by
  exact cutoffRemoval_characterTwist_of_MRTCorollary25
    mrtCorollary25_certified hC

/-- The certified theorem specialized to the first enumerated Type-`d`
Heath--Brown branch.  All scale, support, coefficient, and phase hypotheses
remain visible; the only deleted premise is the named analytic source. -/
theorem cutoffRemoval_typeD1_certified
    {Chi : Type*} [Fintype Chi]
    {C : ℝ} (hC : 1 < C)
    (scale height X1 X2 bound : CutoffBranch → ℝ)
    (source : CutoffBranch → ℕ → ℂ)
    (phase : Chi → ℕ → ℂ)
    (hscale : ∀ branch, 1 ≤ scale branch)
    (hheight : ∀ branch, 1 ≤ height branch)
    (hbound0 : ∀ branch, 0 ≤ bound branch)
    (hsupport : ∀ branch, SupportedNear (scale branch) C (source branch))
    (hsource : ∀ branch n, ‖source branch n‖ ≤ bound branch)
    (hphase : ∀ chi n, ‖phase chi n‖ ≤ 1) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (chi : Chi) (t : ℝ),
        ‖halfLineDirichletPolynomial (scale .typeD1) C
            (intervalCutoff (X1 .typeD1) (X2 .typeD1)
              (characterTwist (phase chi) (source .typeD1))) t‖ ≤
          K * ((∫ u in (-(height .typeD1))..(height .typeD1),
              ‖halfLineDirichletPolynomial (scale .typeD1) C
                (characterTwist (phase chi) (source .typeD1)) (t + u)‖ /
                  (1 + |u|)) +
            bound .typeD1 * Real.sqrt (scale .typeD1) *
              Real.log (2 + height .typeD1) / height .typeD1) := by
  obtain ⟨K, hK, hcut⟩ := cutoffRemoval_all_MAP_convolutionBranches
    mrtCorollary25_certified hC scale height X1 X2 bound source phase
    hscale hheight hbound0 hsupport hsource hphase
  exact ⟨K, hK, fun chi t ↦ hcut .typeD1 chi t⟩

end
end MAPMRTCorollary25CertifiedMAPWeld

#print axioms MAPMRTCorollary25CertifiedMAPWeld.cutoffRemoval_characterTwist_certified
#print axioms MAPMRTCorollary25CertifiedMAPWeld.cutoffRemoval_typeD1_certified
