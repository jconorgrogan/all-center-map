import APWeightedZeroMassIntegrationScaffold
import RelativeNearOneMesh27
import McCurleyRegularLowHeightBridge

/-!
# Applying the relative near-one mesh to the primitive-inducer divisor

This module connects the generic geometric mesh to the literal
`zeroMultiplicity ... 0 T` masses in equation (2.7).  It proves the support
and multiplicity transport to every cumulative density rectangle and then
specializes the result to the regular low- and high-ordinate masses.

No density or zero-free theorem is asserted.  Those two analytic statements
remain local hypotheses with their exact pointwise signatures.
-/

namespace MAPAPRelativeMeshPrimitiveApplication

open scoped BigOperators
open DirichletZeros MAPFixedScaleAPZeroRoute
open MAPAPWeightedZeroMassIntegration MAPRelativeNearOneMesh27

noncomputable section

/-- A predicate-selected mass cut from the literal full primitive-inducer
rectangle used by equation (2.7). -/
def primitiveFilteredNearMass {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (p : ℂ → Prop) [DecidablePred p]
    (X T : ℝ) : ℝ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let psi := chi.primitiveCharacter
  exact ∑ rho ∈ (zeroSupport psi 0 T).filter p,
    (zeroMultiplicity psi 0 T rho : ℝ) *
      Real.rpow X (2 * (rho.re - 1))

/-- Every sub-support of the full rectangle lying to the right of `sigma` is
bounded, with the same analytic multiplicities, by the primitive-inducer
cumulative count at `sigma`. -/
theorem fullSubsupportMultiplicity_le_primitiveCount
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (S : Finset ℂ) {sigma T : ℝ}
    (hS : S ⊆ by
      letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
      exact zeroSupport chi.primitiveCharacter 0 T)
    (hre : ∀ rho ∈ S, sigma ≤ rho.re) :
    (by
      letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
      exact ∑ rho ∈ S, zeroMultiplicity chi.primitiveCharacter 0 T rho) ≤
      primitiveDirichletZeroCount chi sigma T := by
  classical
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let psi := chi.primitiveCharacter
  have hsupport : S ⊆ zeroSupport psi sigma T := by
    intro rho hrho
    have hfull : rho ∈ zeroSupport psi 0 T := hS hrho
    have hfullRect :=
      (zeroDivisor psi 0 T).supportWithinDomain
        ((zeroSupport_mem_iff psi 0 T rho).mp hfull)
    have hinnerRect : rho ∈ zeroRectangle sigma T := by
      rw [zeroRectangle, Complex.mem_reProdIm] at hfullRect ⊢
      exact ⟨⟨hre rho hrho, hfullRect.1.2⟩, hfullRect.2⟩
    apply (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
      psi sigma T hinnerRect).mpr
    exact regularizedLFunction_eq_zero_of_mem_zeroSupport psi 0 T hfull
  have hrewrite :
      (∑ rho ∈ S, zeroMultiplicity psi 0 T rho) =
        ∑ rho ∈ S, zeroMultiplicity psi sigma T rho := by
    apply Finset.sum_congr rfl
    intro rho hrho
    have hfull : rho ∈ zeroSupport psi 0 T := hS hrho
    have hinner : rho ∈ zeroSupport psi sigma T := hsupport hrho
    have hfullRect :=
      (zeroDivisor psi 0 T).supportWithinDomain
        ((zeroSupport_mem_iff psi 0 T rho).mp hfull)
    have hinnerRect :=
      (zeroDivisor psi sigma T).supportWithinDomain
        ((zeroSupport_mem_iff psi sigma T rho).mp hinner)
    exact MAPMellinDetectorLeaf.zeroMultiplicity_eq_of_mem_rectangles
      psi hfullRect hinnerRect
  rw [hrewrite]
  unfold primitiveDirichletZeroCount dirichletZeroCount
  exact Finset.sum_le_sum_of_subset_of_nonneg hsupport
    (fun _ _ _ => Nat.zero_le _)

/-- End-to-end application of the source-base relative mesh to an arbitrary
predicate-selected part of one primitive inducer's full zero divisor. -/
theorem primitiveFilteredNearMass_le_relative_of_source_density
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (p : ℂ → Prop) [DecidablePred p]
    {epsilon u omega X T C R : ℝ} {L : ℕ}
    (hepsilon : 0 ≤ epsilon) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 315)
    (hbetaLow : ∀ rho : ℂ,
      rho ∈ (by
        letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
        exact (zeroSupport chi.primitiveCharacter 0 T).filter p) →
      4 / 5 < rho.re)
    (hbetaGap : ∀ rho : ℂ,
      rho ∈ (by
        letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
        exact (zeroSupport chi.primitiveCharacter 0 T).filter p) →
      rho.re ≤ 1 - omega)
    (hdepth : relativeDistance L ≤ omega)
    (hLlog : (L : ℝ) ≤ Real.log X)
    (hX : 1 ≤ X) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hRtoX : R ≤ Real.rpow X (MAPGuthMaynard.tau epsilon + u))
    (hdensity : ∀ j < L,
      (primitiveDirichletZeroCount chi (relativePoint j) T : ℝ) ≤
        C * Real.rpow R ((21 / 10) * (1 - relativePoint j))) :
    primitiveFilteredNearMass chi p X T ≤
      Real.log X * (C * Real.rpow X (-(omega / 12))) := by
  classical
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let psi := chi.primitiveCharacter
  let S := (zeroSupport psi 0 T).filter p
  apply relativeNearMass_le_log_mul_of_source_density
    S (fun rho => zeroMultiplicity psi 0 T rho) Complex.re
    hepsilon hu0 hu
  · exact hbetaLow
  · exact hbetaGap
  · exact hdepth
  · exact hLlog
  · exact hX
  · exact hC
  · exact hR
  · exact hRtoX
  intro j hj
  have hcount :
      (∑ rho ∈ S.filter (fun rho => relativePoint j ≤ rho.re),
          zeroMultiplicity psi 0 T rho : ℕ) ≤
        primitiveDirichletZeroCount chi (relativePoint j) T := by
    apply fullSubsupportMultiplicity_le_primitiveCount chi
    · intro rho hrho
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hrho).1).1
    · intro rho hrho
      exact (Finset.mem_filter.mp hrho).2
  have hcountReal :
      ((∑ rho ∈ S.filter (fun rho => relativePoint j ≤ rho.re),
          zeroMultiplicity psi 0 T rho : ℕ) : ℝ) ≤
        (primitiveDirichletZeroCount chi (relativePoint j) T : ℝ) := by
    exact_mod_cast hcount
  exact hcountReal.trans (hdensity j hj)

/-- Literal regular bounded-height mass: all mesh and multiplicity deductions
are discharged, leaving only the pointwise zero-free gap and source density. -/
theorem primitiveRegularNearOneLowHeightMass_le_relative
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {epsilon u omega X T C R : ℝ} {L : ℕ}
    (hepsilon : 0 ≤ epsilon) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 315)
    (hbetaGap : ∀ rho : ℂ,
      rho ∈ (by
        letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
        let psi := chi.primitiveCharacter
        exact (zeroSupport psi 0 T).filter (fun rho =>
          (4 / 5 < rho.re ∧
            ¬ (psi ≠ 1 ∧ psi ^ 2 = 1 ∧ rho.im = 0)) ∧ |rho.im| < 3)) →
      rho.re ≤ 1 - omega)
    (hdepth : relativeDistance L ≤ omega)
    (hLlog : (L : ℝ) ≤ Real.log X)
    (hX : 1 ≤ X) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hRtoX : R ≤ Real.rpow X (MAPGuthMaynard.tau epsilon + u))
    (hdensity : ∀ j < L,
      (primitiveDirichletZeroCount chi (relativePoint j) T : ℝ) ≤
        C * Real.rpow R ((21 / 10) * (1 - relativePoint j))) :
    primitiveRegularNearOneLowHeightMass chi X T ≤
      Real.log X * (C * Real.rpow X (-(omega / 12))) := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let psi := chi.primitiveCharacter
  simpa only [primitiveFilteredNearMass,
    primitiveRegularNearOneLowHeightMass] using
    (primitiveFilteredNearMass_le_relative_of_source_density chi
      (fun rho => (4 / 5 < rho.re ∧
        ¬ (psi ≠ 1 ∧ psi ^ 2 = 1 ∧ rho.im = 0)) ∧ |rho.im| < 3)
      hepsilon hu0 hu
      (by
        intro rho hrho
        exact (Finset.mem_filter.mp hrho).2.1.1)
      hbetaGap hdepth hLlog hX hC hR hRtoX hdensity)

/-- Literal regular high-ordinate mass, using the closed `3 ≤ |gamma|`
endpoint consumed by the sign-symmetric Khale bridge. -/
theorem primitiveRegularNearOneHighHeightMass_le_relative
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {epsilon u omega X T C R : ℝ} {L : ℕ}
    (hepsilon : 0 ≤ epsilon) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 315)
    (hbetaGap : ∀ rho : ℂ,
      rho ∈ (by
        letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
        let psi := chi.primitiveCharacter
        exact (zeroSupport psi 0 T).filter (fun rho =>
          (4 / 5 < rho.re ∧
            ¬ (psi ≠ 1 ∧ psi ^ 2 = 1 ∧ rho.im = 0)) ∧ 3 ≤ |rho.im|)) →
      rho.re ≤ 1 - omega)
    (hdepth : relativeDistance L ≤ omega)
    (hLlog : (L : ℝ) ≤ Real.log X)
    (hX : 1 ≤ X) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hRtoX : R ≤ Real.rpow X (MAPGuthMaynard.tau epsilon + u))
    (hdensity : ∀ j < L,
      (primitiveDirichletZeroCount chi (relativePoint j) T : ℝ) ≤
        C * Real.rpow R ((21 / 10) * (1 - relativePoint j))) :
    primitiveRegularNearOneHighHeightMass chi X T ≤
      Real.log X * (C * Real.rpow X (-(omega / 12))) := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let psi := chi.primitiveCharacter
  simpa only [primitiveFilteredNearMass,
    primitiveRegularNearOneHighHeightMass] using
    (primitiveFilteredNearMass_le_relative_of_source_density chi
      (fun rho => (4 / 5 < rho.re ∧
        ¬ (psi ≠ 1 ∧ psi ^ 2 = 1 ∧ rho.im = 0)) ∧ 3 ≤ |rho.im|)
      hepsilon hu0 hu
      (by
        intro rho hrho
        exact (Finset.mem_filter.mp hrho).2.1.1)
      hbetaGap hdepth hLlog hX hC hR hRtoX hdensity)

end

end MAPAPRelativeMeshPrimitiveApplication

#print axioms MAPAPRelativeMeshPrimitiveApplication.fullSubsupportMultiplicity_le_primitiveCount
#print axioms MAPAPRelativeMeshPrimitiveApplication.primitiveFilteredNearMass_le_relative_of_source_density
#print axioms MAPAPRelativeMeshPrimitiveApplication.primitiveRegularNearOneLowHeightMass_le_relative
#print axioms MAPAPRelativeMeshPrimitiveApplication.primitiveRegularNearOneHighHeightMass_le_relative
