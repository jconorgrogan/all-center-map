import JutilaGappedCollarSourceAdapter

/-!
# CGL compact bridge plus the live regular/gapped Jutila collar

This is the premise-minimal replacement for the primary route's use of the
full Jutila ambient count.  Collar density is requested only for the regular
cumulative divisor that actually occurs in the MAP mass.
-/

namespace MAPAPRegularNearCGLGappedCollarRoute

open scoped BigOperators
open DirichletZeros MAPAPWeightedZeroMassIntegration
open MAPAPRelativeMeshPrimitiveApplication MAPRelativeNearOneMesh27
open MAPJutilaCollarMeshCutoff MAPGuthMaynard
open MAPAPRegularNearMeshRoute MAPCGLNearFineMeshSourceAdapter
open MAPAPRegularNearCGLJutilaFineMeshRoute
open MAPJutilaGappedCollarSourceAdapter

noncomputable section

/-- The regular cumulative collar count of the primitive character inducing
`chi`.  Packaging the local `NeZero chi.conductor` instance here keeps the
source-facing family premise well typed. -/
def inducedPrimitiveRegularCumulativeCount {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (sigma T : ℝ) : ℕ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact primitiveRegularCumulativeCount chi.primitiveCharacter sigma T

/-- One primitive inducer with a compact CGL mass and density only for its
regular collar divisor. -/
theorem primitiveRegularNearOneRangeMass_le_compactBridge_gappedCollar
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {epsilon u omega X T BC CJ RJ : ℝ} {L : ℕ}
    (hepsilon : 0 ≤ epsilon) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 315)
    (hgap : ∀ rho : ℂ,
      rho ∈ (by
        letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
        let psi := chi.primitiveCharacter
        exact (zeroSupport psi 0 T).filter (fun rho =>
          4 / 5 < rho.re ∧
            ¬ (psi ≠ 1 ∧ psi ^ 2 = 1 ∧ rho.im = 0))) →
      rho.re ≤ 1 - omega)
    (hdepth : relativeDistance L ≤ omega)
    (hmeshGap : ∀ j < L, omega ≤ relativeDistance j)
    (hLlog : (L : ℝ) ≤ Real.log X)
    (hX : 1 ≤ X) (hBC : 0 ≤ BC) (hCJ : 0 ≤ CJ)
    (hRJ : 0 ≤ RJ) (hRJtoX : RJ ≤ Real.rpow X (tau epsilon + u))
    (hcompact : primitiveRegularCompactBridgeMass chi X T ≤ BC)
    (hcollar : ∀ j < L, collarIndex ≤ j →
      (inducedPrimitiveRegularCumulativeCount chi
          (relativePoint j) T : ℝ) ≤
        CJ * Real.rpow RJ ((21 / 10) * (1 - relativePoint j))) :
    primitiveRegularNearOneRangeMass chi X T ≤
      Real.log X * (BC + CJ * Real.rpow X (-(omega / 12))) := by
  classical
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let psi := chi.primitiveCharacter
  let p : ℂ → Prop := fun rho =>
    4 / 5 < rho.re ∧ ¬ (psi ≠ 1 ∧ psi ^ 2 = 1 ∧ rho.im = 0)
  let S := (zeroSupport psi 0 T).filter p
  let multiplicity : ℂ → ℕ := fun rho => zeroMultiplicity psi 0 T rho
  let beta : ℂ → ℝ := Complex.re
  let BJ : ℝ := CJ * Real.rpow X (-(omega / 12))
  have hBJ : 0 ≤ BJ :=
    mul_nonneg hCJ (Real.rpow_nonneg (zero_le_one.trans hX) _)
  have hcompactCell : ∀ j < L, j < collarIndex →
      (∑ rho ∈ relativeCell S beta j,
        (multiplicity rho : ℝ) * Real.rpow X (2 * (beta rho - 1))) ≤
          BC + BJ := by
    intro j _hjL hj
    have hsucc : j + 1 ≤ collarIndex := by omega
    have hpoint := relativePoint_mono hsucc
    let Scompact := S.filter fun rho => beta rho ≤ relativePoint collarIndex
    have hsubset : relativeCell S beta j ⊆ Scompact := by
      intro rho hrho
      have hr := Finset.mem_filter.mp hrho
      exact Finset.mem_filter.mpr ⟨hr.1, hr.2.2.trans hpoint⟩
    have hsubsum :
        (∑ rho ∈ relativeCell S beta j,
          (multiplicity rho : ℝ) * Real.rpow X (2 * (beta rho - 1))) ≤
        ∑ rho ∈ Scompact,
          (multiplicity rho : ℝ) * Real.rpow X (2 * (beta rho - 1)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro rho _ _
      exact mul_nonneg (Nat.cast_nonneg _)
        (Real.rpow_nonneg (zero_le_one.trans hX) _)
    have hcompactEq :
        (∑ rho ∈ Scompact,
          (multiplicity rho : ℝ) * Real.rpow X (2 * (beta rho - 1))) =
          primitiveRegularCompactBridgeMass chi X T := by
      simp only [primitiveRegularCompactBridgeMass, Scompact, S, p,
        multiplicity, beta, Finset.filter_filter]
      rfl
    calc
      (∑ rho ∈ relativeCell S beta j,
        (multiplicity rho : ℝ) * Real.rpow X (2 * (beta rho - 1))) ≤
          ∑ rho ∈ Scompact,
            (multiplicity rho : ℝ) * Real.rpow X (2 * (beta rho - 1)) :=
        hsubsum
      _ = primitiveRegularCompactBridgeMass chi X T := hcompactEq
      _ ≤ BC := hcompact
      _ ≤ BC + BJ := le_add_of_nonneg_right hBJ
  have hcollarCell : ∀ j < L, collarIndex ≤ j →
      (∑ rho ∈ relativeCell S beta j,
        (multiplicity rho : ℝ) * Real.rpow X (2 * (beta rho - 1))) ≤
          BC + BJ := by
    intro j hjL hj
    have hdensityR :
        ((∑ rho ∈ S.filter (fun rho => relativePoint j ≤ beta rho),
            multiplicity rho : ℕ) : ℝ) ≤
          CJ * Real.rpow RJ ((21 / 10) * (1 - relativePoint j)) := by
      simpa only [inducedPrimitiveRegularCumulativeCount,
        primitiveRegularCumulativeCount, S, p, multiplicity, beta,
        Finset.filter_filter] using hcollar j hjL hj
    have he : 0 ≤ (21 / 10 : ℝ) * (1 - relativePoint j) := by
      exact mul_nonneg (by norm_num) (by linarith [relativePoint_le_one j])
    have hbase : Real.rpow RJ ((21 / 10) * (1 - relativePoint j)) ≤
        Real.rpow (Real.rpow X (tau epsilon + u))
          ((21 / 10) * (1 - relativePoint j)) :=
      Real.rpow_le_rpow hRJ hRJtoX he
    have hdensityX :
        ((∑ rho ∈ S.filter (fun rho => relativePoint j ≤ beta rho),
            multiplicity rho : ℕ) : ℝ) ≤
          CJ * Real.rpow X
            ((21 / 10) * (tau epsilon + u) *
              (1 - relativePoint j)) := by
      calc
        ((∑ rho ∈ S.filter (fun rho => relativePoint j ≤ beta rho),
            multiplicity rho : ℕ) : ℝ) ≤
            CJ * Real.rpow RJ ((21 / 10) * (1 - relativePoint j)) := hdensityR
        _ ≤ CJ * Real.rpow (Real.rpow X (tau epsilon + u))
              ((21 / 10) * (1 - relativePoint j)) :=
          mul_le_mul_of_nonneg_left hbase hCJ
        _ = CJ * Real.rpow X
              ((21 / 10) * (tau epsilon + u) *
                (1 - relativePoint j)) := by
          have hrpow :
              Real.rpow (Real.rpow X (tau epsilon + u))
                  ((21 / 10) * (1 - relativePoint j)) =
                Real.rpow X ((tau epsilon + u) *
                  ((21 / 10) * (1 - relativePoint j))) :=
            (Real.rpow_mul (zero_le_one.trans hX) _ _).symm
          rw [hrpow]
          congr 2
          ring
    have hcell := relativeCellMass_le_of_density
      S multiplicity beta hepsilon hu0 hu (hmeshGap j hjL)
      hX hCJ hdensityX
    exact hcell.trans (le_add_of_nonneg_left hBC)
  have hmass := relativeNearMass_le_log_mul_of_compact_collar_cell_bounds
    S multiplicity beta
    (omega := omega) (X := X) (B := BC + BJ) (L := L)
    (by
      intro rho hrho
      exact (Finset.mem_filter.mp hrho).2.1)
    hgap hdepth hLlog (add_nonneg hBC hBJ) hcompactCell hcollarCell
  simpa only [primitiveRegularNearOneRangeMass, p, S, multiplicity, beta,
    BJ] using hmass

/-- Fixed-scale family adapter.  The collar premise is now exactly the
regular cumulative divisor, with no ambient or exceptional zeros. -/
theorem apRegularNearOneRangeMass_le_of_cglfine_gappedCollar
    {Q L : ℕ} {epsilon eta u omega X : ℝ} {CC CJ : ℝ}
    (hepsilon : 0 < epsilon) (hepsilonCap : epsilon ≤ 1 / 10)
    (heta0 : 0 ≤ eta) (heta : eta ≤ epsilon / 2000)
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 315)
    (hgap : ∀ (q : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q), q ≤ Q → ∀ rho : ℂ,
      rho ∈ (by
        letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
        let psi := chi.primitiveCharacter
        exact (zeroSupport psi 0 (Real.rpow X (tau epsilon))).filter
          (fun rho => 4 / 5 < rho.re ∧
            ¬ (psi ≠ 1 ∧ psi ^ 2 = 1 ∧ rho.im = 0))) →
      rho.re ≤ 1 - omega)
    (hdepth : relativeDistance L ≤ omega)
    (hmeshGap : ∀ j < L, omega ≤ relativeDistance j)
    (hLlog : (L : ℝ) ≤ Real.log X)
    (hX : 1 ≤ X) (hCC : 0 ≤ CC) (hCJ : 0 ≤ CJ)
    (hScaleToX : ∀ (q : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q), q ≤ Q →
        (chi.conductor : ℝ) * Real.rpow X (tau epsilon) ≤
          Real.rpow X (tau epsilon + u))
    (hCGLdensity : ∀ (q : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q), q ≤ Q →
      ∀ sigma : ℝ, 4 / 5 ≤ sigma →
        sigma ≤ relativePoint collarIndex →
          (primitiveDirichletZeroCount chi sigma
            (Real.rpow X (tau epsilon)) : ℝ) ≤
            CC * Real.rpow (Real.rpow X (tau epsilon))
              (densityCoeff * (1 - sigma) + eta))
    (hcollar : ∀ (q : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q), q ≤ Q →
      ∀ j < L, collarIndex ≤ j →
        (inducedPrimitiveRegularCumulativeCount chi
          (relativePoint j) (Real.rpow X (tau epsilon)) : ℝ) ≤
          CJ * Real.rpow
            ((chi.conductor : ℝ) * Real.rpow X (tau epsilon))
              ((21 / 10) * (1 - relativePoint j))) :
    apRegularNearOneRangeMass Q X (Real.rpow X (tau epsilon)) ≤
      (Q : ℝ) ^ 2 *
        (Real.log X *
          ((MAPCGLNearFineMesh.fineCellCount epsilon : ℝ) *
              (CC * Real.rpow X (-(epsilon / 400))) +
            CJ * Real.rpow X (-(omega / 12)))) := by
  let BC : ℝ := (MAPCGLNearFineMesh.fineCellCount epsilon : ℝ) *
    (CC * Real.rpow X (-(epsilon / 400)))
  have hBC : 0 ≤ BC := by dsimp [BC]; positivity
  let BJ : ℝ := CJ * Real.rpow X (-(omega / 12))
  have hBJ : 0 ≤ BJ := by dsimp [BJ]; positivity
  have hprimitive : ∀ (q : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q), q ≤ Q →
        primitiveRegularNearOneRangeMass chi X
          (Real.rpow X (tau epsilon)) ≤ Real.log X * (BC + BJ) := by
    intro q _inst chi hqQ
    letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
    have hcompact : primitiveRegularCompactBridgeMass chi X
        (Real.rpow X (tau epsilon)) ≤ BC := by
      simpa only [BC] using
        (primitiveRegularCompactBridgeMass_le_of_density chi
          hepsilon hepsilonCap heta0 heta hX hCC (hCGLdensity q chi hqQ))
    have hR0 : 0 ≤ (chi.conductor : ℝ) *
        Real.rpow X (tau epsilon) :=
      mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (by positivity) _)
    simpa only [BC, BJ] using
      (primitiveRegularNearOneRangeMass_le_compactBridge_gappedCollar
        (RJ := (chi.conductor : ℝ) * Real.rpow X (tau epsilon)) chi
        hepsilon.le hu0 hu (hgap q chi hqQ) hdepth hmeshGap hLlog hX
        hBC hCJ hR0 (hScaleToX q chi hqQ) hcompact (hcollar q chi hqQ))
  have hB : 0 ≤ Real.log X * (BC + BJ) :=
    mul_nonneg (Real.log_nonneg hX) (add_nonneg hBC hBJ)
  simpa only [BC, BJ] using
    (apRegularNearOneRangeMass_le_sq_mul hB hprimitive)

end
end MAPAPRegularNearCGLGappedCollarRoute

#print axioms MAPAPRegularNearCGLGappedCollarRoute.primitiveRegularNearOneRangeMass_le_compactBridge_gappedCollar
#print axioms MAPAPRegularNearCGLGappedCollarRoute.apRegularNearOneRangeMass_le_of_cglfine_gappedCollar
