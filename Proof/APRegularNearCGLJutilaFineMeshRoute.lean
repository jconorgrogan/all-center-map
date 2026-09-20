import CGLNearFineMeshSourceAdapter
import APRegularNearHuxleyJutilaSourceAdapter

/-!
# Regular near-one mass from the CGL fine mesh and Jutila collar

This replaces the Huxley compact branch of `APRegularNearMeshRoute` by the
epsilon-fine CGL bridge.  The bridge is first bounded as one finite mass;
each of the original relative cells below the collar is then a nonnegative
subsum of that mass.  The published Jutila collar branch is unchanged.
-/

namespace MAPAPRegularNearCGLJutilaFineMeshRoute

open scoped BigOperators
open DirichletZeros MAPFixedScaleAPZeroRoute MAPAPZeroDensityCert
open MAPAPWeightedZeroMassIntegration MAPAPRelativeMeshPrimitiveApplication
open MAPRelativeNearOneMesh27 MAPJutilaCollarMeshCutoff MAPGuthMaynard
open MAPAPRegularNearMeshRoute MAPCGLNearFineMesh
open MAPCGLNearFineMeshSourceAdapter

noncomputable section

/-- One primitive inducer: an already-integrated CGL compact bridge plus the
pointwise Jutila collar count imply the complete regular near-one mass. -/
theorem primitiveRegularNearOneRangeMass_le_compactBridge_jutila
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
    (hJutila : ∀ j < L, collarIndex ≤ j →
      (primitiveDirichletZeroCount chi (relativePoint j) T : ℝ) ≤
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
  have hcumulative (j : ℕ) :
      ((∑ rho ∈ S.filter (fun rho => relativePoint j ≤ beta rho),
          multiplicity rho : ℕ) : ℝ) ≤
        (primitiveDirichletZeroCount chi (relativePoint j) T : ℝ) := by
    have hnat :
        (∑ rho ∈ S.filter (fun rho => relativePoint j ≤ beta rho),
          multiplicity rho : ℕ) ≤
            primitiveDirichletZeroCount chi (relativePoint j) T := by
      apply fullSubsupportMultiplicity_le_primitiveCount chi
      · intro rho hrho
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hrho).1).1
      · intro rho hrho
        exact (Finset.mem_filter.mp hrho).2
    exact_mod_cast hnat
  have hcompactCell : ∀ j < L, j < collarIndex →
      (∑ rho ∈ relativeCell S beta j,
        (multiplicity rho : ℝ) * Real.rpow X (2 * (beta rho - 1))) ≤
          BC + BJ := by
    intro j _hjL hj
    have hsucc : j + 1 ≤ collarIndex := by omega
    have hpoint := relativePoint_mono hsucc
    let Scompact := S.filter fun rho =>
      beta rho ≤ relativePoint collarIndex
    have hsubset : relativeCell S beta j ⊆ Scompact := by
      intro rho hrho
      have hr := (Finset.mem_filter.mp hrho)
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
    have hdensityR := (hcumulative j).trans (hJutila j hjL hj)
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
            CJ * Real.rpow RJ ((21 / 10) * (1 - relativePoint j)) :=
          hdensityR
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

/-- Fixed-scale family version.  This is the deterministic live adapter:
the compact density is needed only on the epsilon-fine mesh and Jutila only
on the closed collar. -/
theorem apRegularNearOneRangeMass_le_of_cglfine_jutila_sources
    {Q L : ℕ} {epsilon eta u omega X : ℝ}
    {CC CJ RJ : ℝ}
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
    (hJutilaScale : ∀ (q : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q), q ≤ Q →
        RJ ≤ (chi.conductor : ℝ) * Real.rpow X (tau epsilon))
    (hCGLdensity : ∀ (q : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q), q ≤ Q →
      ∀ sigma : ℝ, 4 / 5 ≤ sigma →
        sigma ≤ relativePoint collarIndex →
          (primitiveDirichletZeroCount chi sigma
            (Real.rpow X (tau epsilon)) : ℝ) ≤
            CC * Real.rpow (Real.rpow X (tau epsilon))
              (densityCoeff * (1 - sigma) + eta))
    (hJsource : ∀ (r : ℕ) [NeZero r] (S sigma : ℝ),
      1 ≤ S → 279 / 280 ≤ sigma → sigma ≤ 1 →
      RJ ≤ (r : ℝ) * S →
        (ambientZeroCountAtLevel r sigma S : ℝ) ≤
          CJ * Real.rpow ((r : ℝ) * S)
            ((21 / 10) * (1 - sigma))) :
    apRegularNearOneRangeMass Q X (Real.rpow X (tau epsilon)) ≤
      (Q : ℝ) ^ 2 *
        (Real.log X *
          ((fineCellCount epsilon : ℝ) *
              (CC * Real.rpow X (-(epsilon / 400))) +
            CJ * Real.rpow X (-(omega / 12)))) := by
  have hTone : 1 ≤ Real.rpow X (tau epsilon) :=
    Real.one_le_rpow hX (tau_pos hepsilonCap).le
  let BC : ℝ := (fineCellCount epsilon : ℝ) *
    (CC * Real.rpow X (-(epsilon / 400)))
  have hBC : 0 ≤ BC := by
    dsimp [BC]
    positivity
  let BJ : ℝ := CJ * Real.rpow X (-(omega / 12))
  have hBJ : 0 ≤ BJ := by
    dsimp [BJ]
    positivity
  have hprimitive : ∀ (q : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q), q ≤ Q →
        primitiveRegularNearOneRangeMass chi X
          (Real.rpow X (tau epsilon)) ≤
          Real.log X * (BC + BJ) := by
    intro q _inst chi hqQ
    letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
    let psi := chi.primitiveCharacter
    have hcompact : primitiveRegularCompactBridgeMass chi X
        (Real.rpow X (tau epsilon)) ≤ BC := by
      simpa only [BC] using
        (primitiveRegularCompactBridgeMass_le_of_density chi
          hepsilon hepsilonCap heta0 heta hX hCC
          (hCGLdensity q chi hqQ))
    have hJutila : ∀ j < L, collarIndex ≤ j →
        (primitiveDirichletZeroCount chi (relativePoint j)
          (Real.rpow X (tau epsilon)) : ℝ) ≤
          CJ * Real.rpow ((chi.conductor : ℝ) *
            Real.rpow X (tau epsilon))
              ((21 / 10) * (1 - relativePoint j)) := by
      intro j _hjL hj
      have hsingleNat := dirichletZeroCount_le_ambientZeroCountAtLevel
        psi (relativePoint j) (Real.rpow X (tau epsilon))
      have hsingle :
          (primitiveDirichletZeroCount chi (relativePoint j)
            (Real.rpow X (tau epsilon)) : ℝ) ≤
            (ambientZeroCountAtLevel chi.conductor (relativePoint j)
              (Real.rpow X (tau epsilon)) : ℝ) := by
        simpa only [primitiveDirichletZeroCount] using
          (show (dirichletZeroCount psi (relativePoint j)
              (Real.rpow X (tau epsilon)) : ℝ) ≤
            (ambientZeroCountAtLevel chi.conductor (relativePoint j)
              (Real.rpow X (tau epsilon)) : ℝ) by
                exact_mod_cast hsingleNat)
      exact hsingle.trans (hJsource chi.conductor
        (Real.rpow X (tau epsilon)) (relativePoint j) hTone
        (relativePoint_mem_collar hj) (relativePoint_le_one j)
        (hJutilaScale q chi hqQ))
    have hR0 : 0 ≤ (chi.conductor : ℝ) *
        Real.rpow X (tau epsilon) := by positivity
    simpa only [BC, BJ] using
      (primitiveRegularNearOneRangeMass_le_compactBridge_jutila
        (RJ := (chi.conductor : ℝ) * Real.rpow X (tau epsilon)) chi
        hepsilon.le hu0 hu (hgap q chi hqQ) hdepth hmeshGap hLlog hX
        hBC hCJ hR0 (hScaleToX q chi hqQ) hcompact hJutila)
  have hB : 0 ≤ Real.log X * (BC + BJ) := by
    exact mul_nonneg (Real.log_nonneg hX) (add_nonneg hBC hBJ)
  simpa only [BC, BJ] using
    (apRegularNearOneRangeMass_le_sq_mul hB hprimitive)

end
end MAPAPRegularNearCGLJutilaFineMeshRoute

#print axioms MAPAPRegularNearCGLJutilaFineMeshRoute.primitiveRegularNearOneRangeMass_le_compactBridge_jutila
#print axioms MAPAPRegularNearCGLJutilaFineMeshRoute.apRegularNearOneRangeMass_le_of_cglfine_jutila_sources
