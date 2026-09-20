import APRelativeMeshPrimitiveApplication
import HuxleyCompactGapExponent
import JutilaCollarMeshCutoff

/-!
# Narrow regular-near equation-(2.7) constructor

This file uses no all-`sigma` density interface.  Its two count inputs are
only the fixed-modulus cumulative inequalities at the relative mesh points:
Huxley for the first 95 cells and Jutila in the closed collar from index 95
onward.
-/

namespace MAPAPRegularNearMeshRoute

open scoped BigOperators
open DirichletZeros MAPFixedScaleAPZeroRoute MAPAPZeroDensityCert
open MAPAPWeightedZeroMassIntegration MAPAPRelativeMeshPrimitiveApplication
open MAPRelativeNearOneMesh27 MAPJutilaCollarMeshCutoff
open MAPHuxleyCompactGapExponent MAPGuthMaynard

noncomputable section

/-- One primitive inducer's regular near-one mass, after the finite Huxley /
Jutila mesh split.  The only count hypotheses are at the mesh points actually
used by the proof. -/
theorem primitiveRegularNearOneRangeMass_le_huxley_jutila_mesh
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {epsilon u omega X T CH CJ RH RJ : ℝ} {L : ℕ}
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
    (hX : 1 ≤ X)
    (hCH : 0 ≤ CH) (hCJ : 0 ≤ CJ)
    (hRH : 0 ≤ RH) (hRJ : 0 ≤ RJ)
    (hRHtoX : RH ≤ Real.rpow X (tau epsilon + u))
    (hRJtoX : RJ ≤ Real.rpow X (tau epsilon + u))
    (hHuxley : ∀ j < L, j < collarIndex →
      (primitiveDirichletZeroCount chi (relativePoint j) T : ℝ) ≤
        CH * Real.rpow RH
          (huxleyDensityExponent (relativePoint j) + huxleySourceEta))
    (hJutila : ∀ j < L, collarIndex ≤ j →
      (primitiveDirichletZeroCount chi (relativePoint j) T : ℝ) ≤
        CJ * Real.rpow RJ
          ((21 / 10) * (1 - relativePoint j))) :
    primitiveRegularNearOneRangeMass chi X T ≤
      Real.log X *
        (CH * Real.rpow X (-huxleyCompactSaving) +
          CJ * Real.rpow X (-(omega / 12))) := by
  classical
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let psi := chi.primitiveCharacter
  let p : ℂ → Prop := fun rho =>
    4 / 5 < rho.re ∧ ¬ (psi ≠ 1 ∧ psi ^ 2 = 1 ∧ rho.im = 0)
  let S := (zeroSupport psi 0 T).filter p
  let multiplicity : ℂ → ℕ := fun rho => zeroMultiplicity psi 0 T rho
  let beta : ℂ → ℝ := Complex.re
  let BH : ℝ := CH * Real.rpow X (-huxleyCompactSaving)
  let BJ : ℝ := CJ * Real.rpow X (-(omega / 12))
  have hBH : 0 ≤ BH :=
    mul_nonneg hCH (Real.rpow_nonneg (zero_le_one.trans hX) _)
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
  have hcompact : ∀ j < L, j < collarIndex →
      (∑ rho ∈ relativeCell S beta j,
        (multiplicity rho : ℝ) * Real.rpow X (2 * (beta rho - 1))) ≤
          BH + BJ := by
    intro j hjL hj
    have hdensity := (hcumulative j).trans (hHuxley j hjL hj)
    have hcell := huxley_relativeCellMass_le
      S multiplicity beta hj hepsilon hu hX hCH hRH hRHtoX hdensity
    exact hcell.trans (le_add_of_nonneg_right hBJ)
  have hcollar : ∀ j < L, collarIndex ≤ j →
      (∑ rho ∈ relativeCell S beta j,
        (multiplicity rho : ℝ) * Real.rpow X (2 * (beta rho - 1))) ≤
          BH + BJ := by
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
            CJ * Real.rpow RJ
              ((21 / 10) * (1 - relativePoint j)) := hdensityR
        _ ≤ CJ * Real.rpow (Real.rpow X (tau epsilon + u))
              ((21 / 10) * (1 - relativePoint j)) :=
          mul_le_mul_of_nonneg_left hbase hCJ
        _ = CJ * Real.rpow X
              ((21 / 10) * (tau epsilon + u) *
                (1 - relativePoint j)) := by
          have hrpow :
              Real.rpow (Real.rpow X (tau epsilon + u))
                  ((21 / 10) * (1 - relativePoint j)) =
                Real.rpow X
                  ((tau epsilon + u) *
                    ((21 / 10) * (1 - relativePoint j))) :=
            (Real.rpow_mul (zero_le_one.trans hX)
              (tau epsilon + u)
              ((21 / 10) * (1 - relativePoint j))).symm
          rw [hrpow]
          congr 2
          ring
    have hcell := relativeCellMass_le_of_density
      S multiplicity beta hepsilon hu0 hu
      (hmeshGap j hjL)
      hX hCJ hdensityX
    exact hcell.trans (le_add_of_nonneg_left hBH)
  have hmass := relativeNearMass_le_log_mul_of_compact_collar_cell_bounds
    S multiplicity beta
    (omega := omega) (X := X) (B := BH + BJ) (L := L)
    (by
      intro rho hrho
      exact (Finset.mem_filter.mp hrho).2.1)
    hgap hdepth hLlog (add_nonneg hBH hBJ) hcompact hcollar
  simpa only [primitiveRegularNearOneRangeMass, p, S, multiplicity, beta,
    BH, BJ] using hmass

/-- Summing a uniform primitive-inducer regular-near bound over every ambient
character and positive level up to `Q` costs at most `Q^2`. -/
theorem apRegularNearOneRangeMass_le_sq_mul
    {Q : ℕ} {X T B : ℝ} (hB : 0 ≤ B)
    (hprimitive : ∀ (q : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q), q ≤ Q →
        primitiveRegularNearOneRangeMass chi X T ≤ B) :
    apRegularNearOneRangeMass Q X T ≤ (Q : ℝ) ^ 2 * B := by
  classical
  unfold apRegularNearOneRangeMass
  calc
    (∑ q ∈ Finset.Icc 1 Q,
      if hq : q = 0 then 0
      else
        letI : NeZero q := ⟨hq⟩
        ∑ chi : DirichletCharacter ℂ q,
          primitiveRegularNearOneRangeMass chi X T) ≤
        ∑ _q ∈ Finset.Icc 1 Q, (Q : ℝ) * B := by
      apply Finset.sum_le_sum
      intro q hqI
      split_ifs with hq0
      · exact mul_nonneg (Nat.cast_nonneg Q) hB
      · letI : NeZero q := ⟨hq0⟩
        calc
          (∑ chi : DirichletCharacter ℂ q,
              primitiveRegularNearOneRangeMass chi X T) ≤
              ∑ _chi : DirichletCharacter ℂ q, B := by
            apply Finset.sum_le_sum
            intro chi _hchi
            exact hprimitive q chi (Finset.mem_Icc.mp hqI).2
          _ = (Nat.card (DirichletCharacter ℂ q) : ℝ) * B := by
            simp [Nat.card_eq_fintype_card]
          _ ≤ (q : ℝ) * B := by
            apply mul_le_mul_of_nonneg_right _ hB
            exact_mod_cast (show Nat.card (DirichletCharacter ℂ q) ≤ q by
              rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
              exact Nat.totient_le q)
          _ ≤ (Q : ℝ) * B := by
            apply mul_le_mul_of_nonneg_right _ hB
            exact_mod_cast (Finset.mem_Icc.mp hqI).2
    _ = (Q : ℝ) ^ 2 * B := by
      simp
      ring

end
end MAPAPRegularNearMeshRoute

#print axioms MAPAPRegularNearMeshRoute.primitiveRegularNearOneRangeMass_le_huxley_jutila_mesh
#print axioms MAPAPRegularNearMeshRoute.apRegularNearOneRangeMass_le_sq_mul
