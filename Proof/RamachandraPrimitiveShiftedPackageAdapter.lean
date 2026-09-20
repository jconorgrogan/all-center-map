import RamachandraPrimitiveShiftedHighLowWeld
import RamachandraPrincipalRemainderBudget
import RamachandraShiftedDirectShellAbsorption

/-!
# Final package adapter below the shifted long/short contour moments

This file isolates the only two analytic estimates still being assembled:
the literal `I₁` and `I₂` second moments.  Given those exact source-piece
budgets and their continuity, everything else needed by
`PrimitiveShiftedHighNonprincipalConstructionPackage` is constructed here:
the branch-correct identity, the certified direct series, and the exact
principal residue budget.
-/

namespace RamachandraPrimitiveShiftedPackageAdapter

open Complex MeasureTheory
open RamachandraTheorem6SourceProofChain
open RamachandraPrimitiveShiftedContourReduction
open RamachandraPrimitiveShiftedHighLowWeld
open RamachandraPrincipalHighSourceIdentity
open RamachandraPrincipalResidueContinuity
open RamachandraPrincipalRemainderBudget
open RamachandraShiftedDirectFullBudget
open RamachandraShiftedDirectShellAbsorption

noncomputable section

/-- The exact source-range statement for one of the two remaining contour
second moments.  The range excludes only the compact principal branch, which
is handled directly in the high/low weld. -/
structure PrimitiveShiftedSourceMomentPackage
    (moment : (d : ℕ) → [NeZero d] → ℝ → ℝ → ℝ) where
  C : ℝ
  C_pos : 0 < C
  bound : ∀ (q d : ℕ) [NeZero q] [NeZero d] (T sigma : ℝ),
      d ∣ q → 3 ≤ T →
      |sigma - (1 / 2 : ℝ)| ≤
          (100 * Real.log ((q : ℝ) * T))⁻¹ →
      (d ≠ 1 ∨ 9 ≤ T) →
      moment d T sigma ≤
        C * ((d : ℝ) * T) * Real.log ((d : ℝ) * T) ^ 200

/-- Source-range continuity of one literal contour piece. -/
def PrimitiveShiftedSourcePieceContinuity
    (piece : {d : ℕ} → [NeZero d] →
      DirichletCharacter ℂ d → ℝ → ℝ → ℝ → ℂ) : Prop :=
  ∀ (q d : ℕ) [NeZero q] [NeZero d] (T sigma : ℝ),
    d ∣ q → 3 ≤ T →
    |sigma - (1 / 2 : ℝ)| ≤
        (100 * Real.log ((q : ℝ) * T))⁻¹ →
    (d ≠ 1 ∨ 9 ≤ T) →
    ∀ psi : DirichletCharacter ℂ d,
      Continuous (fun t => ‖piece psi T sigma t‖ ^ 2)

/-- The canonical exact identity in the noncompact source range.  For
`d=1` it retains the translated zeta-pole residue; for every other conductor
the remainder is literally zero. -/
noncomputable def canonicalPrimitiveShiftedContourIdentityData
    (q d : ℕ) [NeZero q] [NeZero d] (T sigma : ℝ)
    (hdq : d ∣ q) (hT : 3 ≤ T)
    (hstrip : |sigma - (1 / 2 : ℝ)| ≤
      (100 * Real.log ((q : ℝ) * T))⁻¹)
    (hrange : d ≠ 1 ∨ 9 ≤ T)
    (hlong : ∀ psi : DirichletCharacter ℂ d,
      Continuous (fun t => ‖primitiveShiftedLongContour psi T sigma t‖ ^ 2))
    (hshort : ∀ psi : DirichletCharacter ℂ d,
      Continuous (fun t => ‖primitiveShiftedShortContour psi T sigma t‖ ^ 2)) :
    PrimitiveShiftedContourIdentityData d T sigma := by
  have hTpos : 0 < T := by linarith
  have hsigma := RamachandraPrincipalLowRange.sigma_mem_zero_threequarters_of_ramachandraStrip
    hT hstrip
  have hsigma1 : sigma < 1 :=
    RamachandraTheorem6SourceProofChain.sigma_lt_one_of_ramachandraStrip hT hstrip
  refine
    { remainder := fun psi t => canonicalPrimitiveShiftedRemainder psi T sigma t
      continuous_direct := fun psi =>
        (continuous_primitiveShiftedDirect psi hsigma.1 (by
          unfold primitiveShiftedScale
          exact mul_pos (by exact_mod_cast NeZero.pos d) hTpos)).norm.pow 2
      continuous_long := hlong
      continuous_short := hshort
      continuous_remainder := fun psi =>
        continuous_canonicalPrimitiveShiftedRemainder_sq psi hTpos hsigma1
      decomposition := ?_ }
  intro psi hprim t ht
  rcases hrange with hd | hT9
  · have hpsi : psi ≠ 1 := by
      intro heq
      exact hd
        (JutilaPrimitiveFunctionalEquation.level_eq_one_of_isPrimitive_eq_one
          hprim heq)
    have hnon :=
      RamachandraShiftedNonprincipalContourIdentity.LFunction_sq_eq_sourcePieces_nonprincipal
        psi hprim hpsi hdq hT hstrip (t := t)
    simpa [canonicalPrimitiveShiftedRemainder, hd] using hnon
  · exact LFunction_sq_eq_sourcePieces_allPrimitive
      psi hprim hdq hT9 hstrip (t := t)

/-- Deterministic final adapter.  Its four hypotheses are exactly continuity
and source-shaped second-moment estimates for the literal long and short
pieces; no fourth-moment conclusion occurs among them. -/
noncomputable def highNonprincipalConstructionPackage_of_longShort
    (hlongCont : PrimitiveShiftedSourcePieceContinuity
      (fun psi T sigma t => primitiveShiftedLongContour psi T sigma t))
    (hshortCont : PrimitiveShiftedSourcePieceContinuity
      (fun psi T sigma t => primitiveShiftedShortContour psi T sigma t))
    (hlongBound : PrimitiveShiftedSourceMomentPackage
      primitiveFamilyLongContourSecondMoment)
    (hshortBound : PrimitiveShiftedSourceMomentPackage
      primitiveFamilyShortContourSecondMoment) :
    PrimitiveShiftedHighNonprincipalConstructionPackage := by
  let Clong := hlongBound.C
  let Cshort := hshortBound.C
  have hClong : 0 < Clong := hlongBound.C_pos
  have hCshort : 0 < Cshort := hshortBound.C_pos
  let RemPackage := { C : ℝ // 0 < C ∧
    ∀ (q d : ℕ) [NeZero q] [NeZero d] (T sigma : ℝ), d ∣ q → 3 ≤ T →
      |sigma - (1 / 2 : ℝ)| ≤
          (100 * Real.log ((q : ℝ) * T))⁻¹ →
      primitiveFamilyRemainderSecondMoment d T
          (fun psi t => canonicalPrimitiveShiftedRemainder psi T sigma t) ≤
        C * ((d : ℝ) * T) * Real.log ((d : ℝ) * T) ^ 200 }
  have hRemNonempty : Nonempty RemPackage := by
    rcases exists_canonicalPrimitiveShiftedRemainder_sourceStripBudget with
      ⟨Crem, hCrem, hrem⟩
    exact ⟨⟨Crem, hCrem, hrem⟩⟩
  let remPackage : RemPackage := Classical.choice hRemNonempty
  let Crem : ℝ := remPackage.1
  have hCrem : 0 < Crem := remPackage.2.1
  have hrem := remPackage.2.2
  let Ccompact : ℝ := 2 * (6400 * 13 ^ 6) ^ 4
  let C : ℝ := Ccompact + 200000000000 + Clong + Cshort + Crem + 1
  have hC : 0 < C := by dsimp [C, Ccompact]; positivity
  have hcompact : Ccompact ≤ 16 * C := by
    have hCcompact0 : 0 ≤ Ccompact := by dsimp [Ccompact]; positivity
    dsimp [C]
    nlinarith [hClong, hCshort, hCrem]
  refine
    { C := C
      C_pos := hC
      compact_le := by simpa [Ccompact] using hcompact
      data := ?_ }
  intro q d _instq _instd T sigma hdq hT hstrip hrange
  have hsigma := RamachandraPrincipalLowRange.sigma_mem_zero_threequarters_of_ramachandraStrip
    hT hstrip
  have hscale0 : 0 ≤ ((d : ℝ) * T) := by positivity
  have hlog0 : 0 ≤ Real.log ((d : ℝ) * T) := by
    apply Real.log_nonneg
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast NeZero.pos d
    nlinarith
  let M : ℝ := ((d : ℝ) * T) * Real.log ((d : ℝ) * T) ^ 200
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let identity := canonicalPrimitiveShiftedContourIdentityData q d T sigma
    hdq hT hstrip hrange
      (hlongCont q d T sigma hdq hT hstrip hrange)
      (hshortCont q d T sigma hdq hT hstrip hrange)
  refine ⟨identity, ?_⟩
  have hdirect := primitiveFamilyDirectSecondMoment_le_log200_of_sourceStrip
    q d hdq hT
      (by
        exact inv_nonneg.mpr (mul_nonneg (by norm_num)
          (Real.log_nonneg (by
            have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
            nlinarith))))
      (le_rfl : (100 * Real.log ((q : ℝ) * T))⁻¹ ≤ _)
      hstrip hsigma.1
  have hlong' := hlongBound.bound q d T sigma hdq hT hstrip hrange
  have hshort' := hshortBound.bound q d T sigma hdq hT hstrip hrange
  have hrem' := hrem q d T sigma hdq hT hstrip
  have hCd : (200000000000 : ℝ) ≤ C := by
    dsimp [C, Ccompact]
    nlinarith [hClong, hCshort, hCrem]
  have hCl : Clong ≤ C := by
    dsimp [C, Ccompact]
    nlinarith [hClong, hCshort, hCrem]
  have hCs : Cshort ≤ C := by
    dsimp [C, Ccompact]
    nlinarith [hClong, hCshort, hCrem]
  have hCr : Crem ≤ C := by
    dsimp [C, Ccompact]
    nlinarith [hClong, hCshort, hCrem]
  refine
    { direct := ?_
      long := ?_
      short := ?_
      remainder_budget := ?_ }
  · exact hdirect.trans (by
      simpa [M, mul_assoc] using mul_le_mul_of_nonneg_right hCd hM)
  · exact hlong'.trans (by
      simpa [M, mul_assoc] using mul_le_mul_of_nonneg_right hCl hM)
  · exact hshort'.trans (by
      simpa [M, mul_assoc] using mul_le_mul_of_nonneg_right hCs hM)
  · simpa [identity, canonicalPrimitiveShiftedContourIdentityData] using
      hrem'.trans (by
        simpa [M, mul_assoc] using mul_le_mul_of_nonneg_right hCr hM)

end
end RamachandraPrimitiveShiftedPackageAdapter

#print axioms RamachandraPrimitiveShiftedPackageAdapter.canonicalPrimitiveShiftedContourIdentityData
#print axioms RamachandraPrimitiveShiftedPackageAdapter.highNonprincipalConstructionPackage_of_longShort
