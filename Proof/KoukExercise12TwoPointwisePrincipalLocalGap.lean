import KoukExercise12TwoPointwisePrincipalLocalFormula
import PointwisePerronZeroSumBounds

/-!
# Principal local-horizontal formula with an explicit zero gap
-/

namespace MAPKoukExercise12TwoPointwisePrincipalLocalGap

open Complex Set DirichletZeros PrimitiveExplicitFormulaSpine
open PrimitiveTruncatedExplicitFormulaBridge PaperEdgePrimitiveComponents
open MAPKoukExercise12TwoContourAperture
open MAPKoukExercise12TwoLocalHorizontalAperture

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩

theorem exists_norm_principalPrefix_sub_main_le_of_gap
    {t H : ℝ} (ht : 0 ≤ t) (hN : 1 ≤ ⌊t⌋₊) (hH : 1 ≤ H) :
    ∃ sigma ∈ Set.Ioo (0 : ℝ) (1 / 2),
      ∃ T ∈ Set.Ioo H (H + 1),
        let x := halfIntegerPoint ⌊t⌋₊
        let dLeft := exerciseRealClearance (1 : DirichletCharacter ℂ 1) H
        let dHorizontal := exerciseHorizontalClearance
          (1 : DirichletCharacter ℂ 1) H
        let dCorner := min dLeft dHorizontal
        let L := Real.log (H + 3)
        let RLeft := 2 + 20 * (Real.log 223948800 + 6 * L) +
          30300 * L + 30300 * L / dLeft
        let RHorizontal := 2 + 20 * (Real.log 223948800 + 6 * L) +
          30300 * L + 30300 * L / dHorizontal
        let RCorner := 2 + 20 * (Real.log 223948800 + 6 * L) +
          30300 * L + 30300 * L / dCorner
        dLeft ≤ sigma ∧
        ∀ omega : ℝ, 0 ≤ omega →
          (∀ rho ∈ zeroSupport (1 : DirichletCharacter ℂ 1) sigma T,
            rho.re ≤ 1 - omega) →
          ‖APFoundation.twistedMangoldtSum
                (1 : DirichletCharacter ℂ 1) (Finset.Icc 1 ⌊t⌋₊) -
              MAPSiegelWalfiszCharacterReduction.characterMain
                (1 : DirichletCharacter ℂ 1) t‖ ≤
            1 / 2 +
            ((dirichletZeroCount
                (1 : DirichletCharacter ℂ 1) sigma T : ℝ) / sigma) *
              x ^ (1 - omega) +
            T / Real.pi * (RLeft * x ^ sigma / sigma) +
            (standardEdge ⌊t⌋₊ - sigma) / Real.pi *
              (RCorner * x ^ (1 / 2 : ℝ) / T +
                RHorizontal * x ^ standardEdge ⌊t⌋₊ / T) +
            insideMajorant ⌊t⌋₊ T + outsideMajorant ⌊t⌋₊ T := by
  obtain ⟨sigma, hsigma, T, hT, hpoint⟩ :=
    MAPKoukExercise12TwoPointwisePrincipalLocalFormula.exists_norm_principalPrefix_sub_main_le_zeroSum_add_local_contour
      ht hN hH
  refine ⟨sigma, hsigma, T, hT, ?_⟩
  dsimp only
  refine ⟨hpoint.1, ?_⟩
  intro omega _homega hgap
  have hx : 1 ≤ halfIntegerPoint ⌊t⌋₊ := by
    have hNR : (1 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast hN
    unfold halfIntegerPoint
    linarith
  have hzero :=
    PointwisePerronZeroSumBounds.norm_multiplicityWeightedPerronZeroSum_le_of_gap
      (1 : DirichletCharacter ℂ 1) hx hsigma.1 hgap
  exact hpoint.2.trans (by linarith [hzero])

end
end MAPKoukExercise12TwoPointwisePrincipalLocalGap

#print axioms MAPKoukExercise12TwoPointwisePrincipalLocalGap.exists_norm_principalPrefix_sub_main_le_of_gap
