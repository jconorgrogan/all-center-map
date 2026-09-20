import KoukExercise12TwoPointwiseFormula
import KoukExercise12TwoZeroSum

/-!
# Exercise 12.2(a): pointwise formula with the Theorem 12.3 zero split

This layer combines the selected contour from the pointwise explicit formula
with the source-faithful regular/exceptional decomposition of its finite zero
divisor.  The possible exceptional atom is represented by a scalar budget `E`;
the next layer supplies that budget from the proved Siegel theorem.
-/

namespace MAPKoukExercise12TwoPointwiseZeroSplit

open Complex Set DirichletZeros PrimitiveExplicitFormulaSpine
open PrimitiveTruncatedExplicitFormulaBridge
open PaperEdgePrimitiveComponents
open MAPKoukExercise12TwoContourAperture
open MAPKoukExercise12TwoZeroSum

noncomputable section

/-- Selected-height pointwise Exercise 12.2(a), after splitting the zero sum
into the uniform Theorem 12.3 gap and at most one exceptional real atom. -/
theorem exists_norm_primitivePrefix_sub_characterMain_le_regular_add_exceptional
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {t H : ℝ} (ht : 0 ≤ t) (hN : 1 ≤ ⌊t⌋₊) (hH : 1 ≤ H) :
    ∃ sigma ∈ Set.Ioo (0 : ℝ) (1 / 2),
      ∃ T ∈ Set.Ioo H (H + 1),
        let x := halfIntegerPoint ⌊t⌋₊
        let d := exerciseContourClearance chi H
        let L := Real.log ((q : ℝ) * (H + 3))
        let R := 20 * (Real.log 21600 + 2 * L) + 5520 * L + 5520 * L / d
        d ≤ sigma ∧
        ∀ E : ℝ, 0 ≤ E →
          (∀ rho ∈ theorem12ThreeCollarSupport chi sigma T,
            x ^ rho.re / sigma ≤ E) →
          ‖APFoundation.twistedMangoldtSum chi (Finset.Icc 1 ⌊t⌋₊) -
              MAPSiegelWalfiszCharacterReduction.characterMain chi t‖ ≤
            1 / 2 +
            ((dirichletZeroCount chi sigma T : ℝ) / sigma) *
              x ^ (1 - exercise12TwoGap q T) + E +
            T / Real.pi * (R * x ^ sigma / sigma) +
            (standardEdge ⌊t⌋₊ - sigma) / Real.pi *
              (R * x ^ standardEdge ⌊t⌋₊ / T) +
            insideMajorant ⌊t⌋₊ T + outsideMajorant ⌊t⌋₊ T := by
  obtain ⟨sigma, hsigma, T, hT, hpoint⟩ :=
    MAPKoukExercise12TwoPointwiseFormula.exists_norm_primitivePrefix_sub_characterMain_le_zeroSum_add_contour
      chi hprim hchi ht hN hH
  refine ⟨sigma, hsigma, T, hT, ?_⟩
  dsimp only
  refine ⟨hpoint.1, ?_⟩
  intro E hE hExceptional
  have hx : 1 ≤ halfIntegerPoint ⌊t⌋₊ := by
    have hNR : (1 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast hN
    unfold halfIntegerPoint
    linarith
  have hzero :=
    norm_multiplicityWeightedPerronZeroSum_le_regular_add_exceptional
      chi hprim hchi (by linarith [hH, hT.1] : 0 ≤ T) hx hsigma.1 hE hExceptional
  exact hpoint.2.trans (by linarith [hzero])

#print axioms MAPKoukExercise12TwoPointwiseZeroSplit.exists_norm_primitivePrefix_sub_characterMain_le_regular_add_exceptional

end

end MAPKoukExercise12TwoPointwiseZeroSplit
