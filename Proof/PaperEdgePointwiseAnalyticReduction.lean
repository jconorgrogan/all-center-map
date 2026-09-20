import PaperEdgePrimitiveComponents
import ZeroDistanceLogDerivativeBounds
import PointwisePerronZeroSumBounds

/-!
# Pointwise paper-edge reduction to literal analytic inputs

This theorem substitutes the paper-edge Perron bounds, the pointwise zero-gap
estimate, and the distance-explicit contour bounds into one primitive
explicit formula.  The remaining hypotheses are the actual zero-free gap,
the actual distance to the compact divisor, and a bound for the concrete
zero-deflated logarithmic derivative.
-/

namespace PaperEdgePointwiseAnalyticReduction

open Set
open scoped BigOperators ArithmeticFunction
open DirichletZeros PrimitiveExplicitFormulaSpine
open PrimitiveTruncatedExplicitFormulaBridge
open PaperEdgePrimitiveComponents
open ZeroDistanceLogDerivativeBounds

noncomputable section

theorem norm_primitivePrefix_sub_characterMain_le_analyticQuantities
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {t sigma T omega d R : ℝ}
    (ht : 0 ≤ t) (hN : 1 ≤ ⌊t⌋₊)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hT : 0 < T) (hd : 0 < d)
    (hleftNonzero : ∀ u ∈ Set.Icc (-T) T,
      regularizedLFunction chi
        ((sigma : ℂ) + Complex.I * u) ≠ 0)
    (hbottomNonzero : ∀ r ∈ Set.Icc sigma (standardEdge ⌊t⌋₊),
      regularizedLFunction chi
        ((r : ℂ) - Complex.I * T) ≠ 0)
    (htopNonzero : ∀ r ∈ Set.Icc sigma (standardEdge ⌊t⌋₊),
      regularizedLFunction chi
        ((r : ℂ) + Complex.I * T) ≠ 0)
    (hgap : ∀ rho ∈ zeroSupport chi sigma T,
      rho.re ≤ 1 - omega)
    (hdistLeft : ∀ u ∈ Set.Icc (-T) T,
      ∀ rho ∈ zeroSupport chi 0 T,
        d ≤ ‖((sigma : ℂ) + Complex.I * u) - rho‖)
    (hdistTop : ∀ r ∈ Set.Icc sigma (standardEdge ⌊t⌋₊),
      ∀ rho ∈ zeroSupport chi 0 T,
        d ≤ ‖((r : ℂ) + Complex.I * T) - rho‖)
    (hdistBottom : ∀ r ∈ Set.Icc sigma (standardEdge ⌊t⌋₊),
      ∀ rho ∈ zeroSupport chi 0 T,
        d ≤ ‖((r : ℂ) - Complex.I * T) - rho‖)
    (hdeflatedLeft : ∀ u ∈ Set.Icc (-T) T,
      ‖logDeriv (compactZeroDeflatedRegularizedLFunction chi 0 T)
        ((sigma : ℂ) + Complex.I * u)‖ ≤ R)
    (hdeflatedTop : ∀ r ∈ Set.Icc sigma (standardEdge ⌊t⌋₊),
      ‖logDeriv (compactZeroDeflatedRegularizedLFunction chi 0 T)
        ((r : ℂ) + Complex.I * T)‖ ≤ R)
    (hdeflatedBottom : ∀ r ∈ Set.Icc sigma (standardEdge ⌊t⌋₊),
      ‖logDeriv (compactZeroDeflatedRegularizedLFunction chi 0 T)
        ((r : ℂ) - Complex.I * T)‖ ≤ R) :
    ‖APFoundation.twistedMangoldtSum chi (Finset.Icc 1 ⌊t⌋₊) -
        MAPSiegelWalfiszCharacterReduction.characterMain chi t‖ ≤
      1 / 2 +
      ((dirichletZeroCount chi sigma T : ℝ) / sigma) *
        halfIntegerPoint ⌊t⌋₊ ^ (1 - omega) +
      T / Real.pi *
        ((compactPoleDistanceMajorant chi 0 T d + R) *
          halfIntegerPoint ⌊t⌋₊ ^ sigma / sigma) +
      (standardEdge ⌊t⌋₊ - sigma) / Real.pi *
        ((compactPoleDistanceMajorant chi 0 T d + R) *
          halfIntegerPoint ⌊t⌋₊ ^ standardEdge ⌊t⌋₊ / T) +
      insideMajorant ⌊t⌋₊ T + outsideMajorant ⌊t⌋₊ T := by
  let x := halfIntegerPoint ⌊t⌋₊
  let c := standardEdge ⌊t⌋₊
  have hxone : 1 ≤ x := by
    have hNr : (1 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast hN
    unfold x halfIntegerPoint
    linarith
  have hxpos : 0 < x := zero_lt_one.trans_le hxone
  have hcgt : 1 < c := standardEdge_gt_one ⌊t⌋₊ hN
  have hsigmac : sigma ≤ c := (le_of_lt hsigma1).trans hcgt.le
  have hLleft : ∀ u ∈ Set.Icc (-T) T,
      DirichletCharacter.LFunction chi
        ((sigma : ℂ) + Complex.I * u) ≠ 0 := by
    intro u hu
    simpa [regularizedLFunction, hchi] using hleftNonzero u hu
  have hLtop : ∀ r ∈ Set.Icc sigma c,
      DirichletCharacter.LFunction chi
        ((r : ℂ) + Complex.I * T) ≠ 0 := by
    intro r hr
    simpa [c, regularizedLFunction, hchi] using htopNonzero r hr
  have hLbottom : ∀ r ∈ Set.Icc sigma c,
      DirichletCharacter.LFunction chi
        ((r : ℂ) - Complex.I * T) ≠ 0 := by
    intro r hr
    simpa [c, regularizedLFunction, hchi] using hbottomNonzero r hr
  have hbase := norm_primitivePrefix_sub_characterMain_le_components
    chi ht hN hsigma0 hsigma1 hT
      (by
        intro u hu
        simpa [mul_comm] using hleftNonzero u hu)
      (by
        intro r hr
        simpa [mul_comm, sub_eq_add_neg] using hbottomNonzero r hr)
      (by
        intro r hr
        simpa [mul_comm] using htopNonzero r hr)
  have hzero :=
    PointwisePerronZeroSumBounds.norm_multiplicityWeightedPerronZeroSum_le_of_gap
      chi hxone hsigma0 hgap
  have hleft := norm_leftLineIntegral_le_zeroDistance_add_deflated
    chi hchi hxpos hsigma0 hT.le hd hLleft hdistLeft hdeflatedLeft
  have hhorizontal :=
    norm_horizontalBoundaryIntegral_le_zeroDistance_add_deflated
      chi hchi hxone hsigmac hT hd hLtop hLbottom
        (by simpa [c] using hdistTop)
        (by simpa [c] using hdistBottom)
        (by simpa [c] using hdeflatedTop)
        (by simpa [c] using hdeflatedBottom)
  dsimp only [x, c] at hzero hleft hhorizontal
  exact hbase.trans (by gcongr)

end

end PaperEdgePointwiseAnalyticReduction
