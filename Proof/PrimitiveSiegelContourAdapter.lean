import GoldfeldFourLogAbsorption
import PaperEdgePointwiseAnalyticReduction

/-!
# Unconditional real-zero adapter for the primitive Perron contour

The real-axis branch is discharged by the proved Siegel theorem.  The two
remaining zero-gap inputs are deliberately separated at `|Im rho| = 3`: the
bounded-height nonexceptional collar and the high-height Khale/Ford region.
-/

namespace MAPPrimitiveSiegelContourAdapter

open Set
open DirichletZeros PrimitiveTruncatedExplicitFormulaBridge
open PaperEdgePrimitiveComponents ZeroDistanceLogDerivativeBounds

noncomputable section

/-- Uniformly in the conductor, the unconditional Siegel theorem fills the
real-character/real-zero hole in a divisor gap.  What remains is exactly the
bounded-height regular collar and the closed high-height region. -/
theorem exists_zeroSupport_gap_of_regular_low_high
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
        chi.IsPrimitive →
        ∀ (sigma T omega : ℝ),
          omega ≤ c * Real.rpow (q : ℝ) (-epsilon) →
          (∀ rho ∈ zeroSupport chi sigma T,
            (chi = 1 ∨ chi ^ 2 ≠ 1 ∨ rho.im ≠ 0) → |rho.im| < 3 →
              rho.re ≤ 1 - omega) →
          (∀ rho ∈ zeroSupport chi sigma T,
            3 ≤ |rho.im| → rho.re ≤ 1 - omega) →
          ∀ rho ∈ zeroSupport chi sigma T,
            rho.re ≤ 1 - omega := by
  obtain ⟨c, hc, hSiegelGap⟩ :=
    MAPGoldfeldSiegel.publishedSiegelRealZeroFreeRegion.zero_gap hepsilon
  refine ⟨c, hc, ?_⟩
  intro q _inst chi _hprim sigma T omega homega hlow hhigh rho hrho
  by_cases hheight : 3 ≤ |rho.im|
  · exact hhigh rho hrho hheight
  have hlowHeight : |rho.im| < 3 := lt_of_not_ge hheight
  by_cases hregular : chi = 1 ∨ chi ^ 2 ≠ 1 ∨ rho.im ≠ 0
  · exact hlow rho hrho hregular hlowHeight
  have hnreg := not_or.mp hregular
  have hchi : chi ≠ 1 := hnreg.1
  have hnreg' := not_or.mp hnreg.2
  have hreal : chi ^ 2 = 1 := not_ne_iff.mp hnreg'.1
  have him : rho.im = 0 := not_ne_iff.mp hnreg'.2
  have hregzero : regularizedLFunction chi rho = 0 :=
    regularizedLFunction_eq_zero_of_mem_zeroSupport chi sigma T hrho
  have hLzeroComplex : DirichletCharacter.LFunction chi rho = 0 := by
    simpa [regularizedLFunction, hchi] using hregzero
  have hrho : rho = (rho.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  have hLzero : DirichletCharacter.LFunction chi rho.re = 0 := by
    rw [hrho] at hLzeroComplex
    exact hLzeroComplex
  have hgap := hSiegelGap q chi hchi hreal rho.re hLzero
  linarith


/-- Pointwise Perron zero-sum estimate with the real-axis gap discharged
unconditionally.  The only zero-region inputs left are the bounded regular
collar and the closed high-height region. -/
theorem exists_norm_multiplicityWeightedPerronZeroSum_le_of_regular_low_high
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
        chi.IsPrimitive →
        ∀ {sigma T x omega : ℝ},
          omega ≤ c * Real.rpow (q : ℝ) (-epsilon) →
          1 ≤ x → 0 < sigma →
          (∀ rho ∈ zeroSupport chi sigma T,
            (chi = 1 ∨ chi ^ 2 ≠ 1 ∨ rho.im ≠ 0) → |rho.im| < 3 →
              rho.re ≤ 1 - omega) →
          (∀ rho ∈ zeroSupport chi sigma T,
            3 ≤ |rho.im| → rho.re ≤ 1 - omega) →
          ‖PrimitiveTruncatedExplicitFormulaBridge.multiplicityWeightedPerronZeroSum
              chi sigma T x‖ ≤
            ((dirichletZeroCount chi sigma T : ℝ) / sigma) *
              Real.rpow x (1 - omega) := by
  obtain ⟨c, hc, hgap⟩ :=
    exists_zeroSupport_gap_of_regular_low_high hepsilon
  refine ⟨c, hc, ?_⟩
  intro q _inst chi hprim sigma T x omega homega hx hsigma hlow hhigh
  apply PointwisePerronZeroSumBounds.norm_multiplicityWeightedPerronZeroSum_le_of_gap
    chi hx hsigma
  exact hgap q chi hprim sigma T omega homega hlow hhigh


/-- The exact primitive pointwise estimate used before the final dyadic
Siegel--Walfisz absorption, with no real-zero source premise.  Its remaining
hypotheses are literal contour nonvanishing/distances/deflated-log-derivative
bounds plus the split regular-low/high-height zero regions. -/
theorem exists_norm_primitivePrefix_sub_characterMain_le_analyticQuantities
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
        chi.IsPrimitive → chi ≠ 1 →
        ∀ {t sigma T omega d R : ℝ},
          omega ≤ c * Real.rpow (q : ℝ) (-epsilon) →
          0 ≤ t → 1 ≤ ⌊t⌋₊ →
          0 < sigma → sigma < 1 → 0 < T → 0 < d →
          (∀ u ∈ Set.Icc (-T) T,
            regularizedLFunction chi
              ((sigma : ℂ) + Complex.I * u) ≠ 0) →
          (∀ r ∈ Set.Icc sigma (standardEdge ⌊t⌋₊),
            regularizedLFunction chi
              ((r : ℂ) - Complex.I * T) ≠ 0) →
          (∀ r ∈ Set.Icc sigma (standardEdge ⌊t⌋₊),
            regularizedLFunction chi
              ((r : ℂ) + Complex.I * T) ≠ 0) →
          (∀ rho ∈ zeroSupport chi sigma T,
            (chi = 1 ∨ chi ^ 2 ≠ 1 ∨ rho.im ≠ 0) → |rho.im| < 3 →
              rho.re ≤ 1 - omega) →
          (∀ rho ∈ zeroSupport chi sigma T,
            3 ≤ |rho.im| → rho.re ≤ 1 - omega) →
          (∀ u ∈ Set.Icc (-T) T,
            ∀ rho ∈ zeroSupport chi 0 T,
              d ≤ ‖((sigma : ℂ) + Complex.I * u) - rho‖) →
          (∀ r ∈ Set.Icc sigma (standardEdge ⌊t⌋₊),
            ∀ rho ∈ zeroSupport chi 0 T,
              d ≤ ‖((r : ℂ) + Complex.I * T) - rho‖) →
          (∀ r ∈ Set.Icc sigma (standardEdge ⌊t⌋₊),
            ∀ rho ∈ zeroSupport chi 0 T,
              d ≤ ‖((r : ℂ) - Complex.I * T) - rho‖) →
          (∀ u ∈ Set.Icc (-T) T,
            ‖logDeriv (compactZeroDeflatedRegularizedLFunction chi 0 T)
              ((sigma : ℂ) + Complex.I * u)‖ ≤ R) →
          (∀ r ∈ Set.Icc sigma (standardEdge ⌊t⌋₊),
            ‖logDeriv (compactZeroDeflatedRegularizedLFunction chi 0 T)
              ((r : ℂ) + Complex.I * T)‖ ≤ R) →
          (∀ r ∈ Set.Icc sigma (standardEdge ⌊t⌋₊),
            ‖logDeriv (compactZeroDeflatedRegularizedLFunction chi 0 T)
              ((r : ℂ) - Complex.I * T)‖ ≤ R) →
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
  obtain ⟨c, hc, hgap⟩ :=
    exists_zeroSupport_gap_of_regular_low_high hepsilon
  refine ⟨c, hc, ?_⟩
  intro q _inst chi hprim hchi t sigma T omega d R homega ht hN
    hsigma0 hsigma1 hT hd hleft hbottom htop hlow hhigh
    hdistLeft hdistTop hdistBottom hdeflatedLeft hdeflatedTop hdeflatedBottom
  apply PaperEdgePointwiseAnalyticReduction.norm_primitivePrefix_sub_characterMain_le_analyticQuantities
    chi hchi ht hN hsigma0 hsigma1 hT hd hleft hbottom htop
  · exact hgap q chi hprim sigma T omega homega hlow hhigh
  · exact hdistLeft
  · exact hdistTop
  · exact hdistBottom
  · exact hdeflatedLeft
  · exact hdeflatedTop
  · exact hdeflatedBottom

end
end MAPPrimitiveSiegelContourAdapter

#print axioms MAPPrimitiveSiegelContourAdapter.exists_zeroSupport_gap_of_regular_low_high
#print axioms MAPPrimitiveSiegelContourAdapter.exists_norm_multiplicityWeightedPerronZeroSum_le_of_regular_low_high
#print axioms MAPPrimitiveSiegelContourAdapter.exists_norm_primitivePrefix_sub_characterMain_le_analyticQuantities
