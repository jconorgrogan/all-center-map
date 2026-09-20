import PaperEdgePerronRemainder
import PaperEdgeOutsidePerronTail
import EndpointRegularizedZeroPrimitive
import PsiEndpointImprimitiveAdapters
import FiniteZeroAvoidingRectangle

/-!
# Shared primitive explicit-formula components at the paper edge

The pointwise Siegel--Walfisz route and the AP family-square route use the
same left and horizontal contour terms.  Their zero terms differ: pointwise
Siegel--Walfisz keeps the Perron zero sum, while the AP antiderivative keeps
the endpoint-zero/Perron-zero mismatch.  This file composes the already
proved paper-edge Perron estimates without merging those analytic leaves.
-/

namespace PaperEdgePrimitiveComponents

open Set
open scoped BigOperators ArithmeticFunction
open APFoundation APExplicitFormulaMajorantAdapter
open MAPEndpointRegularizedZeroPrimitive
open PrimitiveExplicitFormulaSpine PrimitiveTruncatedExplicitFormulaBridge
open TruncatedTwistedPerron

noncomputable section

/-- Standard right edge for the half-integer endpoint. -/
def standardEdge (N : ℕ) : ℝ :=
  1 + (Real.log (halfIntegerPoint N))⁻¹

/-- Closed inside-Perron majorant at the standard edge. -/
def insideMajorant (N : ℕ) (T : ℝ) : ℝ :=
  (3 * Real.exp 1 * halfIntegerPoint N *
    Real.log (halfIntegerPoint N) / (Real.pi * T)) *
      ((harmonic N : ℚ) : ℝ)

/-- Closed outside-Perron majorant at the standard edge. -/
def outsideMajorant (N : ℕ) (T : ℝ) : ℝ :=
  (Real.exp 1 * halfIntegerPoint N / (Real.pi * T)) *
    (2 * Real.log (2 * N + 1 : ℝ) *
        ((harmonic (N + 1) : ℚ) : ℝ) +
      (4 / (Real.log (halfIntegerPoint N))⁻¹) *
        (1 + (((Real.log (halfIntegerPoint N))⁻¹ / 2)⁻¹)))

theorem standardEdge_gt_one (N : ℕ) (hN : 1 ≤ N) :
    1 < standardEdge N := by
  have hxone : 1 < halfIntegerPoint N := by
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    unfold halfIntegerPoint
    linarith
  unfold standardEdge
  have hinv : 0 < (Real.log (halfIntegerPoint N))⁻¹ :=
    inv_pos.mpr (Real.log_pos hxone)
  linarith

/-- Pointwise primitive explicit-formula bound with the paper-edge Perron
terms completely evaluated.  The zero, left-line, and horizontal terms remain
separate literal norms. -/
theorem norm_primitivePrefix_sub_characterMain_le_components
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {t σ T : ℝ} (ht : 0 ≤ t) (hN : 1 ≤ ⌊t⌋₊)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hT : 0 < T)
    (hleftNonzero : ∀ u ∈ Set.Icc (-T) T,
      DirichletZeros.regularizedLFunction χ
        ((σ : ℂ) + (u : ℂ) * Complex.I) ≠ 0)
    (hbottomNonzero : ∀ r ∈ Set.Icc σ (standardEdge ⌊t⌋₊),
      DirichletZeros.regularizedLFunction χ
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0)
    (htopNonzero : ∀ r ∈ Set.Icc σ (standardEdge ⌊t⌋₊),
      DirichletZeros.regularizedLFunction χ
        ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    ‖APFoundation.twistedMangoldtSum χ (Finset.Icc 1 ⌊t⌋₊) -
        MAPSiegelWalfiszCharacterReduction.characterMain χ t‖ ≤
      1 / 2 +
      ‖multiplicityWeightedPerronZeroSum χ σ T
        (halfIntegerPoint ⌊t⌋₊)‖ +
      ‖leftLineIntegral χ (halfIntegerPoint ⌊t⌋₊) σ T‖ +
      ‖horizontalBoundaryIntegral χ
        (halfIntegerPoint ⌊t⌋₊) σ (standardEdge ⌊t⌋₊) T‖ +
      insideMajorant ⌊t⌋₊ T + outsideMajorant ⌊t⌋₊ T := by
  have hbase :=
    MAPPsiEndpointImprimitiveAdapters.norm_twistedMangoldtPrefix_sub_characterMain_le_explicitTerms
      χ ht hσ0 hσ1 (standardEdge_gt_one ⌊t⌋₊ hN) hT
      hleftNonzero hbottomNonzero htopNonzero
  have hinside :=
    PaperEdgePerronRemainder.norm_insideKernelError_standardEdge_le_harmonic
      χ ⌊t⌋₊ hN hT
  have houtside :=
    PaperEdgeOutsidePerronTail.norm_coefficientTail_standardEdge_le
      χ ⌊t⌋₊ hN hT
  exact hbase.trans (by
    simp only [standardEdge, insideMajorant, outsideMajorant]
    gcongr)

/-- The finite-divisor aperture theorem supplies the legal rectangle for the
pointwise component bound. -/
theorem exists_primitivePrefix_components
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {t H : ℝ} (ht : 0 ≤ t) (hN : 1 ≤ ⌊t⌋₊) (hH : 0 < H) :
    ∃ σ ∈ Set.Ioo (0 : ℝ) (1 / 2),
      ∃ T ∈ Set.Ioo H (H + 1),
        (∀ u ∈ Set.Icc (-T) T,
          DirichletZeros.regularizedLFunction χ
            ((σ : ℂ) + (u : ℂ) * Complex.I) ≠ 0) ∧
        (∀ r ∈ Set.Icc σ (standardEdge ⌊t⌋₊),
          DirichletZeros.regularizedLFunction χ
            ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0) ∧
        (∀ r ∈ Set.Icc σ (standardEdge ⌊t⌋₊),
          DirichletZeros.regularizedLFunction χ
            ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) ∧
        ‖APFoundation.twistedMangoldtSum χ (Finset.Icc 1 ⌊t⌋₊) -
            MAPSiegelWalfiszCharacterReduction.characterMain χ t‖ ≤
          1 / 2 +
          ‖multiplicityWeightedPerronZeroSum χ σ T
            (halfIntegerPoint ⌊t⌋₊)‖ +
          ‖leftLineIntegral χ (halfIntegerPoint ⌊t⌋₊) σ T‖ +
          ‖horizontalBoundaryIntegral χ
            (halfIntegerPoint ⌊t⌋₊) σ (standardEdge ⌊t⌋₊) T‖ +
          insideMajorant ⌊t⌋₊ T + outsideMajorant ⌊t⌋₊ T := by
  obtain ⟨σ, hσ, T, hT, hleft, hbottom, htop⟩ :=
    FiniteZeroAvoidingRectangle.exists_zeroAvoidingRectangle
      χ (H := H) (c := standardEdge ⌊t⌋₊) hH
  refine ⟨σ, hσ, T, hT, hleft, hbottom, htop, ?_⟩
  exact norm_primitivePrefix_sub_characterMain_le_components
    χ ht hN hσ.1 (by linarith [hσ.2]) (hH.trans hT.1)
      hleft hbottom htop

variable {q : ℕ} [NeZero q]

/-- Exact endpoint remainder at the paper edge.  This is the AP analogue of
the pointwise primitive decomposition above. -/
def endpointRemainder
    (χ : DirichletCharacter ℂ q) (σ T t : ℝ) : ℂ := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  let N := ⌊t⌋₊
  let u := halfIntegerPoint N
  let c := standardEdge N
  exact
    residueMain χ.primitiveCharacter u - principalCoefficient χ * t +
      endpointMultiplicityWeightedZeroTerm χ.primitiveCharacter 0 T t -
      multiplicityWeightedPerronZeroSum χ.primitiveCharacter σ T u +
      leftLineIntegral χ.primitiveCharacter u σ T -
      horizontalBoundaryIntegral χ.primitiveCharacter u σ c T +
      insideKernelError χ.primitiveCharacter N c T -
      coefficientTail χ.primitiveCharacter u c T (Finset.Icc 1 N) -
      APFoundation.imprimitiveMangoldtCorrection χ (Finset.Icc 1 N)

/-- Exact real-endpoint formula with the paper-edge remainder. -/
theorem ambientTwistedPsi_eq_principal_sub_endpoint_add_remainder
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor]
    {σ T t : ℝ} (hN : 1 ≤ ⌊t⌋₊)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hT : 0 < T)
    (hleftNonzero : ∀ u ∈ Set.Icc (-T) T,
      DirichletZeros.regularizedLFunction χ.primitiveCharacter
        ((σ : ℂ) + (u : ℂ) * Complex.I) ≠ 0)
    (hbottomNonzero : ∀ r ∈ Set.Icc σ (standardEdge ⌊t⌋₊),
      DirichletZeros.regularizedLFunction χ.primitiveCharacter
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0)
    (htopNonzero : ∀ r ∈ Set.Icc σ (standardEdge ⌊t⌋₊),
      DirichletZeros.regularizedLFunction χ.primitiveCharacter
        ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    ambientTwistedPsi χ t =
      principalCoefficient χ * t -
        endpointMultiplicityWeightedZeroTerm χ.primitiveCharacter 0 T t +
          endpointRemainder χ σ T t := by
  have hformula :=
    UniformPsiDeterministicBridge.ambientTwistedMangoldtPrefix_eq_primitive_explicit_formula
      χ ⌊t⌋₊ hσ0 hσ1 (standardEdge_gt_one ⌊t⌋₊ hN) hT
      hleftNonzero hbottomNonzero htopNonzero
  unfold ambientTwistedPsi
  rw [hformula]
  simp only [endpointRemainder]
  ring

/-- Literal endpoint-remainder majorant with shared contour components and a
separate endpoint-zero/Perron-zero mismatch. -/
def endpointRemainderMajorant
    (χ : DirichletCharacter ℂ q) (σ T t : ℝ) : ℝ := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  let N := ⌊t⌋₊
  let u := halfIntegerPoint N
  let c := standardEdge N
  exact 1 / 2 +
    ‖endpointMultiplicityWeightedZeroTerm χ.primitiveCharacter 0 T t -
      multiplicityWeightedPerronZeroSum χ.primitiveCharacter σ T u‖ +
    ‖leftLineIntegral χ.primitiveCharacter u σ T‖ +
    ‖horizontalBoundaryIntegral χ.primitiveCharacter u σ c T‖ +
    insideMajorant N T + outsideMajorant N T +
    (⌊Real.log (N : ℝ) / Real.log 2⌋₊ : ℝ) * Real.log q

/-- The AP endpoint remainder is bounded by the same evaluated paper-edge
Perron terms and the same literal left/horizontal contour components used in
the pointwise theorem. -/
theorem norm_endpointRemainder_le_majorant
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor]
    {σ T t : ℝ} (ht : 0 ≤ t) (hN : 1 ≤ ⌊t⌋₊) (hT : 0 < T) :
    ‖endpointRemainder χ σ T t‖ ≤
      endpointRemainderMajorant χ σ T t := by
  let N := ⌊t⌋₊
  let u := halfIntegerPoint N
  let c := standardEdge N
  let M := residueMain χ.primitiveCharacter u - principalCoefficient χ * t
  let Z := endpointMultiplicityWeightedZeroTerm χ.primitiveCharacter 0 T t -
    multiplicityWeightedPerronZeroSum χ.primitiveCharacter σ T u
  let L := leftLineIntegral χ.primitiveCharacter u σ T
  let H := horizontalBoundaryIntegral χ.primitiveCharacter u σ c T
  let I := insideKernelError χ.primitiveCharacter N c T
  let E := coefficientTail χ.primitiveCharacter u c T (Finset.Icc 1 N)
  let Q := APFoundation.imprimitiveMangoldtCorrection χ (Finset.Icc 1 N)
  have hmain : ‖M‖ ≤ 1 / 2 := by
    dsimp only [M, u, N]
    rw [PrimitiveTruncatedExplicitFormulaBridge.residueMain_primitiveCharacter χ]
    by_cases hχ : χ = 1
    · simp only [residueMain, principalCoefficient, hχ, if_true]
      rw [one_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact abs_halfIntegerPoint_floor_sub_le t ht
    · simp [residueMain, principalCoefficient, hχ]
  have hinside : ‖I‖ ≤ insideMajorant N T := by
    dsimp only [I, c, insideMajorant]
    exact PaperEdgePerronRemainder.norm_insideKernelError_standardEdge_le_harmonic
      χ.primitiveCharacter N hN hT
  have houtside : ‖E‖ ≤ outsideMajorant N T := by
    dsimp only [E, c, u, outsideMajorant]
    exact PaperEdgeOutsidePerronTail.norm_coefficientTail_standardEdge_le
      χ.primitiveCharacter N hN hT
  have himprimitive : ‖Q‖ ≤
      (⌊Real.log (N : ℝ) / Real.log 2⌋₊ : ℝ) * Real.log q := by
    exact norm_imprimitiveMangoldtCorrection_prefix_le χ N
  have hsplit : endpointRemainder χ σ T t =
      M + Z + L - H + I - E - Q := by
    simp only [endpointRemainder, M, Z, L, H, I, E, Q, N, u, c]
    ring
  rw [hsplit]
  dsimp only [endpointRemainderMajorant, N, u, c]
  calc
    ‖M + Z + L - H + I - E - Q‖ ≤
        ‖M‖ + ‖Z‖ + ‖L‖ + ‖H‖ + ‖I‖ + ‖E‖ + ‖Q‖ := by
      calc
        ‖M + Z + L - H + I - E - Q‖ ≤
            ‖M + Z + L - H + I - E‖ + ‖Q‖ := norm_sub_le _ _
        _ ≤ (‖M + Z + L - H + I‖ + ‖E‖) + ‖Q‖ := by
          gcongr
          exact norm_sub_le _ _
        _ ≤ ((‖M + Z + L - H‖ + ‖I‖) + ‖E‖) + ‖Q‖ := by
          gcongr
          exact norm_add_le _ _
        _ ≤ (((‖M + Z + L‖ + ‖H‖) + ‖I‖) + ‖E‖) + ‖Q‖ := by
          gcongr
          exact norm_sub_le _ _
        _ ≤ ((((‖M + Z‖ + ‖L‖) + ‖H‖) + ‖I‖) + ‖E‖) + ‖Q‖ := by
          gcongr
          exact norm_add_le _ _
        _ ≤ (((((‖M‖ + ‖Z‖) + ‖L‖) + ‖H‖) + ‖I‖) + ‖E‖) + ‖Q‖ := by
          gcongr
          exact norm_add_le _ _
        _ = ‖M‖ + ‖Z‖ + ‖L‖ + ‖H‖ + ‖I‖ + ‖E‖ + ‖Q‖ := by ring
    _ ≤ 1 / 2 + ‖Z‖ + ‖L‖ + ‖H‖ +
          insideMajorant N T + outsideMajorant N T +
          (⌊Real.log (N : ℝ) / Real.log 2⌋₊ : ℝ) * Real.log q := by
      gcongr

/-- The same zero-avoiding aperture simultaneously supplies the exact AP
endpoint formula and its componentwise remainder bound. -/
theorem exists_endpointFormula_and_remainderMajorant
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor]
    {t H : ℝ} (ht : 0 ≤ t) (hN : 1 ≤ ⌊t⌋₊) (hH : 0 < H) :
    ∃ σ ∈ Set.Ioo (0 : ℝ) (1 / 2),
      ∃ T ∈ Set.Ioo H (H + 1),
        (∀ u ∈ Set.Icc (-T) T,
          DirichletZeros.regularizedLFunction χ.primitiveCharacter
            ((σ : ℂ) + (u : ℂ) * Complex.I) ≠ 0) ∧
        (∀ r ∈ Set.Icc σ (standardEdge ⌊t⌋₊),
          DirichletZeros.regularizedLFunction χ.primitiveCharacter
            ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0) ∧
        (∀ r ∈ Set.Icc σ (standardEdge ⌊t⌋₊),
          DirichletZeros.regularizedLFunction χ.primitiveCharacter
            ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) ∧
        ambientTwistedPsi χ t =
          principalCoefficient χ * t -
            endpointMultiplicityWeightedZeroTerm χ.primitiveCharacter 0 T t +
              endpointRemainder χ σ T t ∧
        ‖endpointRemainder χ σ T t‖ ≤
          endpointRemainderMajorant χ σ T t := by
  obtain ⟨σ, hσ, T, hT, hleft, hbottom, htop⟩ :=
    FiniteZeroAvoidingRectangle.exists_zeroAvoidingRectangle
      χ.primitiveCharacter (H := H) (c := standardEdge ⌊t⌋₊) hH
  refine ⟨σ, hσ, T, hT, hleft, hbottom, htop, ?_, ?_⟩
  · exact ambientTwistedPsi_eq_principal_sub_endpoint_add_remainder
      χ hN hσ.1 (by linarith [hσ.2]) (hH.trans hT.1)
        hleft hbottom htop
  · exact norm_endpointRemainder_le_majorant
      χ ht hN (hH.trans hT.1)

end

end PaperEdgePrimitiveComponents
