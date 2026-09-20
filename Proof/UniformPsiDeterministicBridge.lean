import PrimitiveRemovableClosure
import SharpPerronRemainderBridge
import SiegelWalfiszCharacterReduction

/-!
# Deterministic bridge from the primitive explicit formula to the twisted-psi error

This staging file introduces no analytic contract.  It only combines the
canonical primitive/imprimitive decomposition, finite-pole rectangle identity,
half-integer endpoint comparison, and the already proved Perron and bad-Euler
factor bounds.
-/

namespace UniformPsiDeterministicBridge

open Set
open scoped BigOperators ArithmeticFunction
open PrimitiveExplicitFormulaSpine
open PrimitiveTruncatedExplicitFormulaBridge
open TruncatedTwistedPerron
open DirichletZeros

noncomputable section

/-- The two canonical names for the principal-character main term agree
definitionally after exposing their respective wrappers. -/
theorem residueMain_eq_characterMain
    {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) :
    residueMain χ x =
      MAPSiegelWalfiszCharacterReduction.characterMain χ x := by
  rfl

/-- Moving the principal main term from `t` to the half-integer immediately
above `floor t` costs at most one half; for nonprincipal characters it costs
zero. -/
theorem norm_residueMain_halfInteger_floor_sub_characterMain_le
    {q : ℕ} (χ : DirichletCharacter ℂ q) {t : ℝ} (ht : 0 ≤ t) :
    ‖residueMain χ (halfIntegerPoint ⌊t⌋₊) -
        MAPSiegelWalfiszCharacterReduction.characterMain χ t‖ ≤ 1 / 2 := by
  classical
  by_cases hχ : χ = 1
  · simp only [residueMain, MAPSiegelWalfiszCharacterReduction.characterMain,
      hχ, if_true]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact abs_halfIntegerPoint_floor_sub_le t ht
  · simp [residueMain, MAPSiegelWalfiszCharacterReduction.characterMain, hχ]

/-- The literal omitted-coefficient integral is termwise the corresponding
Perron kernel tsum.  This exposes the route to the missing sharp outside-tail
estimate; the canonical `norm_coefficientTail_le_vonMangoldt_series` instead
uses an absolute integral bound that grows with `T`. -/
theorem coefficientTail_eq_tsum_kernels
    {q : ℕ} (χ : DirichletCharacter ℂ q) {x c T : ℝ}
    (hx : 0 < x) (S : Finset ℕ) :
    coefficientTail χ x c T S =
      ∑' n : {n // n ∉ S},
        twistedMangoldtCoeff χ n * PerronKernel.kernel (x / n) c T := by
  rw [coefficientTail]
  apply tsum_congr
  intro n
  by_cases hn : (n : ℕ) = 0
  · simp [hn, perronTerm, twistedMangoldtCoeff]
  · exact normalized_integral_perronTerm_eq_coeff_mul_kernel χ hx hn

/-- Ambient-character version of the canonical primitive explicit formula.
The removable-singularity premise has already been discharged by
`PrimitiveRemovableClosure`; only literal nonvanishing of the three shifted
edges remains. -/
theorem ambientTwistedMangoldtPrefix_eq_primitive_explicit_formula
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (N : ℕ)
    {σ c T : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hc : 1 < c) (hT : 0 < T)
    (hleftNonzero : ∀ u ∈ Set.Icc (-T) T,
      regularizedLFunction χ.primitiveCharacter
        ((σ : ℂ) + (u : ℂ) * Complex.I) ≠ 0)
    (hbottomNonzero : ∀ r ∈ Set.Icc σ c,
      regularizedLFunction χ.primitiveCharacter
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0)
    (htopNonzero : ∀ r ∈ Set.Icc σ c,
      regularizedLFunction χ.primitiveCharacter
        ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    APFoundation.twistedMangoldtSum χ (Finset.Icc 1 N) =
      residueMain χ.primitiveCharacter (halfIntegerPoint N) -
        multiplicityWeightedPerronZeroSum χ.primitiveCharacter σ T
          (halfIntegerPoint N) +
      leftLineIntegral χ.primitiveCharacter (halfIntegerPoint N) σ T -
      horizontalBoundaryIntegral χ.primitiveCharacter
        (halfIntegerPoint N) σ c T +
      insideKernelError χ.primitiveCharacter N c T -
      coefficientTail χ.primitiveCharacter
        (halfIntegerPoint N) c T (Finset.Icc 1 N) -
      APFoundation.imprimitiveMangoldtCorrection χ (Finset.Icc 1 N) := by
  have hambient :=
    PrimitiveTruncatedExplicitFormulaBridge.ambientTwistedMangoldtPrefix_eq_primitive_contour_decomposition
      χ N (σ := σ) (c := c) (T := T) hc
  rw [hambient]
  rw [PrimitiveRemovableClosure.normalizedRectangleBoundary_eq_residueMain_sub_zeroSum
    χ.primitiveCharacter (halfIntegerPoint_pos N) hσ0 hσ1 hc hT
    hleftNonzero hbottomNonzero htopNonzero]

/-- Exact triangle-inequality reduction of the target character error to the
five primitive explicit-formula terms, the imprimitive correction, and the
half-integer endpoint discrepancy. -/
theorem norm_twistedMangoldtPrefix_sub_characterMain_le_explicit_terms
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] {t σ c T : ℝ}
    (ht : 0 ≤ t) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hc : 1 < c) (hT : 0 < T)
    (hleftNonzero : ∀ u ∈ Set.Icc (-T) T,
      regularizedLFunction χ.primitiveCharacter
        ((σ : ℂ) + (u : ℂ) * Complex.I) ≠ 0)
    (hbottomNonzero : ∀ r ∈ Set.Icc σ c,
      regularizedLFunction χ.primitiveCharacter
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0)
    (htopNonzero : ∀ r ∈ Set.Icc σ c,
      regularizedLFunction χ.primitiveCharacter
        ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    ‖APFoundation.twistedMangoldtSum χ (Finset.Icc 1 ⌊t⌋₊) -
        MAPSiegelWalfiszCharacterReduction.characterMain χ t‖ ≤
      1 / 2 +
      ‖multiplicityWeightedPerronZeroSum χ.primitiveCharacter σ T
        (halfIntegerPoint ⌊t⌋₊)‖ +
      ‖leftLineIntegral χ.primitiveCharacter
        (halfIntegerPoint ⌊t⌋₊) σ T‖ +
      ‖horizontalBoundaryIntegral χ.primitiveCharacter
        (halfIntegerPoint ⌊t⌋₊) σ c T‖ +
      ‖insideKernelError χ.primitiveCharacter ⌊t⌋₊ c T‖ +
      ‖coefficientTail χ.primitiveCharacter
        (halfIntegerPoint ⌊t⌋₊) c T (Finset.Icc 1 ⌊t⌋₊)‖ +
      ‖APFoundation.imprimitiveMangoldtCorrection χ
        (Finset.Icc 1 ⌊t⌋₊)‖ := by
  let R := residueMain χ.primitiveCharacter (halfIntegerPoint ⌊t⌋₊)
  let Z := multiplicityWeightedPerronZeroSum χ.primitiveCharacter σ T
    (halfIntegerPoint ⌊t⌋₊)
  let L := leftLineIntegral χ.primitiveCharacter
    (halfIntegerPoint ⌊t⌋₊) σ T
  let H := horizontalBoundaryIntegral χ.primitiveCharacter
    (halfIntegerPoint ⌊t⌋₊) σ c T
  let I := insideKernelError χ.primitiveCharacter ⌊t⌋₊ c T
  let E := coefficientTail χ.primitiveCharacter
    (halfIntegerPoint ⌊t⌋₊) c T (Finset.Icc 1 ⌊t⌋₊)
  let Q := APFoundation.imprimitiveMangoldtCorrection χ
    (Finset.Icc 1 ⌊t⌋₊)
  let M := MAPSiegelWalfiszCharacterReduction.characterMain χ t
  have hformula := ambientTwistedMangoldtPrefix_eq_primitive_explicit_formula
    χ ⌊t⌋₊ hσ0 hσ1 hc hT hleftNonzero hbottomNonzero htopNonzero
  have hmainPrimitive :
      residueMain χ.primitiveCharacter (halfIntegerPoint ⌊t⌋₊) =
        residueMain χ (halfIntegerPoint ⌊t⌋₊) :=
    residueMain_primitiveCharacter χ (halfIntegerPoint ⌊t⌋₊)
  have hmain : ‖R - M‖ ≤ 1 / 2 := by
    dsimp only [R, M]
    rw [hmainPrimitive]
    exact norm_residueMain_halfInteger_floor_sub_characterMain_le χ ht
  have hdecomp :
      APFoundation.twistedMangoldtSum χ (Finset.Icc 1 ⌊t⌋₊) - M =
        (R - M) + (-Z + L - H + I - E - Q) := by
    dsimp only [R, Z, L, H, I, E, Q, M]
    rw [hformula]
    ring
  rw [hdecomp]
  calc
    ‖(R - M) + (-Z + L - H + I - E - Q)‖ ≤
        ‖R - M‖ + ‖-Z + L - H + I - E - Q‖ := norm_add_le _ _
    _ ≤ 1 / 2 + ‖-Z + L - H + I - E - Q‖ :=
      add_le_add hmain (le_refl _)
    _ ≤ 1 / 2 +
        (((((‖Z‖ + ‖L‖) + ‖H‖) + ‖I‖) + ‖E‖) + ‖Q‖) := by
      gcongr
      calc
        ‖-Z + L - H + I - E - Q‖ ≤
            ‖-Z + L - H + I - E‖ + ‖Q‖ := norm_sub_le _ _
        _ ≤ (‖-Z + L - H + I‖ + ‖E‖) + ‖Q‖ := by
          gcongr
          exact norm_sub_le _ _
        _ ≤ ((‖-Z + L - H‖ + ‖I‖) + ‖E‖) + ‖Q‖ := by
          gcongr
          exact norm_add_le _ _
        _ ≤ (((‖-Z + L‖ + ‖H‖) + ‖I‖) + ‖E‖) + ‖Q‖ := by
          gcongr
          exact norm_sub_le _ _
        _ ≤ ((((‖-Z‖ + ‖L‖) + ‖H‖) + ‖I‖) + ‖E‖) + ‖Q‖ := by
          gcongr
          exact norm_add_le _ _
        _ = (((((‖Z‖ + ‖L‖) + ‖H‖) + ‖I‖) + ‖E‖) + ‖Q‖) := by
          rw [norm_neg]
    _ = 1 / 2 + ‖Z‖ + ‖L‖ + ‖H‖ + ‖I‖ + ‖E‖ + ‖Q‖ := by ring

/-- All purely Perron and primitive/imprimitive error estimates currently
available in the canonical tree, composed into the target error.  The three
terms left in norm are exactly the zero sum and the two shifted contour
segments. -/
theorem norm_twistedMangoldtPrefix_sub_characterMain_le_canonical_majorant
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] {t σ c T : ℝ}
    (ht : 0 ≤ t) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hc : 1 < c) (hT : 0 < T)
    (hleftNonzero : ∀ u ∈ Set.Icc (-T) T,
      regularizedLFunction χ.primitiveCharacter
        ((σ : ℂ) + (u : ℂ) * Complex.I) ≠ 0)
    (hbottomNonzero : ∀ r ∈ Set.Icc σ c,
      regularizedLFunction χ.primitiveCharacter
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0)
    (htopNonzero : ∀ r ∈ Set.Icc σ c,
      regularizedLFunction χ.primitiveCharacter
        ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    ‖APFoundation.twistedMangoldtSum χ (Finset.Icc 1 ⌊t⌋₊) -
        MAPSiegelWalfiszCharacterReduction.characterMain χ t‖ ≤
      1 / 2 +
      ‖multiplicityWeightedPerronZeroSum χ.primitiveCharacter σ T
        (halfIntegerPoint ⌊t⌋₊)‖ +
      ‖leftLineIntegral χ.primitiveCharacter
        (halfIntegerPoint ⌊t⌋₊) σ T‖ +
      ‖horizontalBoundaryIntegral χ.primitiveCharacter
        (halfIntegerPoint ⌊t⌋₊) σ c T‖ +
      (∑ n ∈ Finset.Icc 1 ⌊t⌋₊,
        ArithmeticFunction.vonMangoldt n *
          ((halfIntegerPoint ⌊t⌋₊ / n) ^ c /
            (Real.pi * T *
              |Real.log (halfIntegerPoint ⌊t⌋₊ / n)|))) +
      ((T / Real.pi) * (halfIntegerPoint ⌊t⌋₊ ^ c / c) *
        ∑' n : {n // n ∉ Finset.Icc 1 ⌊t⌋₊},
          ‖LSeries.term (fun k : ℕ =>
            (ArithmeticFunction.vonMangoldt k : ℂ)) (c : ℂ) n‖) +
      (⌊Real.log (⌊t⌋₊ : ℝ) / Real.log 2⌋₊ : ℝ) * Real.log q := by
  have hbase := norm_twistedMangoldtPrefix_sub_characterMain_le_explicit_terms
    χ ht hσ0 hσ1 hc hT hleftNonzero hbottomNonzero htopNonzero
  have hinside := SharpPerronRemainderBridge.norm_insideKernelError_le_sharp
    χ.primitiveCharacter ⌊t⌋₊ (lt_trans zero_lt_one hc) hT
  have htail := TruncatedTwistedPerron.norm_coefficientTail_le_vonMangoldt_series
    χ.primitiveCharacter (halfIntegerPoint_pos ⌊t⌋₊) hc hT.le
      (Finset.Icc 1 ⌊t⌋₊)
  have hbad := norm_imprimitiveMangoldtCorrection_prefix_le χ ⌊t⌋₊
  exact hbase.trans (by gcongr)

end

end UniformPsiDeterministicBridge

#print axioms UniformPsiDeterministicBridge.residueMain_eq_characterMain
#print axioms UniformPsiDeterministicBridge.norm_residueMain_halfInteger_floor_sub_characterMain_le
#print axioms UniformPsiDeterministicBridge.coefficientTail_eq_tsum_kernels
#print axioms UniformPsiDeterministicBridge.ambientTwistedMangoldtPrefix_eq_primitive_explicit_formula
#print axioms UniformPsiDeterministicBridge.norm_twistedMangoldtPrefix_sub_characterMain_le_explicit_terms
#print axioms UniformPsiDeterministicBridge.norm_twistedMangoldtPrefix_sub_characterMain_le_canonical_majorant
