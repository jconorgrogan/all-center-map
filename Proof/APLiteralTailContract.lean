import EndpointRegularizedZeroPrimitive
import SharpOutsidePerronTail

/-!
# Literal AP explicit-formula tail contract

This file makes the one remaining remainder source inspectable term by term.
The outside Perron tail is not reproved: it is discharged by
`SharpOutsidePerronTail.norm_coefficientTail_le_sharp_outside_global`.
-/

namespace MAPAPLiteralTailContract

open MeasureTheory Set
open scoped BigOperators ENNReal ArithmeticFunction
open APFoundation APExplicitFormulaMajorantAdapter
open MAPEndpointRegularizedZeroPrimitive
open PrimitiveTruncatedExplicitFormulaBridge

noncomputable section

variable {q : ℕ} [NeZero q]

/-- The exact endpoint remainder obtained by adding and subtracting the full
closed-rectangle endpoint primitive around the promoted primitive Perron
formula.  Every term is literal. -/
def literalEndpointRemainder
    (chi : DirichletCharacter ℂ q) (sigma T t : ℝ) : ℂ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let N := ⌊t⌋₊
  let u := halfIntegerPoint N
  exact
    residueMain chi.primitiveCharacter u - principalCoefficient chi * t +
      endpointMultiplicityWeightedZeroTerm chi.primitiveCharacter 0 T t -
      multiplicityWeightedPerronZeroSum chi.primitiveCharacter sigma T u +
      leftLineIntegral chi.primitiveCharacter u sigma T -
      horizontalBoundaryIntegral chi.primitiveCharacter u sigma 3 T +
      insideKernelError chi.primitiveCharacter N 3 T -
      TruncatedTwistedPerron.coefficientTail chi.primitiveCharacter u 3 T
        (Finset.Icc 1 N) -
      imprimitiveMangoldtCorrection chi (Finset.Icc 1 N)

/-- Exact real-endpoint formula with the full endpoint-corrected zero
primitive and the literal tail above. -/
theorem ambientTwistedPsi_eq_principal_sub_endpoint_add_literalRemainder
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    {sigma T t : ℝ}
    (ht : 0 ≤ t) (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hT : 0 < T)
    (hleftNonzero : ∀ u ∈ Set.Icc (-T) T,
      DirichletZeros.regularizedLFunction chi.primitiveCharacter
        ((sigma : ℂ) + (u : ℂ) * Complex.I) ≠ 0)
    (hbottomNonzero : ∀ r ∈ Set.Icc sigma 3,
      DirichletZeros.regularizedLFunction chi.primitiveCharacter
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0)
    (htopNonzero : ∀ r ∈ Set.Icc sigma 3,
      DirichletZeros.regularizedLFunction chi.primitiveCharacter
        ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    ambientTwistedPsi chi t =
      principalCoefficient chi * t -
        endpointMultiplicityWeightedZeroTerm chi.primitiveCharacter 0 T t +
          literalEndpointRemainder chi sigma T t := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hformula :=
    UniformPsiDeterministicBridge.ambientTwistedMangoldtPrefix_eq_primitive_explicit_formula
      chi ⌊t⌋₊ hsigma0 hsigma1 (by norm_num : (1 : ℝ) < 3) hT
      hleftNonzero hbottomNonzero htopNonzero
  unfold ambientTwistedPsi
  rw [hformula]
  simp only [literalEndpointRemainder]
  ring

/-- Sharp inside Perron majorant at the fixed legal right edge `c=3`. -/
def insidePerronMajorant (N : ℕ) (T : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    ArithmeticFunction.vonMangoldt n *
      ((halfIntegerPoint N / n) ^ (3 : ℝ) /
        (Real.pi * T * |Real.log (halfIntegerPoint N / n)|))

/-- Sharp outside Perron majorant, reusing the certified global scalar
series. -/
def outsidePerronMajorant (N : ℕ) (T : ℝ) : ℝ :=
  (2 * halfIntegerPoint N ^ (3 : ℕ) / (Real.pi * T)) *
    ∑' n : ℕ,
      ‖LSeries.term (fun k : ℕ =>
        (ArithmeticFunction.vonMangoldt k : ℂ)) (2 : ℂ) n‖

/-- Pointwise literal tail majorant.  Only the zero-mismatch and the two
shifted contour norms remain unevaluated; inside, outside and imprimitive
terms already use their certified quantitative bounds. -/
def literalEndpointRemainderMajorant
    (chi : DirichletCharacter ℂ q) (sigma T t : ℝ) : ℝ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let N := ⌊t⌋₊
  let u := halfIntegerPoint N
  exact 1 / 2 +
    ‖endpointMultiplicityWeightedZeroTerm chi.primitiveCharacter 0 T t -
      multiplicityWeightedPerronZeroSum chi.primitiveCharacter sigma T u‖ +
    ‖leftLineIntegral chi.primitiveCharacter u sigma T‖ +
    ‖horizontalBoundaryIntegral chi.primitiveCharacter u sigma 3 T‖ +
    insidePerronMajorant N T + outsidePerronMajorant N T +
    (⌊Real.log (N : ℝ) / Real.log 2⌋₊ : ℝ) * Real.log q

/-- All deterministic pointwise tail estimates, including the reused sharp
outside Perron theorem, welded into the literal remainder. -/
theorem norm_literalEndpointRemainder_le_majorant
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    {sigma T t : ℝ}
    (ht : 0 ≤ t) (hT : 0 < T) :
    ‖literalEndpointRemainder chi sigma T t‖ ≤
      literalEndpointRemainderMajorant chi sigma T t := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let N := ⌊t⌋₊
  let u := halfIntegerPoint N
  let M := residueMain chi.primitiveCharacter u - principalCoefficient chi * t
  let Z := endpointMultiplicityWeightedZeroTerm chi.primitiveCharacter 0 T t -
    multiplicityWeightedPerronZeroSum chi.primitiveCharacter sigma T u
  let L := leftLineIntegral chi.primitiveCharacter u sigma T
  let H := horizontalBoundaryIntegral chi.primitiveCharacter u sigma 3 T
  let I := insideKernelError chi.primitiveCharacter N 3 T
  let E := TruncatedTwistedPerron.coefficientTail chi.primitiveCharacter u 3 T
    (Finset.Icc 1 N)
  let Q := imprimitiveMangoldtCorrection chi (Finset.Icc 1 N)
  have hmain : ‖M‖ ≤ 1 / 2 := by
    dsimp only [M, u, N]
    rw [residueMain_primitiveCharacter chi]
    by_cases hchi : chi = 1
    · simp only [residueMain, principalCoefficient, hchi, if_true]
      rw [one_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact abs_halfIntegerPoint_floor_sub_le t ht
    · simp [residueMain, principalCoefficient, hchi]
  have hinside : ‖I‖ ≤ insidePerronMajorant N T := by
    exact SharpPerronRemainderBridge.norm_insideKernelError_le_sharp
      chi.primitiveCharacter N (by norm_num : (0 : ℝ) < 3) hT
  have houtside : ‖E‖ ≤ outsidePerronMajorant N T := by
    exact SharpOutsidePerronTail.norm_coefficientTail_le_sharp_outside_global
      chi.primitiveCharacter N hT
  have himprimitive : ‖Q‖ ≤
      (⌊Real.log (N : ℝ) / Real.log 2⌋₊ : ℝ) * Real.log q := by
    exact norm_imprimitiveMangoldtCorrection_prefix_le chi N
  have hsplit : literalEndpointRemainder chi sigma T t =
      M + Z + L - H + I - E - Q := by
    simp only [literalEndpointRemainder, M, Z, L, H, I, E, Q, N, u]
    ring
  rw [hsplit]
  dsimp only [literalEndpointRemainderMajorant, N, u]
  calc
    ‖M + Z + L - H + I - E - Q‖ ≤
        ‖M‖ + ‖Z‖ + ‖L‖ + ‖H‖ + ‖I‖ + ‖E‖ + ‖Q‖ := by
      calc
        ‖M + Z + L - H + I - E - Q‖ ≤
            ‖M + Z + L - H + I - E‖ + ‖Q‖ := norm_sub_le _ _
        _ ≤ (‖M + Z + L - H + I‖ + ‖E‖) + ‖Q‖ := by gcongr; exact norm_sub_le _ _
        _ ≤ ((‖M + Z + L - H‖ + ‖I‖) + ‖E‖) + ‖Q‖ := by gcongr; exact norm_add_le _ _
        _ ≤ (((‖M + Z + L‖ + ‖H‖) + ‖I‖) + ‖E‖) + ‖Q‖ := by gcongr; exact norm_sub_le _ _
        _ ≤ ((((‖M + Z‖ + ‖L‖) + ‖H‖) + ‖I‖) + ‖E‖) + ‖Q‖ := by gcongr; exact norm_add_le _ _
        _ ≤ (((((‖M‖ + ‖Z‖) + ‖L‖) + ‖H‖) + ‖I‖) + ‖E‖) + ‖Q‖ := by gcongr; exact norm_add_le _ _
        _ = ‖M‖ + ‖Z‖ + ‖L‖ + ‖H‖ + ‖I‖ + ‖E‖ + ‖Q‖ := by ring
    _ ≤ 1 / 2 + ‖Z‖ + ‖L‖ + ‖H‖ +
          insidePerronMajorant N T + outsidePerronMajorant N T +
          (⌊Real.log (N : ℝ) / Real.log 2⌋₊ : ℝ) * Real.log q := by
      gcongr

/-! ## The exact remaining family-square source -/

/-- Supremal normalized literal remainder difference for one ambient
character. -/
def literalRemainderMaxSq
    (chi : DirichletCharacter ℂ q) (sigma T epsilon X x : ℝ) : ℝ≥0∞ :=
  ⨆ (Y : ℝ) (_hYlow : Real.rpow X (2 / 15 + epsilon) ≤ Y)
      (_hYhigh : Y ≤ X),
    ENNReal.ofReal
      ‖(literalEndpointRemainder chi sigma T (x + Y) -
          literalEndpointRemainder chi sigma T x) / Y‖ ^ 2

/-- Literal zero-avoiding rectangle conditions for one primitive inducer. -/
def primitiveContourLegal (chi : DirichletCharacter ℂ q)
    (sigma T : ℝ) : Prop := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact 0 < T ∧ 0 < sigma ∧ sigma < 1 ∧
    (∀ u ∈ Set.Icc (-T) T,
      DirichletZeros.regularizedLFunction chi.primitiveCharacter
        ((sigma : ℂ) + (u : ℂ) * Complex.I) ≠ 0) ∧
    (∀ r ∈ Set.Icc sigma 3,
      DirichletZeros.regularizedLFunction chi.primitiveCharacter
        ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0) ∧
    (∀ r ∈ Set.Icc sigma 3,
      DirichletZeros.regularizedLFunction chi.primitiveCharacter
        ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0)

/-- Exact pointwise character-window majorant from the literal tail.  This is
the final deterministic bridge before character Cauchy, the `Y` supremum and
family integration. -/
theorem norm_ambientCharacterWindowError_div_le_primitiveField_add_literalTail
    (chi : DirichletCharacter ℂ q) {sigma T x Y : ℝ}
    (hlegal : primitiveContourLegal chi sigma T)
    (hx : 0 < x) (hY : 0 < Y) :
    ‖APMaximalExplicitFormulaBridge.ambientCharacterWindowError chi
        (Finset.Ioc ⌊x⌋₊ ⌊x + Y⌋₊) Y / Y‖ ≤
      Y⁻¹ * (∫ t : ℝ in x..x + Y,
        ‖MAPFixedScaleAPZeroRoute.primitiveActualZeroField chi T t‖) +
      ‖(literalEndpointRemainder chi sigma T (x + Y) -
          literalEndpointRemainder chi sigma T x) / Y‖ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  rcases hlegal with
    ⟨hT, hsigma0, hsigma1, hleft, hbottom, htop⟩
  have hformula : ∀ t ∈ ({x, x + Y} : Set ℝ),
      ambientTwistedPsi chi t =
        principalCoefficient chi * t -
          endpointFiniteZeroPrimitive
            (DirichletZeros.zeroSupport chi.primitiveCharacter 0 T)
            (DirichletZeros.zeroMultiplicity chi.primitiveCharacter 0 T) t +
          literalEndpointRemainder chi sigma T t := by
    intro t ht
    have ht0 : 0 ≤ t := by
      rcases ht with rfl | rfl
      · exact hx.le
      · linarith
    simpa only [endpointMultiplicityWeightedZeroTerm] using
      ambientTwistedPsi_eq_principal_sub_endpoint_add_literalRemainder
        chi ht0 hsigma0 hsigma1 hT hleft hbottom htop
  simpa only [MAPFixedScaleAPZeroRoute.primitiveActualZeroField,
    actualZeroField] using
    norm_ambientCharacterWindowError_div_le_endpoint_fieldAverage_add_remainder
      chi (DirichletZeros.zeroSupport chi.primitiveCharacter 0 T)
      (DirichletZeros.zeroMultiplicity chi.primitiveCharacter 0 T)
      (fun rho hrho => actualZero_re_nonneg chi.primitiveCharacter hrho)
      (literalEndpointRemainder chi sigma T) hx hY hformula

/-- The smallest remaining family-square tail contract.  It exposes a legal
zero-avoiding contour for each primitive inducer and asks only for the L2
mass of the literal remainder difference.  No zero-field energy and no
zero-density saving is included.

The finite `q,chi` family is deliberately placed inside one outer integral.
The rejected earlier staging signature used a sum of separate integrals; it
would require a still-unproved measurability theorem for the uncountable
`Y : ℝ` supremum in `literalRemainderMaxSq`, so it is not asserted equivalent
to this source-faithful total-family formulation. -/
def APExplicitFormulaTailFamilySquare : Prop :=
  ∀ K A epsilon : ℝ,
    0 < K → 0 < A → 0 < epsilon → epsilon ≤ 13 / 30 →
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
      ∀ X : ℝ, X0 ≤ X →
        let reserve := min epsilon (1 / 10)
        let T := MAPFixedScaleAPZeroRoute.apZeroHeight reserve X
        let Q := ⌊Real.rpow (Real.log X) K⌋₊
        ∃ sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ,
          (∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
              (chi : DirichletCharacter ℂ q),
            @primitiveContourLegal q
              ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩ chi
              (sigma q chi) T) ∧
          (∫⁻ x in Set.Icc (X / 2) (4 * X),
            ∑ q ∈ Finset.Icc 1 Q,
              if hq : q = 0 then 0 else
                letI : NeZero q := ⟨hq⟩
                (q.totient : ℝ≥0∞)⁻¹ *
                  ∑ chi : DirichletCharacter ℂ q,
                    literalRemainderMaxSq chi (sigma q chi) T epsilon X x) ≤
            ENNReal.ofReal (C * X * Real.rpow (Real.log X) (-A))

end
end MAPAPLiteralTailContract

#print axioms MAPAPLiteralTailContract.ambientTwistedPsi_eq_principal_sub_endpoint_add_literalRemainder
#print axioms MAPAPLiteralTailContract.norm_literalEndpointRemainder_le_majorant
#print axioms MAPAPLiteralTailContract.norm_ambientCharacterWindowError_div_le_primitiveField_add_literalTail
