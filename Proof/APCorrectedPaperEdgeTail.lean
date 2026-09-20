import APCorrectedCommonHeightContract
import EndpointPerronZeroMismatch

/-!
# Corrected common-height paper-edge AP tail

The former source contract prescribed one exact height and the fixed right
edge `c=3`.  It is retained only as a rejected diagnostic.  The definitions
below use one height selected in `(H,H+1)` for the whole finite character
family and the manuscript's paper edge `1+1/log(n+1/2)`.

The finite `q,chi` sum remains inside one outer integral.  Thus no
measurability claim for the uncountable real-`Y` supremum is needed.
-/

namespace MAPAPCorrectedPaperEdgeTail

open MeasureTheory Set
open scoped BigOperators ENNReal
open APFoundation APExplicitFormulaMajorantAdapter
open MAPFixedScaleAPZeroRoute
open MAPEndpointRegularizedZeroPrimitive
open PrimitiveTruncatedExplicitFormulaBridge
open MAPAPCorrectedCommonHeightContract
open PaperEdgePrimitiveComponents

noncomputable section

variable {q : ℕ} [NeZero q]

/-- Legal-aperture maximal square of the paper-edge endpoint remainder. -/
def paperEdgeRemainderMaxSq
    (chi : DirichletCharacter ℂ q)
    (sigma T epsilon X x : ℝ) : ℝ≥0∞ :=
  ⨆ (Y : ℝ) (_hYlow : Real.rpow X (2 / 15 + epsilon) ≤ Y)
      (_hYhigh : Y ≤ X),
    ENNReal.ofReal
      ‖(endpointRemainder chi sigma T (x + Y) -
          endpointRemainder chi sigma T x) / Y‖ ^ 2

/-- One-integral finite-family paper-edge tail majorant. -/
def familyPaperEdgeTailMajorant
    (Q : ℕ) (sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ)
    (T epsilon X x : ℝ) : ℝ≥0∞ :=
  ∑ q ∈ Finset.Icc 1 Q,
    if hq : q = 0 then 0 else
      letI : NeZero q := ⟨hq⟩
      (q.totient : ℝ≥0∞)⁻¹ *
        ∑ chi : DirichletCharacter ℂ q,
          paperEdgeRemainderMaxSq chi (sigma q chi) T epsilon X x

/-- The corrected source target.  Quantifiers encode one common height for
all ambient characters; left edges may depend on the character. -/
def CorrectedAPExplicitFormulaTailFamilySquare : Prop :=
  ∀ K A epsilon : ℝ,
    0 < K → 0 < A → 0 < epsilon → epsilon ≤ 13 / 30 →
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
      ∀ X : ℝ, X0 ≤ X →
        let reserve := min epsilon (1 / 10)
        let H := apZeroHeight reserve X
        let Q := ⌊Real.rpow (Real.log X) K⌋₊
        ∃ T ∈ Set.Ioo H (H + 1),
          ∃ sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ,
            (∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
                (chi : DirichletCharacter ℂ q),
              @paperEdgeContourLegal q
                ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
                chi (sigma q chi) T) ∧
            (∫⁻ x in Set.Icc (X / 2) (4 * X),
                familyPaperEdgeTailMajorant Q sigma T epsilon X x) ≤
              ENNReal.ofReal (C * X * Real.rpow (Real.log X) (-A))

/-- The common-height contour gives the exact paper-edge endpoint formula
at any endpoint whose half-integer floor is nonzero. -/
theorem ambientTwistedPsi_eq_principal_sub_endpoint_add_paperEdgeRemainder
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    {sigma T t : ℝ}
    (hlegal : paperEdgeContourLegal chi sigma T)
    (hN : 1 ≤ ⌊t⌋₊) :
    ambientTwistedPsi chi t =
      principalCoefficient chi * t -
        endpointMultiplicityWeightedZeroTerm
          chi.primitiveCharacter 0 T t +
        endpointRemainder chi sigma T t := by
  have hc : 1 ≤ standardEdge ⌊t⌋₊ :=
    (standardEdge_gt_one ⌊t⌋₊ hN).le
  obtain ⟨hbottom, htop⟩ := hlegal.horizontal_nonzero hc
  exact ambientTwistedPsi_eq_principal_sub_endpoint_add_remainder
    chi hN hlegal.2.1.1 (by linarith [hlegal.2.1.2]) hlegal.1
      hlegal.2.2.1 hbottom htop

/-- Paper-edge analogue of the former fixed-`c=3` character-window bridge.
This is the exact deterministic input needed by character Cauchy. -/
theorem norm_ambientCharacterWindowError_div_le_primitiveField_add_paperEdgeTail
    (chi : DirichletCharacter ℂ q) {sigma T x Y : ℝ}
    (hlegal : paperEdgeContourLegal chi sigma T)
    (hx : 0 < x) (hY : 0 < Y)
    (hNx : 1 ≤ ⌊x⌋₊) (hNxY : 1 ≤ ⌊x + Y⌋₊) :
    ‖APMaximalExplicitFormulaBridge.ambientCharacterWindowError chi
        (Finset.Ioc ⌊x⌋₊ ⌊x + Y⌋₊) Y / Y‖ ≤
      Y⁻¹ * (∫ t : ℝ in x..x + Y,
        ‖primitiveActualZeroField chi T t‖) +
      ‖(endpointRemainder chi sigma T (x + Y) -
          endpointRemainder chi sigma T x) / Y‖ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hformula : ∀ t ∈ ({x, x + Y} : Set ℝ),
      ambientTwistedPsi chi t =
        principalCoefficient chi * t -
          endpointFiniteZeroPrimitive
            (DirichletZeros.zeroSupport chi.primitiveCharacter 0 T)
            (DirichletZeros.zeroMultiplicity chi.primitiveCharacter 0 T) t +
          endpointRemainder chi sigma T t := by
    intro t ht
    rcases ht with rfl | rfl
    · simpa only [endpointMultiplicityWeightedZeroTerm] using
        ambientTwistedPsi_eq_principal_sub_endpoint_add_paperEdgeRemainder
          chi hlegal hNx
    · simpa only [endpointMultiplicityWeightedZeroTerm] using
        ambientTwistedPsi_eq_principal_sub_endpoint_add_paperEdgeRemainder
          chi hlegal hNxY
  simpa only [primitiveActualZeroField, actualZeroField] using
    norm_ambientCharacterWindowError_div_le_endpoint_fieldAverage_add_remainder
      chi (DirichletZeros.zeroSupport chi.primitiveCharacter 0 T)
      (DirichletZeros.zeroMultiplicity chi.primitiveCharacter 0 T)
      (fun rho hrho => actualZero_re_nonneg chi.primitiveCharacter hrho)
      (endpointRemainder chi sigma T) hx hY hformula

end
end MAPAPCorrectedPaperEdgeTail

#print axioms MAPAPCorrectedPaperEdgeTail.ambientTwistedPsi_eq_principal_sub_endpoint_add_paperEdgeRemainder
#print axioms MAPAPCorrectedPaperEdgeTail.norm_ambientCharacterWindowError_div_le_primitiveField_add_paperEdgeTail
