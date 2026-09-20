import APCorrectedPaperEdgeTail

/-!
# Literal component source for the corrected paper-edge AP tail

The corrected tail is split into its seven exact signed endpoint components.
They remain inside one scale supremum and one finite-family outer integral, so
no unproved measurability of separate uncountable suprema is used.
-/

namespace MAPAPCorrectedPaperEdgeComponentSource

open MeasureTheory Set
open scoped BigOperators ENNReal ArithmeticFunction
open APFoundation APExplicitFormulaMajorantAdapter
open MAPFixedScaleAPZeroRoute MAPEndpointRegularizedZeroPrimitive
open PrimitiveTruncatedExplicitFormulaBridge TruncatedTwistedPerron
open MAPAPCorrectedCommonHeightContract MAPAPCorrectedPaperEdgeTail
open PaperEdgePrimitiveComponents

noncomputable section

variable {q : ℕ} [NeZero q]

/-- Signed residue/main displacement component. -/
def mainDisplacement
    (chi : DirichletCharacter ℂ q) (t : ℝ) : ℂ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact residueMain chi.primitiveCharacter (halfIntegerPoint ⌊t⌋₊) -
    principalCoefficient chi * t

/-- Signed endpoint-zero/Perron-zero mismatch. -/
def zeroMismatch
    (chi : DirichletCharacter ℂ q) (sigma T t : ℝ) : ℂ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact endpointMultiplicityWeightedZeroTerm chi.primitiveCharacter 0 T t -
    multiplicityWeightedPerronZeroSum chi.primitiveCharacter sigma T
      (halfIntegerPoint ⌊t⌋₊)

/-- Signed left-line endpoint component. -/
def leftComponent
    (chi : DirichletCharacter ℂ q) (sigma T t : ℝ) : ℂ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact leftLineIntegral chi.primitiveCharacter
    (halfIntegerPoint ⌊t⌋₊) sigma T

/-- Signed horizontal-pair endpoint component. -/
def horizontalComponent
    (chi : DirichletCharacter ℂ q) (sigma T t : ℝ) : ℂ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact -horizontalBoundaryIntegral chi.primitiveCharacter
    (halfIntegerPoint ⌊t⌋₊) sigma (standardEdge ⌊t⌋₊) T

/-- Signed inside-Perron endpoint component. -/
def insideComponent
    (chi : DirichletCharacter ℂ q) (T t : ℝ) : ℂ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact insideKernelError chi.primitiveCharacter ⌊t⌋₊
    (standardEdge ⌊t⌋₊) T

/-- Signed outside-Perron endpoint component. -/
def outsideComponent
    (chi : DirichletCharacter ℂ q) (T t : ℝ) : ℂ := by
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact -coefficientTail chi.primitiveCharacter
    (halfIntegerPoint ⌊t⌋₊) (standardEdge ⌊t⌋₊) T
    (Finset.Icc 1 ⌊t⌋₊)

/-- Signed imprimitive endpoint component. -/
def imprimitiveComponent
    (chi : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  -imprimitiveMangoldtCorrection chi (Finset.Icc 1 ⌊t⌋₊)

/-- Exact seven-term decomposition of the paper-edge remainder. -/
theorem endpointRemainder_eq_signedComponents
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    (sigma T t : ℝ) :
    endpointRemainder chi sigma T t =
      mainDisplacement chi t + zeroMismatch chi sigma T t +
      leftComponent chi sigma T t + horizontalComponent chi sigma T t +
      insideComponent chi T t + outsideComponent chi T t +
      imprimitiveComponent chi t := by
  simp only [endpointRemainder, mainDisplacement, zeroMismatch,
    leftComponent, horizontalComponent, insideComponent,
    outsideComponent, imprimitiveComponent]
  ring

private theorem norm_add_sq_le_two (a b : ℂ) :
    ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have h := norm_add_le a b
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a + b),
    sq_nonneg (‖a‖ - ‖b‖)]

/-- Seven-term squared triangle inequality with the binary-tree constant 8. -/
theorem norm_seven_sum_sq_le_eight
    (a b c d e f g : ℂ) :
    ‖a + b + c + d + e + f + g‖ ^ 2 ≤
      8 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2 +
        ‖e‖ ^ 2 + ‖f‖ ^ 2 + ‖g‖ ^ 2) := by
  have hab := norm_add_sq_le_two a b
  have hcd := norm_add_sq_le_two c d
  have hef := norm_add_sq_le_two e f
  have habcd := norm_add_sq_le_two (a + b) (c + d)
  have hefg := norm_add_sq_le_two (e + f) g
  have hall := norm_add_sq_le_two ((a + b) + (c + d)) ((e + f) + g)
  have hid : a + b + c + d + e + f + g =
      ((a + b) + (c + d)) + ((e + f) + g) := by ring
  rw [hid]
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg c,
    norm_nonneg d, norm_nonneg e, norm_nonneg f, norm_nonneg g,
    norm_nonneg (a + b), norm_nonneg (c + d), norm_nonneg (e + f),
    norm_nonneg ((a + b) + (c + d)), norm_nonneg ((e + f) + g)]

/-- Literal scale-by-scale component square.  The terms are signed above,
while norms make the three requested analytic leaves visible. -/
def componentWindowSqAtScale
    (chi : DirichletCharacter ℂ q)
    (sigma T x Y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal <| 8 *
    (‖(mainDisplacement chi (x + Y) - mainDisplacement chi x) / Y‖ ^ 2 +
     ‖(zeroMismatch chi sigma T (x + Y) - zeroMismatch chi sigma T x) / Y‖ ^ 2 +
     ‖(leftComponent chi sigma T (x + Y) - leftComponent chi sigma T x) / Y‖ ^ 2 +
     ‖(horizontalComponent chi sigma T (x + Y) - horizontalComponent chi sigma T x) / Y‖ ^ 2 +
     ‖(insideComponent chi T (x + Y) - insideComponent chi T x) / Y‖ ^ 2 +
     ‖(outsideComponent chi T (x + Y) - outsideComponent chi T x) / Y‖ ^ 2 +
     ‖(imprimitiveComponent chi (x + Y) - imprimitiveComponent chi x) / Y‖ ^ 2)

/-- Legal-aperture supremum of the literal seven-component majorant. -/
def componentWindowMaxSq
    (chi : DirichletCharacter ℂ q)
    (sigma T epsilon X x : ℝ) : ℝ≥0∞ :=
  ⨆ (Y : ℝ) (_hYlow : Real.rpow X (2 / 15 + epsilon) ≤ Y)
      (_hYhigh : Y ≤ X),
    componentWindowSqAtScale chi sigma T x Y

/-- The paper-edge remainder maximum is pointwise dominated by the literal
seven-component maximum. -/
theorem paperEdgeRemainderMaxSq_le_componentWindowMaxSq
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    (sigma T epsilon X x : ℝ) :
    paperEdgeRemainderMaxSq chi sigma T epsilon X x ≤
      componentWindowMaxSq chi sigma T epsilon X x := by
  unfold paperEdgeRemainderMaxSq componentWindowMaxSq
  apply iSup_le
  intro Y
  apply iSup_le
  intro hYlow
  apply iSup_le
  intro hYhigh
  refine le_iSup_of_le Y <| le_iSup_of_le hYlow <|
    le_iSup_of_le hYhigh ?_
  rw [← ENNReal.ofReal_pow (norm_nonneg _) 2]
  unfold componentWindowSqAtScale
  apply ENNReal.ofReal_le_ofReal
  let a := (mainDisplacement chi (x + Y) - mainDisplacement chi x) / Y
  let b := (zeroMismatch chi sigma T (x + Y) - zeroMismatch chi sigma T x) / Y
  let c := (leftComponent chi sigma T (x + Y) - leftComponent chi sigma T x) / Y
  let d := (horizontalComponent chi sigma T (x + Y) - horizontalComponent chi sigma T x) / Y
  let e := (insideComponent chi T (x + Y) - insideComponent chi T x) / Y
  let f := (outsideComponent chi T (x + Y) - outsideComponent chi T x) / Y
  let g := (imprimitiveComponent chi (x + Y) - imprimitiveComponent chi x) / Y
  have hdecomp :
      (endpointRemainder chi sigma T (x + Y) -
          endpointRemainder chi sigma T x) / Y =
        a + b + c + d + e + f + g := by
    rw [endpointRemainder_eq_signedComponents,
      endpointRemainder_eq_signedComponents]
    dsimp only [a, b, c, d, e, f, g]
    ring
  rw [hdecomp]
  exact norm_seven_sum_sq_le_eight a b c d e f g

/-- One-integral finite-family component majorant. -/
def familyPaperEdgeComponentMajorant
    (Q : ℕ) (sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ)
    (T epsilon X x : ℝ) : ℝ≥0∞ :=
  ∑ q ∈ Finset.Icc 1 Q,
    if hq : q = 0 then 0 else
      letI : NeZero q := ⟨hq⟩
      (q.totient : ℝ≥0∞)⁻¹ *
        ∑ chi : DirichletCharacter ℂ q,
          componentWindowMaxSq chi (sigma q chi) T epsilon X x

/-- The single remaining source-faithful analytic proposition.  It asks for
one common zero-avoiding height and directly bounds the one-integral family
sum of all literal endpoint/Perron mismatch, left-line, horizontal-pair,
inside/outside Perron, residue, and imprimitive window components. -/
def CorrectedPaperEdgeComponentFamilySquare : Prop :=
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
                familyPaperEdgeComponentMajorant Q sigma T epsilon X x) ≤
              ENNReal.ofReal (C * X * Real.rpow (Real.log X) (-A))

/-- Pointwise finite-family domination, preserving exact character weights. -/
theorem familyPaperEdgeTailMajorant_le_componentMajorant
    (Q : ℕ) (sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ)
    (T epsilon X x : ℝ) :
    familyPaperEdgeTailMajorant Q sigma T epsilon X x ≤
      familyPaperEdgeComponentMajorant Q sigma T epsilon X x := by
  unfold familyPaperEdgeTailMajorant familyPaperEdgeComponentMajorant
  apply Finset.sum_le_sum
  intro q hq
  split_ifs with hq0
  · exact le_rfl
  · letI : NeZero q := ⟨hq0⟩
    gcongr with chi
    letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
    exact paperEdgeRemainderMaxSq_le_componentWindowMaxSq
      chi (sigma q chi) T epsilon X x

/-- The literal component proposition inhabits the corrected paper-edge tail
contract without any exact-height, fixed-`c=3`, or measurability assumption. -/
theorem correctedTailFamilySquare_of_componentFamilySquare
    (hcomponents : CorrectedPaperEdgeComponentFamilySquare) :
    CorrectedAPExplicitFormulaTailFamilySquare := by
  intro K A epsilon hK hA hepsilon hepsilonCap
  rcases hcomponents K A epsilon hK hA hepsilon hepsilonCap with
    ⟨C, X0, hC, hX0, hX⟩
  refine ⟨C, X0, hC, hX0, ?_⟩
  intro X hXX0
  have hAtX := hX X hXX0
  dsimp only at hAtX
  rcases hAtX with ⟨T, hT, sigma, hlegal, hbound⟩
  refine ⟨T, hT, sigma, hlegal, ?_⟩
  exact (setLIntegral_mono' measurableSet_Icc fun x hx =>
    familyPaperEdgeTailMajorant_le_componentMajorant
      _ _ _ _ _ _).trans hbound

end
end MAPAPCorrectedPaperEdgeComponentSource

#print axioms MAPAPCorrectedPaperEdgeComponentSource.endpointRemainder_eq_signedComponents
#print axioms MAPAPCorrectedPaperEdgeComponentSource.norm_seven_sum_sq_le_eight
#print axioms MAPAPCorrectedPaperEdgeComponentSource.paperEdgeRemainderMaxSq_le_componentWindowMaxSq
#print axioms MAPAPCorrectedPaperEdgeComponentSource.familyPaperEdgeTailMajorant_le_componentMajorant
#print axioms MAPAPCorrectedPaperEdgeComponentSource.correctedTailFamilySquare_of_componentFamilySquare
