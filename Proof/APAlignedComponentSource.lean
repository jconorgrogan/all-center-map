import APAlignedTailToRemainderTransfer
import APCorrectedPaperEdgeComponentSource

/-!
# Six-component source for the aligned AP endpoint tail

Half-integer alignment removes the endpoint/Perron-zero mismatch component.
The release-path remainder is exactly the sum of residue displacement, left
line, horizontal pair, inside Perron, outside Perron, and imprimitive terms.
-/

namespace MAPAPAlignedComponentSource

open MeasureTheory Set
open scoped BigOperators ENNReal
open APFoundation MAPFixedScaleAPZeroRoute MAPAPHalfIntegerAlignedTail
open MAPAPAlignedTailToRemainderTransfer MAPAPCorrectedCommonHeightContract
open MAPAPCorrectedPaperEdgeComponentSource
open MAPBadEulerFactorMass

noncomputable section

variable {q : ℕ} [NeZero q]

/-- Exact six-term aligned remainder decomposition. -/
theorem alignedEndpointRemainder_eq_signedComponents
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    (sigma T t : ℝ) :
    alignedEndpointRemainder chi sigma T t =
      mainDisplacement chi t + leftComponent chi sigma T t +
      horizontalComponent chi sigma T t + insideComponent chi T t +
      outsideComponent chi T t + imprimitiveComponent chi t := by
  simp only [alignedEndpointRemainder, mainDisplacement, leftComponent,
    horizontalComponent, insideComponent, outsideComponent,
    imprimitiveComponent]
  ring

/-- The principal residue displacement at each aligned endpoint is at most
one half; it vanishes for nonprincipal characters. -/
theorem norm_mainDisplacement_le_half
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    {t : ℝ} (ht : 0 ≤ t) :
    ‖mainDisplacement chi t‖ ≤ 1 / 2 := by
  rw [show mainDisplacement chi t =
      PrimitiveTruncatedExplicitFormulaBridge.residueMain
          chi.primitiveCharacter
            (PrimitiveTruncatedExplicitFormulaBridge.halfIntegerPoint ⌊t⌋₊) -
        APExplicitFormulaMajorantAdapter.principalCoefficient chi * t by rfl]
  rw [PrimitiveTruncatedExplicitFormulaBridge.residueMain_primitiveCharacter chi]
  by_cases hchi : chi = 1
  · simp only [PrimitiveTruncatedExplicitFormulaBridge.residueMain,
      APExplicitFormulaMajorantAdapter.principalCoefficient, hchi, if_true]
    rw [one_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact PrimitiveTruncatedExplicitFormulaBridge.abs_halfIntegerPoint_floor_sub_le t ht
  · simp [PrimitiveTruncatedExplicitFormulaBridge.residueMain,
      APExplicitFormulaMajorantAdapter.principalCoefficient, hchi]

/-- Across a legal nonnegative window, the total principal displacement is at
most one. -/
theorem norm_mainDisplacement_window_le_one
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    {x Y : ℝ} (hx : 0 ≤ x) (hY : 0 ≤ Y) :
    ‖mainDisplacement chi (x + Y) - mainDisplacement chi x‖ ≤ 1 := by
  calc
    ‖mainDisplacement chi (x + Y) - mainDisplacement chi x‖ ≤
        ‖mainDisplacement chi (x + Y)‖ + ‖mainDisplacement chi x‖ :=
      norm_sub_le _ _
    _ ≤ 1 / 2 + 1 / 2 := by
      exact add_le_add
        (norm_mainDisplacement_le_half chi (by linarith))
        (norm_mainDisplacement_le_half chi hx)
    _ = 1 := by norm_num

/-- Normalized principal displacement contributes at most `1/Y`. -/
theorem norm_mainDisplacement_window_div_le_inv
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    {x Y : ℝ} (hx : 0 ≤ x) (hY : 0 < Y) :
    ‖(mainDisplacement chi (x + Y) - mainDisplacement chi x) / Y‖ ≤ Y⁻¹ := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY,
    div_eq_mul_inv]
  simpa [mul_comm] using mul_le_mul_of_nonneg_right
    (norm_mainDisplacement_window_le_one chi hx hY.le) (inv_nonneg.mpr hY.le)

/-- Exact prefix-to-window identity for the missing Euler factors. -/
theorem imprimitiveCorrection_prefix_sub_eq_window
    (chi : DirichletCharacter ℂ q) {m N : ℕ} (hmN : m ≤ N) :
    imprimitiveMangoldtCorrection chi (Finset.Icc 1 N) -
        imprimitiveMangoldtCorrection chi (Finset.Icc 1 m) =
      imprimitiveMangoldtCorrection chi (Finset.Ioc m N) := by
  classical
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  let f : ℕ → ℂ := fun n => chi.primitiveCharacter n *
    (ArithmeticFunction.vonMangoldt n : ℂ)
  let A := (Finset.Icc 1 m).filter (fun n => ¬ n.Coprime q)
  let B := (Finset.Icc 1 N).filter (fun n => ¬ n.Coprime q)
  have hsub : A ⊆ B := by
    intro n hn
    simp only [A, B, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨⟨hn.1.1, hn.1.2.trans hmN⟩, hn.2⟩
  have hdiff : B \ A =
      (Finset.Ioc m N).filter (fun n => ¬ n.Coprime q) := by
    ext n
    simp only [A, B, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_Icc, Finset.mem_Ioc]
    omega
  unfold imprimitiveMangoldtCorrection
  change (∑ n ∈ B, f n) - (∑ n ∈ A, f n) =
    ∑ n ∈ (Finset.Ioc m N).filter (fun n => ¬ n.Coprime q), f n
  rw [← Finset.sum_sdiff_eq_sub hsub, hdiff]

/-- The imprimitive aligned component is exactly one missing-factor interval,
not the sum of two endpoint errors. -/
theorem norm_imprimitiveComponent_window_le
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    {x Y : ℝ} (hY : 0 ≤ Y) :
    ‖imprimitiveComponent chi (x + Y) - imprimitiveComponent chi x‖ ≤
      (⌊Real.log (⌊x + Y⌋₊ : ℝ) / Real.log 2⌋₊ : ℝ) * Real.log q := by
  have hfloor : ⌊x⌋₊ ≤ ⌊x + Y⌋₊ := Nat.floor_mono (by linarith)
  have hid := imprimitiveCorrection_prefix_sub_eq_window chi hfloor
  have hcomp : imprimitiveComponent chi (x + Y) -
      imprimitiveComponent chi x =
      -imprimitiveMangoldtCorrection chi (Finset.Ioc ⌊x⌋₊ ⌊x + Y⌋₊) := by
    simp only [imprimitiveComponent]
    rw [← hid]
    ring
  rw [hcomp, norm_neg]
  exact norm_imprimitiveMangoldtCorrection_Ioc_le chi ⌊x⌋₊ ⌊x + Y⌋₊

/-- Six-term squared triangle inequality. -/
theorem norm_six_sum_sq_le_eight
    (a b c d e f : ℂ) :
    ‖a + b + c + d + e + f‖ ^ 2 ≤
      8 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2 +
        ‖e‖ ^ 2 + ‖f‖ ^ 2) := by
  have h := norm_seven_sum_sq_le_eight a b c d e f 0
  simpa only [add_zero, norm_zero, pow_two, zero_mul] using h

/-- Literal aligned six-component square at one legal aperture. -/
def alignedComponentWindowSqAtScale
    (chi : DirichletCharacter ℂ q)
    (sigma T x Y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal <| 8 *
    (‖(mainDisplacement chi (x + Y) - mainDisplacement chi x) / Y‖ ^ 2 +
     ‖(leftComponent chi sigma T (x + Y) - leftComponent chi sigma T x) / Y‖ ^ 2 +
     ‖(horizontalComponent chi sigma T (x + Y) - horizontalComponent chi sigma T x) / Y‖ ^ 2 +
     ‖(insideComponent chi T (x + Y) - insideComponent chi T x) / Y‖ ^ 2 +
     ‖(outsideComponent chi T (x + Y) - outsideComponent chi T x) / Y‖ ^ 2 +
     ‖(imprimitiveComponent chi (x + Y) - imprimitiveComponent chi x) / Y‖ ^ 2)

def alignedComponentWindowMaxSq
    (chi : DirichletCharacter ℂ q)
    (sigma T epsilon X x : ℝ) : ℝ≥0∞ :=
  ⨆ (Y : ℝ) (_hYlow : Real.rpow X (2 / 15 + epsilon) ≤ Y)
      (_hYhigh : Y ≤ X),
    alignedComponentWindowSqAtScale chi sigma T x Y

/-- The aligned endpoint tail is pointwise dominated by the six literal
components; the formerly fatal zero-mismatch component is absent. -/
theorem alignedRemainderMaxSq_le_componentWindowMaxSq
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    (sigma T epsilon X x : ℝ) :
    alignedRemainderMaxSq chi sigma T epsilon X x ≤
      alignedComponentWindowMaxSq chi sigma T epsilon X x := by
  unfold alignedRemainderMaxSq alignedComponentWindowMaxSq
  apply iSup_le
  intro Y
  apply iSup_le
  intro hYlow
  apply iSup_le
  intro hYhigh
  refine le_iSup_of_le Y <| le_iSup_of_le hYlow <|
    le_iSup_of_le hYhigh ?_
  rw [← ENNReal.ofReal_pow (norm_nonneg _) 2]
  unfold alignedComponentWindowSqAtScale
  apply ENNReal.ofReal_le_ofReal
  let a := (mainDisplacement chi (x + Y) - mainDisplacement chi x) / Y
  let b := (leftComponent chi sigma T (x + Y) - leftComponent chi sigma T x) / Y
  let c := (horizontalComponent chi sigma T (x + Y) - horizontalComponent chi sigma T x) / Y
  let d := (insideComponent chi T (x + Y) - insideComponent chi T x) / Y
  let e := (outsideComponent chi T (x + Y) - outsideComponent chi T x) / Y
  let f := (imprimitiveComponent chi (x + Y) - imprimitiveComponent chi x) / Y
  have hdecomp :
      (alignedEndpointRemainder chi sigma T (x + Y) -
          alignedEndpointRemainder chi sigma T x) / Y =
        a + b + c + d + e + f := by
    rw [alignedEndpointRemainder_eq_signedComponents,
      alignedEndpointRemainder_eq_signedComponents]
    dsimp only [a, b, c, d, e, f]
    ring
  rw [hdecomp]
  exact norm_six_sum_sq_le_eight a b c d e f

/-- One-integral finite-family aligned component majorant. -/
def familyAlignedComponentMajorant
    (Q : ℕ) (sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ)
    (T epsilon X x : ℝ) : ℝ≥0∞ :=
  ∑ q ∈ Finset.Icc 1 Q,
    if hq : q = 0 then 0 else
      letI : NeZero q := ⟨hq⟩
      (q.totient : ℝ≥0∞)⁻¹ *
        ∑ chi : DirichletCharacter ℂ q,
          alignedComponentWindowMaxSq chi (sigma q chi) T epsilon X x

/-- Exact first analytic proposition after all deterministic AP bookkeeping.
It contains six literal contour/Perron families and no zero-field mismatch. -/
def AlignedComponentFamilySquare : Prop :=
  ∀ K A epsilon : ℝ,
    0 < K → 0 < A → 0 < epsilon → epsilon ≤ 13 / 30 →
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
      ∀ X : ℝ, X0 ≤ X →
        let reserve := min epsilon (1 / 10)
        let H0 := apZeroHeight reserve X
        let Q := ⌊Real.rpow (Real.log X) K⌋₊
        ∃ T ∈ Set.Ioo H0 (H0 + 1),
          ∃ sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ,
            (∀ (q : ℕ) (hq : q ∈ Finset.Icc 1 Q)
                (chi : DirichletCharacter ℂ q),
              @paperEdgeContourLegal q
                ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
                chi (sigma q chi) T) ∧
            (∫⁻ x in Set.Icc (X / 2) (4 * X),
                familyAlignedComponentMajorant Q sigma T epsilon X x) ≤
              ENNReal.ofReal (C * X * Real.rpow (Real.log X) (-A))

theorem familyAlignedTailMajorant_le_componentMajorant
    (Q : ℕ) (sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ)
    (T epsilon X x : ℝ) :
    familyAlignedTailMajorant Q sigma T epsilon X x ≤
      familyAlignedComponentMajorant Q sigma T epsilon X x := by
  unfold familyAlignedTailMajorant familyAlignedComponentMajorant
  apply Finset.sum_le_sum
  intro q hq
  split_ifs with hq0
  · exact le_rfl
  · letI : NeZero q := ⟨hq0⟩
    gcongr with chi
    letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
    exact alignedRemainderMaxSq_le_componentWindowMaxSq
      chi (sigma q chi) T epsilon X x

/-- The six-component proposition inhabits the aligned tail source. -/
theorem alignedTailFamilySquare_of_componentFamilySquare
    (hcomponents : AlignedComponentFamilySquare) :
    AlignedAPExplicitFormulaTailFamilySquare := by
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
    familyAlignedTailMajorant_le_componentMajorant
      _ _ _ _ _ _).trans hbound

end
end MAPAPAlignedComponentSource

#print axioms MAPAPAlignedComponentSource.alignedEndpointRemainder_eq_signedComponents
#print axioms MAPAPAlignedComponentSource.norm_mainDisplacement_window_div_le_inv
#print axioms MAPAPAlignedComponentSource.imprimitiveCorrection_prefix_sub_eq_window
#print axioms MAPAPAlignedComponentSource.norm_imprimitiveComponent_window_le
#print axioms MAPAPAlignedComponentSource.alignedRemainderMaxSq_le_componentWindowMaxSq
#print axioms MAPAPAlignedComponentSource.alignedTailFamilySquare_of_componentFamilySquare
