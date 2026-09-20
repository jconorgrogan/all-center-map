import APPerronEndpointUniformBound
import APTailReserveAbsorption
import APAlignedComponentSource

/-!
# Direct aligned AP tail closure

The release path keeps the left and horizontal contour windows signed and
joint.  The principal displacement, the two Perron endpoint terms, and the
imprimitive correction are separated into a deterministic remainder.  This
leaves one cancellation-preserving analytic family estimate.
-/

namespace MAPAPDirectAlignedTailClosure

open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open APFoundation MAPFixedScaleAPZeroRoute MAPAPHalfIntegerAlignedTail
open MAPAPAlignedTailToRemainderTransfer MAPAPAlignedComponentSource
open MAPAPCorrectedPaperEdgeComponentSource
open MAPAPPerronEndpointUniformBound MAPAPTailReserveAbsorption
open PaperEdgePrimitiveComponents
open MAPAPCorrectedCommonHeightContract

noncomputable section

variable {q : ℕ} [NeZero q]

/-- The only non-deterministic contour window retained by the direct route. -/
def alignedLeftHorizontalWindowSqAtScale
    (chi : DirichletCharacter ℂ q) (sigma T x Y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal <| 8 *
    ‖((leftComponent chi sigma T (x + Y) - leftComponent chi sigma T x) +
       (horizontalComponent chi sigma T (x + Y) -
         horizontalComponent chi sigma T x)) / Y‖ ^ 2

/-- The four premise-free aligned window terms. -/
def alignedDeterministicWindowSqAtScale
    (chi : DirichletCharacter ℂ q) (T x Y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal <| 8 *
    (‖(mainDisplacement chi (x + Y) - mainDisplacement chi x) / Y‖ ^ 2 +
     ‖(insideComponent chi T (x + Y) - insideComponent chi T x) / Y‖ ^ 2 +
     ‖(outsideComponent chi T (x + Y) - outsideComponent chi T x) / Y‖ ^ 2 +
     ‖(imprimitiveComponent chi (x + Y) - imprimitiveComponent chi x) / Y‖ ^ 2)

/-- The signed aligned tail is bounded without separating left from horizontal. -/
theorem alignedRemainderWindowSq_le_leftHorizontal_add_deterministic
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    (sigma T x Y : ℝ) :
    ENNReal.ofReal
        ‖(alignedEndpointRemainder chi sigma T (x + Y) -
            alignedEndpointRemainder chi sigma T x) / Y‖ ^ 2 ≤
      alignedLeftHorizontalWindowSqAtScale chi sigma T x Y +
        alignedDeterministicWindowSqAtScale chi T x Y := by
  let a := ((leftComponent chi sigma T (x + Y) -
      leftComponent chi sigma T x) +
    (horizontalComponent chi sigma T (x + Y) -
      horizontalComponent chi sigma T x)) / Y
  let b := (mainDisplacement chi (x + Y) - mainDisplacement chi x) / Y
  let c := (insideComponent chi T (x + Y) - insideComponent chi T x) / Y
  let d := (outsideComponent chi T (x + Y) - outsideComponent chi T x) / Y
  let e := (imprimitiveComponent chi (x + Y) - imprimitiveComponent chi x) / Y
  have hdecomp :
      (alignedEndpointRemainder chi sigma T (x + Y) -
          alignedEndpointRemainder chi sigma T x) / Y = a + b + c + d + e := by
    rw [alignedEndpointRemainder_eq_signedComponents,
      alignedEndpointRemainder_eq_signedComponents]
    dsimp only [a, b, c, d, e]
    ring
  have hsquare : ‖a + b + c + d + e‖ ^ 2 ≤
      8 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2 + ‖e‖ ^ 2) := by
    simpa [norm_zero] using
      (norm_six_sum_sq_le_eight a b c d e 0)
  rw [hdecomp]
  rw [← ENNReal.ofReal_pow (norm_nonneg _) 2]
  unfold alignedLeftHorizontalWindowSqAtScale
    alignedDeterministicWindowSqAtScale
  rw [← ENNReal.ofReal_add]
  · apply ENNReal.ofReal_le_ofReal
    dsimp only [a, b, c, d, e] at hsquare ⊢
    linarith
  · nlinarith [
      sq_nonneg (‖(mainDisplacement chi (x + Y) -
        mainDisplacement chi x) / Y‖),
      sq_nonneg (‖(insideComponent chi T (x + Y) -
        insideComponent chi T x) / Y‖),
      sq_nonneg (‖(outsideComponent chi T (x + Y) -
        outsideComponent chi T x) / Y‖),
      sq_nonneg (‖(imprimitiveComponent chi (x + Y) -
        imprimitiveComponent chi x) / Y‖)]
  · nlinarith [
      sq_nonneg (‖(mainDisplacement chi (x + Y) -
        mainDisplacement chi x) / Y‖),
      sq_nonneg (‖(insideComponent chi T (x + Y) -
        insideComponent chi T x) / Y‖),
      sq_nonneg (‖(outsideComponent chi T (x + Y) -
        outsideComponent chi T x) / Y‖),
      sq_nonneg (‖(imprimitiveComponent chi (x + Y) -
        imprimitiveComponent chi x) / Y‖)]

/-- Legal-aperture maximum of the signed left/horizontal window. -/
def alignedLeftHorizontalWindowMaxSq
    (chi : DirichletCharacter ℂ q)
    (sigma T epsilon X x : ℝ) : ℝ≥0∞ :=
  ⨆ (Y : ℝ) (_hYlow : Real.rpow X (2 / 15 + epsilon) ≤ Y)
      (_hYhigh : Y ≤ X),
    alignedLeftHorizontalWindowSqAtScale chi sigma T x Y

/-- Legal-aperture maximum of the four deterministic windows. -/
def alignedDeterministicWindowMaxSq
    (chi : DirichletCharacter ℂ q)
    (T epsilon X x : ℝ) : ℝ≥0∞ :=
  ⨆ (Y : ℝ) (_hYlow : Real.rpow X (2 / 15 + epsilon) ≤ Y)
      (_hYhigh : Y ≤ X),
    alignedDeterministicWindowSqAtScale chi T x Y

/-- The aligned imprimitive window is logarithmic, uniformly on the global
AP strip.  The generous constant ten avoids any hidden endpoint loss. -/
theorem norm_imprimitiveComponent_window_div_le_ten_log
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    {X x Y H : ℝ}
    (hX : Real.exp 1 ≤ X) (hx : x ∈ Set.Icc (X / 2) (4 * X))
    (hY : 0 < Y) (hYX : Y ≤ X) (hH : 0 < H) (hHY : H ≤ Y) :
    ‖(imprimitiveComponent chi (x + Y) - imprimitiveComponent chi x) / Y‖ ≤
      10 * Real.log X * Real.log q / H := by
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlogX : 1 ≤ Real.log X :=
    (Real.le_log_iff_exp_le hX0).2 hX
  have hx1 : 1 ≤ x := by
    have hXtwo : 2 ≤ X := Real.exp_one_gt_two.le.trans hX
    linarith [hx.1]
  have hxy1 : 1 ≤ x + Y := by linarith
  have hfloorOne : 1 ≤ ⌊x + Y⌋₊ :=
    Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ x + Y by simpa using hxy1)
  have hfloorPos : 0 < (⌊x + Y⌋₊ : ℝ) := by exact_mod_cast hfloorOne
  have hfloorLe : (⌊x + Y⌋₊ : ℝ) ≤ 5 * X := by
    calc
      (⌊x + Y⌋₊ : ℝ) ≤ x + Y := Nat.floor_le (by linarith)
      _ ≤ 5 * X := by linarith [hx.2]
  have hlogFloor : Real.log (⌊x + Y⌋₊ : ℝ) ≤ 5 * Real.log X := by
    calc
      Real.log (⌊x + Y⌋₊ : ℝ) ≤ Real.log (5 * X) :=
        Real.log_le_log hfloorPos hfloorLe
      _ = Real.log 5 + Real.log X := by
        rw [Real.log_mul (by norm_num) hX0.ne']
      _ ≤ 4 + Real.log X := by
        gcongr
        convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)
          using 1 <;> norm_num
      _ ≤ 5 * Real.log X := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2half : 1 / 2 < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hinvlog2 : (Real.log 2)⁻¹ ≤ 2 := by
    simpa using
      (inv_le_inv₀ hlog2 (by norm_num : (0 : ℝ) < 1 / 2)).2 hlog2half.le
  have hlogFloor0 : 0 ≤ Real.log (⌊x + Y⌋₊ : ℝ) :=
    Real.log_natCast_nonneg _
  have hfloorFactor :
      (⌊Real.log (⌊x + Y⌋₊ : ℝ) / Real.log 2⌋₊ : ℝ) ≤
        10 * Real.log X := by
    calc
      (⌊Real.log (⌊x + Y⌋₊ : ℝ) / Real.log 2⌋₊ : ℝ) ≤
          Real.log (⌊x + Y⌋₊ : ℝ) / Real.log 2 :=
        Nat.floor_le (div_nonneg hlogFloor0 hlog2.le)
      _ = Real.log (⌊x + Y⌋₊ : ℝ) * (Real.log 2)⁻¹ := by
        rw [div_eq_mul_inv]
      _ ≤ (5 * Real.log X) * 2 := by gcongr
      _ = 10 * Real.log X := by ring
  have hlogq0 : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hnum := norm_imprimitiveComponent_window_le chi (x := x) hY.le
  have hnum' :
      ‖imprimitiveComponent chi (x + Y) - imprimitiveComponent chi x‖ ≤
        10 * Real.log X * Real.log q :=
    hnum.trans (mul_le_mul_of_nonneg_right hfloorFactor hlogq0)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY]
  apply (div_le_div_iff₀ hY hH).2
  exact mul_le_mul hnum' hHY hH.le (by positivity)

/-- Uniform deterministic maximum at the legal lower aperture. -/
theorem alignedDeterministicWindowMaxSq_le
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    {T epsilon X x : ℝ}
    (hX : Real.exp 1 ≤ X) (hT : 0 < T) (hepsilon : 0 < epsilon)
    (hx : x ∈ Set.Icc (X / 2) (4 * X)) :
    alignedDeterministicWindowMaxSq chi T epsilon X x ≤
      ENNReal.ofReal (8 *
        ((Real.rpow X (2 / 15 + epsilon))⁻¹ +
         6000 * X * (Real.log X) ^ 2 /
           (T * Real.rpow X (2 / 15 + epsilon)) +
         18000 * X * (Real.log X) ^ 2 /
           (T * Real.rpow X (2 / 15 + epsilon)) +
         10 * Real.log X * Real.log q /
           Real.rpow X (2 / 15 + epsilon)) ^ 2) := by
  unfold alignedDeterministicWindowMaxSq
  apply iSup_le
  intro Y
  apply iSup_le
  intro hYlow
  apply iSup_le
  intro hYhigh
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  let H := Real.rpow X (2 / 15 + epsilon)
  have hH : 0 < H := Real.rpow_pos_of_pos hX0 _
  have hY : 0 < Y := hH.trans_le hYlow
  have hx1 : 1 ≤ x := by
    have hXtwo : 2 ≤ X := Real.exp_one_gt_two.le.trans hX
    linarith [hx.1]
  have hxy : x + Y ≤ 5 * X := by linarith [hx.2]
  have hb := norm_mainDisplacement_window_div_le_inv chi (zero_le_one.trans hx1) hY
  have hc := norm_insideComponent_window_div_le chi hX hT hx1 hY hxy
    hYlow hH
  have hd := norm_outsideComponent_window_div_le chi hX hT hx1 hY hxy
    hYlow hH
  have he := norm_imprimitiveComponent_window_div_le_ten_log chi hX hx hY
    hYhigh hH hYlow
  have hinv : Y⁻¹ ≤ H⁻¹ := by
    exact inv_anti₀ hH hYlow
  let B := H⁻¹
  let C := 6000 * X * (Real.log X) ^ 2 / (T * H)
  let D := 18000 * X * (Real.log X) ^ 2 / (T * H)
  let E := 10 * Real.log X * Real.log q / H
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg
      ((Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hX)))
      (Real.log_natCast_nonneg q)) hH.le
  have hb' :
      ‖(mainDisplacement chi (x + Y) - mainDisplacement chi x) / Y‖ ≤ B :=
    hb.trans hinv
  have hc' :
      ‖(insideComponent chi T (x + Y) - insideComponent chi T x) / Y‖ ≤ C := hc
  have hd' :
      ‖(outsideComponent chi T (x + Y) - outsideComponent chi T x) / Y‖ ≤ D := hd
  have he' :
      ‖(imprimitiveComponent chi (x + Y) - imprimitiveComponent chi x) / Y‖ ≤ E := he
  have hbSq := (sq_le_sq₀ (norm_nonneg _) hB).2 hb'
  have hcSq := (sq_le_sq₀ (norm_nonneg _) hC).2 hc'
  have hdSq := (sq_le_sq₀ (norm_nonneg _) hD).2 hd'
  have heSq := (sq_le_sq₀ (norm_nonneg _) hE).2 he'
  have hsquares :
      ‖(mainDisplacement chi (x + Y) - mainDisplacement chi x) / Y‖ ^ 2 +
        ‖(insideComponent chi T (x + Y) - insideComponent chi T x) / Y‖ ^ 2 +
        ‖(outsideComponent chi T (x + Y) - outsideComponent chi T x) / Y‖ ^ 2 +
        ‖(imprimitiveComponent chi (x + Y) - imprimitiveComponent chi x) / Y‖ ^ 2 ≤
      (B + C + D + E) ^ 2 := by
    nlinarith [mul_nonneg hB hC, mul_nonneg hB hD,
      mul_nonneg hB hE, mul_nonneg hC hD, mul_nonneg hC hE,
      mul_nonneg hD hE]
  unfold alignedDeterministicWindowSqAtScale
  apply ENNReal.ofReal_le_ofReal
  dsimp only [H, B, C, D, E] at hsquares ⊢
  nlinarith

/-- Uniform real envelope after replacing `log q` by the legal modulus cap. -/
def alignedDeterministicEnvelope
    (Q : ℕ) (T epsilon X : ℝ) : ℝ :=
  (Real.rpow X (2 / 15 + epsilon))⁻¹ +
    6000 * X * (Real.log X) ^ 2 /
      (T * Real.rpow X (2 / 15 + epsilon)) +
    18000 * X * (Real.log X) ^ 2 /
      (T * Real.rpow X (2 / 15 + epsilon)) +
    10 * Real.log X * Q / Real.rpow X (2 / 15 + epsilon)

theorem alignedDeterministicWindowMaxSq_le_envelope
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    {Q : ℕ} {T epsilon X x : ℝ}
    (hqQ : q ≤ Q)
    (hX : Real.exp 1 ≤ X) (hT : 0 < T) (hepsilon : 0 < epsilon)
    (hx : x ∈ Set.Icc (X / 2) (4 * X)) :
    alignedDeterministicWindowMaxSq chi T epsilon X x ≤
      ENNReal.ofReal (8 * (alignedDeterministicEnvelope Q T epsilon X) ^ 2) := by
  refine (alignedDeterministicWindowMaxSq_le chi hX hT hepsilon hx).trans ?_
  apply ENNReal.ofReal_mono
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  have hH : 0 < Real.rpow X (2 / 15 + epsilon) :=
    Real.rpow_pos_of_pos hX0 _
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg
    ((Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hX)
  have hlogq0 : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hlogqQ : Real.log q ≤ (Q : ℝ) := by
    calc
      Real.log q ≤ (q : ℝ) := Real.log_le_self (Nat.cast_nonneg q)
      _ ≤ (Q : ℝ) := by exact_mod_cast hqQ
  let Dq :=
    (Real.rpow X (2 / 15 + epsilon))⁻¹ +
      6000 * X * (Real.log X) ^ 2 /
        (T * Real.rpow X (2 / 15 + epsilon)) +
      18000 * X * (Real.log X) ^ 2 /
        (T * Real.rpow X (2 / 15 + epsilon)) +
      10 * Real.log X * Real.log q /
        Real.rpow X (2 / 15 + epsilon)
  have hDq : 0 ≤ Dq := by
    dsimp only [Dq]
    positivity
  have hDQ : 0 ≤ alignedDeterministicEnvelope Q T epsilon X := by
    unfold alignedDeterministicEnvelope
    positivity
  have hle : Dq ≤ alignedDeterministicEnvelope Q T epsilon X := by
    dsimp only [Dq]
    unfold alignedDeterministicEnvelope
    gcongr
  dsimp only [Dq] at hDq hle ⊢
  nlinarith

theorem alignedRemainderMaxSq_le_leftHorizontal_add_deterministic
    (chi : DirichletCharacter ℂ q) [NeZero chi.conductor]
    (sigma T epsilon X x : ℝ) :
    alignedRemainderMaxSq chi sigma T epsilon X x ≤
      alignedLeftHorizontalWindowMaxSq chi sigma T epsilon X x +
        alignedDeterministicWindowMaxSq chi T epsilon X x := by
  unfold alignedRemainderMaxSq
  apply iSup_le
  intro Y
  apply iSup_le
  intro hYlow
  apply iSup_le
  intro hYhigh
  exact (alignedRemainderWindowSq_le_leftHorizontal_add_deterministic
      chi sigma T x Y).trans <| add_le_add
    (le_iSup_of_le Y <| le_iSup_of_le hYlow <|
      le_iSup_of_le hYhigh le_rfl)
    (le_iSup_of_le Y <| le_iSup_of_le hYlow <|
      le_iSup_of_le hYhigh le_rfl)

/-- One-outer-integral finite family for the joint signed contour window. -/
def familyAlignedLeftHorizontalMajorant
    (Q : ℕ) (sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ)
    (T epsilon X x : ℝ) : ℝ≥0∞ :=
  ∑ q ∈ Finset.Icc 1 Q,
    if hq : q = 0 then 0 else
      letI : NeZero q := ⟨hq⟩
      (q.totient : ℝ≥0∞)⁻¹ *
        ∑ chi : DirichletCharacter ℂ q,
          alignedLeftHorizontalWindowMaxSq chi (sigma q chi) T epsilon X x

/-- One-outer-integral finite family for the premise-free terms. -/
def familyAlignedDeterministicMajorant
    (Q : ℕ) (T epsilon X x : ℝ) : ℝ≥0∞ :=
  ∑ q ∈ Finset.Icc 1 Q,
    if hq : q = 0 then 0 else
      letI : NeZero q := ⟨hq⟩
      (q.totient : ℝ≥0∞)⁻¹ *
        ∑ chi : DirichletCharacter ℂ q,
          alignedDeterministicWindowMaxSq chi T epsilon X x

/-- Deterministic family aggregation with exact character normalization. -/
theorem familyAlignedDeterministicMajorant_le
    {Q : ℕ} {T epsilon X x : ℝ}
    (hX : Real.exp 1 ≤ X) (hT : 0 < T) (hepsilon : 0 < epsilon)
    (hx : x ∈ Set.Icc (X / 2) (4 * X)) :
    familyAlignedDeterministicMajorant Q T epsilon X x ≤
      (Q : ℝ≥0∞) * ENNReal.ofReal
        (8 * (alignedDeterministicEnvelope Q T epsilon X) ^ 2) := by
  let B : ℝ≥0∞ := ENNReal.ofReal
    (8 * (alignedDeterministicEnvelope Q T epsilon X) ^ 2)
  unfold familyAlignedDeterministicMajorant
  calc
    (∑ q ∈ Finset.Icc 1 Q,
      if hq : q = 0 then 0 else
        letI : NeZero q := ⟨hq⟩
        (q.totient : ℝ≥0∞)⁻¹ *
          ∑ chi : DirichletCharacter ℂ q,
            alignedDeterministicWindowMaxSq chi T epsilon X x) ≤
      ∑ _q ∈ Finset.Icc 1 Q, B := by
        apply Finset.sum_le_sum
        intro q hqmem
        have hqpos : 1 ≤ q := (Finset.mem_Icc.mp hqmem).1
        have hqQ : q ≤ Q := (Finset.mem_Icc.mp hqmem).2
        have hq0 : q ≠ 0 := Nat.ne_of_gt hqpos
        simp only [dif_neg hq0]
        letI : NeZero q := ⟨hq0⟩
        have hchars :
            (∑ chi : DirichletCharacter ℂ q,
              alignedDeterministicWindowMaxSq chi T epsilon X x) ≤
            ∑ _chi : DirichletCharacter ℂ q, B := by
          apply Finset.sum_le_sum
          intro chi hchimem
          letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
          exact alignedDeterministicWindowMaxSq_le_envelope chi hqQ
            hX hT hepsilon hx
        calc
          (q.totient : ℝ≥0∞)⁻¹ *
              ∑ chi : DirichletCharacter ℂ q,
                alignedDeterministicWindowMaxSq chi T epsilon X x ≤
            (q.totient : ℝ≥0∞)⁻¹ *
              ∑ _chi : DirichletCharacter ℂ q, B :=
                mul_le_mul_left' hchars _
          _ = B := by
            rw [Finset.sum_const]
            have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
              rw [← Nat.card_eq_fintype_card]
              exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
            rw [Finset.card_univ, hcard, nsmul_eq_mul]
            have hphi0 : (q.totient : ℝ≥0∞) ≠ 0 := by
              exact_mod_cast
                (Nat.totient_pos.mpr (Nat.zero_lt_of_lt hqpos)).ne'
            rw [← mul_assoc, ENNReal.inv_mul_cancel hphi0 (by simp)]
            simp
    _ = (Q : ℝ≥0∞) * B := by
      rw [Finset.sum_const, Nat.card_Icc]
      norm_num [nsmul_eq_mul]
    _ = _ := rfl

theorem familyAlignedDeterministicMajorant_integral_le
    {Q : ℕ} {T epsilon X : ℝ}
    (hX : Real.exp 1 ≤ X) (hT : 0 < T) (hepsilon : 0 < epsilon) :
    (∫⁻ x in Set.Icc (X / 2) (4 * X),
      familyAlignedDeterministicMajorant Q T epsilon X x) ≤
      ((Q : ℝ≥0∞) * ENNReal.ofReal
        (8 * (alignedDeterministicEnvelope Q T epsilon X) ^ 2)) *
          ENNReal.ofReal (7 * X / 2) := by
  calc
    (∫⁻ x in Set.Icc (X / 2) (4 * X),
      familyAlignedDeterministicMajorant Q T epsilon X x) ≤
      ∫⁻ _x in Set.Icc (X / 2) (4 * X),
        ((Q : ℝ≥0∞) * ENNReal.ofReal
          (8 * (alignedDeterministicEnvelope Q T epsilon X) ^ 2)) := by
        apply MeasureTheory.setLIntegral_mono' measurableSet_Icc
        intro x hx
        exact familyAlignedDeterministicMajorant_le hX hT hepsilon hx
    _ = ((Q : ℝ≥0∞) * ENNReal.ofReal
        (8 * (alignedDeterministicEnvelope Q T epsilon X) ^ 2)) *
          ENNReal.ofReal (7 * X / 2) := by
      rw [MeasureTheory.setLIntegral_const, Real.volume_Icc]
      congr 2
      ring

/-- Any fixed inverse aperture power absorbs an arbitrary polylogarithm. -/
theorem eventually_aperture_inv_mul_polylog_le
    (M B epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ X : ℝ in atTop,
      (Real.rpow X (2 / 15 + epsilon))⁻¹ *
          Real.rpow (Real.log X) B ≤
        Real.rpow (Real.log X) (-M) := by
  have hbase := eventually_tail_power_mul_polylog_le M B (4 / 15)
    (by norm_num)
  filter_upwards [hbase, eventually_ge_atTop (1 : ℝ)] with X hbaseX hX
  have hpow : (Real.rpow X (2 / 15 + epsilon))⁻¹ ≤
      Real.rpow X (-(4 / 15) / 2) := by
    have hinvEq : (Real.rpow X (2 / 15 + epsilon))⁻¹ =
        Real.rpow X (-(2 / 15 + epsilon)) :=
      (Real.rpow_neg (zero_le_one.trans hX) (2 / 15 + epsilon)).symm
    rw [hinvEq]
    apply Real.rpow_le_rpow_of_exponent_le hX
    linarith
  exact (mul_le_mul_of_nonneg_right hpow
    (Real.rpow_nonneg (Real.log_nonneg hX) B)).trans hbaseX

/-- The complete deterministic envelope has arbitrary logarithmic saving at
the corrected common height and legal modulus cap. -/
theorem eventually_alignedDeterministicEnvelope_le
    (K M epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (Q : ℕ) (T : ℝ),
        (Q : ℝ) ≤ Real.rpow (Real.log X) K →
        apZeroHeight (min epsilon (1 / 10)) X < T →
        alignedDeterministicEnvelope Q T epsilon X ≤
          24011 * Real.rpow (Real.log X) (-M) := by
  have hmain := eventually_aperture_inv_mul_polylog_le M 0 epsilon hepsilon
  have htail := eventually_literal_tail_ratio_mul_polylog_le M 2 epsilon hepsilon
  have himp := eventually_aperture_inv_mul_polylog_le M (K + 1) epsilon hepsilon
  filter_upwards [hmain, htail, himp,
      eventually_ge_atTop (Real.exp 1)] with X hmainX htailX himpX hX
  intro Q T hQ hT
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  have hXone : 1 ≤ X :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hX
  have hlog : 1 ≤ Real.log X :=
    (Real.le_log_iff_exp_le hX0).2 hX
  have hlog0 : 0 < Real.log X := zero_lt_one.trans_le hlog
  have hH : 0 < Real.rpow X (2 / 15 + epsilon) :=
    Real.rpow_pos_of_pos hX0 _
  have hH0 : 0 < apZeroHeight (min epsilon (1 / 10)) X :=
    Real.rpow_pos_of_pos hX0 _
  have hT0 : 0 < T := hH0.trans hT
  have hmain' : (Real.rpow X (2 / 15 + epsilon))⁻¹ ≤
      Real.rpow (Real.log X) (-M) := by
    simpa using hmainX
  have hratio :
      X / (T * Real.rpow X (2 / 15 + epsilon)) ≤
        X /
          (apZeroHeight (min epsilon (1 / 10)) X *
            Real.rpow X (2 / 15 + epsilon)) := by
    apply div_le_div_of_nonneg_left hX0.le
    · exact mul_pos hH0 hH
    · exact mul_le_mul_of_nonneg_right hT.le hH.le
  have htail' :
      (X / (T * Real.rpow X (2 / 15 + epsilon))) *
          (Real.log X) ^ 2 ≤
        Real.rpow (Real.log X) (-M) := by
    have hmul := mul_le_mul_of_nonneg_right hratio (sq_nonneg (Real.log X))
    have htailX' :
        (X / (apZeroHeight (min epsilon (1 / 10)) X *
            Real.rpow X (2 / 15 + epsilon))) *
          (Real.log X) ^ 2 ≤ Real.rpow (Real.log X) (-M) := by
      have hxpow : Real.rpow X (1 : ℝ) = X := Real.rpow_one X
      have hlpow : Real.rpow (Real.log X) (2 : ℝ) =
          (Real.log X) ^ (2 : ℕ) := Real.rpow_two (Real.log X)
      rw [hxpow, hlpow] at htailX
      exact htailX
    exact hmul.trans htailX'
  have hQlog : (Real.log X) * (Q : ℝ) ≤
      Real.rpow (Real.log X) (K + 1) := by
    calc
      Real.log X * (Q : ℝ) ≤
          Real.log X * Real.rpow (Real.log X) K :=
        mul_le_mul_of_nonneg_left hQ hlog0.le
      _ = Real.rpow (Real.log X) 1 *
          Real.rpow (Real.log X) K := by
            congr 1
            exact (Real.rpow_one _).symm
      _ = Real.rpow (Real.log X) (1 + K) :=
        (Real.rpow_add hlog0 1 K).symm
      _ = Real.rpow (Real.log X) (K + 1) := by ring_nf
  have himp' :
      (Real.rpow X (2 / 15 + epsilon))⁻¹ *
          (Real.log X * (Q : ℝ)) ≤
        Real.rpow (Real.log X) (-M) :=
    (mul_le_mul_of_nonneg_left hQlog
      (inv_nonneg.mpr hH.le)).trans himpX
  unfold alignedDeterministicEnvelope
  have htailNonneg : 0 ≤
      X / (T * Real.rpow X (2 / 15 + epsilon)) := by positivity
  have himpNonneg : 0 ≤
      (Real.rpow X (2 / 15 + epsilon))⁻¹ *
        (Real.log X * (Q : ℝ)) := by positivity
  have htarget : 0 ≤ Real.rpow (Real.log X) (-M) :=
    Real.rpow_nonneg hlog0.le _
  have htail6000 :
      6000 * X * Real.log X ^ 2 /
          (T * Real.rpow X (2 / 15 + epsilon)) ≤
        6000 * Real.rpow (Real.log X) (-M) := by
    calc
      6000 * X * Real.log X ^ 2 /
          (T * Real.rpow X (2 / 15 + epsilon)) =
        6000 * ((X / (T * Real.rpow X (2 / 15 + epsilon))) *
          Real.log X ^ 2) := by ring
      _ ≤ 6000 * Real.rpow (Real.log X) (-M) := by gcongr
  have htail18000 :
      18000 * X * Real.log X ^ 2 /
          (T * Real.rpow X (2 / 15 + epsilon)) ≤
        18000 * Real.rpow (Real.log X) (-M) := by
    calc
      18000 * X * Real.log X ^ 2 /
          (T * Real.rpow X (2 / 15 + epsilon)) =
        18000 * ((X / (T * Real.rpow X (2 / 15 + epsilon))) *
          Real.log X ^ 2) := by ring
      _ ≤ 18000 * Real.rpow (Real.log X) (-M) := by gcongr
  have himp10 :
      10 * Real.log X * (Q : ℝ) /
          Real.rpow X (2 / 15 + epsilon) ≤
        10 * Real.rpow (Real.log X) (-M) := by
    calc
      10 * Real.log X * (Q : ℝ) /
          Real.rpow X (2 / 15 + epsilon) =
        10 * ((Real.rpow X (2 / 15 + epsilon))⁻¹ *
          (Real.log X * (Q : ℝ))) := by ring
      _ ≤ 10 * Real.rpow (Real.log X) (-M) := by gcongr
  calc
    (Real.rpow X (2 / 15 + epsilon))⁻¹ +
        6000 * X * Real.log X ^ 2 /
          (T * Real.rpow X (2 / 15 + epsilon)) +
        18000 * X * Real.log X ^ 2 /
          (T * Real.rpow X (2 / 15 + epsilon)) +
        10 * Real.log X * (Q : ℝ) /
          Real.rpow X (2 / 15 + epsilon) ≤
      Real.rpow (Real.log X) (-M) +
        6000 * Real.rpow (Real.log X) (-M) +
        18000 * Real.rpow (Real.log X) (-M) +
        10 * Real.rpow (Real.log X) (-M) := by
          exact add_le_add (add_le_add (add_le_add hmain' htail6000)
            htail18000) himp10
    _ = 24011 * Real.rpow (Real.log X) (-M) := by ring

/-- Premise-free arbitrary-log family estimate for all four deterministic
aligned terms. -/
theorem alignedDeterministicFamilyEnvelopeSquare :
    ∀ K A epsilon : ℝ,
      0 < K → 0 < A → 0 < epsilon → epsilon ≤ 13 / 30 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
        ∀ X : ℝ, X0 ≤ X →
          let reserve := min epsilon (1 / 10)
          let H0 := apZeroHeight reserve X
          let Q := ⌊Real.rpow (Real.log X) K⌋₊
          ∀ T ∈ Set.Ioo H0 (H0 + 1),
            (((Q : ℝ≥0∞) * ENNReal.ofReal
                (8 * (alignedDeterministicEnvelope Q T epsilon X) ^ 2)) *
              ENNReal.ofReal (7 * X / 2)) ≤
              ENNReal.ofReal (C * X * Real.rpow (Real.log X) (-A)) := by
  intro K A epsilon hK hA hepsilon hepsilonCap
  let M := A + K + 2
  have henv := eventually_alignedDeterministicEnvelope_le K M epsilon hepsilon
  have hall : ∀ᶠ X : ℝ in atTop,
      (∀ (Q : ℕ) (T : ℝ),
        (Q : ℝ) ≤ Real.rpow (Real.log X) K →
        apZeroHeight (min epsilon (1 / 10)) X < T →
        alignedDeterministicEnvelope Q T epsilon X ≤
          24011 * Real.rpow (Real.log X) (-M)) ∧
      Real.exp 1 ≤ X := henv.and (eventually_ge_atTop _)
  rw [eventually_atTop] at hall
  rcases hall with ⟨Xevent, hXevent⟩
  let C : ℝ := 28 * 24011 ^ 2
  let X0 : ℝ := max 2 Xevent
  refine ⟨C, X0, by dsimp [C]; positivity, le_max_left _ _, ?_⟩
  intro X hXX0
  have hXe : Xevent ≤ X := (le_max_right 2 Xevent).trans hXX0
  have hdata := hXevent X hXe
  rcases hdata with ⟨henvX, hX⟩
  dsimp only
  intro T hT
  let Q := ⌊Real.rpow (Real.log X) K⌋₊
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlog : 1 ≤ Real.log X := (Real.le_log_iff_exp_le hX0).2 hX
  have hlog0 : 0 < Real.log X := zero_lt_one.trans_le hlog
  have hQ : (Q : ℝ) ≤ Real.rpow (Real.log X) K := by
    exact Nat.floor_le (Real.rpow_nonneg hlog0.le K)
  have hD := henvX Q T hQ hT.1
  have hD0 : 0 ≤ alignedDeterministicEnvelope Q T epsilon X := by
    unfold alignedDeterministicEnvelope
    have hT0 : 0 < T := (Real.rpow_pos_of_pos hX0 _).trans hT.1
    have hH0 : 0 ≤ Real.rpow X (2 / 15 + epsilon) :=
      Real.rpow_nonneg hX0.le _
    have hlogNonneg : 0 ≤ Real.log X := hlog0.le
    exact add_nonneg (add_nonneg (add_nonneg
      (inv_nonneg.mpr hH0)
      (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hX0.le)
        (sq_nonneg _)) (mul_nonneg hT0.le hH0)))
      (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hX0.le)
        (sq_nonneg _)) (mul_nonneg hT0.le hH0)))
      (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hlogNonneg)
        (Nat.cast_nonneg Q)) hH0)
  have hLM0 : 0 ≤ Real.rpow (Real.log X) (-M) :=
    Real.rpow_nonneg hlog0.le _
  have hDsq : (alignedDeterministicEnvelope Q T epsilon X) ^ 2 ≤
      (24011 * Real.rpow (Real.log X) (-M)) ^ 2 :=
    (sq_le_sq₀ hD0 (mul_nonneg (by norm_num) hLM0)).2 hD
  have hpowprod :
      Real.rpow (Real.log X) K *
          (Real.rpow (Real.log X) (-M)) ^ 2 ≤
        Real.rpow (Real.log X) (-A) := by
    have hsq : (Real.rpow (Real.log X) (-M)) ^ 2 =
        Real.rpow (Real.log X) (-M + -M) := by
      calc
        (Real.rpow (Real.log X) (-M)) ^ 2 =
            Real.rpow (Real.log X) (-M) *
              Real.rpow (Real.log X) (-M) := by ring
        _ = Real.rpow (Real.log X) (-M + -M) :=
          (Real.rpow_add hlog0 (-M) (-M)).symm
    calc
      Real.rpow (Real.log X) K *
          (Real.rpow (Real.log X) (-M)) ^ 2 =
        Real.rpow (Real.log X) K *
          Real.rpow (Real.log X) (-M + -M) := by rw [hsq]
      _ = Real.rpow (Real.log X) (K + (-M + -M)) :=
        (Real.rpow_add hlog0 K (-M + -M)).symm
      _ ≤ Real.rpow (Real.log X) (-A) := by
        apply Real.rpow_le_rpow_of_exponent_le hlog
        dsimp only [M]
        linarith
  have hreal :
      (Q : ℝ) * (8 * (alignedDeterministicEnvelope Q T epsilon X) ^ 2) *
          (7 * X / 2) ≤
        C * X * Real.rpow (Real.log X) (-A) := by
    have hQ0 : 0 ≤ (Q : ℝ) := Nat.cast_nonneg Q
    have hXnonneg : 0 ≤ X := hX0.le
    have hLk0 : 0 ≤ Real.rpow (Real.log X) K :=
      Real.rpow_nonneg hlog0.le _
    have h8 :
        8 * (alignedDeterministicEnvelope Q T epsilon X) ^ 2 ≤
          8 * (24011 * Real.rpow (Real.log X) (-M)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hDsq (by norm_num)
    have hprod :
        (Q : ℝ) * (8 * (alignedDeterministicEnvelope Q T epsilon X) ^ 2) ≤
          Real.rpow (Real.log X) K *
            (8 * (24011 * Real.rpow (Real.log X) (-M)) ^ 2) := by
      exact mul_le_mul hQ h8 (by positivity) hLk0
    calc
      (Q : ℝ) * (8 * (alignedDeterministicEnvelope Q T epsilon X) ^ 2) *
          (7 * X / 2) ≤
        Real.rpow (Real.log X) K *
          (8 * (24011 * Real.rpow (Real.log X) (-M)) ^ 2) *
            (7 * X / 2) := by
              exact mul_le_mul_of_nonneg_right hprod (by positivity)
      _ = C * X * (Real.rpow (Real.log X) K *
          (Real.rpow (Real.log X) (-M)) ^ 2) := by
        dsimp only [C]
        ring
      _ ≤ C * X * Real.rpow (Real.log X) (-A) := by
        gcongr
  have hleft0 : 0 ≤
      (Q : ℝ) * (8 * (alignedDeterministicEnvelope Q T epsilon X) ^ 2) := by
    positivity
  calc
    ((Q : ℝ≥0∞) * ENNReal.ofReal
        (8 * (alignedDeterministicEnvelope Q T epsilon X) ^ 2)) *
          ENNReal.ofReal (7 * X / 2) =
      ENNReal.ofReal ((Q : ℝ) *
        (8 * (alignedDeterministicEnvelope Q T epsilon X) ^ 2) *
          (7 * X / 2)) := by
            rw [← ENNReal.ofReal_natCast,
              ← ENNReal.ofReal_mul (Nat.cast_nonneg Q),
              ← ENNReal.ofReal_mul hleft0]
    _ ≤ ENNReal.ofReal (C * X * Real.rpow (Real.log X) (-A)) :=
      ENNReal.ofReal_mono hreal


/-- Family pointwise reduction.  No measurability of the real-`Y` supremum is
used: both maxima stay under the same outer integral. -/
theorem familyAlignedTailMajorant_le_leftHorizontal_add_deterministic
    (Q : ℕ) (sigma : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ)
    (T epsilon X x : ℝ) :
    familyAlignedTailMajorant Q sigma T epsilon X x ≤
      familyAlignedLeftHorizontalMajorant Q sigma T epsilon X x +
        familyAlignedDeterministicMajorant Q T epsilon X x := by
  unfold familyAlignedTailMajorant familyAlignedLeftHorizontalMajorant
    familyAlignedDeterministicMajorant
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro q hq
  split_ifs with hq0
  · simp
  · letI : NeZero q := ⟨hq0⟩
    rw [← mul_add]
    gcongr
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro chi hchi
    letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
    exact alignedRemainderMaxSq_le_leftHorizontal_add_deterministic
      chi (sigma q chi) T epsilon X x

/-- Weakest source-faithful analytic AP tail contract: left and horizontal
contour windows remain signed and joint. -/
def AlignedLeftHorizontalFamilySquare : Prop :=
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
                familyAlignedLeftHorizontalMajorant Q sigma T epsilon X x) ≤
              ENNReal.ofReal (C * X * Real.rpow (Real.log X) (-A))

/-- The joint signed left/horizontal estimate is the sole remaining analytic
source for the direct aligned tail. -/
theorem alignedTailFamilySquare_of_leftHorizontalFamilySquare
    (hLH : AlignedLeftHorizontalFamilySquare) :
    AlignedAPExplicitFormulaTailFamilySquare := by
  intro K A epsilon hK hA hepsilon hepsilonCap
  rcases hLH K A epsilon hK hA hepsilon hepsilonCap with
    ⟨CL, XL, hCL, hXL, hL⟩
  rcases alignedDeterministicFamilyEnvelopeSquare K A epsilon
      hK hA hepsilon hepsilonCap with ⟨CD, XD, hCD, hXD, hD⟩
  let C := CL + CD
  let X0 := max (max XL XD) (Real.exp 1)
  refine ⟨C, X0, by dsimp only [C]; linarith,
    hXL.trans ((le_max_left XL XD).trans (le_max_left _ _)), ?_⟩
  intro X hXX0
  have hXLX : XL ≤ X :=
    ((le_max_left XL XD).trans (le_max_left _ _)).trans hXX0
  have hXDX : XD ≤ X :=
    ((le_max_right XL XD).trans (le_max_left _ _)).trans hXX0
  have hLx := hL X hXLX
  have hDx := hD X hXDX
  dsimp only at hLx hDx ⊢
  rcases hLx with ⟨T, hT, sigma, hlegal, hLbound⟩
  refine ⟨T, hT, sigma, hlegal, ?_⟩
  have hDbound := hDx T hT
  let Q := ⌊Real.rpow (Real.log X) K⌋₊
  let BD : ℝ≥0∞ :=
    (Q : ℝ≥0∞) * ENNReal.ofReal
      (8 * (alignedDeterministicEnvelope Q T epsilon X) ^ 2)
  have hX : Real.exp 1 ≤ X :=
    (le_max_right (max XL XD) (Real.exp 1)).trans hXX0
  have hT0 : 0 < T := (Real.rpow_pos_of_pos
    ((Real.exp_pos 1).trans_le hX) _).trans hT.1
  have hdetPoint : ∀ x ∈ Set.Icc (X / 2) (4 * X),
      familyAlignedDeterministicMajorant Q T epsilon X x ≤ BD := by
    intro x hx
    exact familyAlignedDeterministicMajorant_le hX hT0 hepsilon hx
  have htailInt :
      (∫⁻ x in Set.Icc (X / 2) (4 * X),
          familyAlignedTailMajorant Q sigma T epsilon X x) ≤
        (∫⁻ x in Set.Icc (X / 2) (4 * X),
          familyAlignedLeftHorizontalMajorant Q sigma T epsilon X x) +
          BD * ENNReal.ofReal (7 * X / 2) := by
    calc
      (∫⁻ x in Set.Icc (X / 2) (4 * X),
          familyAlignedTailMajorant Q sigma T epsilon X x) ≤
        ∫⁻ x in Set.Icc (X / 2) (4 * X),
          (familyAlignedLeftHorizontalMajorant Q sigma T epsilon X x + BD) := by
            apply MeasureTheory.setLIntegral_mono' measurableSet_Icc
            intro x hx
            exact (familyAlignedTailMajorant_le_leftHorizontal_add_deterministic
              Q sigma T epsilon X x).trans
                (add_le_add_right (hdetPoint x hx) _)
      _ = (∫⁻ x in Set.Icc (X / 2) (4 * X),
          familyAlignedLeftHorizontalMajorant Q sigma T epsilon X x) +
          (∫⁻ _x in Set.Icc (X / 2) (4 * X), BD) := by
            exact MeasureTheory.lintegral_add_right _ measurable_const
      _ = (∫⁻ x in Set.Icc (X / 2) (4 * X),
          familyAlignedLeftHorizontalMajorant Q sigma T epsilon X x) +
          BD * ENNReal.ofReal (7 * X / 2) := by
            congr 1
            rw [MeasureTheory.setLIntegral_const, Real.volume_Icc]
            congr 2
            ring
  apply htailInt.trans
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlog0 : 0 < Real.log X :=
    Real.log_pos ((Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hX)
  have htermL0 : 0 ≤ CL * X * Real.rpow (Real.log X) (-A) := by
    exact mul_nonneg (mul_nonneg hCL.le hX0.le)
      (Real.rpow_nonneg hlog0.le _)
  have htermD0 : 0 ≤ CD * X * Real.rpow (Real.log X) (-A) := by
    exact mul_nonneg (mul_nonneg hCD.le hX0.le)
      (Real.rpow_nonneg hlog0.le _)
  calc
    (∫⁻ x in Set.Icc (X / 2) (4 * X),
        familyAlignedLeftHorizontalMajorant Q sigma T epsilon X x) +
        BD * ENNReal.ofReal (7 * X / 2) ≤
      ENNReal.ofReal (CL * X * Real.rpow (Real.log X) (-A)) +
        ENNReal.ofReal (CD * X * Real.rpow (Real.log X) (-A)) :=
          add_le_add hLbound hDbound
    _ = ENNReal.ofReal ((CL + CD) * X *
        Real.rpow (Real.log X) (-A)) := by
      rw [← ENNReal.ofReal_add htermL0 htermD0]
      congr 2
      ring
    _ = ENNReal.ofReal (C * X * Real.rpow (Real.log X) (-A)) := rfl

end
end MAPAPDirectAlignedTailClosure

#print axioms MAPAPDirectAlignedTailClosure.alignedRemainderWindowSq_le_leftHorizontal_add_deterministic
#print axioms MAPAPDirectAlignedTailClosure.alignedRemainderMaxSq_le_leftHorizontal_add_deterministic
#print axioms MAPAPDirectAlignedTailClosure.familyAlignedTailMajorant_le_leftHorizontal_add_deterministic
