import MRTWholeLineOffDiagonalAmplitude

/-!
# Source-size L1 budgets for the whole-line MRT amplitude

The translated whole-line cutoff autocorrelation is differentiated only after
the common-shift change of variables.  Consequently its derivatives are
uniform on their support and no `X / H` boundary term occurs.  The outer
cutoffs confine both logarithmic variables to `(-100,100)`.
-/

namespace MAPMRTWholeLineOffDiagonalAmplitudeL1

open MeasureTheory Set
open MAPMRTWholeLineOffDiagonalAmplitude

noncomputable section

private theorem abs_packetWeight_mul_supportedPair_le
    {H h w Bf Bg : ℝ} {f g : ℝ → ℝ}
    (hH : 0 ≤ H) (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg)
    (hfsupport : ∀ y, 1 ≤ |y| → f y = 0)
    (hgsupport : ∀ y, 1 ≤ |y| → g y = 0)
    (hfbound : ∀ y, |f y| ≤ Bf)
    (hgbound : ∀ y, |g y| ≤ Bg) :
    |wholeLinePacketWeight H h w *
        (f (w / 100) * g ((w + h) / 100))| ≤
      H * Real.exp 100 * (Bf * Bg) := by
  by_cases hf : f (w / 100) = 0
  · simp [hf]
    positivity
  by_cases hg : g ((w + h) / 100) = 0
  · simp [hg]
    positivity
  have hfw : |w / 100| < 1 := by
    by_contra hn
    exact hf (hfsupport _ (le_of_not_gt hn))
  have hgw : |(w + h) / 100| < 1 := by
    by_contra hn
    exact hg (hgsupport _ (le_of_not_gt hn))
  have hw : w ≤ 100 := by
    have := (abs_lt.mp hfw).2
    norm_num at this ⊢
    linarith
  have hwh : w + h ≤ 100 := by
    have := (abs_lt.mp hgw).2
    norm_num at this ⊢
    linarith
  have hexp : Real.exp (w / 2) * Real.exp ((w + h) / 2) ≤ Real.exp 100 := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  unfold wholeLinePacketWeight
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hH,
    abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  calc
    H * Real.exp (w / 2) * Real.exp ((w + h) / 2) *
          (|f (w / 100)| * |g ((w + h) / 100)|) =
        H * (Real.exp (w / 2) * Real.exp ((w + h) / 2)) *
          (|f (w / 100)| * |g ((w + h) / 100)|) := by ring
    _ ≤ H * Real.exp 100 *
          (|f (w / 100)| * |g ((w + h) / 100)|) := by
      gcongr
    _ ≤ H * Real.exp 100 * (Bf * Bg) := by
      gcongr
      · exact hfbound _
      · exact hgbound _

theorem abs_packetWeight_mul_outerProduct_le
    {H h w : ℝ} {outer : ℝ → ℝ}
    (hH : 0 ≤ H)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (houterBound : ∀ y, |outer y| ≤ 1) :
    |wholeLinePacketWeight H h w * wholeLineOuterProduct outer h w| ≤
      H * Real.exp 100 := by
  unfold wholeLineOuterProduct
  simpa using abs_packetWeight_mul_supportedPair_le
    (H := H) (h := h) (w := w) (Bf := 1) (Bg := 1)
    hH (by norm_num) (by norm_num) houterSupport houterSupport
    houterBound houterBound

theorem abs_packetWeight_mul_outerProductDeriv_le
    {H h w B1 : ℝ} {outer outer' : ℝ → ℝ}
    (hH : 0 ≤ H) (hB1 : 0 ≤ B1)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (houter'Support : ∀ y, 1 ≤ |y| → outer' y = 0)
    (houterBound : ∀ y, |outer y| ≤ 1)
    (houter'Bound : ∀ y, |outer' y| ≤ B1) :
    |wholeLinePacketWeight H h w *
        wholeLineOuterProductDeriv outer outer' h w| ≤
      H * Real.exp 100 * (B1 / 50) := by
  have hleft := abs_packetWeight_mul_supportedPair_le
    (H := H) (h := h) (w := w) (Bf := B1) (Bg := 1)
    hH hB1 (by norm_num) houter'Support houterSupport
    houter'Bound houterBound
  have hright := abs_packetWeight_mul_supportedPair_le
    (H := H) (h := h) (w := w) (Bf := 1) (Bg := B1)
    hH (by norm_num) hB1 houterSupport houter'Support
    houterBound houter'Bound
  unfold wholeLineOuterProductDeriv
  let W := wholeLinePacketWeight H h w
  let a := outer' (w / 100)
  let b := outer ((w + h) / 100)
  let c := outer (w / 100)
  let d := outer' ((w + h) / 100)
  change |W * (a / 100 * b + c * (d / 100))| ≤ _
  have hleft' : |W * (a * b)| ≤ H * Real.exp 100 * (B1 * 1) := by
    simpa [W, a, b] using hleft
  have hright' : |W * (c * d)| ≤ H * Real.exp 100 * (1 * B1) := by
    simpa [W, c, d] using hright
  calc
    |W * (a / 100 * b + c * (d / 100))| =
        |W * (a * b) / 100 + W * (c * d) / 100| := by congr 1 <;> ring
    _ ≤ |W * (a * b) / 100| + |W * (c * d) / 100| := abs_add_le _ _
    _ = |W * (a * b)| / 100 + |W * (c * d)| / 100 := by
      rw [abs_div, abs_div]
      norm_num
    _ ≤ (H * Real.exp 100 * (B1 * 1)) / 100 +
        (H * Real.exp 100 * (1 * B1)) / 100 := by gcongr
    _ = H * Real.exp 100 * (B1 / 50) := by ring

theorem abs_packetWeight_mul_outerProductSecond_le
    {H h w B1 B2 : ℝ} {outer outer' outer'' : ℝ → ℝ}
    (hH : 0 ≤ H) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (houter'Support : ∀ y, 1 ≤ |y| → outer' y = 0)
    (houter''Support : ∀ y, 1 ≤ |y| → outer'' y = 0)
    (houterBound : ∀ y, |outer y| ≤ 1)
    (houter'Bound : ∀ y, |outer' y| ≤ B1)
    (houter''Bound : ∀ y, |outer'' y| ≤ B2) :
    |wholeLinePacketWeight H h w *
        wholeLineOuterProductSecond outer outer' outer'' h w| ≤
      H * Real.exp 100 * ((B2 + B1 ^ 2) / 5000) := by
  have ht1 := abs_packetWeight_mul_supportedPair_le
    (H := H) (h := h) (w := w) (Bf := B2) (Bg := 1)
    hH hB2 (by norm_num) houter''Support houterSupport
    houter''Bound houterBound
  have ht2 := abs_packetWeight_mul_supportedPair_le
    (H := H) (h := h) (w := w) (Bf := B1) (Bg := B1)
    hH hB1 hB1 houter'Support houter'Support
    houter'Bound houter'Bound
  have ht3 := abs_packetWeight_mul_supportedPair_le
    (H := H) (h := h) (w := w) (Bf := 1) (Bg := B2)
    hH (by norm_num) hB2 houterSupport houter''Support
    houterBound houter''Bound
  unfold wholeLineOuterProductSecond
  let W := wholeLinePacketWeight H h w
  let a := outer'' (w / 100)
  let b := outer ((w + h) / 100)
  let c := outer' (w / 100)
  let d := outer' ((w + h) / 100)
  let e := outer (w / 100)
  let f := outer'' ((w + h) / 100)
  change |W * (a / 10000 * b + 2 * (c / 100) * (d / 100) +
    e * (f / 10000))| ≤ _
  have ht1' : |W * (a * b)| ≤ H * Real.exp 100 * (B2 * 1) := by
    simpa [W, a, b] using ht1
  have ht2' : |W * (c * d)| ≤ H * Real.exp 100 * (B1 * B1) := by
    simpa [W, c, d] using ht2
  have ht3' : |W * (e * f)| ≤ H * Real.exp 100 * (1 * B2) := by
    simpa [W, e, f] using ht3
  calc
    |W * (a / 10000 * b + 2 * (c / 100) * (d / 100) +
        e * (f / 10000))| =
      |W * (a * b) / 10000 + 2 * (W * (c * d)) / 10000 +
        W * (e * f) / 10000| := by congr 1 <;> ring
    _ ≤ |W * (a * b) / 10000| + |2 * (W * (c * d)) / 10000| +
        |W * (e * f) / 10000| := abs_add_three _ _ _
    _ = |W * (a * b)| / 10000 + 2 * |W * (c * d)| / 10000 +
        |W * (e * f)| / 10000 := by
      simp only [abs_div, abs_mul]
      norm_num
    _ ≤ (H * Real.exp 100 * (B2 * 1)) / 10000 +
        2 * (H * Real.exp 100 * (B1 * B1)) / 10000 +
        (H * Real.exp 100 * (1 * B2)) / 10000 := by gcongr
    _ = H * Real.exp 100 * ((B2 + B1 ^ 2) / 5000) := by ring

private theorem abs_weight_mul_coeff_product_le
    {W K O CK CO : ℝ} (hCK : 0 ≤ CK)
    (hK : |K| ≤ CK) (hWO : |W * O| ≤ CO) :
    |W * (K * O)| ≤ CK * CO := by
  calc
    |W * (K * O)| = |K| * |W * O| := by
      rw [abs_mul, abs_mul, abs_mul]
      ring
    _ ≤ CK * CO := mul_le_mul hK hWO (abs_nonneg _) hCK

private theorem abs_add_five (a b c d e : ℝ) :
    |a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  calc
    |a + b + c + d + e| ≤ |a + b + c + d| + |e| := abs_add_le _ _
    _ ≤ (|a + b + c| + |d|) + |e| := by gcongr <;> exact abs_add_le _ _
    _ ≤ ((|a + b| + |c|) + |d|) + |e| := by gcongr <;> exact abs_add_le _ _
    _ ≤ (((|a| + |b|) + |c|) + |d|) + |e| := by gcongr <;> exact abs_add_le _ _
    _ = |a| + |b| + |c| + |d| + |e| := by ring

theorem abs_wholeLineOffDiagonalAmplitude_le
    {X H h w : ℝ} {cutoff outer : ℝ → ℝ}
    (hH : 0 ≤ H)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (houterBound : ∀ y, |outer y| ≤ 1) :
    |wholeLineOffDiagonalAmplitude X H cutoff outer h w| ≤
      H * Real.exp 100 * 2 := by
  have hK := abs_wholeLineCorrelationAlong_le_two
    (X := X) (H := H) (h := h) (w := w) hcutoffBound
  have hWO := abs_packetWeight_mul_outerProduct_le
    (H := H) (h := h) (w := w) hH houterSupport houterBound
  unfold wholeLineOffDiagonalAmplitude
  exact (abs_weight_mul_coeff_product_le (by norm_num) hK hWO).trans_eq (by ring)

theorem abs_wholeLineOffDiagonalAmplitudeDeriv_le
    {X H h w Bc1 Bo1 : ℝ}
    {cutoff cutoff' outer outer' : ℝ → ℝ}
    (hH : 0 ≤ H) (hBc1 : 0 ≤ Bc1) (hBo1 : 0 ≤ Bo1)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff'Support : ∀ y, 1 ≤ |y| → cutoff' y = 0)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (hcutoff'Bound : ∀ y, |cutoff' y| ≤ Bc1)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (houter'Support : ∀ y, 1 ≤ |y| → outer' y = 0)
    (houterBound : ∀ y, |outer y| ≤ 1)
    (houter'Bound : ∀ y, |outer' y| ≤ Bo1) :
    |wholeLineOffDiagonalAmplitudeDeriv X H cutoff cutoff' outer outer' h w| ≤
      H * Real.exp 100 * (2 + 4 * Bc1 + Bo1 / 25) := by
  let W := wholeLinePacketWeight H h w
  let K := wholeLineCorrelationAlong X H cutoff h w
  let K1 := wholeLineCorrelationAlongDeriv X H cutoff cutoff' h w
  let O := wholeLineOuterProduct outer h w
  let O1 := wholeLineOuterProductDeriv outer outer' h w
  have hK : |K| ≤ 2 := by
    exact abs_wholeLineCorrelationAlong_le_two hcutoffBound
  have hK1 : |K1| ≤ 4 * Bc1 := by
    exact abs_wholeLineCorrelationAlongDeriv_le hBc1 hcutoffSupport
      hcutoff'Support hcutoffBound hcutoff'Bound
  have hWO : |W * O| ≤ H * Real.exp 100 := by
    exact abs_packetWeight_mul_outerProduct_le hH houterSupport houterBound
  have hWO1 : |W * O1| ≤ H * Real.exp 100 * (Bo1 / 50) := by
    exact abs_packetWeight_mul_outerProductDeriv_le hH hBo1 houterSupport
      houter'Support houterBound houter'Bound
  have ht0 : |W * (K * O)| ≤ 2 * (H * Real.exp 100) :=
    abs_weight_mul_coeff_product_le (by norm_num) hK hWO
  have ht1 : |W * (K1 * O)| ≤ (4 * Bc1) * (H * Real.exp 100) :=
    abs_weight_mul_coeff_product_le (by positivity) hK1 hWO
  have ht2 : |W * (K * O1)| ≤ 2 * (H * Real.exp 100 * (Bo1 / 50)) :=
    abs_weight_mul_coeff_product_le (by norm_num) hK hWO1
  unfold wholeLineOffDiagonalAmplitudeDeriv
  change |W * (K * O + K1 * O + K * O1)| ≤ _
  calc
    |W * (K * O + K1 * O + K * O1)| =
        |W * (K * O) + W * (K1 * O) + W * (K * O1)| := by congr 1 <;> ring
    _ ≤ |W * (K * O)| + |W * (K1 * O)| + |W * (K * O1)| := abs_add_three _ _ _
    _ ≤ 2 * (H * Real.exp 100) + (4 * Bc1) * (H * Real.exp 100) +
        2 * (H * Real.exp 100 * (Bo1 / 50)) := by gcongr
    _ = H * Real.exp 100 * (2 + 4 * Bc1 + Bo1 / 25) := by ring

theorem abs_wholeLineOffDiagonalAmplitudeSecond_le
    {X H h w Bc1 Bc2 Bo1 Bo2 : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hH : 0 ≤ H) (hBc1 : 0 ≤ Bc1) (hBc2 : 0 ≤ Bc2)
    (hBo1 : 0 ≤ Bo1) (hBo2 : 0 ≤ Bo2)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff'Support : ∀ y, 1 ≤ |y| → cutoff' y = 0)
    (hcutoff''Support : ∀ y, 1 ≤ |y| → cutoff'' y = 0)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (hcutoff'Bound : ∀ y, |cutoff' y| ≤ Bc1)
    (hcutoff''Bound : ∀ y, |cutoff'' y| ≤ Bc2)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (houter'Support : ∀ y, 1 ≤ |y| → outer' y = 0)
    (houter''Support : ∀ y, 1 ≤ |y| → outer'' y = 0)
    (houterBound : ∀ y, |outer y| ≤ 1)
    (houter'Bound : ∀ y, |outer' y| ≤ Bo1)
    (houter''Bound : ∀ y, |outer'' y| ≤ Bo2) :
    |wholeLineOffDiagonalAmplitudeSecond X H cutoff cutoff' cutoff''
        outer outer' outer'' h w| ≤
      H * Real.exp 100 *
        (2 + 12 * Bc1 + 8 * Bc2 + 2 * Bo1 / 25 +
          4 * Bc1 * Bo1 / 25 + (Bo2 + Bo1 ^ 2) / 2500) := by
  let W := wholeLinePacketWeight H h w
  let K := wholeLineCorrelationAlong X H cutoff h w
  let K1 := wholeLineCorrelationAlongDeriv X H cutoff cutoff' h w
  let K2 := wholeLineCorrelationAlongSecond X H cutoff cutoff' cutoff'' h w
  let O := wholeLineOuterProduct outer h w
  let O1 := wholeLineOuterProductDeriv outer outer' h w
  let O2 := wholeLineOuterProductSecond outer outer' outer'' h w
  have hK : |K| ≤ 2 := abs_wholeLineCorrelationAlong_le_two hcutoffBound
  have hK1 : |K1| ≤ 4 * Bc1 := abs_wholeLineCorrelationAlongDeriv_le
    hBc1 hcutoffSupport hcutoff'Support hcutoffBound hcutoff'Bound
  have hK2 : |K2| ≤ 8 * Bc2 + 4 * Bc1 :=
    abs_wholeLineCorrelationAlongSecond_le hBc1 hBc2 hcutoffSupport
      hcutoff'Support hcutoff''Support hcutoffBound hcutoff'Bound hcutoff''Bound
  have hWO : |W * O| ≤ H * Real.exp 100 :=
    abs_packetWeight_mul_outerProduct_le hH houterSupport houterBound
  have hWO1 : |W * O1| ≤ H * Real.exp 100 * (Bo1 / 50) :=
    abs_packetWeight_mul_outerProductDeriv_le hH hBo1 houterSupport
      houter'Support houterBound houter'Bound
  have hWO2 : |W * O2| ≤ H * Real.exp 100 * ((Bo2 + Bo1 ^ 2) / 5000) :=
    abs_packetWeight_mul_outerProductSecond_le hH hBo1 hBo2 houterSupport
      houter'Support houter''Support houterBound houter'Bound houter''Bound
  have ht0 : |W * (K * O)| ≤ 2 * (H * Real.exp 100) :=
    abs_weight_mul_coeff_product_le (by norm_num) hK hWO
  have ht1 : |W * (K1 * O)| ≤ (4 * Bc1) * (H * Real.exp 100) :=
    abs_weight_mul_coeff_product_le (by positivity) hK1 hWO
  have ht2 : |W * (K * O1)| ≤ 2 * (H * Real.exp 100 * (Bo1 / 50)) :=
    abs_weight_mul_coeff_product_le (by norm_num) hK hWO1
  have ht3 : |W * (K2 * O)| ≤ (8 * Bc2 + 4 * Bc1) * (H * Real.exp 100) :=
    abs_weight_mul_coeff_product_le (by positivity) hK2 hWO
  have ht4 : |W * (K1 * O1)| ≤
      (4 * Bc1) * (H * Real.exp 100 * (Bo1 / 50)) :=
    abs_weight_mul_coeff_product_le (by positivity) hK1 hWO1
  have ht5 : |W * (K * O2)| ≤
      2 * (H * Real.exp 100 * ((Bo2 + Bo1 ^ 2) / 5000)) :=
    abs_weight_mul_coeff_product_le (by norm_num) hK hWO2
  have htail : |2 * W * (K1 * O1) + W * (K * O2)| ≤
      2 * |W * (K1 * O1)| + |W * (K * O2)| := by
    calc
      _ ≤ |2 * W * (K1 * O1)| + |W * (K * O2)| := abs_add_le _ _
      _ = 2 * |W * (K1 * O1)| + |W * (K * O2)| := by
        rw [abs_mul, abs_mul]
        norm_num
        ring
  have h2t1 : |2 * W * (K1 * O)| = 2 * |W * (K1 * O)| := by
    rw [abs_mul, abs_mul]
    norm_num
    ring
  have h2t2 : |2 * W * (K * O1)| = 2 * |W * (K * O1)| := by
    rw [abs_mul, abs_mul]
    norm_num
    ring
  unfold wholeLineOffDiagonalAmplitudeSecond
  change |W * (K * O + 2 * (K1 * O + K * O1) + K2 * O +
    2 * K1 * O1 + K * O2)| ≤ _
  calc
    |W * (K * O + 2 * (K1 * O + K * O1) + K2 * O +
        2 * K1 * O1 + K * O2)| =
      |W * (K * O) + 2 * W * (K1 * O) + 2 * W * (K * O1) +
        W * (K2 * O) + (2 * W * (K1 * O1) + W * (K * O2))| := by
        congr 1 <;> ring
    _ ≤ |W * (K * O)| + |2 * W * (K1 * O)| + |2 * W * (K * O1)| +
        |W * (K2 * O)| + |2 * W * (K1 * O1) + W * (K * O2)| :=
      abs_add_five _ _ _ _ _
    _ ≤ |W * (K * O)| + 2 * |W * (K1 * O)| + 2 * |W * (K * O1)| +
        |W * (K2 * O)| + (2 * |W * (K1 * O1)| + |W * (K * O2)|) := by
      rw [h2t1, h2t2]
      gcongr
    _ ≤ 2 * (H * Real.exp 100) +
        2 * ((4 * Bc1) * (H * Real.exp 100)) +
        2 * (2 * (H * Real.exp 100 * (Bo1 / 50))) +
        (8 * Bc2 + 4 * Bc1) * (H * Real.exp 100) +
        (2 * ((4 * Bc1) * (H * Real.exp 100 * (Bo1 / 50))) +
          2 * (H * Real.exp 100 * ((Bo2 + Bo1 ^ 2) / 5000))) := by gcongr
    _ = H * Real.exp 100 *
        (2 + 12 * Bc1 + 8 * Bc2 + 2 * Bo1 / 25 +
          4 * Bc1 * Bo1 / 25 + (Bo2 + Bo1 ^ 2) / 2500) := by ring

/-! ## Exact outer support and endpoint conventions -/

private theorem one_le_abs_div_hundred {w : ℝ} (hw : 100 ≤ |w|) :
    1 ≤ |w / 100| := by
  rw [abs_div]
  norm_num
  linarith

theorem wholeLineOffDiagonalAmplitude_eq_zero_of_left_outer_support
    {X H h w : ℝ} {cutoff outer : ℝ → ℝ}
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (hw : 100 ≤ |w|) :
    wholeLineOffDiagonalAmplitude X H cutoff outer h w = 0 := by
  have hz := houterSupport (w / 100) (one_le_abs_div_hundred hw)
  simp [wholeLineOffDiagonalAmplitude, wholeLineOuterProduct, hz]

theorem wholeLineOffDiagonalAmplitudeDeriv_eq_zero_of_left_outer_support
    {X H h w : ℝ} {cutoff cutoff' outer outer' : ℝ → ℝ}
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (houter'Support : ∀ y, 1 ≤ |y| → outer' y = 0)
    (hw : 100 ≤ |w|) :
    wholeLineOffDiagonalAmplitudeDeriv X H cutoff cutoff' outer outer' h w = 0 := by
  have ha := one_le_abs_div_hundred hw
  have hz := houterSupport (w / 100) ha
  have hz' := houter'Support (w / 100) ha
  simp [wholeLineOffDiagonalAmplitudeDeriv, wholeLineOuterProduct,
    wholeLineOuterProductDeriv, hz, hz']

theorem wholeLineOffDiagonalAmplitudeSecond_eq_zero_of_left_outer_support
    {X H h w : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (houter'Support : ∀ y, 1 ≤ |y| → outer' y = 0)
    (houter''Support : ∀ y, 1 ≤ |y| → outer'' y = 0)
    (hw : 100 ≤ |w|) :
    wholeLineOffDiagonalAmplitudeSecond X H cutoff cutoff' cutoff''
      outer outer' outer'' h w = 0 := by
  have ha := one_le_abs_div_hundred hw
  have hz := houterSupport (w / 100) ha
  have hz' := houter'Support (w / 100) ha
  have hz'' := houter''Support (w / 100) ha
  simp [wholeLineOffDiagonalAmplitudeSecond, wholeLineOuterProduct,
    wholeLineOuterProductDeriv, wholeLineOuterProductSecond, hz, hz', hz'']

theorem wholeLineOffDiagonalAmplitude_eq_zero_of_right_outer_support
    {X H h w : ℝ} {cutoff outer : ℝ → ℝ}
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (hwh : 100 ≤ |w + h|) :
    wholeLineOffDiagonalAmplitude X H cutoff outer h w = 0 := by
  have hz := houterSupport ((w + h) / 100) (one_le_abs_div_hundred hwh)
  simp [wholeLineOffDiagonalAmplitude, wholeLineOuterProduct, hz]

theorem wholeLineOffDiagonalAmplitudeDeriv_eq_zero_of_right_outer_support
    {X H h w : ℝ} {cutoff cutoff' outer outer' : ℝ → ℝ}
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (houter'Support : ∀ y, 1 ≤ |y| → outer' y = 0)
    (hwh : 100 ≤ |w + h|) :
    wholeLineOffDiagonalAmplitudeDeriv X H cutoff cutoff' outer outer' h w = 0 := by
  have ha := one_le_abs_div_hundred hwh
  have hz := houterSupport ((w + h) / 100) ha
  have hz' := houter'Support ((w + h) / 100) ha
  simp [wholeLineOffDiagonalAmplitudeDeriv, wholeLineOuterProduct,
    wholeLineOuterProductDeriv, hz, hz']

theorem wholeLineOffDiagonalAmplitudeSecond_eq_zero_of_right_outer_support
    {X H h w : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (houter'Support : ∀ y, 1 ≤ |y| → outer' y = 0)
    (houter''Support : ∀ y, 1 ≤ |y| → outer'' y = 0)
    (hwh : 100 ≤ |w + h|) :
    wholeLineOffDiagonalAmplitudeSecond X H cutoff cutoff' cutoff''
      outer outer' outer'' h w = 0 := by
  have ha := one_le_abs_div_hundred hwh
  have hz := houterSupport ((w + h) / 100) ha
  have hz' := houter'Support ((w + h) / 100) ha
  have hz'' := houter''Support ((w + h) / 100) ha
  simp [wholeLineOffDiagonalAmplitudeSecond, wholeLineOuterProduct,
    wholeLineOuterProductDeriv, wholeLineOuterProductSecond, hz, hz', hz'']

theorem wholeLineOffDiagonalAmplitude_endpoints
    {X H h : ℝ} {cutoff outer : ℝ → ℝ}
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0) :
    wholeLineOffDiagonalAmplitude X H cutoff outer h (-100) = 0 ∧
      wholeLineOffDiagonalAmplitude X H cutoff outer h 100 = 0 := by
  constructor <;>
    apply wholeLineOffDiagonalAmplitude_eq_zero_of_left_outer_support houterSupport <;>
    norm_num

theorem wholeLineOffDiagonalAmplitudeDeriv_endpoints
    {X H h : ℝ} {cutoff cutoff' outer outer' : ℝ → ℝ}
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (houter'Support : ∀ y, 1 ≤ |y| → outer' y = 0) :
    wholeLineOffDiagonalAmplitudeDeriv X H cutoff cutoff' outer outer' h (-100) = 0 ∧
      wholeLineOffDiagonalAmplitudeDeriv X H cutoff cutoff' outer outer' h 100 = 0 := by
  constructor <;>
    apply wholeLineOffDiagonalAmplitudeDeriv_eq_zero_of_left_outer_support
      houterSupport houter'Support <;>
    norm_num

#print axioms abs_packetWeight_mul_supportedPair_le
#print axioms abs_packetWeight_mul_outerProductSecond_le
#print axioms abs_wholeLineOffDiagonalAmplitude_le
#print axioms abs_wholeLineOffDiagonalAmplitudeDeriv_le
#print axioms abs_wholeLineOffDiagonalAmplitudeSecond_le
#print axioms wholeLineOffDiagonalAmplitudeSecond_eq_zero_of_left_outer_support
#print axioms wholeLineOffDiagonalAmplitudeDeriv_endpoints

end
end MAPMRTWholeLineOffDiagonalAmplitudeL1
