import MRTWholeLineCutoffAutocorrelation

/-!
# The whole-line off-diagonal amplitude and its first two derivatives

This is the source amplitude on MRT p.50 after the legal whole-line extension
and the substitution `w' = w+h`.  The definitions keep the factor `H` from
the `x` change of variables inside the amplitude, so the three `L¹` budgets
below naturally have size `O(H)`.
-/

namespace MAPMRTWholeLineOffDiagonalAmplitude

open MeasureTheory Set
open MAPMRTWholeLineCutoffAutocorrelation

noncomputable section

def wholeLineCorrelationAlong
    (X H : ℝ) (cutoff : ℝ → ℝ) (h w : ℝ) : ℝ :=
  wholeLineCutoffAutocorrelation cutoff (wholeLinePacketShift X H h w)

def wholeLineCorrelationAlongDeriv
    (X H : ℝ) (cutoff cutoff' : ℝ → ℝ) (h w : ℝ) : ℝ :=
  wholeLineCutoffAutocorrelationDeriv cutoff cutoff'
      (wholeLinePacketShift X H h w) *
    wholeLinePacketShift X H h w

def wholeLineCorrelationAlongSecond
    (X H : ℝ) (cutoff cutoff' cutoff'' : ℝ → ℝ) (h w : ℝ) : ℝ :=
  wholeLineCutoffAutocorrelationSecond cutoff cutoff''
      (wholeLinePacketShift X H h w) *
      wholeLinePacketShift X H h w ^ 2 +
    wholeLineCutoffAutocorrelationDeriv cutoff cutoff'
      (wholeLinePacketShift X H h w) *
      wholeLinePacketShift X H h w

theorem hasDerivAt_wholeLineCorrelationAlong
    {X H h w B1 : ℝ} {cutoff cutoff' : ℝ → ℝ}
    (hcutoffCont : Continuous cutoff)
    (hcutoff'Cont : Continuous cutoff')
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (hcutoff'Bound : ∀ y, |cutoff' y| ≤ B1)
    (hcutoffDeriv : ∀ y, HasDerivAt cutoff (cutoff' y) y) :
    HasDerivAt (wholeLineCorrelationAlong X H cutoff h)
      (wholeLineCorrelationAlongDeriv X H cutoff cutoff' h w) w := by
  unfold wholeLineCorrelationAlong wholeLineCorrelationAlongDeriv
  simpa only [Function.comp_def] using!
    (hasDerivAt_wholeLineCutoffAutocorrelation hcutoffCont hcutoff'Cont
      hcutoffBound hcutoff'Bound hcutoffDeriv).comp w
        hasDerivAt_wholeLinePacketShift

theorem hasDerivAt_wholeLineCorrelationAlongDeriv
    {X H h w B1 B2 : ℝ} {cutoff cutoff' cutoff'' : ℝ → ℝ}
    (hcutoffCont : Continuous cutoff)
    (hcutoff'Cont : Continuous cutoff')
    (hcutoff''Cont : Continuous cutoff'')
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (hcutoff'Bound : ∀ y, |cutoff' y| ≤ B1)
    (hcutoff''Bound : ∀ y, |cutoff'' y| ≤ B2)
    (hcutoffDeriv : ∀ y, HasDerivAt cutoff (cutoff' y) y)
    (hcutoffSecond : ∀ y, HasDerivAt cutoff' (cutoff'' y) y) :
    HasDerivAt (wholeLineCorrelationAlongDeriv X H cutoff cutoff' h)
      (wholeLineCorrelationAlongSecond X H cutoff cutoff' cutoff'' h w) w := by
  let delta : ℝ → ℝ := wholeLinePacketShift X H h
  let C1 : ℝ → ℝ := wholeLineCutoffAutocorrelationDeriv cutoff cutoff'
  let C2 : ℝ → ℝ := wholeLineCutoffAutocorrelationSecond cutoff cutoff''
  have hd : HasDerivAt delta (delta w) w := hasDerivAt_wholeLinePacketShift
  have hC1 : HasDerivAt C1 (C2 (delta w)) (delta w) := by
    exact hasDerivAt_wholeLineCutoffAutocorrelationDeriv hcutoffCont
      hcutoff'Cont hcutoff''Cont hcutoffBound hcutoff''Bound hcutoffSecond
  have hcomp : HasDerivAt (fun z ↦ C1 (delta z))
      (C2 (delta w) * delta w) w := by
    simpa only [Function.comp_def] using! hC1.comp w hd
  have hprod := hcomp.mul hd
  unfold wholeLineCorrelationAlongDeriv wholeLineCorrelationAlongSecond
  change HasDerivAt (fun z ↦ C1 (delta z) * delta z) _ w
  convert hprod using 1 <;> unfold C1 C2 delta <;> ring

def wholeLineOuterProduct (outer : ℝ → ℝ) (h w : ℝ) : ℝ :=
  outer (w / 100) * outer ((w + h) / 100)

def wholeLineOuterProductDeriv
    (outer outer' : ℝ → ℝ) (h w : ℝ) : ℝ :=
  outer' (w / 100) / 100 * outer ((w + h) / 100) +
    outer (w / 100) * (outer' ((w + h) / 100) / 100)

def wholeLineOuterProductSecond
    (outer outer' outer'' : ℝ → ℝ) (h w : ℝ) : ℝ :=
  outer'' (w / 100) / 10000 * outer ((w + h) / 100) +
    2 * (outer' (w / 100) / 100) *
      (outer' ((w + h) / 100) / 100) +
    outer (w / 100) * (outer'' ((w + h) / 100) / 10000)

theorem hasDerivAt_wholeLineOuterProduct
    {h w : ℝ} {outer outer' : ℝ → ℝ}
    (houterDeriv : ∀ y, HasDerivAt outer (outer' y) y) :
    HasDerivAt (wholeLineOuterProduct outer h)
      (wholeLineOuterProductDeriv outer outer' h w) w := by
  unfold wholeLineOuterProduct wholeLineOuterProductDeriv
  have hleft := (houterDeriv (w / 100)).scomp w
    ((hasDerivAt_id w).div_const 100)
  have hright := (houterDeriv ((w + h) / 100)).scomp w
    (((hasDerivAt_id w).add_const h).div_const 100)
  convert hleft.mul hright using 1 <;>
    (try funext z) <;>
    simp only [Function.comp_def, Pi.mul_apply, id_eq, smul_eq_mul] <;> ring

theorem hasDerivAt_wholeLineOuterProductDeriv
    {h w : ℝ} {outer outer' outer'' : ℝ → ℝ}
    (houterDeriv : ∀ y, HasDerivAt outer (outer' y) y)
    (houterSecond : ∀ y, HasDerivAt outer' (outer'' y) y) :
    HasDerivAt (wholeLineOuterProductDeriv outer outer' h)
      (wholeLineOuterProductSecond outer outer' outer'' h w) w := by
  have hoL := (houterDeriv (w / 100)).scomp w
    ((hasDerivAt_id w).div_const 100)
  have hoR := (houterDeriv ((w + h) / 100)).scomp w
    (((hasDerivAt_id w).add_const h).div_const 100)
  have ho'L := (houterSecond (w / 100)).scomp w
    ((hasDerivAt_id w).div_const 100)
  have ho'R := (houterSecond ((w + h) / 100)).scomp w
    (((hasDerivAt_id w).add_const h).div_const 100)
  unfold wholeLineOuterProductDeriv wholeLineOuterProductSecond
  convert ((ho'L.div_const 100).mul hoR).add
    (hoL.mul (ho'R.div_const 100)) using 1 <;>
      (try funext z) <;>
      simp only [Function.comp_def, Pi.mul_apply, Pi.add_apply, id_eq, smul_eq_mul] <;> ring

def wholeLinePacketWeight (H h w : ℝ) : ℝ :=
  H * Real.exp (w / 2) * Real.exp ((w + h) / 2)

theorem hasDerivAt_wholeLinePacketWeight {H h w : ℝ} :
    HasDerivAt (wholeLinePacketWeight H h)
      (wholeLinePacketWeight H h w) w := by
  unfold wholeLinePacketWeight
  have hleft := (Real.hasDerivAt_exp (w / 2)).scomp w
    ((hasDerivAt_id w).div_const 2)
  have hright := (Real.hasDerivAt_exp ((w + h) / 2)).scomp w
    (((hasDerivAt_id w).add_const h).div_const 2)
  convert ((hleft.const_mul H).mul hright) using 1 <;>
    (try funext z) <;>
    simp only [Function.comp_def, Pi.mul_apply, id_eq, smul_eq_mul] <;> ring

def wholeLineOffDiagonalAmplitude
    (X H : ℝ) (cutoff outer : ℝ → ℝ) (h w : ℝ) : ℝ :=
  wholeLinePacketWeight H h w *
    (wholeLineCorrelationAlong X H cutoff h w *
      wholeLineOuterProduct outer h w)

def wholeLineOffDiagonalAmplitudeDeriv
    (X H : ℝ) (cutoff cutoff' outer outer' : ℝ → ℝ) (h w : ℝ) : ℝ :=
  wholeLinePacketWeight H h w *
    (wholeLineCorrelationAlong X H cutoff h w *
        wholeLineOuterProduct outer h w +
      wholeLineCorrelationAlongDeriv X H cutoff cutoff' h w *
        wholeLineOuterProduct outer h w +
      wholeLineCorrelationAlong X H cutoff h w *
        wholeLineOuterProductDeriv outer outer' h w)

def wholeLineOffDiagonalAmplitudeSecond
    (X H : ℝ)
    (cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ)
    (h w : ℝ) : ℝ :=
  wholeLinePacketWeight H h w *
    (wholeLineCorrelationAlong X H cutoff h w *
        wholeLineOuterProduct outer h w +
      2 * (wholeLineCorrelationAlongDeriv X H cutoff cutoff' h w *
          wholeLineOuterProduct outer h w +
        wholeLineCorrelationAlong X H cutoff h w *
          wholeLineOuterProductDeriv outer outer' h w) +
      wholeLineCorrelationAlongSecond X H cutoff cutoff' cutoff'' h w *
        wholeLineOuterProduct outer h w +
      2 * wholeLineCorrelationAlongDeriv X H cutoff cutoff' h w *
        wholeLineOuterProductDeriv outer outer' h w +
      wholeLineCorrelationAlong X H cutoff h w *
        wholeLineOuterProductSecond outer outer' outer'' h w)

theorem hasDerivAt_wholeLineOffDiagonalAmplitude
    {X H h w B1 : ℝ}
    {cutoff cutoff' outer outer' : ℝ → ℝ}
    (hcutoffCont : Continuous cutoff)
    (hcutoff'Cont : Continuous cutoff')
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (hcutoff'Bound : ∀ y, |cutoff' y| ≤ B1)
    (hcutoffDeriv : ∀ y, HasDerivAt cutoff (cutoff' y) y)
    (houterDeriv : ∀ y, HasDerivAt outer (outer' y) y) :
    HasDerivAt (wholeLineOffDiagonalAmplitude X H cutoff outer h)
      (wholeLineOffDiagonalAmplitudeDeriv X H cutoff cutoff' outer outer' h w) w := by
  let W := wholeLinePacketWeight H h
  let K := wholeLineCorrelationAlong X H cutoff h
  let K1 := wholeLineCorrelationAlongDeriv X H cutoff cutoff' h
  let O := wholeLineOuterProduct outer h
  let O1 := wholeLineOuterProductDeriv outer outer' h
  have hW : HasDerivAt W (W w) w := hasDerivAt_wholeLinePacketWeight
  have hK : HasDerivAt K (K1 w) w :=
    hasDerivAt_wholeLineCorrelationAlong hcutoffCont hcutoff'Cont
      hcutoffBound hcutoff'Bound hcutoffDeriv
  have hO : HasDerivAt O (O1 w) w :=
    hasDerivAt_wholeLineOuterProduct houterDeriv
  unfold wholeLineOffDiagonalAmplitude wholeLineOffDiagonalAmplitudeDeriv
  change HasDerivAt (fun z ↦ W z * (K z * O z)) _ w
  convert hW.mul (hK.mul hO) using 1 <;>
    unfold W K K1 O O1 <;>
    simp only [Function.comp_apply, Pi.mul_apply] <;> ring

theorem hasDerivAt_wholeLineOffDiagonalAmplitudeDeriv
    {X H h w B1 B2 : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hcutoffCont : Continuous cutoff)
    (hcutoff'Cont : Continuous cutoff')
    (hcutoff''Cont : Continuous cutoff'')
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (hcutoff'Bound : ∀ y, |cutoff' y| ≤ B1)
    (hcutoff''Bound : ∀ y, |cutoff'' y| ≤ B2)
    (hcutoffDeriv : ∀ y, HasDerivAt cutoff (cutoff' y) y)
    (hcutoffSecond : ∀ y, HasDerivAt cutoff' (cutoff'' y) y)
    (houterDeriv : ∀ y, HasDerivAt outer (outer' y) y)
    (houterSecond : ∀ y, HasDerivAt outer' (outer'' y) y) :
    HasDerivAt
      (wholeLineOffDiagonalAmplitudeDeriv X H cutoff cutoff' outer outer' h)
      (wholeLineOffDiagonalAmplitudeSecond X H cutoff cutoff' cutoff''
        outer outer' outer'' h w) w := by
  let W := wholeLinePacketWeight H h
  let K := wholeLineCorrelationAlong X H cutoff h
  let K1 := wholeLineCorrelationAlongDeriv X H cutoff cutoff' h
  let K2 := wholeLineCorrelationAlongSecond X H cutoff cutoff' cutoff'' h
  let O := wholeLineOuterProduct outer h
  let O1 := wholeLineOuterProductDeriv outer outer' h
  let O2 := wholeLineOuterProductSecond outer outer' outer'' h
  have hW : HasDerivAt W (W w) w := hasDerivAt_wholeLinePacketWeight
  have hK : HasDerivAt K (K1 w) w :=
    hasDerivAt_wholeLineCorrelationAlong hcutoffCont hcutoff'Cont
      hcutoffBound hcutoff'Bound hcutoffDeriv
  have hK1 : HasDerivAt K1 (K2 w) w :=
    hasDerivAt_wholeLineCorrelationAlongDeriv hcutoffCont hcutoff'Cont
      hcutoff''Cont hcutoffBound hcutoff'Bound hcutoff''Bound
      hcutoffDeriv hcutoffSecond
  have hO : HasDerivAt O (O1 w) w :=
    hasDerivAt_wholeLineOuterProduct houterDeriv
  have hO1 : HasDerivAt O1 (O2 w) w :=
    hasDerivAt_wholeLineOuterProductDeriv houterDeriv houterSecond
  unfold wholeLineOffDiagonalAmplitudeDeriv wholeLineOffDiagonalAmplitudeSecond
  change HasDerivAt (fun z ↦ W z *
    (K z * O z + K1 z * O z + K z * O1 z)) _ w
  convert hW.mul (((hK.mul hO).add (hK1.mul hO)).add (hK.mul hO1))
    using 1 <;> unfold W K K1 K2 O O1 O2 <;>
      simp only [Function.comp_apply, Pi.mul_apply, Pi.add_apply] <;> ring

/-! ## Uniform component bounds: the common shift costs no `X/H` -/

theorem abs_wholeLineCorrelationAlong_le_two
    {X H h w : ℝ} {cutoff : ℝ → ℝ}
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1) :
    |wholeLineCorrelationAlong X H cutoff h w| ≤ 2 := by
  exact abs_wholeLineCutoffAutocorrelation_le_two hcutoffBound

theorem abs_wholeLineCorrelationAlongDeriv_le
    {X H h w B1 : ℝ} {cutoff cutoff' : ℝ → ℝ}
    (hB1 : 0 ≤ B1)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff'Support : ∀ y, 1 ≤ |y| → cutoff' y = 0)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (hcutoff'Bound : ∀ y, |cutoff' y| ≤ B1) :
    |wholeLineCorrelationAlongDeriv X H cutoff cutoff' h w| ≤ 4 * B1 := by
  let delta := wholeLinePacketShift X H h w
  by_cases hd : 2 < |delta|
  · have hz := wholeLineCutoffAutocorrelationDeriv_eq_zero_of_two_lt_abs
      hcutoffSupport hcutoff'Support hd
    simp [wholeLineCorrelationAlongDeriv, delta, hz, hB1]
  · have hdle : |delta| ≤ 2 := le_of_not_gt hd
    have hC := abs_wholeLineCutoffAutocorrelationDeriv_le
      (delta := delta) hcutoffBound hcutoff'Bound
    unfold wholeLineCorrelationAlongDeriv
    change |wholeLineCutoffAutocorrelationDeriv cutoff cutoff' delta * delta| ≤ _
    rw [abs_mul]
    calc
      |wholeLineCutoffAutocorrelationDeriv cutoff cutoff' delta| * |delta| ≤
          (2 * B1) * 2 := by gcongr
      _ = 4 * B1 := by ring

theorem abs_wholeLineCorrelationAlongSecond_le
    {X H h w B1 B2 : ℝ} {cutoff cutoff' cutoff'' : ℝ → ℝ}
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff'Support : ∀ y, 1 ≤ |y| → cutoff' y = 0)
    (hcutoff''Support : ∀ y, 1 ≤ |y| → cutoff'' y = 0)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (hcutoff'Bound : ∀ y, |cutoff' y| ≤ B1)
    (hcutoff''Bound : ∀ y, |cutoff'' y| ≤ B2) :
    |wholeLineCorrelationAlongSecond X H cutoff cutoff' cutoff'' h w| ≤
      8 * B2 + 4 * B1 := by
  let delta := wholeLinePacketShift X H h w
  by_cases hd : 2 < |delta|
  · have hz1 := wholeLineCutoffAutocorrelationDeriv_eq_zero_of_two_lt_abs
      hcutoffSupport hcutoff'Support hd
    have hz2 := wholeLineCutoffAutocorrelationSecond_eq_zero_of_two_lt_abs
      hcutoffSupport hcutoff''Support hd
    simp [wholeLineCorrelationAlongSecond, delta, hz1, hz2]
    positivity
  · have hdle : |delta| ≤ 2 := le_of_not_gt hd
    have hC1 := abs_wholeLineCutoffAutocorrelationDeriv_le
      (delta := delta) hcutoffBound hcutoff'Bound
    have hC2 := abs_wholeLineCutoffAutocorrelationSecond_le
      (delta := delta) hcutoffBound hcutoff''Bound
    unfold wholeLineCorrelationAlongSecond
    change |wholeLineCutoffAutocorrelationSecond cutoff cutoff'' delta * delta ^ 2 +
      wholeLineCutoffAutocorrelationDeriv cutoff cutoff' delta * delta| ≤ _
    calc
      _ ≤ |wholeLineCutoffAutocorrelationSecond cutoff cutoff'' delta| *
            |delta| ^ 2 +
          |wholeLineCutoffAutocorrelationDeriv cutoff cutoff' delta| * |delta| := by
        calc
          _ ≤ |wholeLineCutoffAutocorrelationSecond cutoff cutoff'' delta * delta ^ 2| +
              |wholeLineCutoffAutocorrelationDeriv cutoff cutoff' delta * delta| :=
            abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul, abs_pow]
      _ ≤ (2 * B2) * 2 ^ 2 + (2 * B1) * 2 := by gcongr
      _ = 8 * B2 + 4 * B1 := by ring

theorem abs_wholeLineOuterProduct_le_one
    {h w : ℝ} {outer : ℝ → ℝ}
    (houterBound : ∀ y, |outer y| ≤ 1) :
    |wholeLineOuterProduct outer h w| ≤ 1 := by
  unfold wholeLineOuterProduct
  rw [abs_mul]
  calc
    |outer (w / 100)| * |outer ((w + h) / 100)| ≤ 1 * 1 := by
      gcongr
      · exact houterBound _
      · exact houterBound _
    _ = 1 := by ring

theorem abs_wholeLineOuterProductDeriv_le
    {h w B1 : ℝ} {outer outer' : ℝ → ℝ}
    (hB1 : 0 ≤ B1)
    (houterBound : ∀ y, |outer y| ≤ 1)
    (houter'Bound : ∀ y, |outer' y| ≤ B1) :
    |wholeLineOuterProductDeriv outer outer' h w| ≤ B1 / 50 := by
  unfold wholeLineOuterProductDeriv
  calc
    _ ≤ |outer' (w / 100) / 100 * outer ((w + h) / 100)| +
        |outer (w / 100) * (outer' ((w + h) / 100) / 100)| := abs_add_le _ _
    _ ≤ (B1 / 100) * 1 + 1 * (B1 / 100) := by
      simp only [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 100)]
      gcongr
      · exact houter'Bound _
      · exact houterBound _
      · exact houterBound _
      · exact houter'Bound _
    _ = B1 / 50 := by ring

theorem abs_wholeLineOuterProductSecond_le
    {h w B1 B2 : ℝ} {outer outer' outer'' : ℝ → ℝ}
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (houterBound : ∀ y, |outer y| ≤ 1)
    (houter'Bound : ∀ y, |outer' y| ≤ B1)
    (houter''Bound : ∀ y, |outer'' y| ≤ B2) :
    |wholeLineOuterProductSecond outer outer' outer'' h w| ≤
      (B2 + B1 ^ 2) / 5000 := by
  unfold wholeLineOuterProductSecond
  have ht1 :
      |outer'' (w / 100) / 10000 * outer ((w + h) / 100)| ≤
        (B2 / 10000) * 1 := by
    rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 10000)]
    gcongr
    · exact houter''Bound _
    · exact houterBound _
  have ht2 :
      |2 * (outer' (w / 100) / 100) *
        (outer' ((w + h) / 100) / 100)| ≤
        2 * (B1 / 100) * (B1 / 100) := by
    rw [abs_mul, abs_mul, abs_div, abs_div]
    norm_num
    gcongr
    · exact houter'Bound _
    · exact houter'Bound _
  have ht3 :
      |outer (w / 100) * (outer'' ((w + h) / 100) / 10000)| ≤
        1 * (B2 / 10000) := by
    rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 10000)]
    gcongr
    · exact houterBound _
    · exact houter''Bound _
  calc
    _ ≤ |outer'' (w / 100) / 10000 * outer ((w + h) / 100)| +
          |2 * (outer' (w / 100) / 100) *
            (outer' ((w + h) / 100) / 100)| +
        |outer (w / 100) * (outer'' ((w + h) / 100) / 10000)| := by
      exact (abs_add_three _ _ _)
    _ ≤ (B2 / 10000) * 1 + 2 * (B1 / 100) * (B1 / 100) +
        1 * (B2 / 10000) := by
      exact add_le_add (add_le_add ht1 ht2) ht3
    _ = (B2 + B1 ^ 2) / 5000 := by ring

/-! ## Literal `A`, `A'`, `A''` envelopes and `L¹` budgets -/

def wholeLineAmplitudeFirstConstant (Bcut1 Bouter1 : ℝ) : ℝ :=
  2 + 4 * Bcut1 + 2 * (Bouter1 / 50)

def wholeLineAmplitudeSecondConstant
    (Bcut1 Bcut2 Bouter1 Bouter2 : ℝ) : ℝ :=
  2 + 2 * (4 * Bcut1) + 2 * (2 * (Bouter1 / 50)) +
    (8 * Bcut2 + 4 * Bcut1) +
    2 * (4 * Bcut1) * (Bouter1 / 50) +
    2 * ((Bouter2 + Bouter1 ^ 2) / 5000)

private theorem abs_lt_hundred_of_scaled_value_ne_zero
    {f : ℝ → ℝ} {v : ℝ}
    (hsupport : ∀ y, 1 ≤ |y| → f y = 0)
    (hne : f (v / 100) ≠ 0) : |v| < 100 := by
  have hscaled : |v / 100| < 1 := by
    apply lt_of_not_ge
    intro hge
    exact hne (hsupport _ hge)
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 100)] at hscaled
  exact (div_lt_one (by norm_num : (0 : ℝ) < 100)).mp hscaled

private theorem abs_add_six_le (a b c d e f : ℝ) :
    |a + b + c + d + e + f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
  have h1 := abs_add_le (a + b + c + d + e) f
  have h2 := abs_add_le (a + b + c + d) e
  have h3 := abs_add_le (a + b + c) d
  have h4 := abs_add_le (a + b) c
  have h5 := abs_add_le a b
  linarith

private theorem abs_wholeLinePacketWeight_le
    {H h w : ℝ} (hH : 0 ≤ H)
    (hw : w ∈ Set.Icc (-100 : ℝ) 100) (hwh : |w + h| ≤ 100) :
    |wholeLinePacketWeight H h w| ≤ H * Real.exp 100 := by
  have hew : Real.exp (w / 2) ≤ Real.exp 50 := by
    apply Real.exp_le_exp.mpr
    linarith [hw.2]
  have hewh : Real.exp ((w + h) / 2) ≤ Real.exp 50 := by
    apply Real.exp_le_exp.mpr
    have := (abs_le.mp hwh).2
    linarith
  unfold wholeLinePacketWeight
  rw [abs_mul, abs_mul, abs_of_nonneg hH,
    abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  calc
    H * Real.exp (w / 2) * Real.exp ((w + h) / 2) ≤
        H * Real.exp 50 * Real.exp 50 := by gcongr
    _ = H * (Real.exp 50 * Real.exp 50) := by ring
    _ = H * Real.exp (50 + 50) := by rw [Real.exp_add]
    _ = H * Real.exp 100 := by norm_num

theorem abs_wholeLineOffDiagonalAmplitude_le
    {X H h w : ℝ}
    {cutoff outer : ℝ → ℝ}
    (hH : 0 ≤ H) (hw : w ∈ Set.Icc (-100 : ℝ) 100)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (houterBound : ∀ y, |outer y| ≤ 1) :
    |wholeLineOffDiagonalAmplitude X H cutoff outer h w| ≤
      H * Real.exp 100 * 2 := by
  by_cases ho : outer ((w + h) / 100) = 0
  · simp [wholeLineOffDiagonalAmplitude, wholeLineOuterProduct, ho]
    positivity
  · have hwh := (abs_lt_hundred_of_scaled_value_ne_zero houterSupport ho).le
    have hW := abs_wholeLinePacketWeight_le hH hw hwh
    have hK := abs_wholeLineCorrelationAlong_le_two
      (X := X) (H := H) (h := h) (w := w) hcutoffBound
    have hO := abs_wholeLineOuterProduct_le_one
      (h := h) (w := w) houterBound
    unfold wholeLineOffDiagonalAmplitude
    rw [abs_mul, abs_mul]
    calc
      |wholeLinePacketWeight H h w| *
          (|wholeLineCorrelationAlong X H cutoff h w| *
            |wholeLineOuterProduct outer h w|) ≤
          (H * Real.exp 100) * (2 * 1) := by gcongr
      _ = H * Real.exp 100 * 2 := by ring

theorem abs_wholeLineOffDiagonalAmplitudeDeriv_le
    {X H h w Bcut1 Bouter1 : ℝ}
    {cutoff cutoff' outer outer' : ℝ → ℝ}
    (hH : 0 ≤ H) (hBcut1 : 0 ≤ Bcut1) (hBouter1 : 0 ≤ Bouter1)
    (hw : w ∈ Set.Icc (-100 : ℝ) 100)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff'Support : ∀ y, 1 ≤ |y| → cutoff' y = 0)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (hcutoff'Bound : ∀ y, |cutoff' y| ≤ Bcut1)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (houter'Support : ∀ y, 1 ≤ |y| → outer' y = 0)
    (houterBound : ∀ y, |outer y| ≤ 1)
    (houter'Bound : ∀ y, |outer' y| ≤ Bouter1) :
    |wholeLineOffDiagonalAmplitudeDeriv X H cutoff cutoff' outer outer' h w| ≤
      H * Real.exp 100 * wholeLineAmplitudeFirstConstant Bcut1 Bouter1 := by
  by_cases ho : outer ((w + h) / 100) = 0
  · by_cases ho' : outer' ((w + h) / 100) = 0
    · simp [wholeLineOffDiagonalAmplitudeDeriv, wholeLineOuterProduct,
        wholeLineOuterProductDeriv, ho, ho']
      unfold wholeLineAmplitudeFirstConstant
      positivity
    · have hwh := (abs_lt_hundred_of_scaled_value_ne_zero houter'Support ho').le
      have hW := abs_wholeLinePacketWeight_le hH hw hwh
      exact amplitudeDeriv_bound_core hW
  · have hwh := (abs_lt_hundred_of_scaled_value_ne_zero houterSupport ho).le
    have hW := abs_wholeLinePacketWeight_le hH hw hwh
    exact amplitudeDeriv_bound_core hW
  where
  amplitudeDeriv_bound_core
      (hW : |wholeLinePacketWeight H h w| ≤ H * Real.exp 100) :
      |wholeLineOffDiagonalAmplitudeDeriv X H cutoff cutoff' outer outer' h w| ≤
        H * Real.exp 100 * wholeLineAmplitudeFirstConstant Bcut1 Bouter1 := by
    have hK := abs_wholeLineCorrelationAlong_le_two
      (X := X) (H := H) (h := h) (w := w) hcutoffBound
    have hK1 := abs_wholeLineCorrelationAlongDeriv_le
      (X := X) (H := H) (h := h) (w := w) hBcut1
      hcutoffSupport hcutoff'Support hcutoffBound hcutoff'Bound
    have hO := abs_wholeLineOuterProduct_le_one
      (h := h) (w := w) houterBound
    have hO1 := abs_wholeLineOuterProductDeriv_le
      (h := h) (w := w) hBouter1
      houterBound houter'Bound
    let K := wholeLineCorrelationAlong X H cutoff h w
    let K1 := wholeLineCorrelationAlongDeriv X H cutoff cutoff' h w
    let O := wholeLineOuterProduct outer h w
    let O1 := wholeLineOuterProductDeriv outer outer' h w
    have hinner : |K * O + K1 * O + K * O1| ≤
        wholeLineAmplitudeFirstConstant Bcut1 Bouter1 := by
      calc
        _ ≤ |K * O| + |K1 * O| + |K * O1| := abs_add_three _ _ _
        _ = |K| * |O| + |K1| * |O| + |K| * |O1| := by rw [abs_mul, abs_mul, abs_mul]
        _ ≤ 2 * 1 + (4 * Bcut1) * 1 + 2 * (Bouter1 / 50) := by gcongr
        _ = wholeLineAmplitudeFirstConstant Bcut1 Bouter1 := by
          unfold wholeLineAmplitudeFirstConstant
          ring
    unfold wholeLineOffDiagonalAmplitudeDeriv
    change |wholeLinePacketWeight H h w * (K * O + K1 * O + K * O1)| ≤ _
    rw [abs_mul]
    exact mul_le_mul hW hinner (abs_nonneg _) (by positivity)

theorem abs_wholeLineOffDiagonalAmplitudeSecond_le
    {X H h w Bcut1 Bcut2 Bouter1 Bouter2 : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hH : 0 ≤ H) (hBcut1 : 0 ≤ Bcut1) (hBcut2 : 0 ≤ Bcut2)
    (hBouter1 : 0 ≤ Bouter1) (hBouter2 : 0 ≤ Bouter2)
    (hw : w ∈ Set.Icc (-100 : ℝ) 100)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff'Support : ∀ y, 1 ≤ |y| → cutoff' y = 0)
    (hcutoff''Support : ∀ y, 1 ≤ |y| → cutoff'' y = 0)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (hcutoff'Bound : ∀ y, |cutoff' y| ≤ Bcut1)
    (hcutoff''Bound : ∀ y, |cutoff'' y| ≤ Bcut2)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (houter'Support : ∀ y, 1 ≤ |y| → outer' y = 0)
    (houter''Support : ∀ y, 1 ≤ |y| → outer'' y = 0)
    (houterBound : ∀ y, |outer y| ≤ 1)
    (houter'Bound : ∀ y, |outer' y| ≤ Bouter1)
    (houter''Bound : ∀ y, |outer'' y| ≤ Bouter2) :
    |wholeLineOffDiagonalAmplitudeSecond X H cutoff cutoff' cutoff''
        outer outer' outer'' h w| ≤
      H * Real.exp 100 *
        wholeLineAmplitudeSecondConstant Bcut1 Bcut2 Bouter1 Bouter2 := by
  by_cases ho : outer ((w + h) / 100) = 0
  · by_cases ho' : outer' ((w + h) / 100) = 0
    · by_cases ho'' : outer'' ((w + h) / 100) = 0
      · simp [wholeLineOffDiagonalAmplitudeSecond, wholeLineOuterProduct,
          wholeLineOuterProductDeriv, wholeLineOuterProductSecond, ho, ho', ho'']
        unfold wholeLineAmplitudeSecondConstant
        positivity
      · have hwh := (abs_lt_hundred_of_scaled_value_ne_zero houter''Support ho'').le
        have hW := abs_wholeLinePacketWeight_le hH hw hwh
        exact amplitudeSecond_bound_core hW
    · have hwh := (abs_lt_hundred_of_scaled_value_ne_zero houter'Support ho').le
      have hW := abs_wholeLinePacketWeight_le hH hw hwh
      exact amplitudeSecond_bound_core hW
  · have hwh := (abs_lt_hundred_of_scaled_value_ne_zero houterSupport ho).le
    have hW := abs_wholeLinePacketWeight_le hH hw hwh
    exact amplitudeSecond_bound_core hW
  where
  amplitudeSecond_bound_core
      (hW : |wholeLinePacketWeight H h w| ≤ H * Real.exp 100) :
      |wholeLineOffDiagonalAmplitudeSecond X H cutoff cutoff' cutoff''
          outer outer' outer'' h w| ≤
        H * Real.exp 100 *
          wholeLineAmplitudeSecondConstant Bcut1 Bcut2 Bouter1 Bouter2 := by
    let K := wholeLineCorrelationAlong X H cutoff h w
    let K1 := wholeLineCorrelationAlongDeriv X H cutoff cutoff' h w
    let K2 := wholeLineCorrelationAlongSecond X H cutoff cutoff' cutoff'' h w
    let O := wholeLineOuterProduct outer h w
    let O1 := wholeLineOuterProductDeriv outer outer' h w
    let O2 := wholeLineOuterProductSecond outer outer' outer'' h w
    have hK : |K| ≤ 2 := abs_wholeLineCorrelationAlong_le_two hcutoffBound
    have hK1 : |K1| ≤ 4 * Bcut1 := abs_wholeLineCorrelationAlongDeriv_le
      hBcut1 hcutoffSupport hcutoff'Support hcutoffBound hcutoff'Bound
    have hK2 : |K2| ≤ 8 * Bcut2 + 4 * Bcut1 :=
      abs_wholeLineCorrelationAlongSecond_le hBcut1 hBcut2
        hcutoffSupport hcutoff'Support hcutoff''Support hcutoffBound
        hcutoff'Bound hcutoff''Bound
    have hO : |O| ≤ 1 := abs_wholeLineOuterProduct_le_one houterBound
    have hO1 : |O1| ≤ Bouter1 / 50 :=
      abs_wholeLineOuterProductDeriv_le hBouter1 houterBound houter'Bound
    have hO2 : |O2| ≤ (Bouter2 + Bouter1 ^ 2) / 5000 :=
      abs_wholeLineOuterProductSecond_le hBouter1 hBouter2
        houterBound houter'Bound houter''Bound
    have hinner :
        |K * O + 2 * K1 * O + 2 * K * O1 + K2 * O +
          2 * K1 * O1 + K * O2| ≤
        wholeLineAmplitudeSecondConstant Bcut1 Bcut2 Bouter1 Bouter2 := by
      calc
        _ ≤ |K * O| + |2 * K1 * O| + |2 * K * O1| + |K2 * O| +
            |2 * K1 * O1| + |K * O2| := abs_add_six_le _ _ _ _ _ _
        _ = |K| * |O| + 2 * |K1| * |O| + 2 * |K| * |O1| +
            |K2| * |O| + 2 * |K1| * |O1| + |K| * |O2| := by
          simp only [abs_mul]
          norm_num
        _ ≤ 2 * 1 + 2 * (4 * Bcut1) * 1 + 2 * 2 * (Bouter1 / 50) +
            (8 * Bcut2 + 4 * Bcut1) * 1 +
            2 * (4 * Bcut1) * (Bouter1 / 50) +
            2 * ((Bouter2 + Bouter1 ^ 2) / 5000) := by gcongr
        _ = wholeLineAmplitudeSecondConstant Bcut1 Bcut2 Bouter1 Bouter2 := by
          unfold wholeLineAmplitudeSecondConstant
          ring
    unfold wholeLineOffDiagonalAmplitudeSecond
    change |wholeLinePacketWeight H h w *
      (K * O + 2 * (K1 * O + K * O1) + K2 * O + 2 * K1 * O1 + K * O2)| ≤ _
    rw [show K * O + 2 * (K1 * O + K * O1) + K2 * O + 2 * K1 * O1 + K * O2 =
      K * O + 2 * K1 * O + 2 * K * O1 + K2 * O + 2 * K1 * O1 + K * O2 by ring,
      abs_mul]
    exact mul_le_mul hW hinner (abs_nonneg _) (by positivity)

theorem wholeLineOffDiagonalAmplitude_all_zero_of_shift
    {X H h w : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff'Support : ∀ y, 1 ≤ |y| → cutoff' y = 0)
    (hcutoff''Support : ∀ y, 1 ≤ |y| → cutoff'' y = 0)
    (hshift : 2 < |wholeLinePacketShift X H h w|) :
    wholeLineOffDiagonalAmplitude X H cutoff outer h w = 0 ∧
      wholeLineOffDiagonalAmplitudeDeriv X H cutoff cutoff' outer outer' h w = 0 ∧
      wholeLineOffDiagonalAmplitudeSecond X H cutoff cutoff' cutoff''
        outer outer' outer'' h w = 0 := by
  have h0 := wholeLineCutoffAutocorrelation_eq_zero_of_two_lt_abs
    hcutoffSupport hshift
  have h1 := wholeLineCutoffAutocorrelationDeriv_eq_zero_of_two_lt_abs
    hcutoffSupport hcutoff'Support hshift
  have h2 := wholeLineCutoffAutocorrelationSecond_eq_zero_of_two_lt_abs
    hcutoffSupport hcutoff''Support hshift
  simp [wholeLineOffDiagonalAmplitude, wholeLineOffDiagonalAmplitudeDeriv,
    wholeLineOffDiagonalAmplitudeSecond, wholeLineCorrelationAlong,
    wholeLineCorrelationAlongDeriv, wholeLineCorrelationAlongSecond,
    h0, h1, h2]

theorem wholeLineOffDiagonalAmplitude_endpoints
    {X H h : ℝ}
    {cutoff cutoff' outer outer' : ℝ → ℝ}
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (houter'Support : ∀ y, 1 ≤ |y| → outer' y = 0) :
    wholeLineOffDiagonalAmplitude X H cutoff outer h (-100) = 0 ∧
      wholeLineOffDiagonalAmplitude X H cutoff outer h 100 = 0 ∧
      wholeLineOffDiagonalAmplitudeDeriv X H cutoff cutoff' outer outer' h (-100) = 0 ∧
      wholeLineOffDiagonalAmplitudeDeriv X H cutoff cutoff' outer outer' h 100 = 0 := by
  have hoNeg : outer ((-100 : ℝ) / 100) = 0 := by
    apply houterSupport
    norm_num
  have hoPos : outer ((100 : ℝ) / 100) = 0 := by
    apply houterSupport
    norm_num
  have ho'Neg : outer' ((-100 : ℝ) / 100) = 0 := by
    apply houter'Support
    norm_num
  have ho'Pos : outer' ((100 : ℝ) / 100) = 0 := by
    apply houter'Support
    norm_num
  have hoNeg1 : outer (-1) = 0 := by
    apply houterSupport
    norm_num
  have hoPos1 : outer 1 = 0 := by
    apply houterSupport
    norm_num
  have ho'Neg1 : outer' (-1) = 0 := by
    apply houter'Support
    norm_num
  have ho'Pos1 : outer' 1 = 0 := by
    apply houter'Support
    norm_num
  simp [wholeLineOffDiagonalAmplitude, wholeLineOffDiagonalAmplitudeDeriv,
    wholeLineOuterProduct, wholeLineOuterProductDeriv,
    hoNeg, hoPos, ho'Neg, ho'Pos, hoNeg1, hoPos1, ho'Neg1, ho'Pos1]

private theorem continuous_wholeLineCutoffAutocorrelationSecond
    {cutoff cutoff'' : ℝ → ℝ}
    (hcutoffCont : Continuous cutoff) (hcutoff''Cont : Continuous cutoff'') :
    Continuous (wholeLineCutoffAutocorrelationSecond cutoff cutoff'') := by
  unfold wholeLineCutoffAutocorrelationSecond
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold Function.uncurry
  fun_prop

theorem continuous_wholeLineOffDiagonalAmplitudeSecond
    {X H h : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hcutoffCont : Continuous cutoff)
    (hcutoff'Cont : Continuous cutoff')
    (hcutoff''Cont : Continuous cutoff'')
    (houterCont : Continuous outer)
    (houter'Cont : Continuous outer')
    (houter''Cont : Continuous outer'') :
    Continuous (wholeLineOffDiagonalAmplitudeSecond X H cutoff cutoff' cutoff''
      outer outer' outer'' h) := by
  have hC0 : Continuous (wholeLineCutoffAutocorrelation cutoff) := by
    unfold wholeLineCutoffAutocorrelation
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    unfold Function.uncurry
    fun_prop
  have hC1 : Continuous
      (wholeLineCutoffAutocorrelationDeriv cutoff cutoff') := by
    unfold wholeLineCutoffAutocorrelationDeriv
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    unfold Function.uncurry
    fun_prop
  have hC2 : Continuous
      (wholeLineCutoffAutocorrelationSecond cutoff cutoff'') :=
    continuous_wholeLineCutoffAutocorrelationSecond hcutoffCont hcutoff''Cont
  unfold wholeLineOffDiagonalAmplitudeSecond wholeLinePacketWeight
    wholeLineCorrelationAlong wholeLineCorrelationAlongDeriv
    wholeLineCorrelationAlongSecond wholeLineOuterProduct
    wholeLineOuterProductDeriv wholeLineOuterProductSecond
    wholeLinePacketShift
  fun_prop

private theorem integral_abs_le_two_hundred_mul
    {f : ℝ → ℝ} {C : ℝ} (hf : Continuous f)
    (hpoint : ∀ w ∈ Set.Icc (-100 : ℝ) 100, |f w| ≤ C) :
    (∫ w : ℝ in (-100)..100, |f w|) ≤ 200 * C := by
  have hfInt : IntervalIntegrable (fun w ↦ |f w|) volume (-100) 100 :=
    hf.abs.intervalIntegrable _ _
  have hconst : IntervalIntegrable (fun _w : ℝ ↦ C) volume (-100) 100 :=
    intervalIntegrable_const
  calc
    (∫ w : ℝ in (-100)..100, |f w|) ≤ ∫ _w : ℝ in (-100)..100, C := by
      apply intervalIntegral.integral_mono_on (by norm_num) hfInt hconst
      intro w hw
      exact hpoint w hw
    _ = C * (100 - (-100)) := by simp; ring
    _ = 200 * C := by ring

/-- The three literal source budgets used by two integrations by parts.  All
constants are displayed, and none contains `X/H`. -/
theorem wholeLineOffDiagonalAmplitude_L1_budgets
    {X H h Bcut1 Bcut2 Bouter1 Bouter2 : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hH : 0 ≤ H) (hBcut1 : 0 ≤ Bcut1) (hBcut2 : 0 ≤ Bcut2)
    (hBouter1 : 0 ≤ Bouter1) (hBouter2 : 0 ≤ Bouter2)
    (hcutoffCont : Continuous cutoff)
    (hcutoff'Cont : Continuous cutoff')
    (hcutoff''Cont : Continuous cutoff'')
    (houterCont : Continuous outer)
    (houter'Cont : Continuous outer')
    (houter''Cont : Continuous outer'')
    (hcutoffDeriv : ∀ y, HasDerivAt cutoff (cutoff' y) y)
    (hcutoffSecond : ∀ y, HasDerivAt cutoff' (cutoff'' y) y)
    (houterDeriv : ∀ y, HasDerivAt outer (outer' y) y)
    (houterSecond : ∀ y, HasDerivAt outer' (outer'' y) y)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff'Support : ∀ y, 1 ≤ |y| → cutoff' y = 0)
    (hcutoff''Support : ∀ y, 1 ≤ |y| → cutoff'' y = 0)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (hcutoff'Bound : ∀ y, |cutoff' y| ≤ Bcut1)
    (hcutoff''Bound : ∀ y, |cutoff'' y| ≤ Bcut2)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (houter'Support : ∀ y, 1 ≤ |y| → outer' y = 0)
    (houter''Support : ∀ y, 1 ≤ |y| → outer'' y = 0)
    (houterBound : ∀ y, |outer y| ≤ 1)
    (houter'Bound : ∀ y, |outer' y| ≤ Bouter1)
    (houter''Bound : ∀ y, |outer'' y| ≤ Bouter2) :
    (∫ w : ℝ in (-100)..100,
        |wholeLineOffDiagonalAmplitude X H cutoff outer h w|) ≤
          200 * (H * Real.exp 100 * 2) ∧
      (∫ w : ℝ in (-100)..100,
        |wholeLineOffDiagonalAmplitudeDeriv X H cutoff cutoff' outer outer' h w|) ≤
          200 * (H * Real.exp 100 *
            wholeLineAmplitudeFirstConstant Bcut1 Bouter1) ∧
      (∫ w : ℝ in (-100)..100,
        |wholeLineOffDiagonalAmplitudeSecond X H cutoff cutoff' cutoff''
          outer outer' outer'' h w|) ≤
          200 * (H * Real.exp 100 *
            wholeLineAmplitudeSecondConstant Bcut1 Bcut2 Bouter1 Bouter2) := by
  have hACont : Continuous
      (wholeLineOffDiagonalAmplitude X H cutoff outer h) :=
    continuous_iff_continuousAt.mpr fun w ↦
      (hasDerivAt_wholeLineOffDiagonalAmplitude hcutoffCont hcutoff'Cont
        hcutoffBound hcutoff'Bound hcutoffDeriv houterDeriv).continuousAt
  have hA1Cont : Continuous
      (wholeLineOffDiagonalAmplitudeDeriv X H cutoff cutoff' outer outer' h) :=
    continuous_iff_continuousAt.mpr fun w ↦
      (hasDerivAt_wholeLineOffDiagonalAmplitudeDeriv hcutoffCont hcutoff'Cont
        hcutoff''Cont hcutoffBound hcutoff'Bound hcutoff''Bound
        hcutoffDeriv hcutoffSecond houterDeriv houterSecond).continuousAt
  have hA2Cont : Continuous
      (wholeLineOffDiagonalAmplitudeSecond X H cutoff cutoff' cutoff''
        outer outer' outer'' h) :=
    continuous_wholeLineOffDiagonalAmplitudeSecond hcutoffCont hcutoff'Cont
      hcutoff''Cont houterCont houter'Cont houter''Cont
  constructor
  · apply integral_abs_le_two_hundred_mul hACont
    intro w hw
    exact abs_wholeLineOffDiagonalAmplitude_le hH hw hcutoffBound
      houterSupport houterBound
  constructor
  · apply integral_abs_le_two_hundred_mul hA1Cont
    intro w hw
    exact abs_wholeLineOffDiagonalAmplitudeDeriv_le hH hBcut1 hBouter1 hw
      hcutoffSupport hcutoff'Support hcutoffBound hcutoff'Bound
      houterSupport houter'Support houterBound houter'Bound
  · apply integral_abs_le_two_hundred_mul hA2Cont
    intro w hw
    exact abs_wholeLineOffDiagonalAmplitudeSecond_le hH hBcut1 hBcut2
      hBouter1 hBouter2 hw hcutoffSupport hcutoff'Support hcutoff''Support
      hcutoffBound hcutoff'Bound hcutoff''Bound houterSupport houter'Support
      houter''Support houterBound houter'Bound houter''Bound

#print axioms hasDerivAt_wholeLineCorrelationAlongDeriv
#print axioms hasDerivAt_wholeLineOffDiagonalAmplitude
#print axioms hasDerivAt_wholeLineOffDiagonalAmplitudeDeriv
#print axioms abs_wholeLineCorrelationAlongSecond_le
#print axioms abs_wholeLineOuterProductSecond_le
#print axioms abs_wholeLineOffDiagonalAmplitudeSecond_le
#print axioms wholeLineOffDiagonalAmplitude_all_zero_of_shift
#print axioms wholeLineOffDiagonalAmplitude_endpoints
#print axioms wholeLineOffDiagonalAmplitude_L1_budgets

end
end MAPMRTWholeLineOffDiagonalAmplitude
