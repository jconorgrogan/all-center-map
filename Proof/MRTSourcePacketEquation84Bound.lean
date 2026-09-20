import MRTSourcePacketEquation84

/-! Collection of the explicit equation-(84) constants. -/

namespace MAPMRTSourcePacketEquation84Bound

open MeasureTheory Set
open MAPMRTProposition51HardBranch MAPMRTSourcePacketEquation84

noncomputable section

theorem equation84_budget_collection
    {D R P K1 K2 : ℝ}
    (hD : 0 < D) (hR : 1 ≤ R) (hP : P ≤ 2 * R * D)
    (hP0 : 0 ≤ P) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) :
    (1 / (3 * D / 4)) ^ 2 * (R * K2) +
        3 * (1 / (3 * D / 4)) * (P / (3 * D / 4) ^ 2) * K1 +
        ((1 / (3 * D / 4)) *
            (P / (3 * D / 4) ^ 2 + 2 * P ^ 2 / (3 * D / 4) ^ 3) +
          (P / (3 * D / 4) ^ 2) ^ 2) * (24 / R) ≤
      (1500 + 24 * K1 + 4 * K2) * R / D ^ 2 := by
  let d : ℝ := 3 * D / 4
  have hd : 0 < d := by unfold d; positivity
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hq0 : 1 / d ≤ 2 / D := by
    rw [div_le_div_iff₀ hd hD]
    unfold d
    nlinarith
  have hq0n : 0 ≤ 1 / d := by positivity
  have hq1 : P / d ^ 2 ≤ 4 * R / D := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hd) hD]
    have hm := mul_le_mul_of_nonneg_right hP hD.le
    unfold d
    nlinarith [mul_nonneg hR0 (sq_nonneg D)]
  have hq1n : 0 ≤ P / d ^ 2 := by positivity
  have hPsq : P ^ 2 ≤ (2 * R * D) ^ 2 :=
    pow_le_pow_left₀ hP0 hP 2
  have hq2b : 2 * P ^ 2 / d ^ 3 ≤ 19 * R ^ 2 / D := by
    rw [div_le_div_iff₀ (pow_pos hd 3) hD]
    have hm := mul_le_mul_of_nonneg_left hPsq (by norm_num : (0 : ℝ) ≤ 2)
    unfold d
    nlinarith [mul_nonneg (sq_nonneg R) (sq_nonneg D)]
  have hq2 : P / d ^ 2 + 2 * P ^ 2 / d ^ 3 ≤ 23 * R ^ 2 / D := by
    have hRle : R ≤ R ^ 2 := by nlinarith [sq_nonneg (R - 1)]
    have hfirst : 4 * R / D ≤ 4 * R ^ 2 / D := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hRle (by norm_num)) hD.le
    calc
      P / d ^ 2 + 2 * P ^ 2 / d ^ 3 ≤
          4 * R / D + 19 * R ^ 2 / D := add_le_add hq1 hq2b
      _ ≤ 4 * R ^ 2 / D + 19 * R ^ 2 / D := add_le_add hfirst le_rfl
      _ = 23 * R ^ 2 / D := by ring
  have hq2n : 0 ≤ P / d ^ 2 + 2 * P ^ 2 / d ^ 3 := by positivity
  have ht0 : (1 / d) ^ 2 * (R * K2) ≤
      (4 * R * K2) / D ^ 2 := by
    have hs := pow_le_pow_left₀ hq0n hq0 2
    calc
      (1 / d) ^ 2 * (R * K2) ≤ (2 / D) ^ 2 * (R * K2) :=
        mul_le_mul_of_nonneg_right hs (mul_nonneg hR0 hK2)
      _ = (4 * R * K2) / D ^ 2 := by field_simp [ne_of_gt hD]; ring
  have ht1 : 3 * (1 / d) * (P / d ^ 2) * K1 ≤
      (24 * R * K1) / D ^ 2 := by
    calc
      3 * (1 / d) * (P / d ^ 2) * K1 ≤
          3 * (2 / D) * (4 * R / D) * K1 := by gcongr
      _ = (24 * R * K1) / D ^ 2 := by field_simp [ne_of_gt hD]; ring
  have ht2 : ((1 / d) *
          (P / d ^ 2 + 2 * P ^ 2 / d ^ 3) + (P / d ^ 2) ^ 2) *
        (24 / R) ≤ 1488 * R / D ^ 2 := by
    have h24R : 0 ≤ 24 / R := by positivity
    have hinner : (1 / d) *
          (P / d ^ 2 + 2 * P ^ 2 / d ^ 3) + (P / d ^ 2) ^ 2 ≤
        62 * R ^ 2 / D ^ 2 := by
      calc
        _ ≤ (2 / D) * (23 * R ^ 2 / D) + (4 * R / D) ^ 2 := by
          apply add_le_add
          · exact mul_le_mul hq0 hq2 hq2n (by positivity)
          · exact pow_le_pow_left₀ hq1n hq1 2
        _ = 62 * R ^ 2 / D ^ 2 := by field_simp [ne_of_gt hD]; ring
    calc
      _ ≤ (62 * R ^ 2 / D ^ 2) * (24 / R) :=
        mul_le_mul_of_nonneg_right hinner h24R
      _ = 1488 * R / D ^ 2 := by
        field_simp [ne_of_gt hD, ne_of_gt (lt_of_lt_of_le zero_lt_one hR)]
        ring
  change (1 / d) ^ 2 * (R * K2) +
      3 * (1 / d) * (P / d ^ 2) * K1 +
      ((1 / d) * (P / d ^ 2 + 2 * P ^ 2 / d ^ 3) +
        (P / d ^ 2) ^ 2) * (24 / R) ≤ _
  calc
    _ ≤ (4 * R * K2) / D ^ 2 + (24 * R * K1) / D ^ 2 +
        1488 * R / D ^ 2 := by gcongr
    _ ≤ (1500 + 24 * K1 + 4 * K2) * R / D ^ 2 := by
      have hcoef : 4 * K2 + 24 * K1 + 1488 ≤
          1500 + 24 * K1 + 4 * K2 := by linarith
      calc
        _ = (4 * K2 + 24 * K1 + 1488) * R / D ^ 2 := by ring
        _ ≤ (1500 + 24 * K1 + 4 * K2) * R / D ^ 2 := by gcongr

/-- Equation (84) in the source-facing `L(X/H)/D²` form, on the separately
named sharp packet range `H ≤ X/4`. -/
theorem norm_sourceStationaryPacket_equation84_sharp
    {X H x beta t D1 D2 B1 B2 : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hcenter : 4 * max (|beta| * H) (X / H) ≤
      |t / (2 * Real.pi) + beta * x|)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff'Support : ∀ y, 1 ≤ |y| → cutoff' y = 0)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (houterBound : ∀ y, |outer y| ≤ 1)
    (houter'Bound : ∀ y, |outer' y| ≤ B1)
    (houter''Bound : ∀ y, |outer'' y| ≤ B2)
    (hcutoffDeriv : ∀ y, HasDerivAt cutoff (cutoff' y) y)
    (hcutoffSecond : ∀ y, HasDerivAt cutoff' (cutoff'' y) y)
    (houterDeriv : ∀ y, HasDerivAt outer (outer' y) y)
    (houterSecond : ∀ y, HasDerivAt outer' (outer'' y) y)
    (hcutoff''Cont : Continuous cutoff'')
    (houter''Cont : Continuous outer'')
    (hcutoff'Int : Integrable (fun y ↦ |cutoff' y|))
    (hcutoff''Int : Integrable (fun y ↦ |cutoff'' y|))
    (hD1 : (∫ y : ℝ, |cutoff' y|) ≤ D1)
    (hD2 : (∫ y : ℝ, |cutoff'' y|) ≤ D2) :
    ‖sourceStationaryPacket X H x beta t cutoff outer‖ ≤
      (1500 + 24 * (10 * (1 + B1) * (1 + D1)) +
        4 * (10 + 10 * (1 + B1) * D1 + 20 * D2 + B1 + B2)) *
          (X / H) / |t / (2 * Real.pi) + beta * x| ^ 2 := by
  have hexact := norm_sourceStationaryPacket_equation84_exact
    hX hH hHquarter hxLower hxUpper hcenter hcutoffSupport hcutoff'Support
    hcutoffBound houterBound houter'Bound houter''Bound
    hcutoffDeriv hcutoffSecond houterDeriv houterSecond
    hcutoff''Cont houter''Cont hcutoff'Int hcutoff''Int hD1 hD2
  let D : ℝ := |t / (2 * Real.pi) + beta * x|
  let R : ℝ := X / H
  let P : ℝ := 17 * |beta| * X / 4
  let K1 : ℝ := 10 * (1 + B1) * (1 + D1)
  let K2 : ℝ := 10 + 10 * (1 + B1) * D1 + 20 * D2 + B1 + B2
  have hD : 0 < D := by
    have : 0 < 4 * max (|beta| * H) (X / H) := by positivity
    exact lt_of_lt_of_le this hcenter
  have hR : 1 ≤ R := by
    unfold R
    rw [le_div_iff₀ hH]
    linarith
  have hB1 : 0 ≤ B1 := le_trans (abs_nonneg (outer' 0)) (houter'Bound 0)
  have hB2 : 0 ≤ B2 := le_trans (abs_nonneg (outer'' 0)) (houter''Bound 0)
  have hD1n : 0 ≤ D1 := le_trans (integral_nonneg (fun _ ↦ abs_nonneg _)) hD1
  have hD2n : 0 ≤ D2 := le_trans (integral_nonneg (fun _ ↦ abs_nonneg _)) hD2
  have hP0 : 0 ≤ P := by unfold P; positivity
  have hbetaH : |beta| * H ≤ D / 4 := by
    have := (mul_le_mul_of_nonneg_left (le_max_left (|beta| * H) (X / H))
      (by norm_num : (0 : ℝ) ≤ 4)).trans hcenter
    unfold D
    linarith
  have hP : P ≤ 2 * R * D := by
    have hratio := mul_le_mul_of_nonneg_left hbetaH (show 0 ≤ X / H by positivity)
    have hrewrite : (X / H) * (|beta| * H) = |beta| * X := by
      field_simp [ne_of_gt hH]
    rw [hrewrite] at hratio
    unfold P R
    nlinarith
  have hK1 : 0 ≤ K1 := by unfold K1; positivity
  have hK2 : 0 ≤ K2 := by unfold K2; positivity
  have hcollect := equation84_budget_collection hD hR hP hP0 hK1 hK2
  have hA0 : 24 * H / X = 24 / R := by
    unfold R
    field_simp [ne_of_gt hX, ne_of_gt hH]
  rw [hA0] at hexact
  refine hexact.trans ?_
  simpa only [D, R, P, K1, K2] using hcollect

#print axioms equation84_budget_collection
#print axioms norm_sourceStationaryPacket_equation84_sharp

end
end MAPMRTSourcePacketEquation84Bound
