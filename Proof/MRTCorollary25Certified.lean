import MRTCorollary25Almost

/-!
# First-principles certification of MRT Corollary 2.5

This file only absorbs the explicit constants and the lower support endpoint in
`MRTCorollary25Almost`.  The Perron, clipping, and Abel arguments are upstream.
-/

namespace MAPMRTCorollary25Certified

open scoped BigOperators
open MAPMRTCorollary25 MAPMRTCorollary25Almost MixedMeanFrontend

noncomputable section

private theorem one_le_ceil_div
    {C X : ℝ} (hC : 1 < C) (hX : 1 ≤ X) :
    1 ≤ Nat.ceil (X / C) := by
  have hCpos : 0 < C := lt_trans zero_lt_one hC
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  exact Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt (Nat.ceil_pos.mpr (div_pos hXpos hCpos)))

private theorem scale_le_mul_ceil
    {C X : ℝ} (hC : 1 < C) :
    X ≤ C * (Nat.ceil (X / C) : ℝ) := by
  have hCpos : 0 < C := lt_trans zero_lt_one hC
  have h := mul_le_mul_of_nonneg_left (Nat.le_ceil (X / C)) hCpos.le
  calc
    X = C * (X / C) := by field_simp
    _ ≤ C * (Nat.ceil (X / C) : ℝ) := h

private theorem ceil_div_le_two_scale
    {C X : ℝ} (hC : 1 < C) (hX : 1 ≤ X) :
    (Nat.ceil (X / C) : ℝ) ≤ 2 * X := by
  have hCpos : 0 < C := lt_trans zero_lt_one hC
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hXC : X / C ≤ X := by
    apply (div_le_iff₀ hCpos).2
    nlinarith [mul_nonneg hXpos.le (sub_nonneg.mpr hC.le)]
  have hceil : (Nat.ceil (X / C) : ℝ) < X / C + 1 :=
    Nat.ceil_lt_add_one (div_nonneg hXpos.le hCpos.le)
  nlinarith

private theorem sqrt_scale_div_sqrt_ceil_le
    {C X : ℝ} (hC : 1 < C) (hX : 1 ≤ X) :
    Real.sqrt ((C + 2) * X) / Real.sqrt (Nat.ceil (X / C) : ℝ) ≤
      Real.sqrt (C * (C + 2)) := by
  let L := Nat.ceil (X / C)
  have hCpos : 0 < C := lt_trans zero_lt_one hC
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hL : 1 ≤ L := one_le_ceil_div hC hX
  have hL0 : 0 ≤ (L : ℝ) := by positivity
  have hsqrtL : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hXL : X ≤ C * (L : ℝ) := scale_le_mul_ceil hC
  have hprod : (C + 2) * X ≤ (C * (C + 2)) * (L : ℝ) := by
    nlinarith [mul_nonneg (show 0 ≤ C + 2 by linarith) (sub_nonneg.mpr hXL)]
  have hs := Real.sqrt_le_sqrt hprod
  have hQ0 : 0 ≤ C * (C + 2) := mul_nonneg hCpos.le (by linarith)
  rw [Real.sqrt_mul hQ0] at hs
  exact (div_le_iff₀ hsqrtL).2 hs

private theorem scale_div_sqrt_ceil_le
    {C X : ℝ} (hC : 1 < C) (hX : 1 ≤ X) :
    X / Real.sqrt (Nat.ceil (X / C) : ℝ) ≤
      2 * C * Real.sqrt X := by
  let L := Nat.ceil (X / C)
  have hCpos : 0 < C := lt_trans zero_lt_one hC
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hL : 1 ≤ L := one_le_ceil_div hC hX
  have hL0 : 0 ≤ (L : ℝ) := by positivity
  have hsqrtL : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hXL : X ≤ C * (L : ℝ) := scale_le_mul_ceil hC
  have hfirst : X / Real.sqrt (L : ℝ) ≤ C * Real.sqrt (L : ℝ) := by
    apply (div_le_iff₀ hsqrtL).2
    rw [mul_assoc, Real.mul_self_sqrt hL0]
    exact hXL
  have hL2X : (L : ℝ) ≤ 2 * X := ceil_div_le_two_scale hC hX
  have hsqrtL2X := Real.sqrt_le_sqrt hL2X
  have hsqrt2 : Real.sqrt (2 : ℝ) ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hsqrt2X : Real.sqrt (2 * X) ≤ 2 * Real.sqrt X := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_right hsqrt2 (Real.sqrt_nonneg X)
  calc
    X / Real.sqrt (L : ℝ) ≤ C * Real.sqrt (L : ℝ) := hfirst
    _ ≤ C * Real.sqrt (2 * X) := mul_le_mul_of_nonneg_left hsqrtL2X hCpos.le
    _ ≤ C * (2 * Real.sqrt X) := mul_le_mul_of_nonneg_left hsqrt2X hCpos.le
    _ = 2 * C * Real.sqrt X := by ring

private theorem one_add_log_le_log_multiplier
    {T : ℝ} (hT : 1 ≤ T) :
    1 + Real.log (2 + T) ≤
      (1 + (Real.log 3)⁻¹) * Real.log (2 + T) := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog : Real.log 3 ≤ Real.log (2 + T) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hone : 1 ≤ (Real.log 3)⁻¹ * Real.log (2 + T) := by
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ hlog3).2 (by simpa using hlog)
  nlinarith

/-- MRT Corollary 2.5, reconstructed from the finite Perron identity, the
transition-band estimate, real-endpoint clipping, and discrete Abel summation.
The constant below is explicit and depends only on `C`. -/
theorem mrtCorollary25_certified : MAPMRTCorollary25.MRTCorollary25 := by
  intro C hC
  let q := Real.sqrt (C * (C + 2))
  let H := 1 + (Real.log 3)⁻¹
  let c₁ := 12 * q
  let c₂ := 192 * C * (1 + q) * (C + 2) * H
  let K := 1 + c₁ + c₂
  have hCpos : 0 < C := lt_trans zero_lt_one hC
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hHpos : 0 < H := by
    dsimp only [H]
    have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have : 0 < (Real.log 3)⁻¹ := inv_pos.mpr hlog3
    linarith
  have hc₁0 : 0 ≤ c₁ := by dsimp only [c₁]; positivity
  have hc₂0 : 0 ≤ c₂ := by
    dsimp only [c₂]
    have : 0 ≤ C + 2 := by linarith
    positivity
  have hKpos : 0 < K := by dsimp only [K]; linarith
  refine ⟨K, hKpos, ?_⟩
  intro X T X1 X2 t B f hX hT hB hSupp hf
  let L := Nat.ceil (X / C)
  let I := ∫ u in (-T)..T,
    ‖halfLineDirichletPolynomial X C f (t + u)‖ / (1 + |u|)
  let E := B * Real.sqrt X * Real.log (2 + T) / T
  let P :=
    3 * Real.sqrt ((C + 2) * X) * I +
    24 * (1 + q) * (C + 2) * B * X * (1 + Real.log (2 + T)) / T
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hL : 1 ≤ L := one_le_ceil_div hC hX
  have hL0 : 0 ≤ (L : ℝ) := by positivity
  have hsqrtL : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hI0 : 0 ≤ I := by
    dsimp only [I]
    apply intervalIntegral.integral_nonneg (by linarith)
    intro u hu
    positivity
  have hlog0 : 0 ≤ Real.log (2 + T) := Real.log_nonneg (by linarith)
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hlogPlus0 : 0 ≤ 1 + Real.log (2 + T) := by linarith
  have hratio₁ :
      Real.sqrt ((C + 2) * X) / Real.sqrt (L : ℝ) ≤ q := by
    dsimp only [L, q]
    exact sqrt_scale_div_sqrt_ceil_le hC hX
  have hratio₂ : X / Real.sqrt (L : ℝ) ≤ 2 * C * Real.sqrt X := by
    dsimp only [L]
    exact scale_div_sqrt_ceil_le hC hX
  have hlogMult :
      1 + Real.log (2 + T) ≤ H * Real.log (2 + T) := by
    dsimp only [H]
    exact one_add_log_le_log_multiplier hT
  have hcarrier :
      4 * (3 * Real.sqrt ((C + 2) * X) * I) / Real.sqrt (L : ℝ) ≤
        c₁ * I := by
    have hmul := mul_le_mul_of_nonneg_right hratio₁ hI0
    dsimp only [c₁]
    calc
      4 * (3 * Real.sqrt ((C + 2) * X) * I) / Real.sqrt (L : ℝ) =
          12 * (Real.sqrt ((C + 2) * X) / Real.sqrt (L : ℝ) * I) := by ring
      _ ≤ 12 * (q * I) := by gcongr
      _ = 12 * q * I := by ring
  have hlogDiv :
      (1 + Real.log (2 + T)) / T ≤
        (H * Real.log (2 + T)) / T := by
    exact div_le_div_of_nonneg_right hlogMult hTpos.le
  have herror :
      4 * (24 * (1 + q) * (C + 2) * B * X *
          (1 + Real.log (2 + T)) / T) / Real.sqrt (L : ℝ) ≤
        c₂ * E := by
    let A := 96 * (1 + q) * (C + 2) * B
    have hA0 : 0 ≤ A := by
      dsimp only [A]
      have : 0 ≤ C + 2 := by linarith
      positivity
    have hstep₁ :
        A * (X / Real.sqrt (L : ℝ)) *
            ((1 + Real.log (2 + T)) / T) ≤
          A * (2 * C * Real.sqrt X) *
            ((1 + Real.log (2 + T)) / T) := by
      gcongr
    have hstep₂ :
        A * (2 * C * Real.sqrt X) *
            ((1 + Real.log (2 + T)) / T) ≤
          A * (2 * C * Real.sqrt X) *
            ((H * Real.log (2 + T)) / T) := by
      gcongr
    dsimp only [A] at hstep₁ hstep₂
    dsimp only [c₂, E]
    calc
      4 * (24 * (1 + q) * (C + 2) * B * X *
          (1 + Real.log (2 + T)) / T) / Real.sqrt (L : ℝ) =
          96 * (1 + q) * (C + 2) * B *
            (X / Real.sqrt (L : ℝ)) *
              ((1 + Real.log (2 + T)) / T) := by ring
      _ ≤ 96 * (1 + q) * (C + 2) * B * (2 * C * Real.sqrt X) *
              ((1 + Real.log (2 + T)) / T) := hstep₁
      _ ≤ 96 * (1 + q) * (C + 2) * B * (2 * C * Real.sqrt X) *
              ((H * Real.log (2 + T)) / T) := hstep₂
      _ = 192 * C * (1 + q) * (C + 2) * H *
            (B * Real.sqrt X * Real.log (2 + T) / T) := by ring
  have hAlmost := cutoffPolynomial_le_four_rawEnvelope_div_sqrtLower
    (C := C) (X := X) (T := T) (X1 := X1) (X2 := X2) (t := t)
    (B := B) (f := f) hC hX hT hB hSupp hf
  dsimp only at hAlmost
  change ‖halfLineDirichletPolynomial X C (intervalCutoff X1 X2 f) t‖ ≤
    4 * P / Real.sqrt (L : ℝ) at hAlmost
  have hEnvelope : 4 * P / Real.sqrt (L : ℝ) ≤ c₁ * I + c₂ * E := by
    dsimp only [P]
    calc
      4 * (3 * Real.sqrt ((C + 2) * X) * I +
          24 * (1 + q) * (C + 2) * B * X *
            (1 + Real.log (2 + T)) / T) / Real.sqrt (L : ℝ) =
          4 * (3 * Real.sqrt ((C + 2) * X) * I) / Real.sqrt (L : ℝ) +
          4 * (24 * (1 + q) * (C + 2) * B * X *
            (1 + Real.log (2 + T)) / T) / Real.sqrt (L : ℝ) := by ring
      _ ≤ c₁ * I + c₂ * E := add_le_add hcarrier herror
  have hc₁K : c₁ ≤ K := by dsimp only [K]; linarith
  have hc₂K : c₂ ≤ K := by dsimp only [K]; linarith
  have hfinal : c₁ * I + c₂ * E ≤ K * (I + E) := by
    calc
      c₁ * I + c₂ * E ≤ K * I + K * E :=
        add_le_add (mul_le_mul_of_nonneg_right hc₁K hI0)
          (mul_le_mul_of_nonneg_right hc₂K hE0)
      _ = K * (I + E) := by ring
  exact hAlmost.trans (hEnvelope.trans hfinal)

end
end MAPMRTCorollary25Certified

#print axioms MAPMRTCorollary25Certified.mrtCorollary25_certified
