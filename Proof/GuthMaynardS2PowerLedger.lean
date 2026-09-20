import GuthMaynardS2DyadicAssembly

/-! # Numeric normalization for the S2 dyadic reflection budgets -/

namespace GuthMaynardS2PowerLedger

open scoped BigOperators
open MeasureTheory
open GuthMaynardS2DyadicReflection GuthMaynardHeathBrownMajorant

noncomputable section

def sourceMellinMass : ℝ :=
  ∫ r : ℝ, ‖mellin GuthMaynardSectionThreeCutoff.sectionThreeCutoff
    ((1 : ℂ) + r * Complex.I)‖

theorem sourceMellinMass_nonneg : 0 ≤ sourceMellinMass :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem sourceMellinWindowMass_le (R : ℝ) :
    (∫ r : ℝ in Set.Ioc (-R) R,
      ‖mellin GuthMaynardSectionThreeCutoff.sectionThreeCutoff
        ((1 : ℂ) + r * Complex.I)‖) ≤ sourceMellinMass :=
  setIntegral_le_integral
    GuthMaynardLemma62MellinInversion.sectionThreeCutoff_verticalIntegrable.norm
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _))

theorem sourceReflectionScale_sq_le {U R : ℝ}
    (hU : 0 < U) (hR : R ≤ U / 2) (J : ℕ) :
    sourceReflectionScale U R J ^ 2 ≤ 1600 * (J + 1 : ℝ) ^ 2 / U := by
  have hd : 0 < U - R := by linarith
  have heq : sourceReflectionScale U R J ^ 2 =
      (800 / Real.pi) * (J + 1 : ℝ) ^ 2 / (U - R) := by
    unfold sourceReflectionScale
    simp only [mul_pow, div_pow]
    rw [Real.sq_sqrt (by positivity : 0 ≤ 8 * Real.pi), Real.sq_sqrt hd.le]
    field_simp
    ring
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hnum : (800 / Real.pi) * (J + 1 : ℝ) ^ 2 ≤ 800 * (J + 1 : ℝ) ^ 2 := by
    gcongr
    exact (div_le_iff₀ Real.pi_pos).mpr (by linarith)
  calc
    _ = _ := heq
    _ ≤ 800 * (J + 1 : ℝ) ^ 2 / (U / 2) :=
      div_le_div₀ (by positivity) hnum (by positivity) (by linarith)
    _ = _ := by field_simp; ring

/-- Square-root expansion of the k=2 Heath--Brown shape, with nonnegative
root factors kept explicit so it also covers the empty ordinate set. -/
theorem heathBrownShape_sqrt_le {T : ℝ} (hT : 0 ≤ T) (M : ℕ) (W : Finset ℝ) :
    Real.sqrt (heathBrownShape T (M ^ 2) W) ≤
      (W.card : ℝ) * M + Real.sqrt (W.card : ℝ) * (M : ℝ) ^ 2 +
        Real.sqrt (Real.rpow (W.card : ℝ) (5 / 4 : ℝ) * Real.rpow T (1 / 2 : ℝ)) * M := by
  let a := (W.card : ℝ) * M
  let b := Real.sqrt (W.card : ℝ) * (M : ℝ) ^ 2
  let c := Real.sqrt (Real.rpow (W.card : ℝ) (5 / 4 : ℝ) * Real.rpow T (1 / 2 : ℝ)) * M
  have hw : 0 ≤ (W.card : ℝ) := by positivity
  have hv : 0 ≤ Real.rpow (W.card : ℝ) (5 / 4 : ℝ) * Real.rpow T (1 / 2 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hw _) (Real.rpow_nonneg hT _)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have heq : a ^ 2 + b ^ 2 + c ^ 2 = heathBrownShape T (M ^ 2) W := by
    unfold a b c heathBrownShape
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hw, Real.sq_sqrt hv]
    push_cast
    ring
  apply (Real.sqrt_le_iff).2
  constructor
  · exact add_nonneg (add_nonneg ha hb) hc
  · change heathBrownShape T (M ^ 2) W ≤ (a + b + c) ^ 2
    rw [← heq]
    nlinarith [mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]

/-- Logarithmic dyadic counts admit an explicit subpower bound. -/
theorem dyadic_index_le_subpower {T delta : ℝ} (hT : 1 ≤ T) (hd : 0 < delta)
    (J : ℕ) (hJ : (2 : ℝ) ^ J ≤ T) :
    (J + 1 : ℝ) ≤ (1 + 1 / (delta * Real.log 2)) * Real.rpow T delta := by
  have hlog : (J : ℝ) * Real.log 2 ≤ Real.log T := by
    have h := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ J) hJ
    simpa [Real.log_pow] using h
  have hlogT := Real.log_le_rpow_div (le_trans zero_le_one hT) hd
  change Real.log T ≤ Real.rpow T delta / delta at hlogT
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hidx : (J : ℝ) ≤ Real.rpow T delta / (delta * Real.log 2) := by
    apply (le_div_iff₀ (mul_pos hd hlog2)).mpr
    have h := hlog.trans hlogT
    have h' := (le_div_iff₀ hd).mp h
    nlinarith
  have hone := Real.one_le_rpow hT hd.le
  change 1 ≤ Real.rpow T delta at hone
  calc
    (J + 1 : ℝ) ≤ Real.rpow T delta / (delta * Real.log 2) + Real.rpow T delta := by linarith
    _ = _ := by ring

def pairShape (T M w : ℝ) : ℝ :=
  w ^ 2 * M + w * Real.sqrt w * M ^ 2 +
    w * Real.sqrt (Real.rpow w (5 / 4 : ℝ) * Real.rpow T (1 / 2 : ℝ)) * M

theorem pairShape_nonneg {T M w : ℝ} (hM : 0 ≤ M) (hw : 0 ≤ w) :
    0 ≤ pairShape T M w := by unfold pairShape; positivity

theorem pairShape_mono {T M P w : ℝ} (hM : 0 ≤ M) (hMP : M ≤ P) (hw : 0 ≤ w) :
    pairShape T M w ≤ pairShape T P w := by
  unfold pairShape
  gcongr

theorem card_mul_sqrt_shape_le {T : ℝ} (hT : 0 ≤ T) (M : ℕ) (W : Finset ℝ) :
    (W.card : ℝ) * Real.sqrt (heathBrownShape T (M ^ 2) W) ≤
      pairShape T M (W.card : ℝ) := by
  apply (mul_le_mul_of_nonneg_left (heathBrownShape_sqrt_le hT M W) (by positivity)).trans_eq
  unfold pairShape
  ring

def sourceCentralBudget (C eta T : ℝ) (W : Finset ℝ) (U R : ℝ) (J : ℕ) : ℝ :=
  4 * sourceReflectionScale U R J ^ 2 *
    ((∫ r : ℝ in Set.Ioc (-R) R,
        ‖mellin GuthMaynardSectionThreeCutoff.sectionThreeCutoff
          ((1 : ℂ) + r * Complex.I)‖) ^ 2 *
      (((J + 1 : ℕ) : ℝ) * ((W.card : ℝ) ^ 2 +
        ∑ j ∈ Finset.range J,
          C * Real.rpow T eta * (W.card : ℝ) *
            Real.sqrt (heathBrownShape T ((2 ^ j) ^ 2) W))))

/-- Every factor from dyadic prefix splitting is normalized explicitly. -/
theorem sourceCentralBudget_le {C eta T U R : ℝ}
    (hC : 0 ≤ C) (heta : 0 ≤ eta) (hT : 1 ≤ T) (hU : 0 < U)
    (hR : R ≤ U / 2) (W : Finset ℝ) (J : ℕ) :
    sourceCentralBudget C eta T W U R J ≤
      6400 * sourceMellinMass ^ 2 * (1 + C) * (J + 1 : ℝ) ^ 4 *
        Real.rpow T eta / U * pairShape T ((2 ^ J : ℕ) : ℝ) (W.card : ℝ) := by
  let P := pairShape T ((2 ^ J : ℕ) : ℝ) (W.card : ℝ)
  have hP : 0 ≤ P := pairShape_nonneg (by positivity) (by positivity)
  have hT0 := le_trans zero_le_one hT
  have hpow0 : 0 ≤ Real.rpow T eta := Real.rpow_nonneg hT0 eta
  have hpow1 : 1 ≤ Real.rpow T eta := Real.one_le_rpow hT heta
  have hbase : (W.card : ℝ) ^ 2 ≤ P := by
    have hM : (1 : ℝ) ≤ ((2 ^ J : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_pow J 2 (by norm_num)
    unfold P pairShape
    have h₁ : (W.card : ℝ) ^ 2 ≤ (W.card : ℝ) ^ 2 * ((2 ^ J : ℕ) : ℝ) :=
      le_mul_of_one_le_right (sq_nonneg _) hM
    have h₂ : 0 ≤ (W.card : ℝ) * Real.sqrt (W.card : ℝ) * ((2 ^ J : ℕ) : ℝ) ^ 2 := by positivity
    have h₃ : 0 ≤ (W.card : ℝ) * Real.sqrt
        (Real.rpow (W.card : ℝ) (5 / 4 : ℝ) * Real.rpow T (1 / 2 : ℝ)) *
          ((2 ^ J : ℕ) : ℝ) := by positivity
    linarith
  have hsum : (∑ j ∈ Finset.range J,
      C * Real.rpow T eta * (W.card : ℝ) *
        Real.sqrt (heathBrownShape T ((2 ^ j) ^ 2) W)) ≤
      (J : ℝ) * (C * Real.rpow T eta * P) := by
    calc
      _ ≤ ∑ j ∈ Finset.range J, C * Real.rpow T eta * P := by
        apply Finset.sum_le_sum
        intro j hj
        have hlen : ((2 ^ j : ℕ) : ℝ) ≤ ((2 ^ J : ℕ) : ℝ) := by
          exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ))
            (Finset.mem_range.mp hj).le
        have hb := (card_mul_sqrt_shape_le hT0 (2 ^ j) W).trans
          (pairShape_mono (by positivity) hlen (by positivity))
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb (mul_nonneg hC hpow0)
      _ = _ := by simp
  have hbracket : (W.card : ℝ) ^ 2 +
      (∑ j ∈ Finset.range J, C * Real.rpow T eta * (W.card : ℝ) *
        Real.sqrt (heathBrownShape T ((2 ^ j) ^ 2) W)) ≤
      (1 + C) * (J + 1 : ℝ) * Real.rpow T eta * P := by
    have hcoef : 1 + (J : ℝ) * C * Real.rpow T eta ≤
        (1 + C) * (J + 1 : ℝ) * Real.rpow T eta := by
      have h₁ := mul_nonneg (Nat.cast_nonneg J) hpow0
      have h₂ := mul_nonneg hC hpow0
      nlinarith
    have hh := mul_le_mul_of_nonneg_right hcoef hP
    nlinarith
  have hwindow0 : 0 ≤ (∫ r : ℝ in Set.Ioc (-R) R,
      ‖mellin GuthMaynardSectionThreeCutoff.sectionThreeCutoff
        ((1 : ℂ) + r * Complex.I)‖) := integral_nonneg (fun _ => norm_nonneg _)
  have hwindow := pow_le_pow_left₀ hwindow0 (sourceMellinWindowMass_le R) 2
  have hscale := sourceReflectionScale_sq_le hU hR J
  have hbracket0 : 0 ≤ (W.card : ℝ) ^ 2 +
      (∑ j ∈ Finset.range J, C * Real.rpow T eta * (W.card : ℝ) *
        Real.sqrt (heathBrownShape T ((2 ^ j) ^ 2) W)) := by
    apply add_nonneg (sq_nonneg _)
    exact Finset.sum_nonneg fun j _ => mul_nonneg
      (mul_nonneg (mul_nonneg hC hpow0) (by positivity)) (Real.sqrt_nonneg _)
  unfold sourceCentralBudget
  push_cast
  calc
    _ ≤ 4 * (1600 * (J + 1 : ℝ) ^ 2 / U) *
        (sourceMellinMass ^ 2 * ((J + 1 : ℝ) *
          ((1 + C) * (J + 1 : ℝ) * Real.rpow T eta * P))) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hscale (by norm_num))
        (mul_le_mul hwindow
          (mul_le_mul_of_nonneg_left hbracket (by positivity))
          (mul_nonneg (by positivity) hbracket0) (sq_nonneg _))
        (mul_nonneg (sq_nonneg _) (mul_nonneg (by positivity) hbracket0))
        (by positivity)
    _ = _ := by
      have hPcast : P = pairShape T ((2 : ℝ) ^ J) (W.card : ℝ) := by simp [P]
      rw [← hPcast]
      ring

end
end GuthMaynardS2PowerLedger

#print axioms GuthMaynardS2PowerLedger.sourceReflectionScale_sq_le
#print axioms GuthMaynardS2PowerLedger.heathBrownShape_sqrt_le
#print axioms GuthMaynardS2PowerLedger.dyadic_index_le_subpower

#print axioms GuthMaynardS2PowerLedger.sourceCentralBudget_le
