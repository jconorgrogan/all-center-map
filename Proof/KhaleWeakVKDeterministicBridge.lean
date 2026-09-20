import KhaleWeakVKApplication

/-!
# Deterministic bridge from Khale's explicit region to the MAP near collar

This module does not postulate Khale's theorem.  It proves every deduction
after the literal nonvanishing conclusion: a zero must lie outside the stated
region, the reciprocal denominator gives a uniform `(log X)^(-3/4)` gap on
polylogarithmic conductors, and that gap supplies arbitrary logarithmic decay
in the exact MAP near-collar factor.
-/

namespace MAPKhaleWeakVKApplication

open Filter Asymptotics

noncomputable section

/-- The literal denominator in the second assertion of Khale's Appendix-B
corollary. -/
def khaleWeakDenominator (q : ℕ) (t : ℝ) : ℝ :=
  18 * Real.log q +
    104 * Real.rpow (Real.log t) (2 / 3 : ℝ) *
      Real.rpow (Real.log (Real.log t)) (1 / 3 : ℝ)

theorem khaleWeakDenominator_pos
    {q : ℕ} {t : ℝ} (hq : 1 ≤ q) (ht : 3 ≤ t) :
    0 < khaleWeakDenominator q t := by
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hq)
  have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have htpos : 0 < t := by linarith
  have hlogt1 : 1 < Real.log t := by
    rw [Real.lt_log_iff_exp_lt htpos]
    have he3 : Real.exp 1 < 3 :=
      Real.exp_one_lt_d9.trans_le (by norm_num)
    exact he3.trans_le ht
  have hlogtpos : 0 < Real.log t := zero_lt_one.trans hlogt1
  have hloglogtpos : 0 < Real.log (Real.log t) := Real.log_pos hlogt1
  unfold khaleWeakDenominator
  have hsecond : 0 <
      104 * Real.rpow (Real.log t) (2 / 3 : ℝ) *
        Real.rpow (Real.log (Real.log t)) (1 / 3 : ℝ) := by
    have hfirstRpow : 0 < Real.rpow (Real.log t) (2 / 3 : ℝ) :=
      Real.rpow_pos_of_pos hlogtpos _
    have hsecondRpow : 0 <
        Real.rpow (Real.log (Real.log t)) (1 / 3 : ℝ) :=
      Real.rpow_pos_of_pos hloglogtpos _
    positivity
  nlinarith

/-- A zero contradicting a pointwise nonvanishing assertion at the Khale
boundary must have reciprocal-denominator distance from one.  This is the
exact logical conversion from the published nonvanishing formulation to the
zero-gap formulation used by MAP. -/
theorem one_div_khaleWeakDenominator_le_one_sub_sigma_of_zero
    {q : ℕ} [NeZero q] {t σ : ℝ} (χ : DirichletCharacter ℂ q)
    (hq : 1 ≤ q) (ht : 3 ≤ t)
    (hnonzero :
      1 - 1 / khaleWeakDenominator q t ≤ σ →
        DirichletCharacter.LFunction χ
          ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hzero : DirichletCharacter.LFunction χ
      ((σ : ℂ) + (t : ℂ) * Complex.I) = 0) :
    1 / khaleWeakDenominator q t ≤ 1 - σ := by
  have hden := khaleWeakDenominator_pos hq ht
  by_contra hgap
  have hboundary : 1 - 1 / khaleWeakDenominator q t ≤ σ := by
    linarith
  exact (hnonzero hboundary) hzero

/-- Khale's reciprocal denominator dominates a fixed weak-VK gap uniformly
for `q <= (log X)^K` and `3 <= t <= X`. -/
theorem weakGap_le_of_one_div_khaleWeakDenominator_le
    (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) (t σ : ℝ),
      1 ≤ q →
      (q : ℝ) ≤ Real.rpow (Real.log X) K →
      3 ≤ t → t ≤ X →
      1 / khaleWeakDenominator q t ≤ 1 - σ →
      (1 / (18 * K + 104)) *
          Real.rpow (Real.log X) (-(3 / 4 : ℝ)) ≤ 1 - σ := by
  filter_upwards
      [khaleDenominator_le_log_three_quarters K hK,
        eventually_gt_atTop (Real.exp 1)] with X hden hX q t σ hq hqX ht htX hgap
  have hXpos : 0 < X := (Real.exp_pos 1).trans hX
  have hlogX1 : 1 < Real.log X := by
    rw [Real.lt_log_iff_exp_lt hXpos]
    exact hX
  have hlogXpos : 0 < Real.log X := zero_lt_one.trans hlogX1
  have hC : 0 < 18 * K + 104 := by nlinarith
  have hpow : 0 < Real.rpow (Real.log X) (3 / 4 : ℝ) :=
    Real.rpow_pos_of_pos hlogXpos _
  have hD : 0 < khaleWeakDenominator q t :=
    khaleWeakDenominator_pos hq ht
  have hupper : khaleWeakDenominator q t ≤
      (18 * K + 104) * Real.rpow (Real.log X) (3 / 4 : ℝ) := by
    simpa [khaleWeakDenominator] using hden q t hq hqX ht htX
  have hinv :
      1 / ((18 * K + 104) * Real.rpow (Real.log X) (3 / 4 : ℝ)) ≤
        1 / khaleWeakDenominator q t :=
    one_div_le_one_div_of_le hD hupper
  have hid :
      (1 / (18 * K + 104)) *
          Real.rpow (Real.log X) (-(3 / 4 : ℝ)) =
        1 / ((18 * K + 104) *
          Real.rpow (Real.log X) (3 / 4 : ℝ)) := by
    have hneg : Real.rpow (Real.log X) (-(3 / 4 : ℝ)) =
        (Real.rpow (Real.log X) (3 / 4 : ℝ))⁻¹ := by
      exact Real.rpow_neg hlogXpos.le (3 / 4 : ℝ)
    rw [hneg]
    field_simp
  rw [hid]
  exact hinv.trans hgap

/-- Complete deterministic near-collar consequence of the literal Khale
nonvanishing conclusion, with no hidden exponent conversion. -/
theorem khaleWeakRegion_nearFactor_beats_polylog
    (K P A : ℝ) (hK : 0 ≤ K) (hP : 0 ≤ P) (hA : 0 ≤ A) :
    ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (t σ : ℝ)
        (χ : DirichletCharacter ℂ q),
      1 ≤ q →
      (q : ℝ) ≤ Real.rpow (Real.log X) K →
      3 ≤ t → t ≤ X →
      (1 - 1 / khaleWeakDenominator q t ≤ σ →
        DirichletCharacter.LFunction χ
          ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) →
      DirichletCharacter.LFunction χ
          ((σ : ℂ) + (t : ℂ) * Complex.I) = 0 →
      Real.rpow (Real.log X) P *
          Real.rpow X (-((1 - σ) / 12)) ≤
        Real.rpow (Real.log X) (-A) := by
  have hc : 0 < 1 / (18 * K + 104) := by
    positivity
  filter_upwards
      [weakGap_le_of_one_div_khaleWeakDenominator_le K hK,
        WeakVKNear.weakGap_nearFactor_beats_polylog
          (3 / 4 : ℝ) (1 / (18 * K + 104)) P A
          (by norm_num) hc hP hA] with X hgap hdecay q _inst t σ χ hq hqX ht htX hnonzero hzero
  have hrecip := one_div_khaleWeakDenominator_le_one_sub_sigma_of_zero
    χ hq ht hnonzero hzero
  have homega := hgap q t σ hq hqX ht htX hrecip
  exact hdecay (1 - σ) homega

end

end MAPKhaleWeakVKApplication

#print axioms MAPKhaleWeakVKApplication.khaleWeakDenominator_pos
#print axioms MAPKhaleWeakVKApplication.one_div_khaleWeakDenominator_le_one_sub_sigma_of_zero
#print axioms MAPKhaleWeakVKApplication.weakGap_le_of_one_div_khaleWeakDenominator_le
#print axioms MAPKhaleWeakVKApplication.khaleWeakRegion_nearFactor_beats_polylog
