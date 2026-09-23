import MRTNonstationaryPhaseTwoIBP
import GuthMaynardReflectionMellin

/-!
# Quadratic vertical decay for the cutoff Mellin transform

This is the repeated-integration-by-parts step used in Guth--Maynard Lemma
6.2 to truncate the Mellin variable.  It specializes the proved generic
two-IBP theorem to the literal Mellin phase `exp(i r log x)`.
-/

namespace GuthMaynardMellinDecay

open MeasureTheory Set
open MAPMRTNonstationaryPhaseTwoIBP
open MAPMRTCorollary53Source MAPMRTVanDerCorputProof

noncomputable section

def mellinOscillation (r x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (r * Real.log x))

def mellinOscillationDeriv (r x : ℝ) : ℂ :=
  (Complex.I * r / x) * mellinOscillation r x

def mellinInverseDerivative (r x : ℝ) : ℂ :=
  x / (Complex.I * r)

def mellinInverseDerivativeDeriv (r : ℝ) (_x : ℝ) : ℂ :=
  1 / (Complex.I * r)

theorem hasDerivAt_mellinOscillation
    {r x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (mellinOscillation r) (mellinOscillationDeriv r x) x := by
  have hg : HasDerivAt (fun y : ℝ => r * Real.log y / (2 * Real.pi))
      (r / (2 * Real.pi * x)) x := by
    convert (Real.hasDerivAt_log hx).const_mul r |>.div_const (2 * Real.pi) using 1 <;>
      field_simp [Real.pi_ne_zero] <;> ring
  have h := hasDerivAt_additivePhase_comp
    (phase' := fun y : ℝ => r / (2 * Real.pi * y)) hg
  convert h using 1
  · funext y
    unfold mellinOscillation additivePhase
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  · unfold mellinOscillationDeriv mellinOscillation additivePhase
    push_cast
    field_simp [Real.pi_ne_zero, hx]

theorem hasDerivAt_mellinInverseDerivative
    {r x : ℝ} (hr : r ≠ 0) :
    HasDerivAt (mellinInverseDerivative r)
      (mellinInverseDerivativeDeriv r x) x := by
  unfold mellinInverseDerivative mellinInverseDerivativeDeriv
  simpa only [id_eq, Complex.ofReal_one] using!
    (hasDerivAt_id x).ofReal_comp.div_const (Complex.I * r)

theorem hasDerivAt_mellinInverseDerivativeDeriv
    {r x : ℝ} :
    HasDerivAt (mellinInverseDerivativeDeriv r) 0 x := by
  exact hasDerivAt_const x _

/-- A cutoff supported on `[a,b] ⊂ (0,∞)` has Mellin transform equal to the
literal compact oscillatory integral used by the two-IBP theorem. -/
theorem mellin_eq_intervalIntegral_mellinOscillation
    {a b r : ℝ} {f : ℝ → ℂ}
    (haPos : 0 < a) (hab : a ≤ b)
    (hsupport : ∀ x, x ∉ Set.Icc a b → f x = 0) :
    mellin f ((1 : ℂ) + r * Complex.I) =
      ∫ x : ℝ in a..b, mellinOscillation r x * f x := by
  let g : ℝ → ℂ := fun x =>
    (x : ℂ) ^ (((1 : ℂ) + r * Complex.I) - 1) * f x
  have hsubset : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact haPos.trans_le hx.1
  have hrestrict :
      (∫ x : ℝ in Set.Ioi 0, g x) = ∫ x : ℝ in Set.Icc a b, g x := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi hsubset
    intro x hx
    unfold g
    rw [hsupport x hx.2, mul_zero]
  unfold mellin
  change (∫ x : ℝ in Set.Ioi 0, g x) = _
  rw [hrestrict, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]
  apply intervalIntegral.integral_congr
  intro x hx
  have hxIcc : x ∈ Set.Icc a b := by
    simpa [Set.uIcc_of_le hab] using hx
  have hxPos : 0 < x := haPos.trans_le hxIcc.1
  unfold g mellinOscillation
  rw [show ((1 : ℂ) + r * Complex.I) - 1 = r * Complex.I by ring]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hxPos.ne')]
  rw [← Complex.ofReal_log hxPos.le]
  congr 2
  ring

/-- Exact two-IBP decay bound on a positive compact interval.  The displayed
right side is quadratic in `1/|r|`; no asymptotic notation is used. -/
theorem norm_mellinOscillatoryIntegral_le_two_ibp
    {a b r A0 A1 A2 : ℝ}
    {f f' f'' : ℝ → ℂ}
    (haPos : 0 < a) (hab : a ≤ b) (hr : r ≠ 0)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Icc a b, HasDerivAt f' (f'' x) x)
    (hf''Cont : ContinuousOn f'' (Set.Icc a b))
    (hfLeft : f a = 0) (hfRight : f b = 0)
    (hf'Left : f' a = 0) (hf'Right : f' b = 0)
    (hA0 : (∫ x : ℝ in a..b, ‖f x‖) ≤ A0)
    (hA1 : (∫ x : ℝ in a..b, ‖f' x‖) ≤ A1)
    (hA2 : (∫ x : ℝ in a..b, ‖f'' x‖) ≤ A2)
    (hA0nonneg : 0 ≤ A0) (hA1nonneg : 0 ≤ A1) (hA2nonneg : 0 ≤ A2) :
    ‖∫ x : ℝ in a..b, mellinOscillation r x * f x‖ ≤
      (b / |r|) ^ 2 * A2 +
        3 * (b / |r|) * (1 / |r|) * A1 +
          ((b / |r|) * 0 + (1 / |r|) ^ 2) * A0 := by
  have hbPos : 0 < b := haPos.trans_le hab
  have hrAbs : 0 < |r| := abs_pos.mpr hr
  have hE : ∀ x ∈ Set.Icc a b,
      HasDerivAt (mellinOscillation r) (mellinOscillationDeriv r x) x := by
    intro x hx
    exact hasDerivAt_mellinOscillation (ne_of_gt (haPos.trans_le hx.1))
  have hq : ∀ x ∈ Set.Icc a b,
      HasDerivAt (mellinInverseDerivative r)
        (mellinInverseDerivativeDeriv r x) x := by
    intro x hx
    exact hasDerivAt_mellinInverseDerivative hr
  have hqd : ∀ x ∈ Set.Icc a b,
      HasDerivAt (mellinInverseDerivativeDeriv r) 0 x := by
    intro x hx
    exact hasDerivAt_mellinInverseDerivativeDeriv
  have hEdCont : ContinuousOn (mellinOscillationDeriv r)
      (Set.Icc a b) := by
    intro x hx
    have hx0R : x ≠ 0 := ne_of_gt (haPos.trans_le hx.1)
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0R
    have hleft : ContinuousAt (fun y : ℝ => Complex.I * (r : ℂ) / (y : ℂ)) x :=
      continuousAt_const.div Complex.continuous_ofReal.continuousAt hx0
    have hright : ContinuousAt (mellinOscillation r) x :=
      (hasDerivAt_mellinOscillation hx0R).continuousAt
    unfold mellinOscillationDeriv mellinOscillation
    exact (hleft.mul hright).continuousWithinAt
  have hinverse : ∀ x ∈ Set.Icc a b,
      mellinInverseDerivative r x * mellinOscillationDeriv r x =
        mellinOscillation r x := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (haPos.trans_le hx.1))
    have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
    unfold mellinInverseDerivative mellinOscillationDeriv
    field_simp
  have hQ0 : ∀ x ∈ Set.Icc a b,
      ‖mellinInverseDerivative r x‖ ≤ b / |r| := by
    intro x hx
    have hxNonneg : 0 ≤ x := (haPos.trans_le hx.1).le
    unfold mellinInverseDerivative
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_mul,
      Complex.norm_I, one_mul]
    rw [abs_of_nonneg hxNonneg]
    exact div_le_div_of_nonneg_right hx.2 hrAbs.le
  have hQ1 : ∀ x ∈ Set.Icc a b,
      ‖mellinInverseDerivativeDeriv r x‖ ≤ 1 / |r| := by
    intro x hx
    unfold mellinInverseDerivativeDeriv
    simp [norm_div]
  have hEUnit : ∀ x ∈ Set.Icc a b, ‖mellinOscillation r x‖ = 1 := by
    intro x hx
    unfold mellinOscillation
    rw [Complex.norm_exp]
    simp
  apply norm_integral_le_two_ibp_budgets hab hE hq hqd hf hf'
    hEdCont continuousOn_const hf''Cont hinverse hfLeft hfRight
    hf'Left hf'Right hA0 hA1 hA2 hQ0 hQ1 (fun _ _ => by simp) hEUnit
  · positivity
  · positivity
  · norm_num

/-- The literal vertical-line Mellin transform inherits the exact two-IBP
bound.  This is the direct bridge from the cutoff estimates used in
Guth--Maynard Lemma 6.2 to quadratic decay in the Mellin variable. -/
theorem norm_mellin_line_one_le_two_ibp
    {a b r A0 A1 A2 : ℝ}
    {f f' f'' : ℝ → ℂ}
    (haPos : 0 < a) (hab : a ≤ b) (hr : r ≠ 0)
    (hsupport : ∀ x, x ∉ Set.Icc a b → f x = 0)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Icc a b, HasDerivAt f' (f'' x) x)
    (hf''Cont : ContinuousOn f'' (Set.Icc a b))
    (hfLeft : f a = 0) (hfRight : f b = 0)
    (hf'Left : f' a = 0) (hf'Right : f' b = 0)
    (hA0 : (∫ x : ℝ in a..b, ‖f x‖) ≤ A0)
    (hA1 : (∫ x : ℝ in a..b, ‖f' x‖) ≤ A1)
    (hA2 : (∫ x : ℝ in a..b, ‖f'' x‖) ≤ A2)
    (hA0nonneg : 0 ≤ A0) (hA1nonneg : 0 ≤ A1) (hA2nonneg : 0 ≤ A2) :
    ‖mellin f ((1 : ℂ) + r * Complex.I)‖ ≤
      (b / |r|) ^ 2 * A2 +
        3 * (b / |r|) * (1 / |r|) * A1 +
          ((b / |r|) * 0 + (1 / |r|) ^ 2) * A0 := by
  rw [mellin_eq_intervalIntegral_mellinOscillation haPos hab hsupport]
  exact norm_mellinOscillatoryIntegral_le_two_ibp haPos hab hr hf hf'
    hf''Cont hfLeft hfRight hf'Left hf'Right hA0 hA1 hA2
    hA0nonneg hA1nonneg hA2nonneg

/-- The same estimate in the compact `C / |r|²` form used for vertical
integrability and Mellin-tail truncation. -/
theorem norm_mellin_line_one_le_quadratic_decay
    {a b r A0 A1 A2 : ℝ}
    {f f' f'' : ℝ → ℂ}
    (haPos : 0 < a) (hab : a ≤ b) (hr : r ≠ 0)
    (hsupport : ∀ x, x ∉ Set.Icc a b → f x = 0)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Icc a b, HasDerivAt f' (f'' x) x)
    (hf''Cont : ContinuousOn f'' (Set.Icc a b))
    (hfLeft : f a = 0) (hfRight : f b = 0)
    (hf'Left : f' a = 0) (hf'Right : f' b = 0)
    (hA0 : (∫ x : ℝ in a..b, ‖f x‖) ≤ A0)
    (hA1 : (∫ x : ℝ in a..b, ‖f' x‖) ≤ A1)
    (hA2 : (∫ x : ℝ in a..b, ‖f'' x‖) ≤ A2)
    (hA0nonneg : 0 ≤ A0) (hA1nonneg : 0 ≤ A1) (hA2nonneg : 0 ≤ A2) :
    ‖mellin f ((1 : ℂ) + r * Complex.I)‖ ≤
      (b ^ 2 * A2 + 3 * b * A1 + A0) / |r| ^ 2 := by
  have hraw := norm_mellin_line_one_le_two_ibp haPos hab hr hsupport hf hf'
    hf''Cont hfLeft hfRight hf'Left hf'Right hA0 hA1 hA2
    hA0nonneg hA1nonneg hA2nonneg
  convert hraw using 1
  field_simp [abs_ne_zero.mpr hr]
  <;> ring

end

end GuthMaynardMellinDecay

#print axioms GuthMaynardMellinDecay.hasDerivAt_mellinOscillation
#print axioms GuthMaynardMellinDecay.mellin_eq_intervalIntegral_mellinOscillation
#print axioms GuthMaynardMellinDecay.norm_mellinOscillatoryIntegral_le_two_ibp
#print axioms GuthMaynardMellinDecay.norm_mellin_line_one_le_two_ibp
#print axioms GuthMaynardMellinDecay.norm_mellin_line_one_le_quadratic_decay
