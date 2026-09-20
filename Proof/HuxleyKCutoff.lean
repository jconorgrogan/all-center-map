import HuxleyJMellin
import HuxleyHalaszFront

/-!
# Huxley 1973 (2.6)--(2.8): the full kernel and its compact cutoff

This staging module derives the four translated copies of the already
certified inverse Mellin transform (2.5), and identifies their sum with the
literal compact coefficient `b(m,U)` printed in (2.8).
-/

namespace MAPHuxleyKCutoff

open Complex Real Set MeasureTheory Filter
open scoped Topology

noncomputable section

private theorem cpow_neg_line_mul_exp_eq_shifted_cpow
    {x : ℝ} (hx : 0 < x) (a : ℝ) (s : ℂ) :
    (x : ℂ) ^ (-s) * Complex.exp ((a : ℂ) * s) =
      (x / Real.exp a : ℂ) ^ (-s) := by
  have hea : 0 < Real.exp (-a) := Real.exp_pos (-a)
  have hbase : (x : ℂ) / (Real.exp a : ℂ) =
      ((Real.exp (-a) * x : ℝ) : ℂ) := by
    rw [Real.exp_neg]
    push_cast
    simp only [div_eq_mul_inv]
    ring
  rw [hbase, Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg hea.le hx.le]
  have hscale : ((Real.exp (-a) : ℝ) : ℂ) ^ (-s) =
      Complex.exp ((a : ℂ) * s) := by
    rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr hea.ne'),
      ← Complex.ofReal_log hea.le, Real.log_exp]
    push_cast
    congr 1
    ring
  rw [hscale]
  ring

/-- Multiplication of a Mellin-side function by `exp(a s)` translates its
inverse transform from `x` to `x / exp a`.  This is the exact scaling used
four times in Huxley (2.6). -/
theorem mellinInv_exp_mul_eq_shift
    (σ a : ℝ) (F : ℂ → ℂ) {x : ℝ} (hx : 0 < x) :
    mellinInv σ (fun s => Complex.exp ((a : ℂ) * s) * F s) x =
      mellinInv σ F (x / Real.exp a) := by
  unfold mellinInv
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    simp only [smul_eq_mul]
    rw [← mul_assoc, cpow_neg_line_mul_exp_eq_shifted_cpow hx a]
    rw [Complex.ofReal_div])

private theorem integrable_mellinInv_integrand
    {σ x : ℝ} {F : ℂ → ℂ} (hx : 0 < x)
    (hF : Complex.VerticalIntegrable F σ) :
    Integrable (fun t : ℝ =>
      (x : ℂ) ^ (-((σ : ℂ) + t * I)) * F ((σ : ℂ) + t * I)) := by
  unfold Complex.VerticalIntegrable at hF
  apply hF.bdd_mul (c := x ^ (-σ))
  · have hc : Continuous (fun t : ℝ =>
        (x : ℂ) ^ (-((σ : ℂ) + t * I))) := by
      have he : Continuous (fun t : ℝ => -((σ : ℂ) + t * I)) := by fun_prop
      exact he.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
    exact hc.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp)

private theorem verticalIntegrable_exp_mul
    {σ : ℝ} {F : ℂ → ℂ} (hF : Complex.VerticalIntegrable F σ)
    (a : ℝ) :
    Complex.VerticalIntegrable
      (fun s => Complex.exp ((a : ℂ) * s) * F s) σ := by
  unfold Complex.VerticalIntegrable at hF ⊢
  apply hF.bdd_mul
  · fun_prop
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Complex.norm_exp]
      simp only [mul_re, ofReal_re, add_re, ofReal_im, mul_zero,
        ofReal_mul, I_re, mul_im, I_im, zero_mul, add_zero]
      rfl)

private theorem mellinInv_add_of_pos
    {σ x : ℝ} {F G : ℂ → ℂ} (hx : 0 < x)
    (hF : Complex.VerticalIntegrable F σ)
    (hG : Complex.VerticalIntegrable G σ) :
    mellinInv σ (fun s => F s + G s) x =
      mellinInv σ F x + mellinInv σ G x := by
  unfold mellinInv
  rw [show (fun t : ℝ =>
      (x : ℂ) ^ (-((σ : ℂ) + t * I)) •
        (F ((σ : ℂ) + t * I) + G ((σ : ℂ) + t * I))) =
      (fun t : ℝ =>
        (x : ℂ) ^ (-((σ : ℂ) + t * I)) • F ((σ : ℂ) + t * I) +
        (x : ℂ) ^ (-((σ : ℂ) + t * I)) • G ((σ : ℂ) + t * I)) by
      funext t; exact smul_add _ _ _]
  rw [integral_add]
  · exact smul_add _ _ _
  · simpa only [smul_eq_mul] using
      integrable_mellinInv_integrand hx hF
  · simpa only [smul_eq_mul] using
      integrable_mellinInv_integrand hx hG

private theorem mellinInv_sub_of_pos
    {σ x : ℝ} {F G : ℂ → ℂ} (hx : 0 < x)
    (hF : Complex.VerticalIntegrable F σ)
    (hG : Complex.VerticalIntegrable G σ) :
    mellinInv σ (fun s => F s - G s) x =
      mellinInv σ F x - mellinInv σ G x := by
  unfold mellinInv
  rw [show (fun t : ℝ =>
      (x : ℂ) ^ (-((σ : ℂ) + t * I)) •
        (F ((σ : ℂ) + t * I) - G ((σ : ℂ) + t * I))) =
      (fun t : ℝ =>
        (x : ℂ) ^ (-((σ : ℂ) + t * I)) • F ((σ : ℂ) + t * I) -
        (x : ℂ) ^ (-((σ : ℂ) + t * I)) • G ((σ : ℂ) + t * I)) by
      funext t; exact smul_sub _ _ _]
  rw [integral_sub]
  · exact smul_sub _ _ _
  · simpa only [smul_eq_mul] using
      integrable_mellinInv_integrand hx hF
  · simpa only [smul_eq_mul] using
      integrable_mellinInv_integrand hx hG

/-- Before simplifying the four translated source weights, inverse Mellin
transform of the full kernel (2.6) is their exact alternating sum. -/
theorem mellinInv_huxleyK_eq_shifted_sourceWeights
    {x : ℝ} (hx : 0 < x) :
    mellinInv 2 MAPHuxleyReflectionKernelAlgebra.huxleyK x =
      MAPHuxleyJMellin.huxleyJSourceWeight (x / Real.exp 4) +
      MAPHuxleyJMellin.huxleyJSourceWeight (x / Real.exp 3) -
      MAPHuxleyJMellin.huxleyJSourceWeight (x / Real.exp 1) -
      MAPHuxleyJMellin.huxleyJSourceWeight x := by
  let J := MAPHuxleyReflectionKernelAlgebra.huxleyJ
  let E : ℝ → ℂ → ℂ := fun a s => Complex.exp ((a : ℂ) * s) * J s
  have hJ : Complex.VerticalIntegrable J 2 :=
    MAPHuxleyJVertical.verticalIntegrable_huxleyJ
  have hE (a : ℝ) : Complex.VerticalIntegrable (E a) 2 :=
    verticalIntegrable_exp_mul hJ a
  have hE43 : Complex.VerticalIntegrable (fun s => E 4 s + E 3 s) 2 := by
    unfold Complex.VerticalIntegrable at hE ⊢
    simpa only [Pi.add_apply] using (hE 4).add (hE 3)
  have hE431 : Complex.VerticalIntegrable
      (fun s => E 4 s + E 3 s - E 1 s) 2 := by
    unfold Complex.VerticalIntegrable at hE hE43 ⊢
    simpa only [Pi.sub_apply] using hE43.sub (hE 1)
  have hkernel : MAPHuxleyReflectionKernelAlgebra.huxleyK =
      fun s => (E 4 s + E 3 s - E 1 s) - J s := by
    funext s
    unfold MAPHuxleyReflectionKernelAlgebra.huxleyK
      MAPHuxleyReflectionKernelAlgebra.huxleyKernelNumerator E J
    norm_num
    ring
  rw [hkernel,
    mellinInv_sub_of_pos hx hE431 hJ,
    mellinInv_sub_of_pos hx hE43 (hE 1),
    mellinInv_add_of_pos hx (hE 4) (hE 3)]
  rw [mellinInv_exp_mul_eq_shift 2 4 J hx,
    mellinInv_exp_mul_eq_shift 2 3 J hx,
    mellinInv_exp_mul_eq_shift 2 1 J hx]
  rw [MAPHuxleyJMellin.mellinInv_huxleyJ_eq_sourceWeight
      (div_pos hx (Real.exp_pos 4)),
    MAPHuxleyJMellin.mellinInv_huxleyJ_eq_sourceWeight
      (div_pos hx (Real.exp_pos 3)),
    MAPHuxleyJMellin.mellinInv_huxleyJ_eq_sourceWeight
      (div_pos hx (Real.exp_pos 1)),
    MAPHuxleyJMellin.mellinInv_huxleyJ_eq_sourceWeight hx]

private theorem cos_log_div_exp_nat
    {x : ℝ} (hx : 0 < x) (k : ℕ) :
    Real.cos (Real.pi * Real.log (x / Real.exp k)) =
      (-1 : ℝ) ^ k * Real.cos (Real.pi * Real.log x) := by
  rw [Real.log_div hx.ne' (Real.exp_pos k).ne', Real.log_exp]
  convert Real.cos_sub_nat_mul_pi (Real.pi * Real.log x) k using 1 <;> ring

private theorem sourceWeight_div_exp_nat
    {x : ℝ} (hx : 0 < x) (k : ℕ) :
    MAPHuxleyJMellin.huxleyJSourceWeight (x / Real.exp k) =
      if x ≤ Real.exp k then
        (((1 / 2 : ℝ) *
          (1 - (-1 : ℝ) ^ k * Real.cos (Real.pi * Real.log x)) : ℝ) : ℂ)
      else 0 := by
  have hek : 0 < Real.exp (k : ℝ) := Real.exp_pos k
  by_cases hk : x ≤ Real.exp k
  · have hq : x / Real.exp k ≤ 1 := (div_le_one hek).mpr hk
    rw [MAPHuxleyJMellin.huxleyJSourceWeight, if_pos hq, if_pos hk,
      cos_log_div_exp_nat hx k]
  · have hq : ¬x / Real.exp k ≤ 1 := by
      simpa only [div_le_one hek] using hk
    rw [MAPHuxleyJMellin.huxleyJSourceWeight, if_neg hq, if_neg hk]

/-- The ratio form of the compact coefficient in Huxley (2.8).  Testing the
closed plateau first makes all four printed boundary conventions explicit. -/
def huxleyRatioCutoff (x : ℝ) : ℝ :=
  if Real.exp 1 ≤ x ∧ x ≤ Real.exp 3 then 1
  else if x ≤ 1 ∨ Real.exp 4 ≤ x then 0
  else (1 / 2) * (1 - Real.cos (Real.pi * Real.log x))

private theorem exp_one_gt_one : (1 : ℝ) < Real.exp 1 := by
  simpa using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)

private theorem exp_one_lt_exp_three : Real.exp 1 < Real.exp 3 := by
  exact Real.exp_lt_exp.mpr (by norm_num)

private theorem exp_three_lt_exp_four : Real.exp 3 < Real.exp 4 := by
  exact Real.exp_lt_exp.mpr (by norm_num)

private theorem four_real_weights_eq_ratioCutoff (x : ℝ) :
    (if x ≤ Real.exp 4 then
        (1 / 2 : ℝ) * (1 - Real.cos (Real.pi * Real.log x)) else 0) +
      (if x ≤ Real.exp 3 then
        (1 / 2 : ℝ) * (1 + Real.cos (Real.pi * Real.log x)) else 0) -
      (if x ≤ Real.exp 1 then
        (1 / 2 : ℝ) * (1 + Real.cos (Real.pi * Real.log x)) else 0) -
      (if x ≤ 1 then
        (1 / 2 : ℝ) * (1 - Real.cos (Real.pi * Real.log x)) else 0) =
      huxleyRatioCutoff x := by
  unfold huxleyRatioCutoff
  by_cases h0 : x ≤ 1
  · have hnlow : ¬Real.exp 1 ≤ x :=
      not_le.mpr (lt_of_le_of_lt h0 exp_one_gt_one)
    have h1 : x ≤ Real.exp 1 := h0.trans exp_one_gt_one.le
    have h3 : x ≤ Real.exp 3 := h1.trans exp_one_lt_exp_three.le
    have h4 : x ≤ Real.exp 4 := h3.trans exp_three_lt_exp_four.le
    simp [h0, hnlow, h1, h3, h4]
  · have hx0 : 1 < x := lt_of_not_ge h0
    by_cases h4low : Real.exp 4 ≤ x
    · rcases eq_or_lt_of_le h4low with h4eq | h4strict
      · subst x
        have h14 : Real.exp 1 < Real.exp 4 :=
          exp_one_lt_exp_three.trans exp_three_lt_exp_four
        have h04 : (1 : ℝ) < Real.exp 4 := exp_one_gt_one.trans h14
        have hn43 : ¬Real.exp 4 ≤ Real.exp 3 :=
          not_le.mpr exp_three_lt_exp_four
        have hn41 : ¬Real.exp 4 ≤ Real.exp 1 := not_le.mpr h14
        have hn40 : ¬Real.exp 4 ≤ 1 := not_le.mpr h04
        have hc4 : Real.cos (Real.pi * 4) = 1 := by
          convert Real.cos_nat_mul_pi 4 using 1 <;> norm_num <;> ring
        simp [Real.log_exp, hn43, hn41, hn40, hc4]
      · have hn4 : ¬x ≤ Real.exp 4 := not_le.mpr h4strict
        have hn3 : ¬x ≤ Real.exp 3 :=
          not_le.mpr (exp_three_lt_exp_four.trans h4strict)
        have hn1 : ¬x ≤ Real.exp 1 :=
          not_le.mpr
            (exp_one_lt_exp_three.trans (exp_three_lt_exp_four.trans h4strict))
        have hp : ¬(Real.exp 1 ≤ x ∧ x ≤ Real.exp 3) := by simp [hn3]
        simp [h0, hn1, hn3, hn4, hp, h4low]
    · have h4 : x < Real.exp 4 := lt_of_not_ge h4low
      have hout : ¬(x ≤ 1 ∨ Real.exp 4 ≤ x) := by simp [h0, h4low]
      by_cases hp : Real.exp 1 ≤ x ∧ x ≤ Real.exp 3
      · rcases hp with ⟨h1low, h3⟩
        rcases eq_or_lt_of_le h1low with h1eq | h1strict
        · subst x
          have h13 : Real.exp 1 ≤ Real.exp 3 := exp_one_lt_exp_three.le
          have h14 : Real.exp 1 ≤ Real.exp 4 :=
            (exp_one_lt_exp_three.trans exp_three_lt_exp_four).le
          have hn10 : ¬Real.exp 1 ≤ 1 := not_le.mpr exp_one_gt_one
          simp [Real.log_exp, h13, h14, hn10]
          norm_num
        · rcases eq_or_lt_of_le h3 with h3eq | h3strict
          · subst x
            have h34 : Real.exp 3 ≤ Real.exp 4 := exp_three_lt_exp_four.le
            have hn31 : ¬Real.exp 3 ≤ Real.exp 1 :=
              not_le.mpr exp_one_lt_exp_three
            have hn30 : ¬Real.exp 3 ≤ 1 :=
              not_le.mpr (exp_one_gt_one.trans exp_one_lt_exp_three)
            simp [Real.log_exp, h34, hn31, hn30]
            ring
          · have hn1 : ¬x ≤ Real.exp 1 := not_le.mpr h1strict
            have h4le : x ≤ Real.exp 4 :=
              h3strict.le.trans exp_three_lt_exp_four.le
            simp [h0, hn1, h3strict.le, h4le, h1strict.le]
            ring
      · by_cases h1 : x ≤ Real.exp 1
        · have hn1low : ¬Real.exp 1 ≤ x := by
            intro hlow
            exact hp ⟨hlow, h1.trans exp_one_lt_exp_three.le⟩
          have h3 : x ≤ Real.exp 3 := h1.trans exp_one_lt_exp_three.le
          have h4le : x ≤ Real.exp 4 := h3.trans exp_three_lt_exp_four.le
          simp [h0, h1, h3, h4le, hn1low, hp, hout, h4low]
        · have h1strict : Real.exp 1 < x := lt_of_not_ge h1
          have hn3 : ¬x ≤ Real.exp 3 := by
            intro h3
            exact hp ⟨h1strict.le, h3⟩
          have h4le : x ≤ Real.exp 4 := h4.le
          simp [h0, h1, hn3, h4le, hp, hout, h4low]

/-- The alternating four translates of (2.5) are exactly Huxley's compact
ratio cutoff, including the closed endpoints `1,e,e^3,e^4`. -/
theorem shifted_sourceWeights_eq_ratioCutoff
    {x : ℝ} (hx : 0 < x) :
    MAPHuxleyJMellin.huxleyJSourceWeight (x / Real.exp 4) +
      MAPHuxleyJMellin.huxleyJSourceWeight (x / Real.exp 3) -
      MAPHuxleyJMellin.huxleyJSourceWeight (x / Real.exp 1) -
      MAPHuxleyJMellin.huxleyJSourceWeight x =
        (huxleyRatioCutoff x : ℂ) := by
  have hs4 : MAPHuxleyJMellin.huxleyJSourceWeight (x / Real.exp 4) =
      if x ≤ Real.exp 4 then
        (((1 / 2 : ℝ) * (1 - Real.cos (Real.pi * Real.log x)) : ℝ) : ℂ)
      else 0 := by
    convert sourceWeight_div_exp_nat hx 4 using 1 <;> norm_num
  have hs3 : MAPHuxleyJMellin.huxleyJSourceWeight (x / Real.exp 3) =
      if x ≤ Real.exp 3 then
        (((1 / 2 : ℝ) * (1 + Real.cos (Real.pi * Real.log x)) : ℝ) : ℂ)
      else 0 := by
    convert sourceWeight_div_exp_nat hx 3 using 1 <;> norm_num
  have hs1 : MAPHuxleyJMellin.huxleyJSourceWeight (x / Real.exp 1) =
      if x ≤ Real.exp 1 then
        (((1 / 2 : ℝ) * (1 + Real.cos (Real.pi * Real.log x)) : ℝ) : ℂ)
      else 0 := by
    convert sourceWeight_div_exp_nat hx 1 using 1 <;> norm_num
  rw [hs4, hs3, hs1]
  rw [show MAPHuxleyJMellin.huxleyJSourceWeight x =
      if x ≤ 1 then
        (((1 / 2 : ℝ) * (1 - Real.cos (Real.pi * Real.log x)) : ℝ) : ℂ)
      else 0 by
    simpa using sourceWeight_div_exp_nat hx 0]
  have hreal := four_real_weights_eq_ratioCutoff x
  have hc := congrArg (fun r : ℝ => (r : ℂ)) hreal
  simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_zero,
    apply_ite] using hc

/-- Exact inverse Mellin form of the compact cutoff at a positive ratio. -/
theorem mellinInv_huxleyK_eq_ratioCutoff {x : ℝ} (hx : 0 < x) :
    mellinInv 2 MAPHuxleyReflectionKernelAlgebra.huxleyK x =
      (huxleyRatioCutoff x : ℂ) :=
  (mellinInv_huxleyK_eq_shifted_sourceWeights hx).trans
    (shifted_sourceWeights_eq_ratioCutoff hx)

/-- Passing from the positive ratio `m/U` back to Huxley's two-variable
notation gives exactly the repository's previously certified definition of
`b(m,U)`. -/
theorem huxleyRatioCutoff_div_eq_cutoff
    {m U : ℝ} (hU : 0 < U) :
    huxleyRatioCutoff (m / U) =
      MAPHuxleyHalaszFront.huxleyCutoffWeight m U := by
  unfold huxleyRatioCutoff MAPHuxleyHalaszFront.huxleyCutoffWeight
  simp only [le_div_iff₀ hU, div_le_iff₀ hU, one_mul]

/-- Huxley (2.6)--(2.8) as an exact coefficient identity: the inverse Mellin
transform of `K` at `m/U` is the printed compact weight `b(m,U)`. -/
theorem mellinInv_huxleyK_eq_cutoff
    {m U : ℝ} (hm : 0 < m) (hU : 0 < U) :
    mellinInv 2 MAPHuxleyReflectionKernelAlgebra.huxleyK (m / U) =
      (MAPHuxleyHalaszFront.huxleyCutoffWeight m U : ℂ) := by
  rw [mellinInv_huxleyK_eq_ratioCutoff (div_pos hm hU),
    huxleyRatioCutoff_div_eq_cutoff hU]

/-- Real-line parametrization of the upward contour in (2.7), before the
finite Dirichlet-series interchange. -/
theorem inverseMellin_integral_huxleyK_eq_cutoff
    {m U : ℝ} (hm : 0 < m) (hU : 0 < U) :
    (1 / (2 * Real.pi)) •
        ∫ t : ℝ, ((m / U : ℝ) : ℂ) ^ (-((2 : ℂ) + t * I)) •
          MAPHuxleyReflectionKernelAlgebra.huxleyK ((2 : ℂ) + t * I) =
      (MAPHuxleyHalaszFront.huxleyCutoffWeight m U : ℂ) := by
  simpa only [mellinInv] using mellinInv_huxleyK_eq_cutoff hm hU

end

end MAPHuxleyKCutoff

#print axioms MAPHuxleyKCutoff.mellinInv_exp_mul_eq_shift
#print axioms MAPHuxleyKCutoff.mellinInv_huxleyK_eq_shifted_sourceWeights
#print axioms MAPHuxleyKCutoff.shifted_sourceWeights_eq_ratioCutoff
#print axioms MAPHuxleyKCutoff.mellinInv_huxleyK_eq_ratioCutoff
#print axioms MAPHuxleyKCutoff.huxleyRatioCutoff_div_eq_cutoff
#print axioms MAPHuxleyKCutoff.mellinInv_huxleyK_eq_cutoff
#print axioms MAPHuxleyKCutoff.inverseMellin_integral_huxleyK_eq_cutoff
