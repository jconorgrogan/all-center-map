import PrincipalFullStripA5Source
import CompletedLVerticalBound
import GammaFactorInverseGrowth
import PhragmenGrowthAdapter
import Mathlib.Analysis.Complex.PhragmenLindelof

namespace MAPPrincipalZetaFixedStrip

open Complex Filter Topology Asymptotics Real Set MeasureTheory
open scoped Real Topology

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩

def principalRegularized : ℂ → ℂ :=
  DirichletCharacter.LFunctionTrivChar₁ 1

def normalizedPrincipal (z : ℂ) : ℂ :=
  principalRegularized z / (z + 3) ^ 6

theorem principalRegularized_apply_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    principalRegularized s = (s - 1) * riemannZeta s := by
  unfold principalRegularized DirichletCharacter.LFunctionTrivChar₁
  rw [Function.update_of_ne hs,
    DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs]
  norm_num

private theorem normalized_diffContOnCl :
    DiffContOnCl ℂ normalizedPrincipal (re ⁻¹' Ioo (-1 : ℝ) 2) := by
  let d : ℂ → ℂ := fun z => (z + 3) ^ 6
  have hd : Differentiable ℂ d := (differentiable_id.add_const 3).pow 6
  have hdne : ∀ z ∈ closure (re ⁻¹' Ioo (-1 : ℝ) 2), d z ≠ 0 := by
    intro z hz
    rw [Complex.closure_preimage_re, closure_Ioo (by norm_num : (-1 : ℝ) ≠ 2)] at hz
    apply pow_ne_zero
    intro heq
    have hre := congrArg Complex.re heq
    simp at hre
    linarith [hz.1]
  have hinv : DiffContOnCl ℂ d⁻¹ (re ⁻¹' Ioo (-1 : ℝ) 2) :=
    hd.diffContOnCl.inv hdne
  have hF : DiffContOnCl ℂ principalRegularized (re ⁻¹' Ioo (-1 : ℝ) 2) :=
    (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).diffContOnCl
  simpa [normalizedPrincipal, d, div_eq_inv_mul, mul_comm] using hinv.smul hF

private theorem norm_completedZeta_le
    {C : ℝ}
    (hC : ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → ‖completedRiemannZeta₀ s‖ ≤ C)
    {s : ℂ} (hlo : -1 ≤ s.re) (hhi : s.re ≤ 2) (ht : 2 ≤ |s.im|) :
    ‖completedRiemannZeta s‖ ≤ C + 2 := by
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    norm_num at ht
  have hs1 : s ≠ 1 := by
    intro hs
    subst s
    norm_num at ht
  have hsNorm : 1 ≤ ‖s‖ :=
    (show (1 : ℝ) ≤ |s.im| by linarith).trans (Complex.abs_im_le_norm s)
  have h1sNorm : 1 ≤ ‖1 - s‖ := by
    have him : (1 - s).im = -s.im := by simp
    have : 1 ≤ |(1 - s).im| := by rw [him, abs_neg]; linarith
    exact this.trans (Complex.abs_im_le_norm (1 - s))
  rw [completedRiemannZeta_eq]
  calc
    ‖completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)‖ ≤
        ‖completedRiemannZeta₀ s‖ + ‖1 / s‖ + ‖1 / (1 - s)‖ := by
      calc
        _ ≤ ‖completedRiemannZeta₀ s - 1 / s‖ + ‖1 / (1 - s)‖ := norm_sub_le _ _
        _ ≤ (‖completedRiemannZeta₀ s‖ + ‖1 / s‖) + ‖1 / (1 - s)‖ := by
          gcongr
          exact norm_sub_le _ _
    _ ≤ C + 1 + 1 := by
      gcongr
      · exact hC s hlo hhi
      · simpa [norm_div] using inv_le_one_of_one_le₀ hsNorm
      · simpa [norm_div] using inv_le_one_of_one_le₀ h1sNorm
    _ = C + 2 := by ring

private theorem normalized_singleExp_bound
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → ‖completedRiemannZeta₀ s‖ ≤ C)
    (s : ℂ) (hlo : -1 < s.re) (hhi : s.re < 2) (ht : 2 ≤ |s.im|) :
    ‖normalizedPrincipal s‖ ≤
      (384 * (C + 2)) * (1 + |s.im|) ^ 2 *
        Real.exp (Real.pi * |s.im|) := by
  have hs0 : s ≠ 0 := by intro hs; subst s; norm_num at ht
  have hs1 : s ≠ 1 := by intro hs; subst s; norm_num at ht
  have hcomp := norm_completedZeta_le hC hlo.le hhi.le ht
  have hgamma := PLInteriorGrowth.norm_inv_GammaReal_fixedStrip_le
    hlo.le (by linarith) ht
  have hzeta : ‖riemannZeta s‖ ≤
      (C + 2) * (192 * (1 + |s.im|) ^ 2 *
        Real.exp (Real.pi * |s.im|)) := by
    rw [riemannZeta_def_of_ne_zero hs0, norm_div, div_eq_mul_inv,
      ← norm_inv]
    exact mul_le_mul hcomp hgamma (norm_nonneg _) (by positivity)
  have hsub : ‖s - 1‖ ≤ 2 * (1 + |s.im|) := by
    calc
      ‖s - 1‖ ≤ |(s - 1).re| + |(s - 1).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |s.re - 1| + |s.im| := by simp
      _ ≤ 2 + |s.im| := by
        have : |s.re - 1| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
        linarith
      _ ≤ 2 * (1 + |s.im|) := by linarith [abs_nonneg s.im]
  have hF : ‖principalRegularized s‖ ≤
      384 * (C + 2) * (1 + |s.im|) ^ 3 *
        Real.exp (Real.pi * |s.im|) := by
    rw [principalRegularized_apply_of_ne_one hs1, norm_mul]
    calc
      ‖s - 1‖ * ‖riemannZeta s‖ ≤
          (2 * (1 + |s.im|)) *
            ((C + 2) * (192 * (1 + |s.im|) ^ 2 *
              Real.exp (Real.pi * |s.im|))) :=
        mul_le_mul hsub hzeta (norm_nonneg _) (by positivity)
      _ = 384 * (C + 2) * (1 + |s.im|) ^ 3 *
          Real.exp (Real.pi * |s.im|) := by ring
  have hden : (1 + |s.im|) ≤ ‖(s + 3) ^ 6‖ := by
    have him : |s.im| ≤ ‖s + 3‖ := by
      simpa using Complex.abs_im_le_norm (s + 3)
    have hu : 2 ≤ ‖s + 3‖ := ht.trans him
    rw [norm_pow]
    have huSq : 1 + |s.im| ≤ |s.im| ^ 2 := by
      nlinarith [sq_nonneg (|s.im| - 2)]
    have hsq : |s.im| ^ 2 ≤ ‖s + 3‖ ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) him 2
    have hx1 : 1 ≤ ‖s + 3‖ := by linarith
    have hx4 : 1 ≤ ‖s + 3‖ ^ 4 := one_le_pow₀ hx1
    have hx26 : ‖s + 3‖ ^ 2 ≤ ‖s + 3‖ ^ 6 := by
      calc
        ‖s + 3‖ ^ 2 ≤ ‖s + 3‖ ^ 2 * ‖s + 3‖ ^ 4 := by
          simpa using mul_le_mul_of_nonneg_left hx4 (sq_nonneg ‖s + 3‖)
        _ = ‖s + 3‖ ^ 6 := by ring
    exact huSq.trans (hsq.trans hx26)
  have hdenpos : 0 < ‖(s + 3) ^ 6‖ := by
    apply norm_pos_iff.mpr
    exact pow_ne_zero _ (by
      intro hs3
      have him := congrArg Complex.im hs3
      simp at him
      rw [him, abs_zero] at ht
      norm_num at ht)
  rw [normalizedPrincipal, norm_div]
  apply (div_le_iff₀ hdenpos).2
  calc
    ‖principalRegularized s‖ ≤
        384 * (C + 2) * (1 + |s.im|) ^ 3 *
          Real.exp (Real.pi * |s.im|) := hF
    _ = (384 * (C + 2) * (1 + |s.im|) ^ 2 *
          Real.exp (Real.pi * |s.im|)) * (1 + |s.im|) := by ring
    _ ≤ (384 * (C + 2) * (1 + |s.im|) ^ 2 *
          Real.exp (Real.pi * |s.im|)) * ‖(s + 3) ^ 6‖ := by
      gcongr

private theorem normalized_growthHypothesis :
    ∃ c < Real.pi / ((2 : ℝ) - (-1 : ℝ)), ∃ B,
      normalizedPrincipal
        =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo (-1 : ℝ) 2)]
          fun z => Real.exp (B * Real.exp (c * |z.im|)) := by
  obtain ⟨C, hC0, hC⟩ :=
    PLInteriorGrowth.exists_norm_completedHurwitzZetaEven₀_le_fixedStrip
      (0 : UnitAddCircle)
  have hCz : ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 →
      ‖completedRiemannZeta₀ s‖ ≤ C := by
    intro s hlo hhi
    simpa [completedRiemannZeta₀] using hC s hlo hhi
  refine ⟨1, by
    have hpi : 3 < Real.pi := Real.pi_gt_three
    norm_num
    nlinarith, 1, ?_⟩
  simpa using PLInteriorGrowth.isBigO_doubleExp_of_singleExpPoly
    (f := normalizedPrincipal) (384 * (C + 2)) (-1) 2
    (by positivity)
    (fun s hlo hhi ht => normalized_singleExp_bound hC0 hCz s hlo hhi ht)

private theorem norm_denominator_ge_one
    {z : ℂ} (hz : -1 ≤ z.re) : 1 ≤ ‖(z + 3) ^ 6‖ := by
  rw [norm_pow]
  have hre : 2 ≤ |(z + 3).re| := by
    rw [abs_of_nonneg (by simp; linarith)]
    simp
    linarith
  have hn : 2 ≤ ‖z + 3‖ := hre.trans (Complex.abs_re_le_norm _)
  exact one_le_pow₀ (by linarith)

private theorem abs_im_pow_le_denominator (z : ℂ) :
    |z.im| ^ 6 ≤ ‖(z + 3) ^ 6‖ := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (by
    simpa using Complex.abs_im_le_norm (z + 3)) 6

private theorem normalized_left_boundary_le
    (z : ℂ) (hz : z.re = -1) : ‖normalizedPrincipal z‖ ≤ 1600 := by
  let t := z.im
  have hzform : z = -1 + Complex.I * t := by
    apply Complex.ext <;> simp [t, hz]
  have hz1 : z ≠ 1 := by
    intro h
    have h' := congrArg Complex.re h
    norm_num [hz] at h'
  have hL : ‖riemannZeta z‖ ≤ 100 * (1 + |t|) ^ 2 := by
    have h := MAPDirichletLQuantitative.norm_LFunction_neg_one_add_mul_I_le
      (1 : DirichletCharacter ℂ 1) t
    rw [DirichletCharacter.LFunction_modOne_eq] at h
    simpa [hzform] using h
  have hsub : ‖z - 1‖ ≤ 2 * (1 + |t|) := by
    calc
      ‖z - 1‖ ≤ |(z - 1).re| + |(z - 1).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = 2 + |t| := by simp [hz, t]; norm_num
      _ ≤ 2 * (1 + |t|) := by linarith [abs_nonneg t]
  have hF : ‖principalRegularized z‖ ≤ 200 * (1 + |t|) ^ 3 := by
    rw [principalRegularized_apply_of_ne_one hz1, norm_mul]
    calc
      ‖z - 1‖ * ‖riemannZeta z‖ ≤
          (2 * (1 + |t|)) * (100 * (1 + |t|) ^ 2) :=
        mul_le_mul hsub hL (norm_nonneg _) (by positivity)
      _ = 200 * (1 + |t|) ^ 3 := by ring
  have hdenpos : 0 < ‖(z + 3) ^ 6‖ :=
    lt_of_lt_of_le zero_lt_one (norm_denominator_ge_one hz.symm.le)
  rw [normalizedPrincipal, norm_div]
  apply (div_le_iff₀ hdenpos).2
  by_cases ht : |t| ≤ 1
  · calc
      ‖principalRegularized z‖ ≤ 200 * (1 + |t|) ^ 3 := hF
      _ ≤ 1600 := by nlinarith [abs_nonneg t]
      _ ≤ 1600 * ‖(z + 3) ^ 6‖ := by
        nlinarith [norm_denominator_ge_one hz.symm.le]
  · have ht1 : 1 ≤ |t| := le_of_lt (lt_of_not_ge ht)
    have hpoly : (1 + |t|) ^ 3 ≤ 8 * |t| ^ 6 := by
      have htwo : 1 + |t| ≤ 2 * |t| := by linarith
      have hcub := pow_le_pow_left₀ (by positivity) htwo 3
      have h36 : |t| ^ 3 ≤ |t| ^ 6 := by
        have h3 : 1 ≤ |t| ^ 3 := one_le_pow₀ ht1
        calc |t| ^ 3 ≤ |t| ^ 3 * |t| ^ 3 := by
               simpa using mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ |t| ^ 3)
             _ = |t| ^ 6 := by ring
      nlinarith
    have himden : |t| ^ 6 ≤ ‖(z + 3) ^ 6‖ := by
      simpa [t] using abs_im_pow_le_denominator z
    calc
      ‖principalRegularized z‖ ≤ 200 * (1 + |t|) ^ 3 := hF
      _ ≤ 1600 * |t| ^ 6 := by nlinarith
      _ ≤ 1600 * ‖(z + 3) ^ 6‖ := by gcongr

private theorem normalized_right_boundary_le
    (z : ℂ) (hz : z.re = 2) : ‖normalizedPrincipal z‖ ≤ 1600 := by
  let t := z.im
  have hzform : z = 2 + Complex.I * t := by
    apply Complex.ext <;> simp [t, hz]
  have hz1 : z ≠ 1 := by
    intro h
    have h' := congrArg Complex.re h
    norm_num [hz] at h'
  have hL : ‖riemannZeta z‖ ≤ 3 := by
    have h := MAPDirichletLQuantitative.norm_LFunction_two_add_mul_I_le_zeta_two
      (1 : DirichletCharacter ℂ 1) t
    rw [DirichletCharacter.LFunction_modOne_eq] at h
    have hpi : Real.pi ^ 2 / 6 ≤ 3 := by
      nlinarith [Real.pi_pos.le, Real.pi_le_four]
    have h' : ‖riemannZeta z‖ ≤ Real.pi ^ 2 / 6 := by
      simpa [hzform] using h
    exact h'.trans hpi
  have hsub : ‖z - 1‖ ≤ 1 + |t| := by
    calc
      ‖z - 1‖ ≤ |(z - 1).re| + |(z - 1).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = 1 + |t| := by simp [hz, t]; norm_num
  have hF : ‖principalRegularized z‖ ≤ 3 * (1 + |t|) := by
    rw [principalRegularized_apply_of_ne_one hz1, norm_mul]
    calc
      ‖z - 1‖ * ‖riemannZeta z‖ ≤
          (1 + |t|) * ‖riemannZeta z‖ :=
        mul_le_mul_of_nonneg_right hsub (norm_nonneg _)
      _ ≤ (1 + |t|) * 3 :=
        mul_le_mul_of_nonneg_left hL (by positivity)
      _ = 3 * (1 + |t|) := by ring
  have hdenpos : 0 < ‖(z + 3) ^ 6‖ :=
    lt_of_lt_of_le zero_lt_one (norm_denominator_ge_one (by linarith [hz]))
  rw [normalizedPrincipal, norm_div]
  apply (div_le_iff₀ hdenpos).2
  by_cases ht : |t| ≤ 1
  · calc
      ‖principalRegularized z‖ ≤ 3 * (1 + |t|) := hF
      _ ≤ 6 := by nlinarith [abs_nonneg t]
      _ ≤ 1600 * ‖(z + 3) ^ 6‖ := by
        nlinarith [norm_denominator_ge_one (by linarith [hz])]
  · have ht1 : 1 ≤ |t| := le_of_lt (lt_of_not_ge ht)
    have himden : |t| ^ 6 ≤ ‖(z + 3) ^ 6‖ := by
      simpa [t] using abs_im_pow_le_denominator z
    have ht6 : |t| ≤ |t| ^ 6 := by
      have h5 : 1 ≤ |t| ^ 5 := one_le_pow₀ ht1
      calc |t| ≤ |t| * |t| ^ 5 := by
             simpa using mul_le_mul_of_nonneg_left h5 (abs_nonneg t)
           _ = |t| ^ 6 := by ring
    calc
      ‖principalRegularized z‖ ≤ 3 * (1 + |t|) := hF
      _ ≤ 6 * |t| := by nlinarith
      _ ≤ 1600 * |t| ^ 6 := by nlinarith
      _ ≤ 1600 * ‖(z + 3) ^ 6‖ := by gcongr

/-- Polynomial fixed-strip bound for the regularized conductor-one zeta
function.  The constant is deliberately coarse. -/
theorem norm_principalRegularized_fixedStrip_le
    {z : ℂ} (hzlo : -1 ≤ z.re) (hzhi : z.re ≤ 2) :
    ‖principalRegularized z‖ ≤ 1600 * ‖z + 3‖ ^ 6 := by
  have hnorm : ‖normalizedPrincipal z‖ ≤ 1600 :=
    PhragmenLindelof.vertical_strip
      (f := normalizedPrincipal) (C := 1600)
      normalized_diffContOnCl normalized_growthHypothesis
      normalized_left_boundary_le normalized_right_boundary_le hzlo hzhi
  have hzadd : z + 3 ≠ 0 := by
    intro heq
    have hre := congrArg Complex.re heq
    simp at hre
    linarith
  have heq : principalRegularized z = normalizedPrincipal z * (z + 3) ^ 6 := by
    simp [normalizedPrincipal, hzadd]
  rw [heq, norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right hnorm (by positivity)

#print axioms norm_principalRegularized_fixedStrip_le

end
end MAPPrincipalZetaFixedStrip
