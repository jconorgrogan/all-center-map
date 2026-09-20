import GammaFactorInverseGrowth
import CompletedLVerticalBound
import Mathlib.Analysis.Complex.PhragmenLindelof

open Complex Filter Topology Asymptotics Real Set
open scoped Real Topology

namespace PLInteriorGrowth

noncomputable section

private theorem eventually_poly_exp_le_double_exp : ∀ᶠ t : ℝ in atTop,
    (1 + t) ^ 2 * Real.exp (Real.pi * t) ≤ Real.exp (Real.exp t) := by
  have hratio : ∀ᶠ t : ℝ in atTop, Real.pi + 2 ≤ Real.exp t / t := by
    simpa using (Real.tendsto_exp_div_pow_atTop 1).eventually
      (eventually_ge_atTop (Real.pi + 2))
  filter_upwards [hratio, eventually_gt_atTop (0 : ℝ)] with t hratio ht
  have hone : 1 + t ≤ Real.exp t := by
    simpa [add_comm] using Real.add_one_le_exp t
  have hsq : (1 + t) ^ 2 ≤ Real.exp (2 * t) := by
    calc
      (1 + t) ^ 2 ≤ (Real.exp t) ^ 2 := pow_le_pow_left₀ (by linarith) hone 2
      _ = Real.exp (2 * t) := by
        rw [show (2 : ℝ) * t = t + t by ring, Real.exp_add]
        ring
  have hlin : (Real.pi + 2) * t ≤ Real.exp t := (le_div_iff₀ ht).mp hratio
  calc
    (1 + t) ^ 2 * Real.exp (Real.pi * t) ≤
        Real.exp (2 * t) * Real.exp (Real.pi * t) :=
      mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
    _ = Real.exp ((Real.pi + 2) * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (Real.exp t) := Real.exp_le_exp.mpr hlin

/-- A source-neutral adapter: a polynomial times a single exponential in the
vertical variable is enough for Mathlib's double-exponential strip hypothesis.
This isolates the only asymptotic bookkeeping needed by the PL application. -/
theorem isBigO_doubleExp_of_singleExpPoly
    {E : Type*} [NormedAddCommGroup E] (f : ℂ → E) (A a b : ℝ) (hA : 0 ≤ A)
    (hf : ∀ z : ℂ, a < z.re → z.re < b → 2 ≤ |z.im| →
      ‖f z‖ ≤ A * (1 + |z.im|) ^ 2 * Real.exp (Real.pi * |z.im|)) :
    f =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)]
      fun z => Real.exp (Real.exp |z.im|) := by
  let u : ℂ → ℝ := _root_.abs ∘ im
  have hdouble_comap : ∀ᶠ z : ℂ in comap u atTop,
      (1 + |z.im|) ^ 2 * Real.exp (Real.pi * |z.im|) ≤
        Real.exp (Real.exp |z.im|) := by
    rw [eventually_comap]
    filter_upwards [eventually_poly_exp_le_double_exp] with t ht
    intro z hz
    rw [← hz] at ht
    exact ht
  have hheight_comap : ∀ᶠ z : ℂ in comap u atTop, 2 ≤ |z.im| := by
    rw [eventually_comap]
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
    intro z hz
    rw [← hz] at ht
    exact ht
  refine IsBigO.of_bound A ?_
  rw [eventually_inf_principal]
  filter_upwards [hdouble_comap, hheight_comap] with z hdouble hheight
  intro hz
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact (hf z hz.1 hz.2 hheight).trans
    (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hdouble hA)

variable {N : ℕ} [NeZero N]

/-- For each fixed nontrivial character, the completed-Hurwitz representation
and the reciprocal-gamma estimate give a completely proved crude interior
majorant.  Dependence of `A` on the fixed character is intentional and harmless
for Phragmen--Lindelof. -/
theorem exists_LFunction_singleExpPoly_fixedStrip
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| →
      ‖DirichletCharacter.LFunction χ s‖ ≤
        A * (1 + |s.im|) ^ 2 * Real.exp (Real.pi * |s.im|) := by
  obtain ⟨C, hC, hcomp⟩ :=
    exists_norm_completedDirichletLFunction_le_level_fixedStrip χ hχ
  let A : ℝ := C * (N : ℝ) * 192
  have hN : (0 : ℝ) ≤ N := by positivity
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro s hslo hshi ht
  have hlevel : N ≠ 1 := fun hN => hχ (DirichletCharacter.level_one' χ hN)
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s
    (Or.inr hlevel), norm_div, div_eq_mul_inv]
  have hgamma := norm_inv_gammaFactor_fixedStrip_le χ hslo hshi ht
  rw [norm_inv] at hgamma
  calc
    ‖DirichletCharacter.completedLFunction χ s‖ *
        ‖DirichletCharacter.gammaFactor χ s‖⁻¹ ≤
      (C * (N : ℝ)) *
        (192 * (1 + |s.im|) ^ 2 * Real.exp (Real.pi * |s.im|)) :=
      mul_le_mul (hcomp s hslo hshi) hgamma (inv_nonneg.mpr (norm_nonneg _))
        (mul_nonneg hC hN)
    _ = A * (1 + |s.im|) ^ 2 * Real.exp (Real.pi * |s.im|) := by
      dsimp [A]
      ring

/-- The exact growth premise expected by `PhragmenLindelof.vertical_strip`,
with the admissible rate `c = 1 < π/3`. -/
theorem LFunction_verticalStrip_growthHypothesis
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∃ c < Real.pi / ((2 : ℝ) - (-1 : ℝ)), ∃ B,
      DirichletCharacter.LFunction χ
        =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo (-1 : ℝ) 2)]
          fun z => Real.exp (B * Real.exp (c * |z.im|)) := by
  obtain ⟨A, hA, hbound⟩ := exists_LFunction_singleExpPoly_fixedStrip χ hχ
  refine ⟨1, by
    have hpi : 3 < Real.pi := Real.pi_gt_three
    norm_num
    nlinarith, 1, ?_⟩
  simpa using isBigO_doubleExp_of_singleExpPoly
    (f := DirichletCharacter.LFunction χ) A (-1) 2 hA
    (fun z hlo hhi ht => hbound z hlo.le hhi.le ht)

end

end PLInteriorGrowth

#print axioms PLInteriorGrowth.LFunction_verticalStrip_growthHypothesis
