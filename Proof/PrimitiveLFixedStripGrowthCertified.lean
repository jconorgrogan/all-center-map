import PhragmenGrowthAdapter
import DirichletLQuantitativeFoundation
import AppendixA4Detector

open Complex Filter Topology Asymptotics Real Set
open scoped Real Topology

namespace PLInteriorGrowth

noncomputable section

variable {N : ℕ} [NeZero N]

private def normalizedL (χ : DirichletCharacter ℂ N) (z : ℂ) : ℂ :=
  DirichletCharacter.LFunction χ z / (z + 3) ^ 2

private theorem normalizedL_diffContOnCl
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    DiffContOnCl ℂ (normalizedL χ) (re ⁻¹' Ioo (-1 : ℝ) 2) := by
  let d : ℂ → ℂ := fun z => (z + 3) ^ 2
  have hd : Differentiable ℂ d := by
    exact (differentiable_id.add_const 3).pow 2
  have hdne : ∀ z ∈ closure (re ⁻¹' Ioo (-1 : ℝ) 2), d z ≠ 0 := by
    intro z hz
    rw [Complex.closure_preimage_re, closure_Ioo (by norm_num : (-1 : ℝ) ≠ 2)] at hz
    have hzadd : z + 3 ≠ 0 := by
      intro heq
      have hre := congrArg Complex.re heq
      simp at hre
      linarith [hz.1]
    exact pow_ne_zero _ hzadd
  have hinv : DiffContOnCl ℂ d⁻¹ (re ⁻¹' Ioo (-1 : ℝ) 2) :=
    hd.diffContOnCl.inv hdne
  have hL : DiffContOnCl ℂ (DirichletCharacter.LFunction χ)
      (re ⁻¹' Ioo (-1 : ℝ) 2) :=
    (DirichletCharacter.differentiable_LFunction hχ).diffContOnCl
  have hmul := hinv.smul hL
  simpa [normalizedL, d, div_eq_inv_mul, mul_comm] using! hmul

private theorem one_le_norm_shift_sq {z : ℂ} (hz : -1 ≤ z.re) :
    1 ≤ ‖(z + 3) ^ 2‖ := by
  have hre : (2 : ℝ) ≤ |(z + 3).re| := by
    rw [abs_of_nonneg (by simp; linarith)]
    simp
    linarith
  have hnorm : 2 ≤ ‖z + 3‖ := hre.trans (Complex.abs_re_le_norm _)
  rw [norm_pow]
  nlinarith

private theorem norm_normalizedL_le
    (χ : DirichletCharacter ℂ N) {z : ℂ} (hz : -1 ≤ z.re) :
    ‖normalizedL χ z‖ ≤ ‖DirichletCharacter.LFunction χ z‖ := by
  rw [normalizedL, norm_div]
  exact div_le_self (norm_nonneg _) (one_le_norm_shift_sq hz)

private theorem normalizedL_growthHypothesis
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∃ c < Real.pi / ((2 : ℝ) - (-1 : ℝ)), ∃ B,
      normalizedL χ
        =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo (-1 : ℝ) 2)]
          fun z => Real.exp (B * Real.exp (c * |z.im|)) := by
  obtain ⟨c, hc, B, hL⟩ := LFunction_verticalStrip_growthHypothesis χ hχ
  refine ⟨c, hc, B, ?_⟩
  have hnorm : normalizedL χ
      =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo (-1 : ℝ) 2)]
        DirichletCharacter.LFunction χ := by
    refine IsBigO.of_bound 1 ?_
    rw [eventually_inf_principal]
    exact Eventually.of_forall fun z hz => by
      simpa using norm_normalizedL_le χ hz.1.le
  exact hnorm.trans hL

private theorem left_boundary_normalizedL_le
    (χ : DirichletCharacter ℂ N) (z : ℂ) (hz : z.re = -1) :
    ‖normalizedL χ z‖ ≤ 200 * (N : ℝ) ^ 2 := by
  let t := z.im
  have hzform : z = -1 + Complex.I * t := by
    apply Complex.ext <;> simp [t, hz]
  have hL : ‖DirichletCharacter.LFunction χ z‖ ≤
      100 * (N : ℝ) ^ 2 * (1 + |t|) ^ 2 := by
    rw [hzform]
    exact MAPDirichletLQuantitative.norm_LFunction_neg_one_add_mul_I_le χ t
  have hden : ‖z + 3‖ ^ 2 = 4 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [t, hz]
    ring
  have hpoly : (1 + |t|) ^ 2 ≤ 2 * ‖z + 3‖ ^ 2 := by
    rw [hden]
    nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
  have hdenpos : 0 < ‖(z + 3) ^ 2‖ := by
    rw [norm_pow, hden]
    positivity
  rw [normalizedL, norm_div]
  apply (div_le_iff₀ hdenpos).2
  rw [norm_pow]
  calc
    ‖DirichletCharacter.LFunction χ z‖ ≤
        100 * (N : ℝ) ^ 2 * (1 + |t|) ^ 2 := hL
    _ ≤ 100 * (N : ℝ) ^ 2 * (2 * ‖z + 3‖ ^ 2) := by
      gcongr
    _ = 200 * (N : ℝ) ^ 2 * ‖z + 3‖ ^ 2 := by ring

private theorem right_boundary_normalizedL_le
    (χ : DirichletCharacter ℂ N) (z : ℂ) (hz : z.re = 2) :
    ‖normalizedL χ z‖ ≤ 200 * (N : ℝ) ^ 2 := by
  let t := z.im
  have hzform : z = 2 + Complex.I * t := by
    apply Complex.ext <;> simp [t, hz]
  have hL : ‖DirichletCharacter.LFunction χ z‖ ≤ Real.pi ^ 2 / 6 := by
    rw [hzform]
    exact MAPDirichletLQuantitative.norm_LFunction_two_add_mul_I_le_zeta_two χ t
  have hthree : Real.pi ^ 2 / 6 ≤ 3 := by
    nlinarith [Real.pi_pos.le, Real.pi_le_four]
  have hNnat : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hNnat
  calc
    ‖normalizedL χ z‖ ≤ ‖DirichletCharacter.LFunction χ z‖ :=
      norm_normalizedL_le χ (by linarith)
    _ ≤ Real.pi ^ 2 / 6 := hL
    _ ≤ 3 := hthree
    _ ≤ 200 * (N : ℝ) ^ 2 := by nlinarith [sq_nonneg ((N : ℝ) - 1)]

/-- Uniform polynomial growth on the entire PL strip.  This is the quantitative
interior leaf shared by Appendix A.4 and A.5. -/
theorem norm_LFunction_fixedStrip_le
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {z : ℂ}
    (hzlo : -1 ≤ z.re) (hzhi : z.re ≤ 2) :
    ‖DirichletCharacter.LFunction χ z‖ ≤
      200 * (N : ℝ) ^ 2 * ‖z + 3‖ ^ 2 := by
  have hnorm : ‖normalizedL χ z‖ ≤ 200 * (N : ℝ) ^ 2 :=
    PhragmenLindelof.vertical_strip
    (f := normalizedL χ) (C := 200 * (N : ℝ) ^ 2)
    (normalizedL_diffContOnCl χ hχ)
    (normalizedL_growthHypothesis χ hχ)
    (left_boundary_normalizedL_le χ)
    (right_boundary_normalizedL_le χ) (z := z) hzlo hzhi
  have hzadd : z + 3 ≠ 0 := by
    intro heq
    have hre := congrArg Complex.re heq
    simp at hre
    linarith
  have heq : DirichletCharacter.LFunction χ z =
      normalizedL χ z * (z + 3) ^ 2 := by
    simp [normalizedL, hzadd]
  calc
    ‖DirichletCharacter.LFunction χ z‖ =
        ‖normalizedL χ z‖ * ‖z + 3‖ ^ 2 := by
      rw [heq, norm_mul, norm_pow]
    _ ≤ 200 * (N : ℝ) ^ 2 * ‖z + 3‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hnorm (by positivity)

/-- The exact universal proposition consumed by `AppendixA4Detector`.  No
primitivity is used: the theorem is stronger than the requested interface. -/
theorem primitiveLPolynomialStripGrowth :
    MAPAppendixA4Detector.PrimitiveLPolynomialStripGrowth := by
  refine ⟨2000, 4, by norm_num, by norm_num, ?_⟩
  intro q _ χ _hprim hχ s hslo hshi
  have hbase := norm_LFunction_fixedStrip_le χ hχ
    (by linarith [hslo]) (by linarith [hshi])
  have hqnat : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast hqnat
  have ht : 0 ≤ |s.im| := abs_nonneg _
  have hshift : ‖s + 3‖ ≤ 5 + |s.im| := by
    calc
      ‖s + 3‖ ≤ |(s + 3).re| + |(s + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |s.re + 3| + |s.im| := by simp
      _ ≤ 5 + |s.im| := by
        rw [abs_of_nonneg (by linarith [hslo])]
        linarith [hshi]
  have hfive : 5 + |s.im| ≤ 3 * (|s.im| + 2) := by linarith
  have hscale : 1 ≤ (q : ℝ) * (|s.im| + 2) := by nlinarith
  calc
    ‖DirichletCharacter.LFunction χ s‖ ≤
        200 * (q : ℝ) ^ 2 * ‖s + 3‖ ^ 2 := hbase
    _ ≤ 200 * (q : ℝ) ^ 2 * (5 + |s.im|) ^ 2 := by
      gcongr
    _ ≤ 1800 * ((q : ℝ) * (|s.im| + 2)) ^ 2 := by
      have hsquare : (5 + |s.im|) ^ 2 ≤ (3 * (|s.im| + 2)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hfive 2
      calc
        200 * (q : ℝ) ^ 2 * (5 + |s.im|) ^ 2 ≤
            200 * (q : ℝ) ^ 2 * (3 * (|s.im| + 2)) ^ 2 := by gcongr
        _ = 1800 * ((q : ℝ) * (|s.im| + 2)) ^ 2 := by ring
    _ ≤ 2000 * ((q : ℝ) * (|s.im| + 2)) ^ 4 := by
      let x : ℝ := (q : ℝ) * (|s.im| + 2)
      have hx2 : 1 ≤ x ^ 2 := one_le_pow₀ hscale
      have hpow : x ^ 2 ≤ x ^ (4 : ℕ) := by
        nlinarith [sq_nonneg (x ^ 2 - 1)]
      change 1800 * x ^ 2 ≤ 2000 * x ^ (4 : ℕ)
      exact (mul_le_mul_of_nonneg_left hpow (by norm_num)).trans
        (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
    _ = 2000 * ((q : ℝ) * (|s.im| + 2)) ^ (4 : ℝ) := by
      norm_num [Real.rpow_natCast]

end

end PLInteriorGrowth

#print axioms PLInteriorGrowth.norm_LFunction_fixedStrip_le
#print axioms PLInteriorGrowth.primitiveLPolynomialStripGrowth
