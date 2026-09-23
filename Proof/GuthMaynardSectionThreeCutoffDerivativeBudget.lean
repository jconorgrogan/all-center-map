import GuthMaynardSectionThreeCutoff
import GuthMaynardLemma43FourierIBP

/-!
# The literal derivative budget in Guth--Maynard Lemma 4.3(1)

This file keeps the paper's concrete function
`h_t(u) = sectionThreeCutoff u * u^(I*t)`.  The first step is the exact
all-order derivative formula for the real-variable complex power on the
positive half-line.  It is stated separately so that the eventual `L^1`
estimate cannot hide the dependence on `t` in a generic smoothness constant.
-/

namespace GuthMaynardSectionThreeCutoffDerivativeBudget

open Real Complex Set MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff
open scoped Topology
open GuthMaynardSectionThreeCutoff GuthMaynardLemma43FourierIBP

noncomputable section

/-- The descending coefficient in the `j`th derivative of `u^c`. -/
def cpowDescending (c : ℂ) : ℕ → ℂ
  | 0 => 1
  | j + 1 => cpowDescending c j * (c - (j : ℂ))

/-- Exact all-order derivative formula for a real-variable complex power,
away from the branch point `u=0`. -/
theorem iteratedDeriv_ofReal_cpow
    (c : ℂ) (j : ℕ) {u : ℝ} (hu : 0 < u) :
    iteratedDeriv j (fun x : ℝ => (x : ℂ) ^ c) u =
      cpowDescending c j * (u : ℂ) ^ (c - (j : ℂ)) := by
  induction j generalizing u with
  | zero => simp [cpowDescending]
  | succ j ih =>
      rw [iteratedDeriv_succ]
      have heq :
          iteratedDeriv j (fun x : ℝ => (x : ℂ) ^ c) =ᶠ[𝓝 u]
            fun x : ℝ => cpowDescending c j *
              (x : ℂ) ^ (c - (j : ℂ)) := by
        filter_upwards [Ioi_mem_nhds hu] with x hx
        exact ih hx
      rw [heq.deriv_eq]
      by_cases hzero : c - (j : ℂ) = 0
      · have hconst :
            (fun x : ℝ => cpowDescending c j *
                (x : ℂ) ^ (c - (j : ℂ))) =
              fun _x : ℝ => cpowDescending c j := by
          funext x
          simp [hzero]
        rw [hconst, deriv_const]
        simp [cpowDescending, hzero]
      · have hderiv :=
          (hasDerivAt_ofReal_cpow_const hu.ne'
            hzero).const_mul (cpowDescending c j)
        rw [hderiv.deriv]
        simp only [cpowDescending]
        have hexp :
            c - (j : ℂ) - 1 = c - ((j + 1 : ℕ) : ℂ) := by
          push_cast
          ring
        rw [hexp]
        ring

/-- Each new descending factor costs at most `(j+1)(1+|t|)`.  This is the
literal source of the polynomial dependence on the spectral parameter. -/
theorem norm_imaginary_descending_factor_le
    (t : ℝ) (j : ℕ) :
    ‖Complex.I * (t : ℂ) - (j : ℂ)‖ ≤
      (j + 1 : ℝ) * (1 + |t|) := by
  calc
    ‖Complex.I * (t : ℂ) - (j : ℂ)‖ ≤
        ‖Complex.I * (t : ℂ)‖ + ‖(j : ℂ)‖ := norm_sub_le _ _
    _ = |t| + j := by
      simp [Real.norm_eq_abs]
    _ ≤ (j + 1 : ℝ) * (1 + |t|) := by
      have habs : 0 ≤ |t| := abs_nonneg t
      nlinarith

/-- Uniform factorial bound for the exact descending coefficient. -/
theorem norm_cpowDescending_imaginary_le
    (t : ℝ) (j : ℕ) :
    ‖cpowDescending (Complex.I * (t : ℂ)) j‖ ≤
      (j.factorial : ℝ) * (1 + |t|) ^ j := by
  induction j with
  | zero => simp [cpowDescending]
  | succ j ih =>
      rw [cpowDescending, norm_mul]
      have hfactor := norm_imaginary_descending_factor_le t j
      have hnonnegCoeff :
          0 ≤ (j.factorial : ℝ) * (1 + |t|) ^ j := by positivity
      have hnonnegFactor :
          0 ≤ ‖Complex.I * (t : ℂ) - (j : ℂ)‖ := norm_nonneg _
      calc
        ‖cpowDescending (Complex.I * (t : ℂ)) j‖ *
            ‖Complex.I * (t : ℂ) - (j : ℂ)‖ ≤
          ((j.factorial : ℝ) * (1 + |t|) ^ j) *
            ((j + 1 : ℝ) * (1 + |t|)) :=
              mul_le_mul ih hfactor hnonnegFactor hnonnegCoeff
        _ = (((j + 1).factorial : ℕ) : ℝ) *
            (1 + |t|) ^ (j + 1) := by
              rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
              simp only [Nat.cast_add, Nat.cast_one]
              ring

/-- Smoothness of the complex power on the positive half-line.  The proof
uses the literal `exp(log(x) * c)` definition, so no branch assertion is
being hidden. -/
theorem ofReal_cpow_contDiffAt_of_pos
    (c : ℂ) {u : ℝ} (hu : 0 < u) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => (x : ℂ) ^ c) u := by
  have hlogR : ContDiffAt ℝ (⊤ : ℕ∞) Real.log u :=
    (Real.contDiffAt_log).2 hu.ne'
  have hlogC : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : ℝ => (Real.log x : ℂ)) u :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp u hlogR
  have harg : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : ℝ => (Real.log x : ℂ) * c) u :=
    hlogC.mul contDiffAt_const
  have hexp : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : ℝ => Complex.exp ((Real.log x : ℂ) * c)) u :=
    Complex.contDiff_exp.contDiffAt.comp u harg
  apply hexp.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hu] with x hx
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  rw [← Complex.ofReal_log hx.le]

def sectionThreeOscillatory (t x : ℝ) : ℂ :=
  sectionThreeCutoff x * (x : ℂ) ^ (Complex.I * (t : ℂ))

theorem sectionThreeOscillatory_supported
    (t x : ℝ) (hx : x ∉ Set.Icc (1 : ℝ) 2) :
    sectionThreeOscillatory t x = 0 := by
  rw [sectionThreeOscillatory, sectionThreeCutoff_supported x hx, zero_mul]

/-- The cutoff removes the branch point at zero, making the literal
oscillatory function globally smooth. -/
theorem sectionThreeOscillatory_contDiff (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (sectionThreeOscillatory t) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : 0 < x
  · exact sectionThreeCutoff_contDiff.contDiffAt.mul
      (ofReal_cpow_contDiffAt_of_pos _ hx)
  · have hxOne : x < 1 := by linarith
    apply (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun _y : ℝ => (0 : ℂ)) x).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hxOne] with y hy
    apply sectionThreeOscillatory_supported
    simp only [Set.mem_Icc, not_and_or, not_le]
    exact Or.inl hy

theorem sectionThreeOscillatory_hasCompactSupport (t : ℝ) :
    HasCompactSupport (sectionThreeOscillatory t) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) 2))
  exact sectionThreeOscillatory_supported t

def sectionThreeCutoffSchwartz : 𝓢(ℝ, ℂ) :=
  (HasCompactSupport.intro
      (isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) 2))
      sectionThreeCutoff_supported).toSchwartzMap sectionThreeCutoff_contDiff

def sectionThreeOscillatorySchwartz (t : ℝ) : 𝓢(ℝ, ℂ) :=
  (sectionThreeOscillatory_hasCompactSupport t).toSchwartzMap
    (sectionThreeOscillatory_contDiff t)

@[simp] theorem sectionThreeOscillatorySchwartz_apply (t x : ℝ) :
    sectionThreeOscillatorySchwartz t x = sectionThreeOscillatory t x := rfl

def cutoffDerivativeSup (i : ℕ) : ℝ :=
  SchwartzMap.seminorm ℂ 0 0
    (schwartzIteratedDerivative i sectionThreeCutoffSchwartz)

/-- Every cutoff derivative is bounded by one fixed Schwartz seminorm. -/
theorem norm_iteratedDeriv_sectionThreeCutoff_le
    (i : ℕ) (x : ℝ) :
    ‖iteratedDeriv i sectionThreeCutoff x‖ ≤ cutoffDerivativeSup i := by
  have hseminorm := SchwartzMap.norm_le_seminorm ℂ
    (schwartzIteratedDerivative i sectionThreeCutoffSchwartz) x
  rw [schwartzIteratedDerivative_apply] at hseminorm
  simpa [cutoffDerivativeSup, sectionThreeCutoffSchwartz,
    HasCompactSupport.toSchwartzMap] using! hseminorm

/-- The exact imaginary-power derivative budget on the support interval. -/
theorem norm_iteratedDeriv_imaginary_cpow_le
    (t : ℝ) (j : ℕ) {u : ℝ} (hu : u ∈ Set.Icc (1 : ℝ) 2) :
    ‖iteratedDeriv j
        (fun x : ℝ => (x : ℂ) ^ (Complex.I * (t : ℂ))) u‖ ≤
      (j.factorial : ℝ) * (1 + |t|) ^ j := by
  rw [iteratedDeriv_ofReal_cpow _ j (by linarith [hu.1]), norm_mul]
  have hpow :
      ‖(u : ℂ) ^ (Complex.I * (t : ℂ) - (j : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [hu.1])]
    apply Real.rpow_le_one_of_one_le_of_nonpos hu.1
    simp
  calc
    ‖cpowDescending (Complex.I * (t : ℂ)) j‖ *
        ‖(u : ℂ) ^ (Complex.I * (t : ℂ) - (j : ℂ))‖ ≤
      ((j.factorial : ℝ) * (1 + |t|) ^ j) * 1 :=
        mul_le_mul (norm_cpowDescending_imaginary_le t j) hpow
          (norm_nonneg _) (by positivity)
    _ = (j.factorial : ℝ) * (1 + |t|) ^ j := mul_one _

/-- An explicit fixed constant for the `j`th derivative budget. -/
def lemma43DerivativeConstant (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * cutoffDerivativeSup i * ((j - i).factorial : ℝ)

theorem cutoffDerivativeSup_nonneg (i : ℕ) :
    0 ≤ cutoffDerivativeSup i := by
  exact apply_nonneg _ _

/-- Pointwise form of the all-order product-rule estimate.  All binomial,
cutoff-derivative, and descending-power factors remain visible. -/
theorem norm_iteratedDeriv_sectionThreeOscillatory_le
    (t : ℝ) (j : ℕ) {u : ℝ} (hu : u ∈ Set.Icc (1 : ℝ) 2) :
    ‖iteratedDeriv j (sectionThreeOscillatory t) u‖ ≤
      lemma43DerivativeConstant j * (1 + |t|) ^ j := by
  have hcut : ContDiffAt ℝ (j : WithTop ℕ∞) sectionThreeCutoff u :=
    sectionThreeCutoff_contDiff.contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hpowSmooth : ContDiffAt ℝ (j : WithTop ℕ∞)
      (fun x : ℝ => (x : ℂ) ^ (Complex.I * (t : ℂ))) u :=
    (ofReal_cpow_contDiffAt_of_pos _ (by linarith [hu.1])).of_le
      (WithTop.coe_le_coe.mpr le_top)
  change ‖iteratedDeriv j
      (sectionThreeCutoff *
        fun x : ℝ => (x : ℂ) ^ (Complex.I * (t : ℂ))) u‖ ≤ _
  rw [iteratedDeriv_mul hcut hpowSmooth]
  calc
    ‖∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℂ) * iteratedDeriv i sectionThreeCutoff u *
          iteratedDeriv (j - i)
            (fun x : ℝ => (x : ℂ) ^ (Complex.I * (t : ℂ))) u‖ ≤
      ∑ i ∈ Finset.range (j + 1),
        ‖(j.choose i : ℂ) * iteratedDeriv i sectionThreeCutoff u *
          iteratedDeriv (j - i)
            (fun x : ℝ => (x : ℂ) ^ (Complex.I * (t : ℂ))) u‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (j + 1),
        ((j.choose i : ℝ) * cutoffDerivativeSup i *
          ((j - i).factorial : ℝ)) * (1 + |t|) ^ j := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hcutBound := norm_iteratedDeriv_sectionThreeCutoff_le i u
      have hpowBound := norm_iteratedDeriv_imaginary_cpow_le t (j - i) hu
      have hbase : (1 : ℝ) ≤ 1 + |t| := by
        linarith [abs_nonneg t]
      have hpowerMono : (1 + |t|) ^ (j - i) ≤ (1 + |t|) ^ j :=
        pow_le_pow_right₀ hbase (Nat.sub_le j i)
      have hchooseNonneg : 0 ≤ (j.choose i : ℝ) := by positivity
      have hcutNonneg : 0 ≤ cutoffDerivativeSup i :=
        cutoffDerivativeSup_nonneg i
      have hfactorialNonneg : 0 ≤ ((j - i).factorial : ℝ) := by positivity
      simp only [norm_mul, Complex.norm_natCast]
      calc
        (j.choose i : ℝ) * ‖iteratedDeriv i sectionThreeCutoff u‖ *
            ‖iteratedDeriv (j - i)
              (fun x : ℝ => (x : ℂ) ^ (Complex.I * (t : ℂ))) u‖ ≤
          (j.choose i : ℝ) * cutoffDerivativeSup i *
            ‖iteratedDeriv (j - i)
              (fun x : ℝ => (x : ℂ) ^ (Complex.I * (t : ℂ))) u‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hcutBound hchooseNonneg)
                (norm_nonneg _)
        _ ≤
          (j.choose i : ℝ) * cutoffDerivativeSup i *
            (((j - i).factorial : ℝ) * (1 + |t|) ^ (j - i)) := by
              exact mul_le_mul_of_nonneg_left hpowBound
                (mul_nonneg hchooseNonneg hcutNonneg)
        _ = ((j.choose i : ℝ) * cutoffDerivativeSup i *
              ((j - i).factorial : ℝ)) * (1 + |t|) ^ (j - i) := by
              ring
        _ ≤ ((j.choose i : ℝ) * cutoffDerivativeSup i *
              ((j - i).factorial : ℝ)) * (1 + |t|) ^ j := by
              exact mul_le_mul_of_nonneg_left hpowerMono
                (mul_nonneg (mul_nonneg hchooseNonneg hcutNonneg)
                  hfactorialNonneg)
    _ = lemma43DerivativeConstant j * (1 + |t|) ^ j := by
      rw [lemma43DerivativeConstant, Finset.sum_mul]

theorem iteratedDeriv_sectionThreeOscillatory_eq_zero_of_not_mem
    (t : ℝ) (j : ℕ) {u : ℝ} (hu : u ∉ Set.Icc (1 : ℝ) 2) :
    iteratedDeriv j (sectionThreeOscillatory t) u = 0 := by
  have heq : sectionThreeOscillatory t =ᶠ[𝓝 u]
      fun _x : ℝ => (0 : ℂ) := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hu] with x hx
    exact sectionThreeOscillatory_supported t x hx
  rw [heq.iteratedDeriv_eq j, iteratedDeriv_const]
  split <;> simp_all

theorem integrable_norm_iteratedDeriv_sectionThreeOscillatory
    (t : ℝ) (j : ℕ) :
    Integrable (fun u : ℝ =>
      ‖iteratedDeriv j (sectionThreeOscillatory t) u‖) := by
  have hschwartz :=
    (schwartzIteratedDerivative j
      (sectionThreeOscillatorySchwartz t)).integrable
      (μ := (volume : Measure ℝ))
  have hnorm := hschwartz.norm
  apply hnorm.congr
  filter_upwards with x
  rw [schwartzIteratedDerivative_apply]
  congr 1

theorem lemma43DerivativeConstant_nonneg (j : ℕ) :
    0 ≤ lemma43DerivativeConstant j := by
  unfold lemma43DerivativeConstant
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg
    (mul_nonneg (by positivity) (cutoffDerivativeSup_nonneg i))
    (by positivity)

/-- The exact remaining calculus leaf in Lemma 4.3(1): for every natural
`j`, the `L¹` norm of the `j`th derivative is at most an explicit fixed
constant times `(1+|t|)^j`. -/
theorem integral_norm_iteratedDeriv_sectionThreeOscillatory_le
    (t : ℝ) (j : ℕ) :
    (∫ u : ℝ, ‖iteratedDeriv j (sectionThreeOscillatory t) u‖) ≤
      lemma43DerivativeConstant j * (1 + |t|) ^ j := by
  have hrestrict :
      (∫ u : ℝ, ‖iteratedDeriv j (sectionThreeOscillatory t) u‖) =
        ∫ u : ℝ in Set.Icc (1 : ℝ) 2,
          ‖iteratedDeriv j (sectionThreeOscillatory t) u‖ := by
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    by_cases hu : u ∈ Set.Icc (1 : ℝ) 2
    · simp [hu]
    · simp [hu,
        iteratedDeriv_sectionThreeOscillatory_eq_zero_of_not_mem t j hu]
  rw [hrestrict]
  calc
    (∫ u : ℝ in Set.Icc (1 : ℝ) 2,
        ‖iteratedDeriv j (sectionThreeOscillatory t) u‖) ≤
      ∫ _u : ℝ in Set.Icc (1 : ℝ) 2,
        lemma43DerivativeConstant j * (1 + |t|) ^ j := by
      apply MeasureTheory.integral_mono_ae
      · exact (integrable_norm_iteratedDeriv_sectionThreeOscillatory t j).integrableOn
      · exact MeasureTheory.integrableOn_const
          (hs := by simp [Real.volume_Icc])
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
        exact norm_iteratedDeriv_sectionThreeOscillatory_le t j hu
    _ = lemma43DerivativeConstant j * (1 + |t|) ^ j := by
      rw [MeasureTheory.setIntegral_const]
      norm_num [Real.volume_Icc]

/-- Guth--Maynard Lemma 4.3(1) for the literal Section 3 cutoff, with the
paper's dependence on `t` and arbitrary Fourier decay order exposed. -/
theorem lemma43_part_one_sectionThreeOscillatory
    (t : ℝ) (j : ℕ) {xi : ℝ} (hxi : xi ≠ 0) :
    ‖(𝓕 (sectionThreeOscillatorySchwartz t) : 𝓢(ℝ, ℂ)) xi‖ ≤
      (lemma43DerivativeConstant j * (1 + |t|) ^ j) / |xi| ^ j := by
  apply norm_fourier_le_derivativeBudget_div_absPow
    (sectionThreeOscillatorySchwartz t) j hxi
  have hcoe :
      (fun y : ℝ => sectionThreeOscillatorySchwartz t y) =
        sectionThreeOscillatory t := by
    funext y
    exact sectionThreeOscillatorySchwartz_apply t y
  rw [hcoe]
  exact integral_norm_iteratedDeriv_sectionThreeOscillatory_le t j


end

end GuthMaynardSectionThreeCutoffDerivativeBudget

#print axioms GuthMaynardSectionThreeCutoffDerivativeBudget.iteratedDeriv_ofReal_cpow
#print axioms GuthMaynardSectionThreeCutoffDerivativeBudget.norm_cpowDescending_imaginary_le
#print axioms GuthMaynardSectionThreeCutoffDerivativeBudget.sectionThreeOscillatory_contDiff
#print axioms GuthMaynardSectionThreeCutoffDerivativeBudget.norm_iteratedDeriv_sectionThreeOscillatory_le
#print axioms GuthMaynardSectionThreeCutoffDerivativeBudget.integral_norm_iteratedDeriv_sectionThreeOscillatory_le
#print axioms GuthMaynardSectionThreeCutoffDerivativeBudget.lemma43_part_one_sectionThreeOscillatory
