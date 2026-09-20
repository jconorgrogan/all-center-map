import GuthMaynardS3LiteralLemma83Energy
import GuthMaynardS3LiteralProfile
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Lemma 8.3 transfer: profile L4 and smoothedRatio^4 by unit-collar energy

The Energy module bounds the weighted log-coordinate fourth moment by the
source additive energy `E(W)` with collar `|w1+w2-w3-w4| ≤ 1`. This module
changes variables on the compact ratio-profile support and applies the
existing 16× smoothing stability. Cardinality `|W|^4` appears only as the
explicit Schwartz tail of the plateau bump, not as energy control.
-/

namespace GuthMaynardS3LiteralLemma83Transfer

open MeasureTheory Set
open scoped BigOperators Real
open GuthMaynardS3LiteralLemma83Energy
open GuthMaynardS3LiteralProfile
open GuthMaynardJIteration GuthMaynardRatioKernelIdentity

noncomputable section

set_option maxHeartbeats 800000

/-- Two-term energy/tail envelope from the weighted log-coordinate bound. -/
def lemma83EnergyBound (W : Finset ℝ) (R : ℝ) (hR : 0 < R) (q : ℕ) : ℝ :=
  R * sourceBumpFourierConstant 1 zero_lt_one 0 *
    (sourceApproximateAdditiveEnergy W : ℝ) +
  R * sourceBumpFourierConstant 1 zero_lt_one q /
    (1 + R / (2 * Real.pi)) ^ q * (W.card : ℝ) ^ 4

/-- Jacobian of both signed log charts on the profile support `|u| ≤ 6`. -/
def lemma83ProfileJacobian : ℝ := 12

theorem four_pos : (0 : ℝ) < 4 := by norm_num

theorem one_div_sixteen_pos : (0 : ℝ) < 1 / 16 := by norm_num

theorem one_div_sixteen_le_six : (1 / 16 : ℝ) ≤ 6 := by norm_num

theorem six_pos : (0 : ℝ) < 6 := by norm_num

theorem log_inv_sixteen :
    Real.log (1 / 16 : ℝ) = -Real.log 16 := by
  rw [one_div, Real.log_inv]

theorem log_inv_sixteen_gt_neg_four :
    -4 < Real.log (1 / 16 : ℝ) := by
  rw [log_inv_sixteen]
  linarith [log_sixteen_lt_four]

theorem log_inv_sixteen_le_log_six :
    Real.log (1 / 16 : ℝ) ≤ Real.log 6 :=
  Real.log_le_log one_div_sixteen_pos one_div_sixteen_le_six

theorem logSupport_subset_Icc_four :
    Icc (Real.log (1 / 16 : ℝ)) (Real.log 6) ⊆ Icc (-4 : ℝ) 4 := by
  intro τ hτ
  have h := mem_Icc.mp hτ
  refine mem_Icc.mpr ⟨?_, ?_⟩
  · linarith [log_inv_sixteen_gt_neg_four, h.1]
  · exact h.2.trans log_six_lt_four.le

theorem Icc_four_subset_Icc_radius {R : ℝ} (hR : 4 ≤ R) :
    Icc (-4 : ℝ) 4 ⊆ Icc (-R) R := by
  intro τ hτ
  have h := mem_Icc.mp hτ
  exact mem_Icc.mpr ⟨by linarith, by linarith⟩

theorem R_pos_of_four_le {R : ℝ} (hR : 4 ≤ R) : 0 < R :=
  four_pos.trans_le hR

/-! ## Compact support of `ratioProfile²` -/

theorem ratioProfile_eq_zero_of_abs_le_inv_sixteen
    (W : Finset ℝ) {u : ℝ} (hu : |u| ≤ (1 / 16 : ℝ)) :
    ratioProfile W u = 0 := by
  simp [ratioProfile, ratioCutoff_eq_zero_near_zero hu]

theorem ratioProfile_eq_zero_of_six_lt_abs
    (W : Finset ℝ) {u : ℝ} (hu : 6 < |u|) :
    ratioProfile W u = 0 := by
  by_contra hne
  exact (not_le.mpr hu) (ratioProfile_supported W hne)

theorem six_lt_abs_of_not_mem {u : ℝ}
    (hpos : u ∉ Icc (1 / 16 : ℝ) 6)
    (hneg : u ∉ Icc (-6 : ℝ) (-1 / 16))
    (hsmall : ¬ |u| ≤ (1 / 16 : ℝ)) :
    6 < |u| := by
  have hgt : (1 / 16 : ℝ) < |u| := lt_of_not_ge hsmall
  cases le_total 0 u with
  | inl hu0 =>
      have huu : |u| = u := abs_of_nonneg hu0
      rw [huu] at hgt ⊢
      rw [mem_Icc, not_and_or] at hpos
      rcases hpos with h | h
      · exact (lt_asymm hgt (lt_of_not_ge h)).elim
      · exact lt_of_not_ge h
  | inr hu0 =>
      have hu0' : u < 0 := by
        by_contra hnot
        have : u = 0 := le_antisymm hu0 (le_of_not_gt hnot)
        subst u
        norm_num at hgt
      have huu : |u| = -u := abs_of_neg hu0'
      rw [huu] at hgt ⊢
      rw [mem_Icc, not_and_or] at hneg
      rcases hneg with h | h
      · have : u < -6 := lt_of_not_ge h
        linarith
      · have : -1 / 16 < u := lt_of_not_ge h
        linarith

theorem ratioProfile_sq_eq_zero_of_not_mem (W : Finset ℝ) {u : ℝ}
    (hpos : u ∉ Icc (1 / 16 : ℝ) 6)
    (hneg : u ∉ Icc (-6 : ℝ) (-1 / 16)) :
    ratioProfile W u ^ 2 = 0 := by
  by_cases hsmall : |u| ≤ (1 / 16 : ℝ)
  · simp [ratioProfile_eq_zero_of_abs_le_inv_sixteen W hsmall]
  · have hbig := six_lt_abs_of_not_mem hpos hneg hsmall
    simp [ratioProfile_eq_zero_of_six_lt_abs W hbig]

theorem ratioProfile_sq_eq_indicator_add (W : Finset ℝ) (u : ℝ) :
    ratioProfile W u ^ 2 =
      (Icc (1 / 16 : ℝ) 6).indicator (fun v => ratioProfile W v ^ 2) u +
      (Icc (-6 : ℝ) (-1 / 16)).indicator (fun v => ratioProfile W v ^ 2) u := by
  by_cases hpos : u ∈ Icc (1 / 16 : ℝ) 6
  · have hneg : u ∉ Icc (-6 : ℝ) (-1 / 16) := by
      intro h
      linarith [(mem_Icc.mp hpos).1, (mem_Icc.mp h).2]
    rw [Set.indicator_of_mem hpos, Set.indicator_of_notMem hneg]
    ring
  · by_cases hneg : u ∈ Icc (-6 : ℝ) (-1 / 16)
    · rw [Set.indicator_of_notMem hpos, Set.indicator_of_mem hneg]
      ring
    · have hz := ratioProfile_sq_eq_zero_of_not_mem W hpos hneg
      rw [Set.indicator_of_notMem hpos, Set.indicator_of_notMem hneg]
      simpa using hz

theorem integral_ratioProfile_sq_eq_pos_add_neg (W : Finset ℝ) :
    (∫ u : ℝ, ratioProfile W u ^ 2) =
      (∫ u : ℝ in Icc (1 / 16 : ℝ) 6, ratioProfile W u ^ 2) +
      (∫ u : ℝ in Icc (-6 : ℝ) (-1 / 16), ratioProfile W u ^ 2) := by
  have hf := ratioProfile_squareIntegrable W
  have hpos :
      Integrable ((Icc (1 / 16 : ℝ) 6).indicator fun u => ratioProfile W u ^ 2) :=
    (hf.integrableOn (s := Icc (1 / 16 : ℝ) 6)).integrable_indicator
      measurableSet_Icc
  have hneg :
      Integrable ((Icc (-6 : ℝ) (-1 / 16)).indicator fun u => ratioProfile W u ^ 2) :=
    (hf.integrableOn (s := Icc (-6 : ℝ) (-1 / 16))).integrable_indicator
      measurableSet_Icc
  have hpoint :
      (fun u => ratioProfile W u ^ 2) =
        fun u =>
          (Icc (1 / 16 : ℝ) 6).indicator (fun v => ratioProfile W v ^ 2) u +
          (Icc (-6 : ℝ) (-1 / 16)).indicator (fun v => ratioProfile W v ^ 2) u := by
    funext u
    exact ratioProfile_sq_eq_indicator_add W u
  calc
    (∫ u : ℝ, ratioProfile W u ^ 2) =
        ∫ u : ℝ,
          (Icc (1 / 16 : ℝ) 6).indicator (fun v => ratioProfile W v ^ 2) u +
          (Icc (-6 : ℝ) (-1 / 16)).indicator (fun v => ratioProfile W v ^ 2) u := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun u => congrFun hpoint u)
    _ = (∫ u : ℝ, (Icc (1 / 16 : ℝ) 6).indicator
          (fun v => ratioProfile W v ^ 2) u) +
        (∫ u : ℝ, (Icc (-6 : ℝ) (-1 / 16)).indicator
          (fun v => ratioProfile W v ^ 2) u) := integral_add hpos hneg
    _ = (∫ u : ℝ in Icc (1 / 16 : ℝ) 6, ratioProfile W u ^ 2) +
        (∫ u : ℝ in Icc (-6 : ℝ) (-1 / 16), ratioProfile W u ^ 2) := by
      rw [integral_indicator measurableSet_Icc, integral_indicator measurableSet_Icc]

theorem ratioProfile_sq_le_norm_four (W : Finset ℝ) (u : ℝ) :
    ratioProfile W u ^ 2 ≤ ‖ratioDirichletKernel W u‖ ^ 4 := by
  have hc := ratioCutoff_le_one u
  have h0 := ratioCutoff_nonneg u
  have hc2 : ratioCutoff u ^ 2 ≤ 1 := by nlinarith
  unfold ratioProfile
  have hpow :
      (ratioCutoff u * ‖ratioDirichletKernel W u‖ ^ 2) ^ 2 =
        ratioCutoff u ^ 2 * ‖ratioDirichletKernel W u‖ ^ 4 := by ring
  rw [hpow]
  have hmul :=
    mul_le_mul_of_nonneg_right hc2 (by positivity :
      0 ≤ ‖ratioDirichletKernel W u‖ ^ 4)
  simpa using hmul

/-! ## Exponential substitution on the positive and negative rays -/

theorem exp_image_Icc_log {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.exp '' Icc (Real.log a) (Real.log b) = Icc a b := by
  ext x
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    have hτ' := mem_Icc.mp hτ
    refine mem_Icc.mpr ⟨?_, ?_⟩
    · have := Real.exp_le_exp.mpr hτ'.1
      rwa [Real.exp_log ha] at this
    · have := Real.exp_le_exp.mpr hτ'.2
      rwa [Real.exp_log (ha.trans_le hab)] at this
  · intro hx
    have hx' := mem_Icc.mp hx
    have hxpos : 0 < x := ha.trans_le hx'.1
    refine ⟨Real.log x, mem_Icc.mpr ⟨?_, ?_⟩, Real.exp_log hxpos⟩
    · exact Real.log_le_log ha hx'.1
    · exact Real.log_le_log hxpos hx'.2

theorem neg_image_Icc (a b : ℝ) :
    (fun y : ℝ => -y) '' Icc a b = Icc (-b) (-a) := by
  ext x
  simp only [mem_image, mem_Icc]
  constructor
  · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
    exact ⟨neg_le_neg hy2, neg_le_neg hy1⟩
  · intro hx
    refine ⟨-x, ⟨?_, ?_⟩, by ring⟩
    · linarith
    · linarith

theorem negExp_image_Icc_log {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (fun τ : ℝ => -Real.exp τ) '' Icc (Real.log a) (Real.log b) =
      Icc (-b) (-a) := by
  have hcomp :
      (fun τ : ℝ => -Real.exp τ) '' Icc (Real.log a) (Real.log b) =
        (fun y : ℝ => -y) '' (Real.exp '' Icc (Real.log a) (Real.log b)) :=
    by
      ext x
      constructor
      · rintro ⟨τ, hτ, rfl⟩
        exact ⟨Real.exp τ, ⟨τ, hτ, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨τ, hτ, rfl⟩, rfl⟩
        exact ⟨τ, hτ, rfl⟩
  rw [hcomp, exp_image_Icc_log ha hab, neg_image_Icc]

theorem negExp_injective : Function.Injective fun τ : ℝ => -Real.exp τ := by
  intro x z hxz
  exact Real.exp_injective (neg_injective hxz)

theorem integral_Icc_comp_exp (g : ℝ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ u : ℝ in Icc a b, g u) =
      ∫ τ : ℝ in Icc (Real.log a) (Real.log b),
        g (Real.exp τ) * Real.exp τ := by
  have hjac :=
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (s := Icc (Real.log a) (Real.log b)) (f := Real.exp) (f' := Real.exp)
      measurableSet_Icc
      (fun τ _ => (Real.hasDerivAt_exp τ).hasDerivWithinAt)
      Real.exp_injective.injOn g
  rw [exp_image_Icc_log ha hab] at hjac
  rw [hjac]
  apply setIntegral_congr_fun measurableSet_Icc
  intro τ _hτ
  change |Real.exp τ| * g (Real.exp τ) = g (Real.exp τ) * Real.exp τ
  rw [abs_of_pos (Real.exp_pos τ)]
  ring

theorem integral_Icc_comp_neg_exp (g : ℝ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ u : ℝ in Icc (-b) (-a), g u) =
      ∫ τ : ℝ in Icc (Real.log a) (Real.log b),
        g (-Real.exp τ) * Real.exp τ := by
  have hjac :=
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (s := Icc (Real.log a) (Real.log b))
      (f := fun τ : ℝ => -Real.exp τ)
      (f' := fun τ : ℝ => -Real.exp τ)
      measurableSet_Icc
      (fun τ _ => (HasDerivAt.neg (Real.hasDerivAt_exp τ)).hasDerivWithinAt)
      negExp_injective.injOn g
  rw [negExp_image_Icc_log ha hab] at hjac
  rw [hjac]
  apply setIntegral_congr_fun measurableSet_Icc
  intro τ _hτ
  change |(-Real.exp τ)| * g (-Real.exp τ) = g (-Real.exp τ) * Real.exp τ
  rw [abs_neg, abs_of_pos (Real.exp_pos τ)]
  ring

theorem exp_le_six_of_mem_logSupport
    {τ : ℝ} (hτ : τ ∈ Icc (Real.log (1 / 16 : ℝ)) (Real.log 6)) :
    Real.exp τ ≤ 6 := by
  have := Real.exp_le_exp.mpr (mem_Icc.mp hτ).2
  rwa [Real.exp_log six_pos] at this

theorem integrableOn_ratioProfile_sq_comp_exp (W : Finset ℝ) :
    IntegrableOn
      (fun τ : ℝ => ratioProfile W (Real.exp τ) ^ 2 * Real.exp τ)
      (Icc (Real.log (1 / 16 : ℝ)) (Real.log 6)) :=
  ((((ratioProfile_continuous W).comp Real.continuous_exp).pow 2).mul
    Real.continuous_exp).continuousOn.integrableOn_compact
      (μ := volume) isCompact_Icc

theorem integrableOn_ratioProfile_sq_comp_negExp (W : Finset ℝ) :
    IntegrableOn
      (fun τ : ℝ => ratioProfile W (-Real.exp τ) ^ 2 * Real.exp τ)
      (Icc (Real.log (1 / 16 : ℝ)) (Real.log 6)) :=
  ((((ratioProfile_continuous W).comp
        (continuous_neg.comp Real.continuous_exp)).pow 2).mul
    Real.continuous_exp).continuousOn.integrableOn_compact
      (μ := volume) isCompact_Icc

theorem integrableOn_logDirichlet_four_logSupport (W : Finset ℝ) :
    IntegrableOn (fun τ : ℝ => ‖logDirichletKernel W τ‖ ^ 4)
      (Icc (Real.log (1 / 16 : ℝ)) (Real.log 6)) :=
  ((logDirichletKernel_continuous W).norm.pow 4).continuousOn.integrableOn_compact
    (μ := volume) isCompact_Icc

theorem integrableOn_logDirichlet_four_Icc_four (W : Finset ℝ) :
    IntegrableOn (fun τ : ℝ => ‖logDirichletKernel W τ‖ ^ 4)
      (Icc (-4 : ℝ) 4) :=
  ((logDirichletKernel_continuous W).norm.pow 4).continuousOn.integrableOn_compact
    (μ := volume) isCompact_Icc

theorem ratioProfile_sq_mul_exp_le_six_kernel
    (W : Finset ℝ) {τ : ℝ}
    (hτ : τ ∈ Icc (Real.log (1 / 16 : ℝ)) (Real.log 6)) :
    ratioProfile W (Real.exp τ) ^ 2 * Real.exp τ ≤
      6 * ‖logDirichletKernel W τ‖ ^ 4 := by
  have hexp := exp_le_six_of_mem_logSupport hτ
  have hker := ratioProfile_sq_le_norm_four W (Real.exp τ)
  have hlog :
      ‖ratioDirichletKernel W (Real.exp τ)‖ ^ 4 =
        ‖logDirichletKernel W τ‖ ^ 4 := by
    rw [ratioDirichletKernel_eq_logDirichletKernel, abs_of_pos (Real.exp_pos τ),
      Real.log_exp]
  rw [hlog] at hker
  have hmul :=
    mul_le_mul_of_nonneg_right hker (Real.exp_pos τ).le
  have h6 :=
    mul_le_mul_of_nonneg_left hexp (by positivity :
      0 ≤ ‖logDirichletKernel W τ‖ ^ 4)
  have : ‖logDirichletKernel W τ‖ ^ 4 * Real.exp τ ≤
      ‖logDirichletKernel W τ‖ ^ 4 * 6 := h6
  linarith

theorem ratioProfile_sq_mul_negExp_le_six_kernel
    (W : Finset ℝ) {τ : ℝ}
    (hτ : τ ∈ Icc (Real.log (1 / 16 : ℝ)) (Real.log 6)) :
    ratioProfile W (-Real.exp τ) ^ 2 * Real.exp τ ≤
      6 * ‖logDirichletKernel W τ‖ ^ 4 := by
  have hexp := exp_le_six_of_mem_logSupport hτ
  have hker := ratioProfile_sq_le_norm_four W (-Real.exp τ)
  have hlog :
      ‖ratioDirichletKernel W (-Real.exp τ)‖ ^ 4 =
        ‖logDirichletKernel W τ‖ ^ 4 := by
    rw [ratioDirichletKernel_eq_logDirichletKernel, abs_neg,
      abs_of_pos (Real.exp_pos τ), Real.log_exp]
  rw [hlog] at hker
  have hmul :=
    mul_le_mul_of_nonneg_right hker (Real.exp_pos τ).le
  have h6 :=
    mul_le_mul_of_nonneg_left hexp (by positivity :
      0 ≤ ‖logDirichletKernel W τ‖ ^ 4)
  have : ‖logDirichletKernel W τ‖ ^ 4 * Real.exp τ ≤
      ‖logDirichletKernel W τ‖ ^ 4 * 6 := h6
  linarith

theorem integral_ratioProfile_sq_pos_le (W : Finset ℝ) :
    (∫ u : ℝ in Icc (1 / 16 : ℝ) 6, ratioProfile W u ^ 2) ≤
      6 * ∫ τ : ℝ in Icc (Real.log (1 / 16 : ℝ)) (Real.log 6),
        ‖logDirichletKernel W τ‖ ^ 4 := by
  rw [integral_Icc_comp_exp (fun u => ratioProfile W u ^ 2)
    one_div_sixteen_pos one_div_sixteen_le_six]
  have hleft := integrableOn_ratioProfile_sq_comp_exp W
  have hright :
      IntegrableOn (fun τ : ℝ => 6 * ‖logDirichletKernel W τ‖ ^ 4)
        (Icc (Real.log (1 / 16 : ℝ)) (Real.log 6)) :=
    (continuous_const.mul
      ((logDirichletKernel_continuous W).norm.pow 4)).continuousOn.integrableOn_compact
      (μ := volume) isCompact_Icc
  have hle :=
    setIntegral_mono_on hleft hright measurableSet_Icc
      (fun τ hτ => ratioProfile_sq_mul_exp_le_six_kernel W hτ)
  refine hle.trans (le_of_eq ?_)
  exact integral_const_mul (6 : ℝ)
    (fun τ : ℝ => ‖logDirichletKernel W τ‖ ^ 4)

theorem integral_ratioProfile_sq_neg_le (W : Finset ℝ) :
    (∫ u : ℝ in Icc (-6 : ℝ) (-1 / 16), ratioProfile W u ^ 2) ≤
      6 * ∫ τ : ℝ in Icc (Real.log (1 / 16 : ℝ)) (Real.log 6),
        ‖logDirichletKernel W τ‖ ^ 4 := by
  have hnegEndpoint : (-1 / 16 : ℝ) = -(1 / 16 : ℝ) := by ring
  rw [hnegEndpoint]
  rw [integral_Icc_comp_neg_exp (fun u => ratioProfile W u ^ 2)
    one_div_sixteen_pos one_div_sixteen_le_six]
  have hleft := integrableOn_ratioProfile_sq_comp_negExp W
  have hright :
      IntegrableOn (fun τ : ℝ => 6 * ‖logDirichletKernel W τ‖ ^ 4)
        (Icc (Real.log (1 / 16 : ℝ)) (Real.log 6)) :=
    (continuous_const.mul
      ((logDirichletKernel_continuous W).norm.pow 4)).continuousOn.integrableOn_compact
      (μ := volume) isCompact_Icc
  have hle :=
    setIntegral_mono_on hleft hright measurableSet_Icc
      (fun τ hτ => ratioProfile_sq_mul_negExp_le_six_kernel W hτ)
  refine hle.trans (le_of_eq ?_)
  exact integral_const_mul (6 : ℝ)
    (fun τ : ℝ => ‖logDirichletKernel W τ‖ ^ 4)

theorem integral_logDirichlet_four_logSupport_le_Icc_four (W : Finset ℝ) :
    (∫ τ : ℝ in Icc (Real.log (1 / 16 : ℝ)) (Real.log 6),
        ‖logDirichletKernel W τ‖ ^ 4) ≤
      ∫ τ : ℝ in Icc (-4 : ℝ) 4, ‖logDirichletKernel W τ‖ ^ 4 :=
  setIntegral_mono_set (integrableOn_logDirichlet_four_Icc_four W)
    (Filter.Eventually.of_forall fun _ => by positivity)
    (Filter.Eventually.of_forall logSupport_subset_Icc_four)

theorem integral_logDirichlet_four_Icc_four_le_energy
    (W : Finset ℝ) {R : ℝ} (hR : 4 ≤ R) (q : ℕ) :
    (∫ τ : ℝ in Icc (-4 : ℝ) 4, ‖logDirichletKernel W τ‖ ^ 4) ≤
      lemma83EnergyBound W R (R_pos_of_four_le hR) q := by
  have hpos := R_pos_of_four_le hR
  have hIcc :=
    integral_Icc_le_weighted_four W hpos (a := (-4 : ℝ)) (b := (4 : ℝ))
      (by norm_num; exact hR) (by norm_num; exact hR)
  refine hIcc.trans ?_
  simpa [lemma83EnergyBound] using
    integral_bump_logDirichlet_four_le_energy W hpos q

/-! ## Unsmoothed profile L4 by unit-collar energy -/

theorem integral_ratioProfile_sq_le_energy
    (W : Finset ℝ) {R : ℝ} (hR : 4 ≤ R) (q : ℕ) :
    (∫ u : ℝ, ratioProfile W u ^ 2) ≤
      lemma83ProfileJacobian * lemma83EnergyBound W R (R_pos_of_four_le hR) q := by
  have hsplit := integral_ratioProfile_sq_eq_pos_add_neg W
  have hpos := integral_ratioProfile_sq_pos_le W
  have hneg := integral_ratioProfile_sq_neg_le W
  have hlog := integral_logDirichlet_four_logSupport_le_Icc_four W
  have hE := integral_logDirichlet_four_Icc_four_le_energy W hR q
  have h6 : (0 : ℝ) ≤ 6 := by norm_num
  have hlogE := hlog.trans hE
  have hposE : (∫ u : ℝ in Icc (1 / 16 : ℝ) 6, ratioProfile W u ^ 2) ≤
      6 * lemma83EnergyBound W R (R_pos_of_four_le hR) q :=
    hpos.trans (mul_le_mul_of_nonneg_left hlogE h6)
  have hnegE : (∫ u : ℝ in Icc (-6 : ℝ) (-1 / 16), ratioProfile W u ^ 2) ≤
      6 * lemma83EnergyBound W R (R_pos_of_four_le hR) q :=
    hneg.trans (mul_le_mul_of_nonneg_left hlogE h6)
  have hsum := add_le_add hposE hnegE
  rw [hsplit]
  unfold lemma83ProfileJacobian
  linarith

/-- Source range `v ≍ 1`: on `[1/2,2]` the cutoff equals one. -/
theorem ratioProfile_sq_eq_norm_four_on_unit
    (W : Finset ℝ) {u : ℝ} (hu : u ∈ Icc (1 / 2 : ℝ) 2) :
    ratioProfile W u ^ 2 = ‖ratioDirichletKernel W u‖ ^ 4 := by
  have hu' : u ∈ Icc (1 / 8 : ℝ) 4 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  unfold ratioProfile
  rw [ratioCutoff_eq_one hu']
  ring

theorem integral_ratioDirichletKernel_four_on_unit_le
    (W : Finset ℝ) {R : ℝ} (hR : 4 ≤ R) (q : ℕ) :
    (∫ v : ℝ in Icc (1 / 2 : ℝ) 2, ‖ratioDirichletKernel W v‖ ^ 4) ≤
      lemma83ProfileJacobian * lemma83EnergyBound W R (R_pos_of_four_le hR) q := by
  have hpt : ∀ v ∈ Icc (1 / 2 : ℝ) 2,
      ‖ratioDirichletKernel W v‖ ^ 4 = ratioProfile W v ^ 2 :=
    fun v hv => (ratioProfile_sq_eq_norm_four_on_unit W hv).symm
  have hnonneg : ∀ v : ℝ, 0 ≤ ratioProfile W v ^ 2 := fun _ => sq_nonneg _
  rw [setIntegral_congr_fun measurableSet_Icc hpt]
  exact (setIntegral_le_integral (ratioProfile_squareIntegrable W)
      (Filter.Eventually.of_forall hnonneg)).trans
    (integral_ratioProfile_sq_le_energy W hR q)

/-! ## Smoothing stability transfers the energy bound -/

theorem integral_smoothedRatio_four_le_energy
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ) {R : ℝ} (hR : 4 ≤ R) (q : ℕ) :
    (∫ u : ℝ, smoothedRatio B W u ^ 4) ≤
      16 * lemma83ProfileJacobian *
        lemma83EnergyBound W R (R_pos_of_four_le hR) q := by
  have hstab := GuthMaynardS3LiteralProfile.integral_smoothedRatio_four_le hB W
  have hprof := integral_ratioProfile_sq_le_energy W hR q
  have h16 : (0 : ℝ) ≤ 16 := by norm_num
  have hmul := mul_le_mul_of_nonneg_left hprof h16
  exact hstab.trans (by
    convert hmul using 1
    ring)

end
end GuthMaynardS3LiteralLemma83Transfer

#print axioms GuthMaynardS3LiteralLemma83Transfer.integral_ratioProfile_sq_le_energy
#print axioms GuthMaynardS3LiteralLemma83Transfer.integral_ratioDirichletKernel_four_on_unit_le
#print axioms GuthMaynardS3LiteralLemma83Transfer.integral_smoothedRatio_four_le_energy
