import MRTFaithfulLowPage47Geometry
import MRTEquation81Kernel

/-!
# MRT Proposition 5.1: page-47 two-window Schur bound

This file closes the `x`-variable Cauchy--Schwarz estimate after the exact
page-47 recentering.  It retains the faithful radius-`H` ordinary sliding mass.
-/

namespace MAPMRTFaithfulLowPage47Schur

open MeasureTheory Set
open MAPMRTCorollary53Source
open MAPMRTProposition51FirstAnalytic
open MAPMRTProposition51ProjectionHighGeometry
open MAPMRTFaithfulLowPage47Geometry
open MAPMRTEquation81Kernel

noncomputable section

/-- The normalized quadratic page-47 kernel has a uniform whole-line mass.
The constant `4` reuses the certified equation-(81) Cauchy comparison. -/
theorem integral_scaled_abs_decay_le_four {a : ℝ} (ha : 0 < a) :
    (∫ z : ℝ, a / (1 + a * |z|) ^ 2) ≤ 4 := by
  have hk := integral_equation81Kernel_le_four
    (R := 1 / a) (x := 0) (by positivity)
  have hpoint : (fun z : ℝ ↦ a / (1 + a * |z|) ^ 2) =
      fun z : ℝ ↦ a * equation81Kernel (1 / a) 0 z := by
    funext z
    unfold equation81Kernel
    simp only [zero_sub, abs_neg]
    field_simp [ha.ne']
  rw [hpoint, integral_const_mul]
  calc
    a * (∫ z : ℝ, equation81Kernel (1 / a) 0 z) ≤
        a * (4 * (1 / a)) := mul_le_mul_of_nonneg_left hk ha.le
    _ = 4 := by field_simp [ha.ne']

theorem integrable_scaled_abs_decay {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : ℝ ↦ a / (1 + a * |z|) ^ 2) := by
  have hk := integrable_equation81Kernel (R := 1 / a) (x := 0) (by positivity)
  have heq : (fun z : ℝ ↦ a / (1 + a * |z|) ^ 2) =
      fun z : ℝ ↦ a * equation81Kernel (1 / a) 0 z := by
    funext z
    unfold equation81Kernel
    simp only [zero_sub, abs_neg]
    field_simp [ha.ne']
  rw [heq]
  exact hk.const_mul a

/-- The two-window page-47 majorant has square mass at most four times the
ordinary sliding mass, with the exact logarithmic Jacobian `exp z`. -/
theorem integral_sq_faithfulPage47OrdinaryMajorant_le
    (X H z : ℝ) (f : ℕ → ℂ) :
    (∫ x : ℝ, faithfulPage47OrdinaryMajorant X H z f x ^ 2) ≤
      4 * Real.exp z * ordinarySlidingMass X H f := by
  let A : ℝ → ℝ := fun y ↦ ordinaryWindowSum X H f (y - H)
  let B : ℝ → ℝ := fun y ↦ ordinaryWindowSum X H f y
  have hbase : Integrable (fun y : ℝ ↦ B y ^ 2) := by
    simpa [B] using integrable_sq_ordinaryWindowSum X H f
  have hA : Integrable (fun y : ℝ ↦ A y ^ 2) := by
    simpa [A, B, sub_eq_add_neg] using hbase.comp_add_right (-H)
  have hright : Integrable (fun x : ℝ ↦
      2 * (A (Real.exp (-z) * x) ^ 2 + B (Real.exp (-z) * x) ^ 2)) := by
    have hs : Real.exp (-z) ≠ 0 := ne_of_gt (Real.exp_pos _)
    exact (((hA.comp_mul_left' hs).add (hbase.comp_mul_left' hs)).const_mul 2)
  have hpoint (x : ℝ) :
      faithfulPage47OrdinaryMajorant X H z f x ^ 2 ≤
        2 * (A (Real.exp (-z) * x) ^ 2 +
          B (Real.exp (-z) * x) ^ 2) := by
    unfold faithfulPage47OrdinaryMajorant A B
    nlinarith [sq_nonneg
      (ordinaryWindowSum X H f (Real.exp (-z) * x - H) -
        ordinaryWindowSum X H f (Real.exp (-z) * x))]
  have hscaleA := Measure.integral_comp_mul_left
    (fun y : ℝ ↦ A y ^ 2) (Real.exp (-z))
  have hscaleB := Measure.integral_comp_mul_left
    (fun y : ℝ ↦ B y ^ 2) (Real.exp (-z))
  have hinvabs : |(Real.exp (-z))⁻¹| = Real.exp z := by
    rw [abs_of_pos (inv_pos.mpr (Real.exp_pos _)), Real.exp_neg]
    simp
  have hIntA : (∫ y : ℝ, A y ^ 2) = ordinarySlidingMass X H f := by
    unfold A
    have ht := MeasureTheory.integral_add_right_eq_self
      (μ := volume) (fun y : ℝ ↦ ordinaryWindowSum X H f y ^ 2) (-H)
    simpa [sub_eq_add_neg, ordinarySlidingMass_eq_integral_ordinaryWindowSum]
      using ht
  have hIntB : (∫ y : ℝ, B y ^ 2) = ordinarySlidingMass X H f := by
    simpa [B] using (ordinarySlidingMass_eq_integral_ordinaryWindowSum X H f).symm
  have hScaledA :
      (∫ x : ℝ, A (Real.exp (-z) * x) ^ 2) =
        Real.exp z * (∫ y : ℝ, A y ^ 2) := by
    calc
      _ = |(Real.exp (-z))⁻¹| • (∫ y : ℝ, A y ^ 2) := hscaleA
      _ = _ := by rw [hinvabs]; rfl
  have hScaledB :
      (∫ x : ℝ, B (Real.exp (-z) * x) ^ 2) =
        Real.exp z * (∫ y : ℝ, B y ^ 2) := by
    calc
      _ = |(Real.exp (-z))⁻¹| • (∫ y : ℝ, B y ^ 2) := hscaleB
      _ = _ := by rw [hinvabs]; rfl
  calc
    (∫ x : ℝ, faithfulPage47OrdinaryMajorant X H z f x ^ 2) ≤
        ∫ x : ℝ, 2 * (A (Real.exp (-z) * x) ^ 2 +
          B (Real.exp (-z) * x) ^ 2) := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun x ↦ sq_nonneg _
      · exact hright
      · exact Filter.Eventually.of_forall hpoint
    _ = 2 * ((∫ x : ℝ, A (Real.exp (-z) * x) ^ 2) +
          ∫ x : ℝ, B (Real.exp (-z) * x) ^ 2) := by
      rw [integral_const_mul, integral_add
        (hA.comp_mul_left' (ne_of_gt (Real.exp_pos _)))
        (hbase.comp_mul_left' (ne_of_gt (Real.exp_pos _)))]
    _ = 2 * (Real.exp z * (∫ y : ℝ, A y ^ 2) +
          Real.exp z * (∫ y : ℝ, B y ^ 2)) := by
      rw [hScaledA, hScaledB]
    _ = 4 * Real.exp z * ordinarySlidingMass X H f := by
      rw [hIntA, hIntB]
      ring

/-- Cauchy--Schwarz against an `L²`-normalized dual function. -/
theorem integral_norm_mul_faithfulPage47OrdinaryMajorant_sq_le
    {X H z : ℝ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (hgL1 : Integrable g)
    (hg : Integrable (fun x : ℝ ↦ ‖g x‖ ^ 2))
    (hgOne : (∫ x : ℝ, ‖g x‖ ^ 2) ≤ 1) :
    (∫ x : ℝ, ‖g x‖ * faithfulPage47OrdinaryMajorant X H z f x) ^ 2 ≤
      4 * Real.exp z * ordinarySlidingMass X H f := by
  have hwInt : Integrable (fun x : ℝ ↦
      faithfulPage47OrdinaryMajorant X H z f x ^ 2) := by
    unfold faithfulPage47OrdinaryMajorant
    let A : ℝ → ℝ := fun y ↦ ordinaryWindowSum X H f (y - H)
    let B : ℝ → ℝ := fun y ↦ ordinaryWindowSum X H f y
    have hbase : Integrable (fun y : ℝ ↦ B y ^ 2) := by
      simpa [B] using integrable_sq_ordinaryWindowSum X H f
    have hA : Integrable (fun y : ℝ ↦ A y ^ 2) := by
      simpa [A, B, sub_eq_add_neg] using hbase.comp_add_right (-H)
    have hs : Real.exp (-z) ≠ 0 := ne_of_gt (Real.exp_pos _)
    have hAs := hA.comp_mul_left' hs
    have hBs := hbase.comp_mul_left' hs
    have hright : Integrable (fun x : ℝ ↦
        2 * (A (Real.exp (-z) * x) ^ 2 +
          B (Real.exp (-z) * x) ^ 2)) :=
      (hAs.add hBs).const_mul 2
    have hmeas : AEStronglyMeasurable (fun x : ℝ ↦
        faithfulPage47OrdinaryMajorant X H z f x ^ 2) := by
      unfold faithfulPage47OrdinaryMajorant
      have hBlin : Integrable (ordinaryWindowSum X H f) :=
        integrable_ordinaryWindowSum X H f
      have hAlin : Integrable (fun y : ℝ ↦ ordinaryWindowSum X H f (y - H)) := by
        simpa [sub_eq_add_neg] using hBlin.comp_add_right (-H)
      exact ((hAlin.comp_mul_left' hs).aestronglyMeasurable.add
        (hBlin.comp_mul_left' hs).aestronglyMeasurable).pow 2
    apply hright.mono' hmeas
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    unfold faithfulPage47OrdinaryMajorant A B
    nlinarith [sq_nonneg
      (ordinaryWindowSum X H f (Real.exp (-z) * x - H) -
        ordinaryWindowSum X H f (Real.exp (-z) * x))]
  have hmajorNonneg : ∀ x,
      0 ≤ faithfulPage47OrdinaryMajorant X H z f x := by
    intro x
    unfold faithfulPage47OrdinaryMajorant
    exact add_nonneg (ordinaryWindowSum_nonneg _ _ _ _)
      (ordinaryWindowSum_nonneg _ _ _ _)
  have hgMem : MemLp g 2 := by
    rw [memLp_two_iff_integrable_sq_norm hgL1.aestronglyMeasurable]
    exact hg
  have hgLp : MemLp (fun x : ℝ ↦ ‖g x‖) (ENNReal.ofReal (2 : ℝ)) := by
    simpa using hgMem.norm
  have hwMeas : AEStronglyMeasurable
      (faithfulPage47OrdinaryMajorant X H z f) := by
    have hsqrt := Real.continuous_sqrt.comp_aestronglyMeasurable
      hwInt.aestronglyMeasurable
    apply hsqrt.congr
    filter_upwards with x
    rw [Real.sqrt_sq (hmajorNonneg x)]
  have hwLpBase : MemLp (faithfulPage47OrdinaryMajorant X H z f) 2 := by
    rw [memLp_two_iff_integrable_sq_norm hwMeas]
    apply hwInt.congr
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hmajorNonneg x)]
  have hwLp : MemLp (faithfulPage47OrdinaryMajorant X H z f)
      (ENNReal.ofReal (2 : ℝ)) := by simpa using hwLpBase
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr (by norm_num)
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall fun x ↦ norm_nonneg (g x))
    (Filter.Eventually.of_forall hmajorNonneg) hgLp hwLp
  have hholder' :
      (∫ x : ℝ, ‖g x‖ * faithfulPage47OrdinaryMajorant X H z f x) ≤
        Real.sqrt (∫ x : ℝ, ‖g x‖ ^ 2) *
          Real.sqrt (∫ x : ℝ,
            faithfulPage47OrdinaryMajorant X H z f x ^ 2) := by
    simpa [Real.sqrt_eq_rpow, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)] using hholder
  have hleft0 : 0 ≤ ∫ x : ℝ,
      ‖g x‖ * faithfulPage47OrdinaryMajorant X H z f x :=
    integral_nonneg fun x ↦ mul_nonneg (norm_nonneg _) (hmajorNonneg x)
  have htarget0 : 0 ≤ 4 * Real.exp z * ordinarySlidingMass X H f := by
    unfold ordinarySlidingMass
    positivity
  have hsqrtG : Real.sqrt (∫ x : ℝ, ‖g x‖ ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact hgOne
  have hbound :
      (∫ x : ℝ, ‖g x‖ * faithfulPage47OrdinaryMajorant X H z f x) ≤
        Real.sqrt (4 * Real.exp z * ordinarySlidingMass X H f) := by
    calc
      _ ≤ Real.sqrt (∫ x : ℝ, ‖g x‖ ^ 2) *
          Real.sqrt (∫ x : ℝ,
            faithfulPage47OrdinaryMajorant X H z f x ^ 2) := hholder'
      _ ≤ 1 * Real.sqrt (∫ x : ℝ,
            faithfulPage47OrdinaryMajorant X H z f x ^ 2) := by gcongr
      _ ≤ Real.sqrt (4 * Real.exp z * ordinarySlidingMass X H f) := by
        simpa using Real.sqrt_le_sqrt
          (integral_sq_faithfulPage47OrdinaryMajorant_le X H z f)
  calc
    _ ≤ (Real.sqrt (4 * Real.exp z * ordinarySlidingMass X H f)) ^ 2 :=
      pow_le_pow_left₀ hleft0 hbound 2
    _ = _ := Real.sq_sqrt htarget0

/-- The complete normalized page-47 Schur integral on the sharp logarithmic
support.  This is the deterministic weighted summation left after Tonelli has
moved the finite coefficient sum past the localized oscillatory integral. -/
theorem weighted_page47_schur_integral_sq_le
    {a X H : ℝ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (ha : 0 < a) (hgL1 : Integrable g)
    (hg : Integrable (fun x : ℝ ↦ ‖g x‖ ^ 2))
    (hgOne : (∫ x : ℝ, ‖g x‖ ^ 2) ≤ 1) :
    (∫ z : ℝ,
        (a / (1 + a * |z|) ^ 2) *
          if 15 / 64 ≤ Real.exp z ∧ Real.exp z ≤ 129 / 32 then
            ∫ x : ℝ, ‖g x‖ * faithfulPage47OrdinaryMajorant X H z f x
          else 0) ^ 2 ≤
      258 * ordinarySlidingMass X H f := by
  let M : ℝ := ordinarySlidingMass X H f
  let C : ℝ := Real.sqrt ((129 / 8) * M)
  have hM : 0 ≤ M := by
    unfold M ordinarySlidingMass
    exact integral_nonneg fun _ ↦ sq_nonneg _
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hkInt := integrable_scaled_abs_decay ha
  have hright : Integrable (fun z : ℝ ↦
      (a / (1 + a * |z|) ^ 2) * C) := hkInt.mul_const C
  have hinner (z : ℝ)
      (hz : 15 / 64 ≤ Real.exp z ∧ Real.exp z ≤ 129 / 32) :
      (∫ x : ℝ, ‖g x‖ * faithfulPage47OrdinaryMajorant X H z f x) ≤ C := by
    apply Real.le_sqrt_of_sq_le
    have hs := integral_norm_mul_faithfulPage47OrdinaryMajorant_sq_le
      (X := X) (H := H) (z := z) (f := f) hgL1 hg hgOne
    calc
      _ ≤ 4 * Real.exp z * M := by simpa [M] using hs
      _ ≤ (129 / 8) * M := by
        exact mul_le_mul_of_nonneg_right (by nlinarith [hz.2]) hM
  have hleftNonneg : ∀ z : ℝ, 0 ≤
      (a / (1 + a * |z|) ^ 2) *
        (if 15 / 64 ≤ Real.exp z ∧ Real.exp z ≤ 129 / 32 then
          ∫ x : ℝ, ‖g x‖ * faithfulPage47OrdinaryMajorant X H z f x
        else 0) := by
    intro z
    apply mul_nonneg (by positivity)
    split_ifs
    · exact integral_nonneg fun x ↦ mul_nonneg (norm_nonneg _)
        (by
          unfold faithfulPage47OrdinaryMajorant
          exact add_nonneg (ordinaryWindowSum_nonneg _ _ _ _)
            (ordinaryWindowSum_nonneg _ _ _ _))
    · positivity
  have hmono :
      (∫ z : ℝ,
          (a / (1 + a * |z|) ^ 2) *
            if 15 / 64 ≤ Real.exp z ∧ Real.exp z ≤ 129 / 32 then
              ∫ x : ℝ, ‖g x‖ * faithfulPage47OrdinaryMajorant X H z f x
            else 0) ≤
        ∫ z : ℝ, (a / (1 + a * |z|) ^ 2) * C := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall hleftNonneg
    · exact hright
    · filter_upwards with z
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      by_cases hz : 15 / 64 ≤ Real.exp z ∧ Real.exp z ≤ 129 / 32
      · rw [if_pos hz]
        exact hinner z hz
      · rw [if_neg hz]
        exact hC
  have hk := integral_scaled_abs_decay_le_four ha
  have hrightEval :
      (∫ z : ℝ, (a / (1 + a * |z|) ^ 2) * C) ≤ 4 * C := by
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right hk hC
  have htotal := hmono.trans hrightEval
  have htotal0 : 0 ≤ ∫ z : ℝ,
      (a / (1 + a * |z|) ^ 2) *
        if 15 / 64 ≤ Real.exp z ∧ Real.exp z ≤ 129 / 32 then
          ∫ x : ℝ, ‖g x‖ * faithfulPage47OrdinaryMajorant X H z f x
        else 0 := integral_nonneg hleftNonneg
  calc
    _ ≤ (4 * C) ^ 2 := pow_le_pow_left₀ htotal0 htotal 2
    _ = 258 * M := by
      unfold C
      rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num) hM)]
      ring
    _ = _ := rfl

theorem weighted_page47_schur_integral_sq_le_half_range
    {a X H : ℝ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (ha : 0 < a) (hgL1 : Integrable g)
    (hg : Integrable (fun x : ℝ ↦ ‖g x‖ ^ 2))
    (hgOne : (∫ x : ℝ, ‖g x‖ ^ 2) ≤ 1) :
    (∫ z : ℝ,
        (a / (1 + a * |z|) ^ 2) *
          if 7 / 32 ≤ Real.exp z ∧ Real.exp z ≤ 65 / 16 then
            ∫ x : ℝ, ‖g x‖ * faithfulPage47OrdinaryMajorant X H z f x
          else 0) ^ 2 ≤
      260 * ordinarySlidingMass X H f := by
  let M : ℝ := ordinarySlidingMass X H f
  let C : ℝ := Real.sqrt ((65 / 4) * M)
  have hM : 0 ≤ M := by
    unfold M ordinarySlidingMass
    exact integral_nonneg fun _ ↦ sq_nonneg _
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hkInt := integrable_scaled_abs_decay ha
  have hright : Integrable (fun z : ℝ ↦
      (a / (1 + a * |z|) ^ 2) * C) := hkInt.mul_const C
  have hinner (z : ℝ)
      (hz : 7 / 32 ≤ Real.exp z ∧ Real.exp z ≤ 65 / 16) :
      (∫ x : ℝ, ‖g x‖ * faithfulPage47OrdinaryMajorant X H z f x) ≤ C := by
    apply Real.le_sqrt_of_sq_le
    have hs := integral_norm_mul_faithfulPage47OrdinaryMajorant_sq_le
      (X := X) (H := H) (z := z) (f := f) hgL1 hg hgOne
    calc
      _ ≤ 4 * Real.exp z * M := by simpa [M] using hs
      _ ≤ (65 / 4) * M := by
        exact mul_le_mul_of_nonneg_right (by nlinarith [hz.2]) hM
  have hleftNonneg : ∀ z : ℝ, 0 ≤
      (a / (1 + a * |z|) ^ 2) *
        (if 7 / 32 ≤ Real.exp z ∧ Real.exp z ≤ 65 / 16 then
          ∫ x : ℝ, ‖g x‖ * faithfulPage47OrdinaryMajorant X H z f x
        else 0) := by
    intro z
    apply mul_nonneg (by positivity)
    split_ifs
    · exact integral_nonneg fun x ↦ mul_nonneg (norm_nonneg _)
        (by
          unfold faithfulPage47OrdinaryMajorant
          exact add_nonneg (ordinaryWindowSum_nonneg _ _ _ _)
            (ordinaryWindowSum_nonneg _ _ _ _))
    · positivity
  have hmono :
      (∫ z : ℝ,
          (a / (1 + a * |z|) ^ 2) *
            if 7 / 32 ≤ Real.exp z ∧ Real.exp z ≤ 65 / 16 then
              ∫ x : ℝ, ‖g x‖ * faithfulPage47OrdinaryMajorant X H z f x
            else 0) ≤
        ∫ z : ℝ, (a / (1 + a * |z|) ^ 2) * C := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall hleftNonneg
    · exact hright
    · filter_upwards with z
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      by_cases hz : 7 / 32 ≤ Real.exp z ∧ Real.exp z ≤ 65 / 16
      · rw [if_pos hz]
        exact hinner z hz
      · rw [if_neg hz]
        exact hC
  have hk := integral_scaled_abs_decay_le_four ha
  have hrightEval :
      (∫ z : ℝ, (a / (1 + a * |z|) ^ 2) * C) ≤ 4 * C := by
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right hk hC
  have htotal := hmono.trans hrightEval
  have htotal0 : 0 ≤ ∫ z : ℝ,
      (a / (1 + a * |z|) ^ 2) *
        if 7 / 32 ≤ Real.exp z ∧ Real.exp z ≤ 65 / 16 then
          ∫ x : ℝ, ‖g x‖ * faithfulPage47OrdinaryMajorant X H z f x
        else 0 := integral_nonneg hleftNonneg
  calc
    _ ≤ (4 * C) ^ 2 := pow_le_pow_left₀ htotal0 htotal 2
    _ = 260 * M := by
      unfold C
      rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num) hM)]
      ring
    _ = _ := rfl

#print axioms integral_sq_faithfulPage47OrdinaryMajorant_le
#print axioms integral_norm_mul_faithfulPage47OrdinaryMajorant_sq_le
#print axioms integral_scaled_abs_decay_le_four
#print axioms weighted_page47_schur_integral_sq_le

end
end MAPMRTFaithfulLowPage47Schur
