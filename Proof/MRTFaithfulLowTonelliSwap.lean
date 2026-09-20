import MRTFaithfulLowTonelli

/-! Exact page-47 finite-sum/Tonelli swap before the two-window domination. -/
namespace MAPMRTFaithfulLowTonelliSwap

open MeasureTheory Set
open MAPMRTCorollary53Source MAPMRTProposition51FirstAnalytic
open MAPMRTFaithfulLowPage47Geometry MAPMRTFaithfulLowTonelli
open MAPMRTFaithfulLowPage47Schur

noncomputable section

theorem measurable_faithfulPage47OrdinaryMajorant
    (X H : ℝ) (f : ℕ → ℂ) :
    Measurable (fun p : ℝ × ℝ ↦
      faithfulPage47OrdinaryMajorant X H p.1 f p.2) := by
  unfold faithfulPage47OrdinaryMajorant ordinaryWindowSum
  apply Measurable.add
  · apply Finset.measurable_sum
    intro n hn
    let c : ℝ × ℝ → ℝ := fun p ↦ Real.exp (-p.1) * p.2 - H
    have hc : Measurable c := by unfold c; fun_prop
    apply Measurable.ite
    · exact (measurableSet_le hc measurable_const).inter
        (measurableSet_le measurable_const (hc.add measurable_const))
    · exact measurable_const
    · exact measurable_const
  · apply Finset.measurable_sum
    intro n hn
    let c : ℝ × ℝ → ℝ := fun p ↦ Real.exp (-p.1) * p.2
    have hc : Measurable c := by unfold c; fun_prop
    apply Measurable.ite
    · exact (measurableSet_le hc measurable_const).inter
        (measurableSet_le measurable_const (hc.add measurable_const))
    · exact measurable_const
    · exact measurable_const

/-- The exact page-47 Fubini identity.  Crude coefficient mass is used only to
certify absolute integrability; it does not enter the quantitative estimate. -/
theorem integral_norm_mul_sum_integral_decay_eq_swapped
    {A X H : ℝ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (hA : 0 < A) (hg : Integrable g) :
    (∫ x : ℝ, ‖g x‖ *
      (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        ‖f n‖ * ∫ w : ℝ, faithfulLocalizedDecay A X H x
          (Real.log n - Real.log X) w)) =
      ∫ z : ℝ, (1 / (1 + A * |z|) ^ 2) *
        (∫ x : ℝ, ‖g x‖ *
          faithfulPage47ChangedPhysicalWindowSum X H z f x) := by
  let K : ℝ → ℝ := fun z ↦ 1 / (1 + A * |z|) ^ 2
  let F : ℝ → ℝ → ℝ := fun z x ↦
    K z * ‖g x‖ * faithfulPage47ChangedPhysicalWindowSum X H z f x
  have hK : Integrable K := by
    have hs := integrable_scaled_abs_decay hA
    have hAK : Integrable (fun z : ℝ ↦ A * K z) := by
      convert hs using 1
      funext z
      unfold K
      ring
    have hunit : IsUnit A := isUnit_iff_ne_zero.mpr hA.ne'
    exact (integrable_const_mul_iff hunit K).mp hAK
  have hFmeas : AEStronglyMeasurable (Function.uncurry F) := by
    unfold F
    exact ((hK.aestronglyMeasurable.comp_fst.mul
      hg.norm.aestronglyMeasurable.comp_snd).mul
      (measurable_faithfulPage47ChangedPhysicalWindowSum X H f).aestronglyMeasurable)
  have hmajor : Integrable (fun p : ℝ × ℝ ↦
      coefficientMass X f * (K p.1 * ‖g p.2‖)) :=
    (hK.mul_prod hg.norm).const_mul (coefficientMass X f)
  have hFint : Integrable (Function.uncurry F) := by
    apply hmajor.mono' hFmeas
    filter_upwards with p
    change |K p.1 * ‖g p.2‖ *
      faithfulPage47ChangedPhysicalWindowSum X H p.1 f p.2| ≤ _
    have hK0 : 0 ≤ K p.1 := by unfold K; positivity
    have hw0 := faithfulPage47ChangedPhysicalWindowSum_nonneg X H p.1 f p.2
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg hK0 (norm_nonneg _)) hw0)]
    have h := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (faithfulPage47ChangedPhysicalWindowSum_le_coefficientMass X H p.1 f p.2)
        (norm_nonneg (g p.2))) hK0
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  have hswap := MeasureTheory.integral_integral_swap hFint
  calc
    (∫ x : ℝ, ‖g x‖ *
      (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        ‖f n‖ * ∫ w : ℝ, faithfulLocalizedDecay A X H x
          (Real.log n - Real.log X) w)) =
        ∫ x : ℝ, ‖g x‖ * (∫ z : ℝ, K z *
          faithfulPage47ChangedPhysicalWindowSum X H z f x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [sum_integral_faithfulLocalizedDecay_eq hA X H x f]
    _ = ∫ x : ℝ, ∫ z : ℝ, F z x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with z
      unfold F
      ring
    _ = ∫ z : ℝ, ∫ x : ℝ, F z x := hswap.symm
    _ = ∫ z : ℝ, K z * (∫ x : ℝ, ‖g x‖ *
          faithfulPage47ChangedPhysicalWindowSum X H z f x) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      unfold F
      ring
    _ = _ := by rfl

/-- Exact on/off-strip domination of the swapped inner integral. -/
theorem changed_inner_le_strip_majorant
    {X H z : ℝ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 ≤ H) (hHquarter : H ≤ X / 4)
    (hg : Integrable g)
    (hgSupport : ∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0) :
    (∫ x : ℝ, ‖g x‖ *
        faithfulPage47ChangedPhysicalWindowSum X H z f x) ≤
      if 15 / 64 ≤ Real.exp z ∧ Real.exp z ≤ 129 / 32 then
        ∫ x : ℝ, ‖g x‖ * faithfulPage47OrdinaryMajorant X H z f x
      else 0 := by
  by_cases hz : 15 / 64 ≤ Real.exp z ∧ Real.exp z ≤ 129 / 32
  · rw [if_pos hz]
    have hright : Integrable (fun x : ℝ ↦
        ‖g x‖ * faithfulPage47OrdinaryMajorant X H z f x) := by
      have hm : AEStronglyMeasurable (fun x : ℝ ↦
          faithfulPage47OrdinaryMajorant X H z f x) :=
        (measurable_faithfulPage47OrdinaryMajorant X H f).comp
          (measurable_const.prodMk measurable_id) |>.aestronglyMeasurable
      have hb : ∀ᵐ x : ℝ ∂volume,
          ‖faithfulPage47OrdinaryMajorant X H z f x‖ ≤
            2 * coefficientMass X f := Filter.Eventually.of_forall fun x ↦ by
        have h1 := ordinaryWindowSum_le_coefficientMass X H f
          (Real.exp (-z) * x - H)
        have h2 := ordinaryWindowSum_le_coefficientMass X H f
          (Real.exp (-z) * x)
        unfold faithfulPage47OrdinaryMajorant
        rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg
          (ordinaryWindowSum_nonneg _ _ _ _)
          (ordinaryWindowSum_nonneg _ _ _ _))]
        linarith
      simpa [mul_comm] using hg.norm.bdd_mul hm hb
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun x ↦ mul_nonneg (norm_nonneg _)
        (faithfulPage47ChangedPhysicalWindowSum_nonneg X H z f x)
    · exact hright
    · filter_upwards with x
      by_cases hx : x ∈ Icc (X / 2) (4 * X)
      · exact mul_le_mul_of_nonneg_left
          (faithfulPage47ChangedPhysicalWindowSum_le_majorant
            hX hH hHquarter hx.1 hx.2) (norm_nonneg _)
      · rw [hgSupport x hx]
        simp
  · rw [if_neg hz]
    rw [show (∫ x : ℝ, ‖g x‖ *
          faithfulPage47ChangedPhysicalWindowSum X H z f x) = 0 by
          apply integral_eq_zero_of_ae
          filter_upwards with x
          by_cases hx : x ∈ Icc (X / 2) (4 * X)
          · rw [faithfulPage47ChangedPhysicalWindowSum_eq_zero_off_strip
              hX hH hHquarter hx.1 hx.2 hz]
            simp
          · rw [hgSupport x hx]
            simp]

theorem changed_inner_le_strip_majorant_half_range
    {X H z : ℝ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 ≤ H) (hHquarter : H ≤ X / 2)
    (hg : Integrable g)
    (hgSupport : ∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0) :
    (∫ x : ℝ, ‖g x‖ *
        faithfulPage47ChangedPhysicalWindowSum X H z f x) ≤
      if 7 / 32 ≤ Real.exp z ∧ Real.exp z ≤ 65 / 16 then
        ∫ x : ℝ, ‖g x‖ * faithfulPage47OrdinaryMajorant X H z f x
      else 0 := by
  by_cases hz : 7 / 32 ≤ Real.exp z ∧ Real.exp z ≤ 65 / 16
  · rw [if_pos hz]
    have hright : Integrable (fun x : ℝ ↦
        ‖g x‖ * faithfulPage47OrdinaryMajorant X H z f x) := by
      have hm : AEStronglyMeasurable (fun x : ℝ ↦
          faithfulPage47OrdinaryMajorant X H z f x) :=
        (measurable_faithfulPage47OrdinaryMajorant X H f).comp
          (measurable_const.prodMk measurable_id) |>.aestronglyMeasurable
      have hb : ∀ᵐ x : ℝ ∂volume,
          ‖faithfulPage47OrdinaryMajorant X H z f x‖ ≤
            2 * coefficientMass X f := Filter.Eventually.of_forall fun x ↦ by
        have h1 := ordinaryWindowSum_le_coefficientMass X H f
          (Real.exp (-z) * x - H)
        have h2 := ordinaryWindowSum_le_coefficientMass X H f
          (Real.exp (-z) * x)
        unfold faithfulPage47OrdinaryMajorant
        rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg
          (ordinaryWindowSum_nonneg _ _ _ _)
          (ordinaryWindowSum_nonneg _ _ _ _))]
        linarith
      simpa [mul_comm] using hg.norm.bdd_mul hm hb
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun x ↦ mul_nonneg (norm_nonneg _)
        (faithfulPage47ChangedPhysicalWindowSum_nonneg X H z f x)
    · exact hright
    · filter_upwards with x
      by_cases hx : x ∈ Icc (X / 2) (4 * X)
      · exact mul_le_mul_of_nonneg_left
          (faithfulPage47ChangedPhysicalWindowSum_le_majorant_half_range
            hX hH hHquarter hx.1 hx.2) (norm_nonneg _)
      · rw [hgSupport x hx]
        simp
  · rw [if_neg hz]
    rw [show (∫ x : ℝ, ‖g x‖ *
          faithfulPage47ChangedPhysicalWindowSum X H z f x) = 0 by
          apply integral_eq_zero_of_ae
          filter_upwards with x
          by_cases hx : x ∈ Icc (X / 2) (4 * X)
          · rw [faithfulPage47ChangedPhysicalWindowSum_eq_zero_off_strip_half_range
              hX hH hHquarter hx.1 hx.2 hz]
            simp
          · rw [hgSupport x hx]
            simp]

theorem weighted_changed_window_integral_sq_le_half_range
    {a X H : ℝ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (ha : 0 < a) (hX : 0 < X) (hH : 0 ≤ H) (hHalf : H ≤ X / 2)
    (hgSupport : ∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0)
    (hgL1 : Integrable g)
    (hg : Integrable (fun x : ℝ ↦ ‖g x‖ ^ 2))
    (hgOne : (∫ x : ℝ, ‖g x‖ ^ 2) ≤ 1) :
    (∫ z : ℝ,
        (a / (1 + a * |z|) ^ 2) *
          (∫ x : ℝ, ‖g x‖ * faithfulPage47ChangedPhysicalWindowSum X H z f x)) ^ 2 ≤
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
  have hchanged (z : ℝ) :
      (∫ x : ℝ, ‖g x‖ * faithfulPage47ChangedPhysicalWindowSum X H z f x) ≤ C := by
    have hm := changed_inner_le_strip_majorant_half_range
      (z := z) (f := f) hX hH hHalf hgL1 hgSupport
    by_cases hz : 7 / 32 ≤ Real.exp z ∧ Real.exp z ≤ 65 / 16
    · rw [if_pos hz] at hm
      exact hm.trans (hinner z hz)
    · rw [if_neg hz] at hm
      exact hm.trans hC
  have hleftNonneg : ∀ z : ℝ, 0 ≤
      (a / (1 + a * |z|) ^ 2) *
        ((∫ x : ℝ, ‖g x‖ * faithfulPage47ChangedPhysicalWindowSum X H z f x)) := by
    intro z
    apply mul_nonneg (by positivity)
    exact integral_nonneg fun x ↦ mul_nonneg (norm_nonneg _)
      (faithfulPage47ChangedPhysicalWindowSum_nonneg X H z f x)
  have hmono :
      (∫ z : ℝ,
          (a / (1 + a * |z|) ^ 2) *
            (∫ x : ℝ, ‖g x‖ * faithfulPage47ChangedPhysicalWindowSum X H z f x)) ≤
        ∫ z : ℝ, (a / (1 + a * |z|) ^ 2) * C := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall hleftNonneg
    · exact hright
    · filter_upwards with z
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hchanged z
  have hk := integral_scaled_abs_decay_le_four ha
  have hrightEval :
      (∫ z : ℝ, (a / (1 + a * |z|) ^ 2) * C) ≤ 4 * C := by
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right hk hC
  have htotal := hmono.trans hrightEval
  have htotal0 : 0 ≤ ∫ z : ℝ,
      (a / (1 + a * |z|) ^ 2) *
        (∫ x : ℝ, ‖g x‖ * faithfulPage47ChangedPhysicalWindowSum X H z f x) := integral_nonneg hleftNonneg
  calc
    _ ≤ (4 * C) ^ 2 := pow_le_pow_left₀ htotal0 htotal 2
    _ = 260 * M := by
      unfold C
      rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num) hM)]
      ring
    _ = _ := rfl

/-- Literal finite coefficient sum before the Tonelli swap, with its
normalized Fourier decay. No oscillatory or projection bound is assumed. -/
theorem normalized_localized_decay_sum_sq_le_half_range
    {a X H : ℝ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (ha : 0 < a) (hX : 0 < X) (hH : 0 ≤ H) (hHalf : H ≤ X / 2)
    (hgSupport : ∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0)
    (hgL1 : Integrable g)
    (hg : Integrable (fun x : ℝ ↦ ‖g x‖ ^ 2))
    (hgOne : (∫ x : ℝ, ‖g x‖ ^ 2) ≤ 1) :
    (a * ∫ x : ℝ, ‖g x‖ *
      (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        ‖f n‖ * ∫ w : ℝ, faithfulLocalizedDecay a X H x
          (Real.log n - Real.log X) w)) ^ 2 ≤
      260 * ordinarySlidingMass X H f := by
  rw [integral_norm_mul_sum_integral_decay_eq_swapped ha hgL1,
    ← integral_const_mul]
  convert weighted_changed_window_integral_sq_le_half_range
    ha hX hH hHalf hgSupport hgL1 hg hgOne using 1
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  ring

#print axioms normalized_localized_decay_sum_sq_le_half_range
#print axioms weighted_changed_window_integral_sq_le_half_range

#print axioms integral_norm_mul_sum_integral_decay_eq_swapped
#print axioms changed_inner_le_strip_majorant

end
end MAPMRTFaithfulLowTonelliSwap
