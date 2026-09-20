import MRTFaithfulLowHalfRangeIBP
import MRTFaithfulLowTonelliSwap
import MAPFinishP51Projection

namespace MAPMRTFaithfulLowEstimate
open MeasureTheory Set
open MAPMRTCorollary53Source MAPMRTProposition51HardBranch
open MAPMRTProposition51ProjectionLowAmplitude MAPMRTFaithfulLowHalfRangeIBP
open MAPMRTFaithfulSmoothCutoff MAPMRTFaithfulSmoothCutoffBudgets
open MAPMRTFaithfulLowTonelli MAPMRTFaithfulLowTonelliSwap
open MAPMRTFaithfulLowPage47Schur MAPMRTEquation81Kernel
noncomputable section
set_option maxHeartbeats 800000

def faithfulLowIBPBudget (X H beta eta : ℝ) : ℝ :=
  (1 / (|beta| * X / 4)) *
    ((3 / 2 + 51 * faithfulCutoffDerivBudget * X / (4 * H)) *
        faithfulCutoffFourierDecayConstant 2 +
      3 * |lowProjectionScale X beta eta / (2 * Real.pi)| *
        faithfulCutoffFourierDerivDecayConstant 2) +
    ((17 * |beta| * X / 4) / (|beta| * X / 4) ^ 2) *
      (3 * faithfulCutoffFourierDecayConstant 2)

theorem faithfulLowIBPBudget_nonneg {X H beta eta : ℝ}
    (hX : 0 < X) (hH : 0 < H) : 0 ≤ faithfulLowIBPBudget X H beta eta := by
  have hd := faithfulCutoffDerivBudget_nonneg
  have hk := faithfulCutoffFourierDecayConstant_nonneg 2
  have hkd := faithfulCutoffFourierDerivDecayConstant_nonneg 2
  unfold faithfulLowIBPBudget
  positivity

theorem integrable_norm_mul_integral_localizedDecay
    {a X H u : ℝ} {g : ℝ → ℂ} (ha : 0 < a) (hg : Integrable g) :
    Integrable (fun x : ℝ ↦ ‖g x‖ *
      ∫ w : ℝ, faithfulLocalizedDecay a X H x u w) := by
  let K : ℝ → ℝ := fun w ↦ equation81Kernel (1 / a) u w
  have hK : Integrable K := integrable_equation81Kernel (by positivity)
  have he (w : ℝ) : 1 / (1 + |a * (u - w)|) ^ 2 = K w := by
    unfold K equation81Kernel
    rw [abs_mul, abs_of_pos ha, abs_sub_comm]
    field_simp [ha.ne']
  have hm : Measurable (fun p : ℝ × ℝ ↦ faithfulLocalizedDecay a X H p.2 u p.1) := by
    unfold faithfulLocalizedDecay
    apply Measurable.ite
    · exact measurableSet_le (by fun_prop) measurable_const
    · fun_prop
    · fun_prop
  have hi : Integrable (fun p : ℝ × ℝ ↦
      ‖g p.2‖ * faithfulLocalizedDecay a X H p.2 u p.1) := by
    apply (hK.mul_prod hg.norm).mono'
      (hg.norm.aestronglyMeasurable.comp_snd.mul hm.aestronglyMeasurable)
    filter_upwards with p
    change ‖‖g p.2‖ * faithfulLocalizedDecay a X H p.2 u p.1‖ ≤ K p.1 * ‖g p.2‖
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _)
      (faithfulLocalizedDecay_nonneg _ _ _ _ _ _))]
    have hk0 : 0 ≤ K p.1 := equation81Kernel_nonneg
    have hb : faithfulLocalizedDecay a X H p.2 u p.1 ≤ K p.1 := by
      unfold faithfulLocalizedDecay
      split_ifs
      · exact (he p.1).le
      · exact hk0
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hb (norm_nonneg (g p.2))
  have hv := hi.integral_prod_right
  simpa only [integral_const_mul] using hv

theorem norm_faithfulLowProjection_le
    {X H beta eta u : ℝ} {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hbeta : beta ≠ 0) (heta : 0 < eta) (hg : Integrable g)
    (hgSupport : ∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0) :
    ‖lowFrequencyProjection X beta eta faithfulCutoff
      (logarithmicDualFunction X H beta faithfulCutoff g) u‖ ≤
      (Real.sqrt X * (lowProjectionScale X beta eta / (2 * Real.pi))) *
        (faithfulLowIBPBudget X H beta eta *
          ∫ x : ℝ, ‖g x‖ * ∫ w : ℝ, faithfulLocalizedDecay
            (lowProjectionScale X beta eta / (2 * Real.pi)) X H x u w) := by
  have ha : 0 < lowProjectionScale X beta eta / (2 * Real.pi) := by
    unfold lowProjectionScale
    positivity
  have hb := faithfulLowIBPBudget_nonneg (beta := beta) (eta := eta) hX hH
  rw [faithfulLowFrequencyProjection_half_range_eq hX hH hHalf hbeta heta hgSupport hg,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) ha.le)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∫ x : ℝ, ‖g x * faithfulHalfRangeLowIntegral X H beta eta x u‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, faithfulLowIBPBudget X H beta eta *
        (‖g x‖ * ∫ w : ℝ, faithfulLocalizedDecay
          (lowProjectionScale X beta eta / (2 * Real.pi)) X H x u w) := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun x ↦ norm_nonneg _
      · exact (integrable_norm_mul_integral_localizedDecay ha hg).const_mul _
      · filter_upwards with x
        rw [norm_mul]
        by_cases hx : x ∈ Icc (X / 2) (4 * X)
        · have h := norm_faithfulHalfRangeLowIntegral_le_decay_integral
            (u := u) hX hH hHalf hx.1 hx.2 hbeta heta
          simpa [faithfulLowIBPBudget, mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul_of_nonneg_left h (norm_nonneg (g x))
        · rw [hgSupport x hx]
          simp
    _ = _ := integral_const_mul _ _

theorem faithful_lowProjectedSum_norm_le
    {X H beta eta : ℝ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hbeta : beta ≠ 0) (heta : 0 < eta) (hg : Integrable g)
    (hgSupport : ∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0) :
    ‖∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
      f n * (Real.sqrt n : ℂ)⁻¹ * lowFrequencyProjection X beta eta faithfulCutoff
        (logarithmicDualFunction X H beta faithfulCutoff g)
        (Real.log n - Real.log X)‖ ≤
      faithfulLowIBPBudget X H beta eta *
        ((lowProjectionScale X beta eta / (2 * Real.pi)) *
          ∫ x : ℝ, ‖g x‖ *
            (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, ‖f n‖ *
              ∫ w : ℝ, faithfulLocalizedDecay
                (lowProjectionScale X beta eta / (2 * Real.pi)) X H x
                (Real.log n - Real.log X) w)) := by
  let a := lowProjectionScale X beta eta / (2 * Real.pi)
  let B := faithfulLowIBPBudget X H beta eta
  let J : ℕ → ℝ := fun n ↦ ∫ x : ℝ, ‖g x‖ *
    ∫ w : ℝ, faithfulLocalizedDecay a X H x (Real.log n - Real.log X) w
  have ha : 0 < a := by unfold a lowProjectionScale; positivity
  have hB : 0 ≤ B := faithfulLowIBPBudget_nonneg hX hH
  have hJ (n : ℕ) : 0 ≤ J n := integral_nonneg fun x ↦
    mul_nonneg (norm_nonneg _) (integral_nonneg (faithfulLocalizedDecay_nonneg _ _ _ _ _))
  have hterm (n : ℕ) (hn : n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊) :
      ‖f n * (Real.sqrt n : ℂ)⁻¹ * lowFrequencyProjection X beta eta faithfulCutoff
        (logarithmicDualFunction X H beta faithfulCutoff g)
        (Real.log n - Real.log X)‖ ≤ a * B * (‖f n‖ * J n) := by
    have hnX : X < (n : ℝ) := (Nat.floor_lt hX.le).mp (Finset.mem_Ioc.mp hn).1
    have hnpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (hX.trans hnX)
    have hs : Real.sqrt X * (Real.sqrt (n : ℝ))⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv]
      exact (div_le_one hnpos).2 (Real.sqrt_le_sqrt hnX.le)
    have hp := norm_faithfulLowProjection_le
      (u := Real.log n - Real.log X) hX hH hHalf hbeta heta hg hgSupport
    rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ ≤ (‖f n‖ * (Real.sqrt (n : ℝ))⁻¹) *
          ((Real.sqrt X * a) * (B * J n)) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = (Real.sqrt X * (Real.sqrt (n : ℝ))⁻¹) *
          (a * B * (‖f n‖ * J n)) := by ring
      _ ≤ 1 * (a * B * (‖f n‖ * J n)) :=
        mul_le_mul_of_nonneg_right hs (mul_nonneg (mul_nonneg ha.le hB) (mul_nonneg (norm_nonneg _) (hJ n)))
      _ = _ := one_mul _
  have hsum : (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, ‖f n‖ * J n) =
      ∫ x : ℝ, ‖g x‖ *
        (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, ‖f n‖ *
          ∫ w : ℝ, faithfulLocalizedDecay a X H x (Real.log n - Real.log X) w) := by
    have he (n : ℕ) : ‖f n‖ * J n = ∫ x : ℝ, ‖f n‖ *
        (‖g x‖ * ∫ w : ℝ, faithfulLocalizedDecay a X H x (Real.log n - Real.log X) w) :=
      (integral_const_mul _ _).symm
    simp_rw [he]
    rw [← integral_finsetSum]
    · apply integral_congr_ae
      filter_upwards with x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    · intro n hn
      exact (integrable_norm_mul_integral_localizedDecay ha hg).const_mul _
  calc
    _ ≤ ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        ‖f n * (Real.sqrt n : ℂ)⁻¹ * lowFrequencyProjection X beta eta faithfulCutoff
          (logarithmicDualFunction X H beta faithfulCutoff g)
          (Real.log n - Real.log X)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, a * B * (‖f n‖ * J n) :=
      Finset.sum_le_sum hterm
    _ = a * B * (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, ‖f n‖ * J n) :=
      (Finset.mul_sum _ _ _).symm
    _ = _ := by rw [hsum]; ring

/-- A single fixed constant from the faithful cutoff's Schwartz budgets. -/
def faithfulLowConstant : ℝ :=
  (210 + 51 * faithfulCutoffDerivBudget) * faithfulCutoffFourierDecayConstant 2 +
    (60 / Real.pi) * faithfulCutoffFourierDerivDecayConstant 2

theorem faithfulLowConstant_nonneg : 0 ≤ faithfulLowConstant := by
  have hd := faithfulCutoffDerivBudget_nonneg
  have hk := faithfulCutoffFourierDecayConstant_nonneg 2
  have hkd := faithfulCutoffFourierDerivDecayConstant_nonneg 2
  unfold faithfulLowConstant
  positivity

theorem faithfulLowIBPBudget_le
    {X H beta eta : ℝ} (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hbeta : beta ≠ 0) (heta : 0 < eta) :
    faithfulLowIBPBudget X H beta eta ≤
      faithfulLowConstant * (eta + 1 / (|beta| * H)) := by
  have hd := faithfulCutoffDerivBudget_nonneg
  have hk := faithfulCutoffFourierDecayConstant_nonneg 2
  have hkd := faithfulCutoffFourierDerivDecayConstant_nonneg 2
  have hb : 0 < |beta| := abs_pos.mpr hbeta
  have ha : 0 ≤ lowProjectionScale X beta eta / (2 * Real.pi) := by
    unfold lowProjectionScale; positivity
  have he : faithfulLowIBPBudget X H beta eta =
      (210 / (|beta| * X) + 51 * faithfulCutoffDerivBudget / (|beta| * H)) *
        faithfulCutoffFourierDecayConstant 2 +
      eta * (60 / Real.pi) * faithfulCutoffFourierDerivDecayConstant 2 := by
    unfold faithfulLowIBPBudget
    rw [abs_of_nonneg ha]
    unfold lowProjectionScale
    field_simp [hX.ne', hH.ne', hb.ne', Real.pi_ne_zero]
    <;> ring
  have hfrac : 210 / (|beta| * X) ≤ 210 / (|beta| * H) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos hb hH)
      (mul_le_mul_of_nonneg_left (by linarith : H ≤ X) hb.le)
  rw [he]
  calc
    _ ≤ (210 / (|beta| * H) + 51 * faithfulCutoffDerivBudget / (|beta| * H)) *
        faithfulCutoffFourierDecayConstant 2 +
      eta * (60 / Real.pi) * faithfulCutoffFourierDerivDecayConstant 2 := by gcongr
    _ ≤ faithfulLowConstant * (eta + 1 / (|beta| * H)) := by
      unfold faithfulLowConstant
      have hi : 0 ≤ 1 / (|beta| * H) := by positivity
      have h1 : 0 ≤ eta * ((210 + 51 * faithfulCutoffDerivBudget) *
          faithfulCutoffFourierDecayConstant 2) := by positivity
      have h2 : 0 ≤ (1 / (|beta| * H)) *
          ((60 / Real.pi) * faithfulCutoffFourierDerivDecayConstant 2) := by positivity
      apply sub_nonneg.mp
      convert add_nonneg h1 h2 using 1 <;> ring

theorem faithful_lowProjectionEnergy_le
    {X H beta eta : ℝ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hbeta : beta ≠ 0) (heta : 0 < eta) (hg : Integrable g)
    (hgSq : Integrable (fun x : ℝ ↦ ‖g x‖ ^ 2))
    (hgOne : (∫ x : ℝ, ‖g x‖ ^ 2) ≤ 1)
    (hgSupport : ∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0) :
    MAPFinishP51Projection.lowProjectionEnergy X H beta eta faithfulCutoff g f ≤
      (260 * faithfulLowConstant ^ 2) *
        (eta + 1 / (|beta| * H)) ^ 2 * ordinarySlidingMass X H f := by
  let a := lowProjectionScale X beta eta / (2 * Real.pi)
  let T := a * ∫ x : ℝ, ‖g x‖ *
    (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, ‖f n‖ *
      ∫ w : ℝ, faithfulLocalizedDecay a X H x (Real.log n - Real.log X) w)
  have ha : 0 < a := by unfold a lowProjectionScale; positivity
  have hT : 0 ≤ T := by
    apply mul_nonneg ha.le
    apply integral_nonneg
    intro x
    apply mul_nonneg (norm_nonneg _)
    exact Finset.sum_nonneg fun n hn ↦ mul_nonneg (norm_nonneg _)
      (integral_nonneg (faithfulLocalizedDecay_nonneg _ _ _ _ _))
  have hs := faithful_lowProjectedSum_norm_le (f := f)
    hX hH hHalf hbeta heta hg hgSupport
  have hbudget := faithfulLowIBPBudget_le hX hH hHalf hbeta heta
  have htotal := hs.trans (mul_le_mul_of_nonneg_right hbudget hT)
  have hschur := normalized_localized_decay_sum_sq_le_half_range (f := f)
    ha hX hH.le hHalf hgSupport hg hgSq hgOne
  unfold MAPFinishP51Projection.lowProjectionEnergy
  calc
    _ ≤ (faithfulLowConstant * (eta + 1 / (|beta| * H)) * T) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htotal 2
    _ = (faithfulLowConstant * (eta + 1 / (|beta| * H))) ^ 2 * T ^ 2 := mul_pow _ _ _
    _ ≤ (faithfulLowConstant * (eta + 1 / (|beta| * H))) ^ 2 *
        (260 * ordinarySlidingMass X H f) :=
      mul_le_mul_of_nonneg_left hschur (sq_nonneg _)
    _ = _ := by ring

/-- The source's low error after the equation-(72) aperture normalization. -/
theorem faithful_lowProjectionEnergy_div_sq_le_ordinaryError
    {X H beta eta : ℝ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hbeta : beta ≠ 0) (heta : 0 < eta) (hg : Integrable g)
    (hgSq : Integrable (fun x : ℝ ↦ ‖g x‖ ^ 2))
    (hgOne : (∫ x : ℝ, ‖g x‖ ^ 2) ≤ 1)
    (hgSupport : ∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0) :
    MAPFinishP51Projection.lowProjectionEnergy X H beta eta faithfulCutoff g f / H ^ 2 ≤
      (260 * faithfulLowConstant ^ 2) * ordinaryError X H f beta eta := by
  have h := div_le_div_of_nonneg_right
    (faithful_lowProjectionEnergy_le (f := f) hX hH hHalf hbeta heta hg hgSq hgOne hgSupport)
    (sq_nonneg H)
  convert h using 1
  unfold ordinaryError
  ring

#print axioms faithful_lowProjectionEnergy_div_sq_le_ordinaryError

#print axioms faithful_lowProjectionEnergy_le
end
end MAPMRTFaithfulLowEstimate
