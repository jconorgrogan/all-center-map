import MRTFaithfulLowPage47Schur

/-!
# MRT Proposition 5.1: faithful low-projection Tonelli majorants

Pointwise majorants here retain both the sharp physical support and the
quadratic translated Fourier decay.  They are the concrete inputs for the
finite-sum/Tonelli passage on page 47.
-/

namespace MAPMRTFaithfulLowTonelli

open MeasureTheory Set
open MAPMRTCorollary53Source MAPMRTProposition51HardBranch
open MAPMRTProposition51FirstAnalytic
open MAPMRTProposition51ProjectionLowAmplitude
open MAPMRTFaithfulSmoothCutoff MAPMRTFaithfulSmoothCutoffBudgets
open MAPMRTFaithfulLowProjectionIdentity MAPMRTFaithfulLowPage47Geometry
open MAPMRTEquation81Kernel
open MAPMRTFaithfulLowPage47Schur

noncomputable section

/-- The undifferentiated faithful amplitude vanishes outside the true
radius-`H/8` packet, not merely outside the coarser radius `H`. -/
theorem faithfulLowProjectionAmplitude_eq_zero_of_outside
    {X H beta eta x u w : ℝ} (hH : 0 < H)
    (hout : H / 8 < |X * Real.exp w - x|) :
    lowProjectionAmplitude X H beta eta x u faithfulCutoff
      (cutoffFourierKernel faithfulCutoff) w = 0 := by
  have harg : 1 / 8 < |(X * Real.exp w - x) / H| := by
    rw [abs_div, abs_of_pos hH]
    calc
      1 / 8 = (H / 8) / H := by field_simp [hH.ne']
      _ < |X * Real.exp w - x| / H :=
        (div_lt_div_iff_of_pos_right hH).2 hout
  unfold lowProjectionAmplitude
  rw [faithfulCutoff_zero harg.le]
  simp

/-- Quadratic kernel with its faithful physical support retained. -/
def faithfulLocalizedDecay
    (A X H x u w : ℝ) : ℝ :=
  if |X * Real.exp w - x| ≤ H / 8 then
    1 / (1 + |A * (u - w)|) ^ 2
  else 0

theorem faithfulLocalizedDecay_nonneg
    (A X H x u w : ℝ) : 0 ≤ faithfulLocalizedDecay A X H x u w := by
  unfold faithfulLocalizedDecay
  split_ifs <;> positivity

theorem integrable_faithfulLocalizedDecay
    {A X H x u : ℝ} (hA : 0 < A) :
    Integrable (faithfulLocalizedDecay A X H x u) := by
  let K : ℝ → ℝ := fun w ↦ equation81Kernel (1 / A) u w
  have hK : Integrable K := by
    exact integrable_equation81Kernel (R := 1 / A) (x := u) (by positivity)
  have hmeas : AEStronglyMeasurable (faithfulLocalizedDecay A X H x u) := by
    unfold faithfulLocalizedDecay
    apply Measurable.aestronglyMeasurable
    apply Measurable.ite
    · exact measurableSet_le (by fun_prop) measurable_const
    · fun_prop
    · fun_prop
  apply hK.mono' hmeas
  filter_upwards with w
  rw [Real.norm_eq_abs,
    abs_of_nonneg (faithfulLocalizedDecay_nonneg A X H x u w)]
  have hEq : 1 / (1 + |A * (u - w)|) ^ 2 = K w := by
    unfold K equation81Kernel
    rw [abs_mul, abs_of_pos hA, abs_sub_comm]
    field_simp [hA.ne']
  unfold faithfulLocalizedDecay
  split_ifs
  · exact le_of_eq hEq
  · exact (equation81Kernel_nonneg (R := 1 / A) (x := u) (y := w))

/-- Global pointwise envelope for the faithful undifferentiated amplitude. -/
theorem norm_faithfulLowProjectionAmplitude_le_localizedDecay
    {X H beta eta x u w : ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X) :
    ‖lowProjectionAmplitude X H beta eta x u faithfulCutoff
        (cutoffFourierKernel faithfulCutoff) w‖ ≤
      3 * faithfulCutoffFourierDecayConstant 2 *
        faithfulLocalizedDecay
          (lowProjectionScale X beta eta / (2 * Real.pi)) X H x u w := by
  by_cases hp : |X * Real.exp w - x| ≤ H / 8
  · have hw : w ∈ sourcePacketWindow X H x := by
      unfold sourcePacketWindow
      have hp' : |X * Real.exp w - x| ≤ H := hp.trans (by linarith)
      rw [abs_le] at hp'
      have hxMinus : 0 < x - H := by nlinarith
      have hxPlus : 0 < x + H := by nlinarith
      constructor
      · rw [← Real.exp_le_exp, Real.exp_log (div_pos hxMinus hX)]
        exact (div_le_iff₀ hX).2 (by linarith [hp'.1])
      · rw [← Real.exp_le_exp, Real.exp_log (div_pos hxPlus hX)]
        exact (le_div_iff₀ hX).2 (by linarith [hp'.2])
    have hb := norm_faithfulLowProjectionAmplitude_le_decay
      (beta := beta) (eta := eta) (u := u)
      hX hH.le hHquarter hxLower hxUpper hw
    unfold faithfulLocalizedDecay
    rw [if_pos hp]
    simpa [lowKernelArgument] using hb
  · have hz := faithfulLowProjectionAmplitude_eq_zero_of_outside
      (X := X) (beta := beta) (eta := eta) (u := u) hH
      (lt_of_not_ge hp)
    rw [hz, norm_zero]
    simp [faithfulLocalizedDecay, hp]

/-- Global pointwise envelope for the differentiated faithful amplitude. -/
theorem norm_faithfulLowProjectionAmplitudeDeriv_le_localizedDecay
    {X H beta eta x u w : ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X) :
    ‖lowProjectionAmplitudeDeriv X H beta eta x u
        faithfulCutoff faithfulCutoffDeriv
        (cutoffFourierKernel faithfulCutoff)
        faithfulCutoffFourierDeriv w‖ ≤
      ((3 / 2 + 51 * faithfulCutoffDerivBudget * X / (4 * H)) *
          faithfulCutoffFourierDecayConstant 2 +
        3 * |lowProjectionScale X beta eta / (2 * Real.pi)| *
          faithfulCutoffFourierDerivDecayConstant 2) *
        faithfulLocalizedDecay
          (lowProjectionScale X beta eta / (2 * Real.pi)) X H x u w := by
  by_cases hp : |X * Real.exp w - x| ≤ H / 8
  · have hw : w ∈ sourcePacketWindow X H x := by
      unfold sourcePacketWindow
      have hp' : |X * Real.exp w - x| ≤ H := hp.trans (by linarith)
      rw [abs_le] at hp'
      have hxMinus : 0 < x - H := by nlinarith
      have hxPlus : 0 < x + H := by nlinarith
      constructor
      · rw [← Real.exp_le_exp, Real.exp_log (div_pos hxMinus hX)]
        exact (div_le_iff₀ hX).2 (by linarith [hp'.1])
      · rw [← Real.exp_le_exp, Real.exp_log (div_pos hxPlus hX)]
        exact (le_div_iff₀ hX).2 (by linarith [hp'.2])
    have hb := norm_faithfulLowProjectionAmplitudeDeriv_le_decay
      (beta := beta) (eta := eta) (u := u)
      hX hH hHquarter hxLower hxUpper hw
    unfold faithfulLocalizedDecay
    rw [if_pos hp]
    simpa [lowKernelArgument] using hb
  · have hz := faithfulLowProjectionAmplitudeDeriv_eq_zero_of_outside
      (X := X) (beta := beta) (eta := eta) (u := u) hH
      (lt_of_not_ge hp)
    rw [hz, norm_zero]
    simp [faithfulLocalizedDecay, hp]

/-- After the page-47 translation `w = z + log n - log X`, the entire
translated quadratic kernel is independent of `n`; the remaining finite sum
is exactly the faithful physical-window sum. -/
theorem faithfulLocalizedDecay_shifted_sum_eq
    (A X H z x : ℝ) (f : ℕ → ℂ) (hA : 0 ≤ A) :
    (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        ‖f n‖ * faithfulLocalizedDecay A X H x
          (Real.log n - Real.log X)
          (z + Real.log n - Real.log X)) =
      (1 / (1 + A * |z|) ^ 2) *
        faithfulPage47ChangedPhysicalWindowSum X H z f x := by
  unfold faithfulLocalizedDecay faithfulPage47ChangedPhysicalWindowSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp :
      |X * Real.exp (z + Real.log n - Real.log X) - x| ≤ H / 8
  · rw [if_pos hp, if_pos hp]
    rw [show (Real.log n - Real.log X) -
        (z + Real.log n - Real.log X) = -z by ring,
      abs_mul, abs_neg, abs_of_nonneg hA]
    ring
  · rw [if_neg hp, if_neg hp]
    ring

/-- Exact finite-sum/Tonelli and translation seam on page 47.  No coefficient
or support information is discarded: after translating each `w` by its own
`log n - log X`, the common decay kernel factors out and the remaining sum is
the literal faithful physical-window sum. -/
theorem sum_integral_faithfulLocalizedDecay_eq
    {A : ℝ} (hA : 0 < A) (X H x : ℝ) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        ‖f n‖ * ∫ w : ℝ, faithfulLocalizedDecay A X H x
          (Real.log n - Real.log X) w) =
      ∫ z : ℝ, (1 / (1 + A * |z|) ^ 2) *
        faithfulPage47ChangedPhysicalWindowSum X H z f x := by
  let S := Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊
  have hshift (n : ℕ) :
      (∫ w : ℝ, faithfulLocalizedDecay A X H x
          (Real.log n - Real.log X) w) =
        ∫ z : ℝ, faithfulLocalizedDecay A X H x
          (Real.log n - Real.log X)
          (z + (Real.log n - Real.log X)) := by
    exact (integral_add_right_eq_self
      (faithfulLocalizedDecay A X H x (Real.log n - Real.log X))
      (Real.log n - Real.log X)).symm
  have hint (n : ℕ) : Integrable (fun z : ℝ ↦
      ‖f n‖ * faithfulLocalizedDecay A X H x
        (Real.log n - Real.log X)
        (z + (Real.log n - Real.log X))) := by
    exact ((integrable_faithfulLocalizedDecay (X := X) (H := H) (x := x)
      (u := Real.log n - Real.log X) hA).comp_add_right
        (Real.log n - Real.log X)).const_mul ‖f n‖
  calc
    (∑ n ∈ S, ‖f n‖ * ∫ w : ℝ, faithfulLocalizedDecay A X H x
          (Real.log n - Real.log X) w) =
        ∑ n ∈ S, ‖f n‖ * ∫ z : ℝ, faithfulLocalizedDecay A X H x
          (Real.log n - Real.log X)
          (z + (Real.log n - Real.log X)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hshift n]
    _ = ∫ z : ℝ, ∑ n ∈ S, ‖f n‖ *
          faithfulLocalizedDecay A X H x
            (Real.log n - Real.log X)
            (z + (Real.log n - Real.log X)) := by
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro n hn
        rw [integral_const_mul]
      · intro n hn
        exact hint n
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with z
      have hz := faithfulLocalizedDecay_shifted_sum_eq A X H z x f hA.le
      simpa only [S, one_div, sub_eq_add_neg, add_assoc] using hz

theorem faithfulPage47ChangedPhysicalWindowSum_nonneg
    (X H z : ℝ) (f : ℕ → ℂ) (x : ℝ) :
    0 ≤ faithfulPage47ChangedPhysicalWindowSum X H z f x := by
  unfold faithfulPage47ChangedPhysicalWindowSum
  positivity

theorem faithfulPage47ChangedPhysicalWindowSum_le_coefficientMass
    (X H z : ℝ) (f : ℕ → ℂ) (x : ℝ) :
    faithfulPage47ChangedPhysicalWindowSum X H z f x ≤
      MAPMRTProposition51FirstAnalytic.coefficientMass X f := by
  unfold faithfulPage47ChangedPhysicalWindowSum
    MAPMRTProposition51FirstAnalytic.coefficientMass
  apply Finset.sum_le_sum
  intro n hn
  split_ifs <;> simp

theorem faithfulPage47ChangedPhysicalWindowSum_eq_zero_off_strip
    {X H z x : ℝ} {f : ℕ → ℂ}
    (hX : 0 < X) (hH : 0 ≤ H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hz : ¬ (15 / 64 ≤ Real.exp z ∧ Real.exp z ≤ 129 / 32)) :
    faithfulPage47ChangedPhysicalWindowSum X H z f x = 0 := by
  unfold faithfulPage47ChangedPhysicalWindowSum
  apply Finset.sum_eq_zero
  intro n hn
  rw [if_neg]
  intro hp
  have hnbox := Finset.mem_Ioc.mp hn
  have hnLower : X ≤ (n : ℝ) :=
    ((Nat.floor_lt hX.le).mp hnbox.1).le
  have hnFloor : (n : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by exact_mod_cast hnbox.2
  have hnUpper : (n : ℝ) ≤ 2 * X :=
    hnFloor.trans (Nat.floor_le (by positivity : 0 ≤ 2 * X))
  have he := faithful_exp_page47LogDisplacement_mem
    (X := X) (H := H) (x := x)
    (w := z + Real.log n - Real.log X) (n := n)
    hX hH hHquarter hnLower hnUpper hxLower hxUpper hp
  rw [page47LogDisplacement_inverse_substitution] at he
  exact hz he

theorem faithfulPage47ChangedPhysicalWindowSum_eq_zero_off_strip_half_range
    {X H z x : ℝ} {f : ℕ → ℂ}
    (hX : 0 < X) (hH : 0 ≤ H) (hHquarter : H ≤ X / 2)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hz : ¬ (7 / 32 ≤ Real.exp z ∧ Real.exp z ≤ 65 / 16)) :
    faithfulPage47ChangedPhysicalWindowSum X H z f x = 0 := by
  unfold faithfulPage47ChangedPhysicalWindowSum
  apply Finset.sum_eq_zero
  intro n hn
  rw [if_neg]
  intro hp
  have hnbox := Finset.mem_Ioc.mp hn
  have hnLower : X ≤ (n : ℝ) :=
    ((Nat.floor_lt hX.le).mp hnbox.1).le
  have hnFloor : (n : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by exact_mod_cast hnbox.2
  have hnUpper : (n : ℝ) ≤ 2 * X :=
    hnFloor.trans (Nat.floor_le (by positivity : 0 ≤ 2 * X))
  have he := faithful_exp_page47LogDisplacement_mem_half_range
    (X := X) (H := H) (x := x)
    (w := z + Real.log n - Real.log X) (n := n)
    hX hH hHquarter hnLower hnUpper hxLower hxUpper hp
  rw [page47LogDisplacement_inverse_substitution] at he
  exact hz he

theorem measurable_faithfulPage47ChangedPhysicalWindowSum
    (X H : ℝ) (f : ℕ → ℂ) :
    Measurable (fun p : ℝ × ℝ ↦
      faithfulPage47ChangedPhysicalWindowSum X H p.1 f p.2) := by
  unfold faithfulPage47ChangedPhysicalWindowSum
  apply Finset.measurable_sum
  intro n hn
  apply Measurable.ite
  · exact measurableSet_le (by fun_prop) measurable_const
  · fun_prop
  · exact measurable_const

#print axioms faithfulLowProjectionAmplitude_eq_zero_of_outside
#print axioms norm_faithfulLowProjectionAmplitude_le_localizedDecay
#print axioms norm_faithfulLowProjectionAmplitudeDeriv_le_localizedDecay
#print axioms faithfulLocalizedDecay_shifted_sum_eq
#print axioms sum_integral_faithfulLocalizedDecay_eq

end
end MAPMRTFaithfulLowTonelli
