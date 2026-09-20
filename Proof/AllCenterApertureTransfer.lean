import FejerMAPInterfaceWeld

/-!
# Exact aperture transfer in the all-center MAP proof

The analytic near/far argument in the paper works at one enlarged aperture
`H₀ = (1/2) X^(2/15 + min (ε/4) (1/1200))`.  This file proves the exact
manuscript-owned step which transfers that single-aperture estimate to every
`H ≥ X^(2/15+ε)`.  It introduces no analytic estimate and does not rename
`AllCenterLocalMAP`: the sole premise below is the literal base-aperture bound
which the Gallagher/MRT argument must supply.
-/

namespace MAPAllCenterApertureTransfer

open AddCircle MeasureTheory Set
open scoped BigOperators ArithmeticFunction

noncomputable section

open PrimePairEndpoints MAPHarmonicEndpoint FejerMAPInterfaceWeld

/-- The reserve used in the manuscript's proof of Theorem 1.1. -/
def apertureReserve (ε : ℝ) : ℝ := min (ε / 4) (1 / 1200)

/-- The single enlarged aperture at which the near/far proof is run. -/
def baseAperture (ε X : ℝ) : ℝ :=
  (1 / 2) * Real.rpow X (2 / 15 + apertureReserve ε)

theorem apertureReserve_pos {ε : ℝ} (hε : 0 < ε) :
    0 < apertureReserve ε := by
  unfold apertureReserve
  exact lt_min (div_pos hε (by norm_num)) (by norm_num)

theorem apertureReserve_le_epsilon {ε : ℝ} (hε : 0 < ε) :
    apertureReserve ε ≤ ε := by
  calc
    apertureReserve ε ≤ ε / 4 := min_le_left _ _
    _ ≤ ε := by linarith

theorem baseAperture_pos {ε X : ℝ} (hX : 0 < X) :
    0 < baseAperture ε X := by
  unfold baseAperture
  exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hX _)

/-- The paper's base aperture is no larger than every legal requested
aperture.  This is the exact exponent comparison behind the concentric-arc
reduction. -/
theorem baseAperture_le_legal
    {ε X H : ℝ} (hε : 0 < ε) (hX : 1 ≤ X)
    (hH : Real.rpow X (2 / 15 + ε) ≤ H) :
    baseAperture ε X ≤ H := by
  have hpow :
      Real.rpow X (2 / 15 + apertureReserve ε) ≤
        Real.rpow X (2 / 15 + ε) := by
    apply Real.rpow_le_rpow_of_exponent_le hX
    linarith [apertureReserve_le_epsilon hε]
  have hhalf :
      baseAperture ε X ≤
        Real.rpow X (2 / 15 + apertureReserve ε) := by
    unfold baseAperture
    exact mul_le_of_le_one_left
      (Real.rpow_nonneg (le_trans (by norm_num) hX)
        (2 / 15 + apertureReserve ε)) (by norm_num)
  exact hhalf.trans (hpow.trans hH)

/-- Increasing the aperture parameter shrinks the centered closed arc. -/
theorem centeredArc_anti_aperture
    {H₀ H : ℝ} (hH₀ : 0 < H₀) (hH : H₀ ≤ H)
    (center : UnitAddCircle) :
    centeredArc H center ⊆ centeredArc H₀ center := by
  have hHpos : 0 < H := hH₀.trans_le hH
  have hrad : (2 * H)⁻¹ ≤ (2 * H₀)⁻¹ := by
    exact (inv_le_inv₀ (mul_pos (by norm_num) hHpos)
      (mul_pos (by norm_num) hH₀)).2 (by nlinarith)
  intro a ha
  rw [centeredArc, Metric.mem_closedBall] at ha ⊢
  exact ha.trans hrad

/-- Restricting a nonnegative minor density to the smaller legal arc cannot
increase its mass. -/
theorem integral_minorWeight_anti_aperture
    {X H₀ H : ℝ} (B D : ℕ) (hH₀ : 0 < H₀) (hH : H₀ ≤ H)
    (center : UnitAddCircle) :
    (∫ a in centeredArc H center, minorWeight X B D a
        ∂AddCircle.haarAddCircle) ≤
      ∫ a in centeredArc H₀ center, minorWeight X B D a
        ∂AddCircle.haarAddCircle := by
  have hsubset := centeredArc_anti_aperture hH₀ hH center
  simp only [centeredArc]
  rw [← integral_indicator measurableSet_closedBall,
    ← integral_indicator measurableSet_closedBall]
  apply integral_mono
  · exact (minorWeight_integrable X B D).indicator measurableSet_closedBall
  · exact (minorWeight_integrable X B D).indicator measurableSet_closedBall
  · intro a
    by_cases ha : a ∈ centeredArc H center
    · have haH : a ∈ Metric.closedBall center (2 * H)⁻¹ := by
        simpa [centeredArc] using ha
      have haH₀ : a ∈ Metric.closedBall center (2 * H₀)⁻¹ := by
        simpa [centeredArc] using hsubset ha
      simp only [Set.indicator_of_mem haH, Set.indicator_of_mem haH₀]
      exact le_rfl
    · have haH : a ∉ Metric.closedBall center (2 * H)⁻¹ := by
        simpa [centeredArc] using ha
      simp only [Set.indicator_of_notMem haH]
      by_cases haH₀ : a ∈ Metric.closedBall center (2 * H₀)⁻¹
      · simp only [Set.indicator_of_mem haH₀]
        exact minorWeight_nonneg X B D a
      · simp only [Set.indicator_of_notMem haH₀]
        exact le_rfl

/-- The literal single-aperture analytic obligation left to the near/far
Gallagher--MRT proof.  Unlike `AllCenterLocalMAP`, it has no aperture variable
after `X`: only the paper's one prescribed `baseAperture` occurs. -/
def BaseApertureAllCenterEstimate : Prop :=
  ∀ A ε : ℝ, 0 < A → 0 < ε →
    ∃ B D : ℕ, ∃ C X₀ : ℝ,
      0 < C ∧ 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X →
        ∀ center : UnitAddCircle,
          (∫ a in centeredArc (baseAperture ε X) center,
              minorWeight X B D a ∂AddCircle.haarAddCircle) ≤
            C * X * Real.rpow (Real.log X) (-A)

/-- Exact all-`H` aperture weld.  Once the analytic near/far proof supplies
its bound at the manuscript's base aperture, no further analytic premise is
needed to inhabit `AllCenterLocalMAP`. -/
theorem allCenterLocalMAP_of_baseAperture
    (hbase : BaseApertureAllCenterEstimate) :
    AllCenterLocalMAP := by
  intro A ε hA hε
  obtain ⟨B, D, C, X₀, hC, hX₀, hbound⟩ := hbase A ε hA hε
  refine ⟨B, D, C, X₀, hC, hX₀, ?_⟩
  intro X H hXX₀ hH center
  have hXone : 1 ≤ X := (by norm_num : (1 : ℝ) ≤ 2).trans (hX₀.trans hXX₀)
  have hbasepos : 0 < baseAperture ε X :=
    baseAperture_pos (zero_lt_one.trans_le hXone)
  have hbaseH : baseAperture ε X ≤ H :=
    baseAperture_le_legal hε hXone hH
  rw [← integral_minorWeight_centeredArc]
  exact (integral_minorWeight_anti_aperture B D hbasepos hbaseH center).trans
    (hbound X hXX₀ center)

end
end MAPAllCenterApertureTransfer
