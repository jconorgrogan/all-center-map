import JutilaCollarA5FiberCap
import JutilaCollarMeshCutoff
import WeakVKNearDecay

/-!
# Exact A.5 budget inside Jutila's terminal collar

Replacing Linnik's local Lemma 8 by the certified Appendix A.5 box count
introduces one standalone `log D` fiber factor.  On the live MAP branch the
Appendix-B weak zero-free gap absorbs that factor.  This file records the
source-faithful allocation without changing the final `21/10` coefficient.

The page-52 choice `delta = 1/280` spends `24/280`.  We spend `4/560` on
the logarithms already raised to `1-alpha`, and the remaining `1/140` on the
A.5 fiber logarithm using the weak gap.  The three costs add exactly to
`1/10`.
-/

namespace MAPJutilaCollarA5Budget

open Filter MAPJutilaCollarMeshCutoff

noncomputable section

/-- Budget for the detector logarithms which already occur to a multiple of
`1-alpha`. -/
def detectorLogBudget : ℝ := 1 / 560

/-- Gap-dependent budget for the standalone Appendix A.5 fiber logarithm. -/
def a5FiberGapBudget : ℝ := 1 / 140

/-- Jutila's equation-(3.1) ordinate width `Delta = 1/log D`. -/
def sourceBoxWidth (D : ℝ) : ℝ := 1 / Real.log D

theorem sourceBoxWidth_pos {D : ℝ} (hlog : 0 < Real.log D) :
    0 < sourceBoxWidth D := by
  unfold sourceBoxWidth
  positivity

theorem sourceBoxWidth_le_one {D : ℝ} (hlog : 1 ≤ Real.log D) :
    sourceBoxWidth D ≤ 1 := by
  unfold sourceBoxWidth
  exact (div_le_one (by linarith)).2 hlog

/-- The exact coefficient ledger after replacing Linnik's local count by
Appendix A.5. -/
theorem collar_density_coefficient_with_A5 :
    2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget +
      a5FiberGapBudget = 21 / 10 := by
  norm_num [collarDelta, detectorLogBudget, a5FiberGapBudget]

/-- Appendix B's weak-VK gap absorbs the standalone A.5 fiber logarithm in
exactly the reserved `1/140` exponent. -/
theorem eventually_log_le_A5_gap_power (c : ℝ) (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop, ∀ omega : ℝ,
      c * Real.rpow (Real.log X) (-(3 / 4 : ℝ)) ≤ omega →
      Real.log X ≤ Real.rpow X (a5FiberGapBudget * omega) := by
  have hc' : 0 < 12 * a5FiberGapBudget * c := by
    norm_num [a5FiberGapBudget]
    positivity
  have hdecay := WeakVKNear.weakGap_nearFactor_beats_polylog
    (3 / 4 : ℝ) (12 * a5FiberGapBudget * c) 1 0
    (by norm_num) hc' (by norm_num) (by norm_num)
  have hlarge : ∀ᶠ X : ℝ in atTop, 1 < X := eventually_gt_atTop 1
  filter_upwards [hdecay, hlarge] with X hXdecay hX omega homega
  let omega' : ℝ := 12 * a5FiberGapBudget * omega
  have homega' :
      (12 * a5FiberGapBudget * c) *
          Real.rpow (Real.log X) (-(3 / 4 : ℝ)) ≤ omega' := by
    dsimp [omega']
    have hb : 0 ≤ 12 * a5FiberGapBudget := by
      norm_num [a5FiberGapBudget]
    calc
      (12 * a5FiberGapBudget * c) *
          Real.rpow (Real.log X) (-(3 / 4 : ℝ)) =
        (12 * a5FiberGapBudget) *
          (c * Real.rpow (Real.log X) (-(3 / 4 : ℝ))) := by ring
      _ ≤ (12 * a5FiberGapBudget) * omega :=
        mul_le_mul_of_nonneg_left homega hb
      _ = omega' := by simp [omega']
  have hprod := hXdecay omega' homega'
  norm_num at hprod
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hpow0 : 0 ≤ Real.rpow X (a5FiberGapBudget * omega) :=
    Real.rpow_nonneg hXpos.le _
  have hcancel :
      Real.rpow X (-(a5FiberGapBudget * omega)) *
          Real.rpow X (a5FiberGapBudget * omega) = 1 := by
    calc
      Real.rpow X (-(a5FiberGapBudget * omega)) *
          Real.rpow X (a5FiberGapBudget * omega) =
        Real.rpow X (-(a5FiberGapBudget * omega) +
          (a5FiberGapBudget * omega)) :=
            (Real.rpow_add hXpos (-(a5FiberGapBudget * omega))
              (a5FiberGapBudget * omega)).symm
      _ = 1 := by norm_num
  calc
    Real.log X =
        (Real.log X * Real.rpow X (-(a5FiberGapBudget * omega))) *
          Real.rpow X (a5FiberGapBudget * omega) := by
      rw [mul_assoc, hcancel, mul_one]
    _ ≤ 1 * Real.rpow X (a5FiberGapBudget * omega) :=
      mul_le_mul_of_nonneg_right (by
        simpa only [omega', show -(12 * a5FiberGapBudget * omega / 12) =
          -(a5FiberGapBudget * omega) by ring] using! hprod) hpow0
    _ = Real.rpow X (a5FiberGapBudget * omega) := one_mul _

/-- The same weak-gap reserve absorbs every fixed polylogarithmic loss, not
only the single logarithm coming from the A.5 fiber cap.  This permits the
live gapped branch to use coarse finite divisor-weight estimates in place of
sharp asymptotics whenever the only extra loss is polylogarithmic. -/
theorem eventually_log_rpow_le_A5_gap_power
    (P c : ℝ) (hP : 0 ≤ P) (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop, ∀ omega : ℝ,
      c * Real.rpow (Real.log X) (-(3 / 4 : ℝ)) ≤ omega →
      Real.rpow (Real.log X) P ≤
        Real.rpow X (a5FiberGapBudget * omega) := by
  have hc' : 0 < 12 * a5FiberGapBudget * c := by
    norm_num [a5FiberGapBudget]
    positivity
  have hdecay := WeakVKNear.weakGap_nearFactor_beats_polylog
    (3 / 4 : ℝ) (12 * a5FiberGapBudget * c) P 0
    (by norm_num) hc' hP (by norm_num)
  have hlarge : ∀ᶠ X : ℝ in atTop, 1 < X := eventually_gt_atTop 1
  filter_upwards [hdecay, hlarge] with X hXdecay hX omega homega
  let omega' : ℝ := 12 * a5FiberGapBudget * omega
  have homega' :
      (12 * a5FiberGapBudget * c) *
          Real.rpow (Real.log X) (-(3 / 4 : ℝ)) ≤ omega' := by
    dsimp [omega']
    have hb : 0 ≤ 12 * a5FiberGapBudget := by
      norm_num [a5FiberGapBudget]
    calc
      (12 * a5FiberGapBudget * c) *
          Real.rpow (Real.log X) (-(3 / 4 : ℝ)) =
        (12 * a5FiberGapBudget) *
          (c * Real.rpow (Real.log X) (-(3 / 4 : ℝ))) := by ring
      _ ≤ (12 * a5FiberGapBudget) * omega :=
        mul_le_mul_of_nonneg_left homega hb
      _ = omega' := by simp [omega']
  have hprod := hXdecay omega' homega'
  norm_num at hprod
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hpow0 : 0 ≤ Real.rpow X (a5FiberGapBudget * omega) :=
    Real.rpow_nonneg hXpos.le _
  have hcancel :
      Real.rpow X (-(a5FiberGapBudget * omega)) *
          Real.rpow X (a5FiberGapBudget * omega) = 1 := by
    calc
      Real.rpow X (-(a5FiberGapBudget * omega)) *
          Real.rpow X (a5FiberGapBudget * omega) =
        Real.rpow X (-(a5FiberGapBudget * omega) +
          (a5FiberGapBudget * omega)) :=
            (Real.rpow_add hXpos (-(a5FiberGapBudget * omega))
              (a5FiberGapBudget * omega)).symm
      _ = 1 := by norm_num
  calc
    Real.rpow (Real.log X) P =
        (Real.rpow (Real.log X) P *
          Real.rpow X (-(a5FiberGapBudget * omega))) *
            Real.rpow X (a5FiberGapBudget * omega) := by
      rw [mul_assoc, hcancel, mul_one]
    _ ≤ 1 * Real.rpow X (a5FiberGapBudget * omega) :=
      mul_le_mul_of_nonneg_right (by
        simpa only [omega', show -(12 * a5FiberGapBudget * omega / 12) =
          -(a5FiberGapBudget * omega) by ring] using! hprod) hpow0
    _ = Real.rpow X (a5FiberGapBudget * omega) := one_mul _

/-- Generic terminal weld for a finite nonnegative factor already shown to
fit inside the weak-gap reserve.  It lets the caller combine the A.5 fiber
logarithm with any additional fixed polylogarithmic losses before spending
the reserve once. -/
theorem total_le_final_density_of_gapFactor_and_p53
    {D alpha omega total selected C K gapFactor : ℝ}
    (hD : 1 < D) (_halpha : alpha ≤ 1) (hgap : omega ≤ 1 - alpha)
    (_hC : 0 ≤ C) (hK : 0 ≤ K) (hselected0 : 0 ≤ selected)
    (hgapFactor : gapFactor ≤
      Real.rpow D (a5FiberGapBudget * omega))
    (htotal : total ≤ K * gapFactor * selected)
    (hselected : selected ≤
      C * Real.rpow D
        ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
          (1 - alpha))) :
    total ≤ K * C * Real.rpow D ((21 / 10) * (1 - alpha)) := by
  have hD0 : 0 ≤ D := (zero_lt_one.trans hD).le
  have hgapBudget0 : 0 ≤ a5FiberGapBudget := by
    norm_num [a5FiberGapBudget]
  have hgapPower :
      Real.rpow D (a5FiberGapBudget * omega) ≤
        Real.rpow D (a5FiberGapBudget * (1 - alpha)) := by
    apply Real.rpow_le_rpow_of_exponent_le hD.le
    exact mul_le_mul_of_nonneg_left hgap hgapBudget0
  have hfactor' : gapFactor ≤
      Real.rpow D (a5FiberGapBudget * (1 - alpha)) :=
    hgapFactor.trans hgapPower
  have hpowA0 : 0 ≤
      Real.rpow D (a5FiberGapBudget * (1 - alpha)) :=
    Real.rpow_nonneg hD0 _
  calc
    total ≤ K * gapFactor * selected := htotal
    _ ≤ K * Real.rpow D (a5FiberGapBudget * (1 - alpha)) *
          selected := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfactor' hK) hselected0
    _ ≤ K * Real.rpow D (a5FiberGapBudget * (1 - alpha)) *
          (C * Real.rpow D
            ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
              (1 - alpha))) := by
      exact mul_le_mul_of_nonneg_left hselected (mul_nonneg hK hpowA0)
    _ = K * C *
          (Real.rpow D (a5FiberGapBudget * (1 - alpha)) *
            Real.rpow D
              ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
                (1 - alpha))) := by ring
    _ = K * C * Real.rpow D
          (a5FiberGapBudget * (1 - alpha) +
            (2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
              (1 - alpha)) := by
      exact congrArg (fun z : ℝ => K * C * z)
        (Real.rpow_add (zero_lt_one.trans hD)
          (a5FiberGapBudget * (1 - alpha))
          ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
            (1 - alpha))).symm
    _ = K * C * Real.rpow D ((21 / 10) * (1 - alpha)) := by
      congr 2
      rw [← collar_density_coefficient_with_A5]
      ring

/-- Exact deterministic weld from the surviving p.53 selected-system bound
to the final collar density power.  This theorem makes the remaining analytic
leaf explicit: `hselected` is the p.53 correlation/detector estimate; the
source-box compression and all exponent bookkeeping are already discharged. -/
theorem total_le_final_density_of_A5_and_p53
    {D alpha omega total selected C : ℝ}
    (hD : 1 < D) (_halpha : alpha ≤ 1) (hgap : omega ≤ 1 - alpha)
    (_hC : 0 ≤ C) (hselected0 : 0 ≤ selected)
    (hlog : Real.log D ≤ Real.rpow D (a5FiberGapBudget * omega))
    (htotal : total ≤ 153 * Real.log D * selected)
    (hselected : selected ≤
      C * Real.rpow D
        ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
          (1 - alpha))) :
    total ≤ 153 * C * Real.rpow D ((21 / 10) * (1 - alpha)) := by
  have hD0 : 0 ≤ D := (zero_lt_one.trans hD).le
  have hgapBudget0 : 0 ≤ a5FiberGapBudget := by
    norm_num [a5FiberGapBudget]
  have hgapPower :
      Real.rpow D (a5FiberGapBudget * omega) ≤
        Real.rpow D (a5FiberGapBudget * (1 - alpha)) := by
    apply Real.rpow_le_rpow_of_exponent_le hD.le
    exact mul_le_mul_of_nonneg_left hgap hgapBudget0
  have hlog' : Real.log D ≤
      Real.rpow D (a5FiberGapBudget * (1 - alpha)) :=
    hlog.trans hgapPower
  have hpowA0 : 0 ≤
      Real.rpow D (a5FiberGapBudget * (1 - alpha)) :=
    Real.rpow_nonneg hD0 _
  have hpowB0 : 0 ≤ Real.rpow D
      ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
        (1 - alpha)) := Real.rpow_nonneg hD0 _
  calc
    total ≤ 153 * Real.log D * selected := htotal
    _ ≤ 153 * Real.rpow D (a5FiberGapBudget * (1 - alpha)) *
          selected := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog' (by norm_num)) hselected0
    _ ≤ 153 * Real.rpow D (a5FiberGapBudget * (1 - alpha)) *
          (C * Real.rpow D
            ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
              (1 - alpha))) := by
      exact mul_le_mul_of_nonneg_left hselected
        (mul_nonneg (by norm_num) hpowA0)
    _ = 153 * C *
          (Real.rpow D (a5FiberGapBudget * (1 - alpha)) *
            Real.rpow D
              ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
                (1 - alpha))) := by ring
    _ = 153 * C * Real.rpow D
          (a5FiberGapBudget * (1 - alpha) +
            (2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
              (1 - alpha)) := by
      exact congrArg (fun z : ℝ => 153 * C * z)
        (Real.rpow_add (zero_lt_one.trans hD)
          (a5FiberGapBudget * (1 - alpha))
          ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
            (1 - alpha))).symm
    _ = 153 * C * Real.rpow D ((21 / 10) * (1 - alpha)) := by
      congr 2
      rw [← collar_density_coefficient_with_A5]
      ring

/-- Coefficient-parametric form of the preceding weld.  This is used when
the finite occupied-box extraction takes the uniform principal/nonprincipal
A.5 constant rather than the sharper nonprincipal constant `153`. -/
theorem total_le_final_density_of_logFiber_and_p53
    {D alpha omega total selected C K : ℝ}
    (hD : 1 < D) (_halpha : alpha ≤ 1) (hgap : omega ≤ 1 - alpha)
    (_hC : 0 ≤ C) (hK : 0 ≤ K) (hselected0 : 0 ≤ selected)
    (hlog : Real.log D ≤ Real.rpow D (a5FiberGapBudget * omega))
    (htotal : total ≤ K * Real.log D * selected)
    (hselected : selected ≤
      C * Real.rpow D
        ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
          (1 - alpha))) :
    total ≤ K * C * Real.rpow D ((21 / 10) * (1 - alpha)) := by
  have hD0 : 0 ≤ D := (zero_lt_one.trans hD).le
  have hgapBudget0 : 0 ≤ a5FiberGapBudget := by
    norm_num [a5FiberGapBudget]
  have hgapPower :
      Real.rpow D (a5FiberGapBudget * omega) ≤
        Real.rpow D (a5FiberGapBudget * (1 - alpha)) := by
    apply Real.rpow_le_rpow_of_exponent_le hD.le
    exact mul_le_mul_of_nonneg_left hgap hgapBudget0
  have hlog' : Real.log D ≤
      Real.rpow D (a5FiberGapBudget * (1 - alpha)) :=
    hlog.trans hgapPower
  have hpowA0 : 0 ≤
      Real.rpow D (a5FiberGapBudget * (1 - alpha)) :=
    Real.rpow_nonneg hD0 _
  calc
    total ≤ K * Real.log D * selected := htotal
    _ ≤ K * Real.rpow D (a5FiberGapBudget * (1 - alpha)) *
          selected := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog' hK) hselected0
    _ ≤ K * Real.rpow D (a5FiberGapBudget * (1 - alpha)) *
          (C * Real.rpow D
            ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
              (1 - alpha))) := by
      exact mul_le_mul_of_nonneg_left hselected (mul_nonneg hK hpowA0)
    _ = K * C *
          (Real.rpow D (a5FiberGapBudget * (1 - alpha)) *
            Real.rpow D
              ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
                (1 - alpha))) := by ring
    _ = K * C * Real.rpow D
          (a5FiberGapBudget * (1 - alpha) +
            (2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
              (1 - alpha)) := by
      exact congrArg (fun z : ℝ => K * C * z)
        (Real.rpow_add (zero_lt_one.trans hD)
          (a5FiberGapBudget * (1 - alpha))
          ((2 * (1 + 12 * collarDelta) + 4 * detectorLogBudget) *
            (1 - alpha))).symm
    _ = K * C * Real.rpow D ((21 / 10) * (1 - alpha)) := by
      congr 2
      rw [← collar_density_coefficient_with_A5]
      ring

end

end MAPJutilaCollarA5Budget

#print axioms MAPJutilaCollarA5Budget.collar_density_coefficient_with_A5
#print axioms MAPJutilaCollarA5Budget.sourceBoxWidth_pos
#print axioms MAPJutilaCollarA5Budget.sourceBoxWidth_le_one
#print axioms MAPJutilaCollarA5Budget.eventually_log_le_A5_gap_power
#print axioms MAPJutilaCollarA5Budget.eventually_log_rpow_le_A5_gap_power
#print axioms MAPJutilaCollarA5Budget.total_le_final_density_of_A5_and_p53
#print axioms MAPJutilaCollarA5Budget.total_le_final_density_of_logFiber_and_p53
#print axioms MAPJutilaCollarA5Budget.total_le_final_density_of_gapFactor_and_p53
