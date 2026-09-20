import JutilaDeterministicCore

/-!
# The deterministic final closure of Jutila's Theorem 1

This module certifies two source-suppressed steps on pp. 51--53 of Jutila
(1977): the weld of the thin-box compression with the terminal quadratic
inequality, and the relabeling of the internal detector loss into the
`(2 + eta) * (1 - alpha)` exponent in (1.7).

It proves no zero-density estimate.  After this file, the remaining work is
analytic: the p. 48 hybrid convexity estimate, Graham's Lemma 4, the detector
and contour estimates, Linnik's thin-box Lemma 8, and the p. 53 correlation
bound that furnishes the displayed quadratic inequality.
-/

namespace MAPJutilaTheoremOneFiniteClosure

open MAPJutilaDeterministicCore

noncomputable section

/-- The detector scale denoted `x` on pp. 50--53 after the p. 52 choice
`X = D^(1+12*delta)`: `x = X log^2 D`. -/
def detectorLength (D delta : ℝ) : ℝ :=
  Real.rpow D (1 + 12 * delta) * (Real.log D) ^ 2

/-- A uniform internal loss allocation.  The cap makes the p. 52 detector
condition `delta <= 1/21` automatic for every requested final `eta`; the
smaller branch retains a strict reserve in the final coefficient. -/
def internalDelta (eta : ℝ) : ℝ := min (eta / 56) (1 / 42)

def logarithmicKappa (eta : ℝ) : ℝ := eta / 112

theorem internalDelta_pos {eta : ℝ} (heta : 0 < eta) :
    0 < internalDelta eta := by
  unfold internalDelta
  exact lt_min (by positivity) (by norm_num)

theorem internalDelta_le_one_twenty_first (eta : ℝ) :
    internalDelta eta ≤ 1 / 21 := by
  unfold internalDelta
  exact (min_le_right _ _).trans (by norm_num)

theorem logarithmicKappa_pos {eta : ℝ} (heta : 0 < eta) :
    0 < logarithmicKappa eta := by
  unfold logarithmicKappa
  positivity

/-- The exact loss hidden in the final epsilon relabeling on p. 53.  The
factor `24*delta` comes from `X^(2-2*alpha)` and `4*kappa` pays for
`log(D)^(4(1-alpha))`. -/
theorem allocated_density_coefficient_le
    {eta : ℝ} (heta : 0 ≤ eta) :
    logBudgetedDensityCoefficient (internalDelta eta)
        (logarithmicKappa eta) ≤ 2 + eta := by
  have hdelta : internalDelta eta ≤ eta / 56 := by
    exact min_le_left _ _
  unfold logBudgetedDensityCoefficient directDensityCoefficient
    logarithmicKappa
  nlinarith

/-- The source detector parameter inequality remains legal under the chosen
internal loss whenever `alpha >= 1-internalDelta eta`. -/
theorem allocated_detector_parameter
    {eta alpha : ℝ} (heta : 0 < eta)
    (halpha : 1 - internalDelta eta ≤ alpha) :
    (1 + internalDelta eta) *
        (1 / 2 + internalDelta eta +
          (1 / 2 + 8 * internalDelta eta)) ≤
      alpha * (1 + 12 * internalDelta eta) := by
  exact detector_parameter_exponent
    (internalDelta_pos heta).le
    (internalDelta_le_one_twenty_first eta)
    halpha

/-- Source-faithful exponent conversion from Jutila's literal detector
length `x = D^(1+12*delta) log^2 D` to the final `(2+eta)(1-alpha)`
power.  No asymptotic notation is used: the only logarithmic input is the
explicit inequality `log D <= D^kappa`. -/
theorem detectorLength_rpow_le_final_density_power
    {D eta alpha : ℝ}
    (hD : 1 ≤ D) (heta : 0 < eta) (halpha : alpha ≤ 1)
    (hlog : Real.log D ≤ Real.rpow D (logarithmicKappa eta)) :
    Real.rpow (detectorLength D (internalDelta eta))
        (2 * (1 - alpha)) ≤
      Real.rpow D ((2 + eta) * (1 - alpha)) := by
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hlog0 : 0 ≤ Real.log D := Real.log_nonneg hD
  have hk0 : 0 ≤ logarithmicKappa eta :=
    (logarithmicKappa_pos heta).le
  have hu0 : 0 ≤ 1 - alpha := sub_nonneg.mpr halpha
  have he0 : 0 ≤ 2 * (1 - alpha) := mul_nonneg (by norm_num) hu0
  have hlogPow : (Real.log D) ^ 2 ≤
      (Real.rpow D (logarithmicKappa eta)) ^ 2 := by
    exact pow_le_pow_left₀ hlog0 hlog 2
  have hlength : detectorLength D (internalDelta eta) ≤
      Real.rpow D (1 + 12 * internalDelta eta +
        2 * logarithmicKappa eta) := by
    calc
      detectorLength D (internalDelta eta) =
          Real.rpow D (1 + 12 * internalDelta eta) *
            (Real.log D) ^ 2 := rfl
      _ ≤ Real.rpow D (1 + 12 * internalDelta eta) *
            (Real.rpow D (logarithmicKappa eta)) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hlogPow
          (Real.rpow_nonneg hDpos.le _)
      _ = Real.rpow D (1 + 12 * internalDelta eta +
          2 * logarithmicKappa eta) := by
        rw [pow_two]
        calc
          Real.rpow D (1 + 12 * internalDelta eta) *
                (Real.rpow D (logarithmicKappa eta) *
                  Real.rpow D (logarithmicKappa eta)) =
              (Real.rpow D (1 + 12 * internalDelta eta) *
                  Real.rpow D (logarithmicKappa eta)) *
                Real.rpow D (logarithmicKappa eta) := by ring
          _ = Real.rpow D
                ((1 + 12 * internalDelta eta) +
                  logarithmicKappa eta) *
                Real.rpow D (logarithmicKappa eta) := by
              exact congrArg
                (fun z : ℝ => z * Real.rpow D (logarithmicKappa eta))
                (Real.rpow_add hDpos
                  (1 + 12 * internalDelta eta)
                  (logarithmicKappa eta)).symm
          _ = Real.rpow D
                (((1 + 12 * internalDelta eta) +
                  logarithmicKappa eta) + logarithmicKappa eta) := by
              exact (Real.rpow_add hDpos
                ((1 + 12 * internalDelta eta) +
                  logarithmicKappa eta)
                (logarithmicKappa eta)).symm
          _ = Real.rpow D (1 + 12 * internalDelta eta +
                2 * logarithmicKappa eta) := by
              congr 1
              ring
  have hlength0 : 0 ≤ detectorLength D (internalDelta eta) := by
    unfold detectorLength
    exact mul_nonneg (Real.rpow_nonneg hDpos.le _) (sq_nonneg _)
  have hpowLength := Real.rpow_le_rpow hlength0 hlength he0
  have hnormalize :
      Real.rpow
          (Real.rpow D (1 + 12 * internalDelta eta +
            2 * logarithmicKappa eta))
          (2 * (1 - alpha)) =
        Real.rpow D
          (logBudgetedDensityCoefficient (internalDelta eta)
            (logarithmicKappa eta) * (1 - alpha)) := by
    calc
      Real.rpow
          (Real.rpow D (1 + 12 * internalDelta eta +
            2 * logarithmicKappa eta))
          (2 * (1 - alpha)) =
        Real.rpow D
          ((1 + 12 * internalDelta eta +
            2 * logarithmicKappa eta) * (2 * (1 - alpha))) := by
          exact (Real.rpow_mul hDpos.le _ _).symm
      _ = Real.rpow D
          (logBudgetedDensityCoefficient (internalDelta eta)
            (logarithmicKappa eta) * (1 - alpha)) := by
          congr 1
          unfold logBudgetedDensityCoefficient directDensityCoefficient
          ring
  have hcoeff := allocated_density_coefficient_le heta.le
  have hexp :
      logBudgetedDensityCoefficient (internalDelta eta)
          (logarithmicKappa eta) * (1 - alpha) ≤
        (2 + eta) * (1 - alpha) :=
    mul_le_mul_of_nonneg_right hcoeff hu0
  exact (hpowLength.trans_eq hnormalize).trans
    (Real.rpow_le_rpow_of_exponent_le hD hexp)

/-- Jutila's thin-box compression (Lemma 8 and the even/odd split), followed
by the terminal p. 53 quadratic absorption, in one reusable finite theorem.

`total` is the multiplicity-weighted zero count, `selected` is the larger
well-spaced system, and `fiberCap` is the local Lemma-8 cost.  The analytic
proof is isolated in `hquadratic`; everything after it is certified here. -/
theorem total_le_of_thinBoxes_and_p53_quadratic
    {total fiberCap selected A C E W : ℝ}
    (hfiber : 0 ≤ fiberCap)
    (hselected : 0 ≤ selected) (hW : 0 ≤ W) (hC : 0 ≤ C)
    (hcompress : total ≤ 2 * fiberCap * selected)
    (hquadratic : A * selected ^ 2 ≤
      C * selected * W + E * selected ^ 2)
    (habsorb : E < A - C) :
    total ≤ 2 * fiberCap * (C * W / (A - C - E)) := by
  have hselectedBound : selected ≤ C * W / (A - C - E) :=
    quadratic_density_absorption hselected hW hC hquadratic habsorb
  have hfactor0 : 0 ≤ 2 * fiberCap := by positivity
  exact hcompress.trans
    (mul_le_mul_of_nonneg_left hselectedBound hfactor0)

/-- Natural-cardinality version matching the actual finite zero and box
systems.  The casts are explicit, so analytic multiplicity is not silently
replaced by distinct support cardinality. -/
theorem nat_total_le_of_thinBoxes_and_p53_quadratic
    {total fiberCap selected : ℕ} {A C E W : ℝ}
    (hW : 0 ≤ W) (hC : 0 ≤ C)
    (hcompress : total ≤ 2 * fiberCap * selected)
    (hquadratic : A * (selected : ℝ) ^ 2 ≤
      C * (selected : ℝ) * W + E * (selected : ℝ) ^ 2)
    (habsorb : E < A - C) :
    (total : ℝ) ≤
      2 * (fiberCap : ℝ) * (C * W / (A - C - E)) := by
  apply total_le_of_thinBoxes_and_p53_quadratic
    (total := (total : ℝ)) (fiberCap := (fiberCap : ℝ))
    (selected := (selected : ℝ))
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hW hC
  · exact_mod_cast hcompress
  · exact hquadratic
  · exact habsorb

end

end MAPJutilaTheoremOneFiniteClosure

#print axioms MAPJutilaTheoremOneFiniteClosure.allocated_density_coefficient_le
#print axioms MAPJutilaTheoremOneFiniteClosure.allocated_detector_parameter
#print axioms MAPJutilaTheoremOneFiniteClosure.detectorLength_rpow_le_final_density_power
#print axioms MAPJutilaTheoremOneFiniteClosure.total_le_of_thinBoxes_and_p53_quadratic
#print axioms MAPJutilaTheoremOneFiniteClosure.nat_total_le_of_thinBoxes_and_p53_quadratic
