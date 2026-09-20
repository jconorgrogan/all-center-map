import MRTCorollary53SourceBridge
import MajorArcPublicLiftBridge

/-!
# MAP far-arc circle/source comparison

This file proves the deterministic measure-normalization part of
`MAPFarSourceReduction`. It contains no MRT, Heath--Brown, padded-cell, or
far-annulus estimate.
-/

namespace MAPFarCircleSourceWeld

open AddCircle MeasureTheory Metric Set
open MAPMRTCorollary53Source MAPMajorArcPublicLiftBridge MAPMajorArcWeld
open MAPAllCenterApertureTransfer PrimePairEndpoints

noncomputable section

/-- The normalized-Haar parameterization of a short circle arc, generalized
from the complex-valued public lift theorem to a real-valued integrand. -/
theorem setIntegral_closedBall_eq_intervalIntegral_lift_real
    {t R : ℝ} (hR0 : 0 ≤ R) (hRhalf : R < (1 : ℝ) / 2)
    (f : UnitAddCircle → ℝ) :
    (∫ alpha in closedBall (t : UnitAddCircle) R, f alpha
        ∂AddCircle.haarAddCircle) =
      ∫ beta in -R..R,
        f ((t : UnitAddCircle) + (beta : UnitAddCircle)) := by
  let g : UnitAddCircle → ℝ := (closedBall (t : UnitAddCircle) R).indicator f
  have hball : MeasurableSet (closedBall (t : UnitAddCircle) R) :=
    measurableSet_closedBall
  calc
    (∫ alpha in closedBall (t : UnitAddCircle) R, f alpha
        ∂AddCircle.haarAddCircle) =
        ∫ alpha : UnitAddCircle, g alpha ∂AddCircle.haarAddCircle := by
      rw [show g = (closedBall (t : UnitAddCircle) R).indicator f by rfl,
        integral_indicator hball]
    _ = ∫ x in Set.Ioc (t - 1 / 2) (t - 1 / 2 + 1),
          g (x : UnitAddCircle) := by
      simpa [AddCircle.volume_eq_smul_haarAddCircle] using
        (UnitAddCircle.integral_preimage (t - 1 / 2) g).symm
    _ = ∫ x in
          Set.Ioc (t - 1 / 2) (t - 1 / 2 + 1) ∩
            ((fun x : ℝ => (x : UnitAddCircle)) ⁻¹'
              closedBall (t : UnitAddCircle) R),
          f (x : UnitAddCircle) := by
      change (∫ x in Set.Ioc (t - 1 / 2) (t - 1 / 2 + 1),
          (((fun x : ℝ => (x : UnitAddCircle)) ⁻¹'
            closedBall (t : UnitAddCircle) R).indicator
              (fun x : ℝ => f (x : UnitAddCircle))) x) = _
      exact setIntegral_indicator
        (hball.preimage AddCircle.measurable_mk')
    _ = ∫ x in Set.Icc (t - R) (t + R),
          f (x : UnitAddCircle) := by
      rw [fundamental_inter_preimage_closedBall hRhalf]
    _ = ∫ x in Set.Ioc (t - R) (t + R),
          f (x : UnitAddCircle) := integral_Icc_eq_integral_Ioc
    _ = ∫ x in t - R..t + R, f (x : UnitAddCircle) := by
      rw [intervalIntegral.integral_of_le (by linarith)]
    _ = ∫ beta in -R..R,
          f ((t : UnitAddCircle) + (beta : UnitAddCircle)) := by
      symm
      calc
        (∫ beta in -R..R,
            f ((t : UnitAddCircle) + (beta : UnitAddCircle))) =
            ∫ beta in -R..R, f ((beta + t : ℝ) : UnitAddCircle) := by
          apply intervalIntegral.integral_congr
          intro beta hbeta
          change f ((t : UnitAddCircle) + (beta : UnitAddCircle)) =
            f ((beta + t : ℝ) : UnitAddCircle)
          rw [← QuotientAddGroup.mk_add]
          congr 1
          ring_nf
        _ = ∫ x in -R + t..R + t, f (x : UnitAddCircle) :=
          intervalIntegral.integral_comp_add_right
            (fun x : ℝ => f (x : UnitAddCircle)) t
        _ = ∫ x in t - R..t + R, f (x : UnitAddCircle) := by
          congr 1 <;> ring_nf

/-- The public centered circle arc is contained in the literal real source
interval from MRT Corollary 5.3.  The source interval has twice the radius.
No analytic estimate is used. -/
theorem centeredArc_primeEnergy_le_sourceEnergy
    {X H beta : ℝ} {q a : ℕ}
    (hH : 1 < H) :
    (∫ alpha in centeredArc H
          (rationalCenter q a + (beta : UnitAddCircle)),
        ‖primeExponentialSum X alpha‖ ^ 2
          ∂AddCircle.haarAddCircle) ≤
      sourceEnergy (mapCorollary53Input X H q a beta (1 : ℝ)) := by
  let t : ℝ := (a : ℝ) / (q : ℝ) + beta
  let R : ℝ := (2 * H)⁻¹
  let F : UnitAddCircle → ℝ := fun alpha => ‖primeExponentialSum X alpha‖ ^ 2
  have hHpos : 0 < H := zero_lt_one.trans hH
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hRhalf : R < (1 : ℝ) / 2 := by
    dsimp [R]
    have htwo : (2 : ℝ) < 2 * H := by nlinarith
    simpa [one_div] using (inv_lt_inv₀ (by positivity : (0 : ℝ) < 2 * H)
      (by norm_num : (0 : ℝ) < 2)).2 htwo
  have hcenter : (t : UnitAddCircle) =
      rationalCenter q a + (beta : UnitAddCircle) := by
    dsimp [t]
    unfold rationalCenter
    exact AddCircle.coe_add 1 ((a : ℝ) / (q : ℝ)) beta
  have harc :
      (∫ alpha in centeredArc H
          (rationalCenter q a + (beta : UnitAddCircle)), F alpha
            ∂AddCircle.haarAddCircle) =
        ∫ theta in -R..R,
          F ((t : UnitAddCircle) + (theta : UnitAddCircle)) := by
    rw [centeredArc, ← hcenter]
    exact setIntegral_closedBall_eq_intervalIntegral_lift_real hR0 hRhalf F
  have hleft : beta - 1 / H ≤ -R + beta := by
    dsimp [R]
    have hinvH : 0 < 1 / H := by positivity
    have hhalf : (2 * H)⁻¹ = (1 / H) / 2 := by field_simp
    rw [hhalf]
    linarith
  have hright : R + beta ≤ beta + 1 / H := by
    dsimp [R]
    have hinvH : 0 < 1 / H := by positivity
    have hhalf : (2 * H)⁻¹ = (1 / H) / 2 := by field_simp
    rw [hhalf]
    linarith
  have hsmallOrder : -R + beta ≤ R + beta := by
    linarith [hR0]
  let G : ℝ → ℝ := fun theta =>
    ‖exponentialSum X (mapMangoldtCoeff X) ((a : ℝ) / q + theta)‖ ^ 2
  have hGcont : Continuous G := by
    dsimp [G, exponentialSum, mapMangoldtCoeff]
    fun_prop
  have hmono :
      (∫ theta in (-R + beta)..(R + beta), G theta) ≤
        ∫ theta in (beta - 1 / H)..(beta + 1 / H), G theta := by
    apply intervalIntegral.integral_mono_interval hleft hsmallOrder hright
    · exact Filter.Eventually.of_forall fun _ => sq_nonneg _
    · exact hGcont.intervalIntegrable _ _
  rw [harc]
  have htranslate :
      (∫ theta in -R..R,
          F ((t : UnitAddCircle) + (theta : UnitAddCircle))) =
        ∫ theta in (-R + beta)..(R + beta), G theta := by
    calc
      (∫ theta in -R..R,
          F ((t : UnitAddCircle) + (theta : UnitAddCircle))) =
          ∫ theta in -R..R, G (theta + beta) := by
        apply intervalIntegral.integral_congr
        intro theta htheta
        dsimp [F, G, t]
        rw [exponentialSum_mapMangoldtCoeff_eq_primeExponentialSum]
        apply congrArg (fun z : ℂ => ‖z‖ ^ 2)
        congr 1
        change ((((a : ℝ) / (q : ℝ) + beta) + theta : ℝ) : UnitAddCircle) =
          (((a : ℝ) / (q : ℝ) + (theta + beta) : ℝ) : UnitAddCircle)
        congr 1
        ring
      _ = ∫ theta in (-R + beta)..(R + beta), G theta :=
        intervalIntegral.integral_comp_add_right G beta
  rw [htranslate]
  simpa [sourceEnergy, mapCorollary53Input] using hmono

/-- Version with the eta used by the MAP source reduction. -/
theorem centeredArc_primeEnergy_le_mapSourceEnergy
    {X H beta eta : ℝ} {q a : ℕ}
    (hH : 1 < H) :
    (∫ alpha in centeredArc H
          (rationalCenter q a + (beta : UnitAddCircle)),
        ‖primeExponentialSum X alpha‖ ^ 2
          ∂AddCircle.haarAddCircle) ≤
      sourceEnergy (mapCorollary53Input X H q a beta eta) := by
  simpa [sourceEnergy, mapCorollary53Input] using
    (centeredArc_primeEnergy_le_sourceEnergy
      (X := X) (H := H) (beta := beta) (q := q) (a := a) hH)

end
end MAPFarCircleSourceWeld

#print axioms MAPFarCircleSourceWeld.setIntegral_closedBall_eq_intervalIntegral_lift_real
#print axioms MAPFarCircleSourceWeld.centeredArc_primeEnergy_le_mapSourceEnergy
