import MRTWholeLineEq83ParallelVdC
import MRTWholeLineEq83ParallelEnergySplit
import MRTWholeLineHighCellEquation84

/-!
# Source-faithful whole-line MRT equation (83)

This module combines the fixed-outer-window van der Corput estimate, the
effective lower cell of length `5H`, and the high-cell equation-(84) estimate.
The split follows the source regimes `|beta| H^2 < X` and
`X ≤ |beta| H^2`; the fixed outer-window inflation is absorbed only into an
absolute constant.
-/

namespace MAPMRTWholeLineEq83Parallel

open MeasureTheory Set
open MAPMRTProposition51HardBranch
open MAPMRTWholeLinePacketMemLp
open MAPMRTWholeLinePacketTrivialBound
open MAPMRTWholeLineEq83ParallelVdC
open MAPMRTWholeLineEq83ParallelLowCell
open MAPMRTWholeLineEq83ParallelEnergySplit
open MAPMRTWholeLineHighCellEquation84

noncomputable section

def outerScaleInflation : ℝ := (4 / 3 : ℝ) * Real.exp 100
def curvatureFloor : ℝ := Real.exp (-100)

def wholeLineTrivialCoefficient (D0 : ℝ) : ℝ := Real.exp 50 * D0

def wholeLineVdCCoefficient (D1 Dout : ℝ) : ℝ :=
  10 * Real.exp 50 * (101 + D1 + Dout)

def wholeLineFarCoefficient (D1 D2 B1 B2 : ℝ) : ℝ :=
  4 * Real.exp 200 * highCellEquation84BaseConstant D1 D2 B1 B2

def wholeLineEquation83Constant
    (D0 D1 D2 B1 B2 Dout : ℝ) : ℝ :=
  let K := outerScaleInflation
  let E := curvatureFloor
  let T := wholeLineTrivialCoefficient D0
  let V := wholeLineVdCCoefficient D1 Dout
  let F := wholeLineFarCoefficient D1 D2 B1 B2
  (5 + 16 * Real.pi * K) * ((T + F) ^ 2 + (V + F) ^ 2) / E

theorem outerScaleInflation_one_le : 1 ≤ outerScaleInflation := by
  unfold outerScaleInflation
  have he : 1 ≤ Real.exp 100 := Real.one_le_exp (by norm_num)
  nlinarith

theorem curvatureFloor_pos : 0 < curvatureFloor := by
  unfold curvatureFloor
  positivity

theorem curvatureFloor_le_one : curvatureFloor ≤ 1 := by
  unfold curvatureFloor
  exact Real.exp_le_one_iff.mpr (by norm_num)

set_option maxHeartbeats 1000000 in
/-- The literal unrestricted equation-(83) estimate. -/
theorem source_packet_energy_equation83_wholeLine
    {X H beta t D0 D1 D2 B1 B2 Dout : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hH : 1 ≤ H) (hHalf : H ≤ X / 2)
    (hhard : 1 < |beta| * H)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff'Support : ∀ y, 1 ≤ |y| → cutoff' y = 0)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (houterBound : ∀ y, |outer y| ≤ 1)
    (houter'Bound : ∀ y, |outer' y| ≤ B1)
    (houter''Bound : ∀ y, |outer'' y| ≤ B2)
    (hcutoffDeriv : ∀ y, HasDerivAt cutoff (cutoff' y) y)
    (hcutoffSecond : ∀ y, HasDerivAt cutoff' (cutoff'' y) y)
    (houterDeriv : ∀ y, HasDerivAt outer (outer' y) y)
    (houterSecond : ∀ y, HasDerivAt outer' (outer'' y) y)
    (hcutoff''Cont : Continuous cutoff'')
    (houter''Cont : Continuous outer'')
    (hcutoffInt : Integrable (fun y ↦ |cutoff y|))
    (hcutoff'Int : Integrable (fun y ↦ |cutoff' y|))
    (hcutoff''Int : Integrable (fun y ↦ |cutoff'' y|))
    (houter'Int : Integrable (fun y ↦ |outer' y|))
    (hD0 : (∫ y : ℝ, |cutoff y|) ≤ D0)
    (hD1 : (∫ y : ℝ, |cutoff' y|) ≤ D1)
    (hD2 : (∫ y : ℝ, |cutoff'' y|) ≤ D2)
    (hDout : (∫ y : ℝ, |outer' y|) ≤ Dout) :
    (∫ x : ℝ,
      ‖sourceStationaryPacket X H x beta t cutoff outer‖ ^ 2) ≤
      wholeLineEquation83Constant D0 D1 D2 B1 B2 Dout *
        H / (|beta| * X) := by
  let q : ℝ := |beta|
  let K : ℝ := outerScaleInflation
  let E : ℝ := curvatureFloor
  let T : ℝ := wholeLineTrivialCoefficient D0
  let V : ℝ := wholeLineVdCCoefficient D1 Dout
  let F : ℝ := wholeLineFarCoefficient D1 D2 B1 B2
  let R : ℝ := 4 * max (q * H) (K * (X / H))
  let J : ℝ → ℂ := fun x ↦
    sourceStationaryPacket X H x beta t cutoff outer
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hX : 0 < X := by linarith
  have hbeta : beta ≠ 0 := by
    intro hb
    subst beta
    norm_num at hhard
  have hq : 0 < q := by exact abs_pos.mpr hbeta
  have hK : 1 ≤ K := by exact outerScaleInflation_one_le
  have hE : 0 < E := curvatureFloor_pos
  have hEle : E ≤ 1 := curvatureFloor_le_one
  have hD0n : 0 ≤ D0 :=
    (integral_nonneg (fun y ↦ abs_nonneg (cutoff y))).trans hD0
  have hD1n : 0 ≤ D1 :=
    (integral_nonneg (fun y ↦ abs_nonneg (cutoff' y))).trans hD1
  have hD2n : 0 ≤ D2 :=
    (integral_nonneg (fun y ↦ abs_nonneg (cutoff'' y))).trans hD2
  have hDoutn : 0 ≤ Dout :=
    (integral_nonneg (fun y ↦ abs_nonneg (outer' y))).trans hDout
  have hB1n : 0 ≤ B1 :=
    (abs_nonneg (outer' 0)).trans (houter'Bound 0)
  have hB2n : 0 ≤ B2 :=
    (abs_nonneg (outer'' 0)).trans (houter''Bound 0)
  have hT : 0 ≤ T := by unfold T wholeLineTrivialCoefficient; positivity
  have hV : 0 ≤ V := by
    unfold V wholeLineVdCCoefficient
    positivity
  have hF : 0 ≤ F := by
    unfold F wholeLineFarCoefficient highCellEquation84BaseConstant
    positivity
  have hR : 0 < R := by
    unfold R
    have : 0 < q * H := mul_pos hq hHpos
    positivity
  have hcutoffCont : Continuous cutoff :=
    continuous_iff_continuousAt.mpr
      (fun y ↦ (hcutoffDeriv y).continuousAt)
  have hcutoff'Cont : Continuous cutoff' :=
    continuous_iff_continuousAt.mpr
      (fun y ↦ (hcutoffSecond y).continuousAt)
  have houterCont : Continuous outer :=
    continuous_iff_continuousAt.mpr
      (fun y ↦ (houterDeriv y).continuousAt)
  have houter'Cont : Continuous outer' :=
    continuous_iff_continuousAt.mpr
      (fun y ↦ (houterSecond y).continuousAt)
  have hInt : Integrable (fun x ↦ ‖J x‖ ^ 2) := by
    exact integrable_norm_sourceStationaryPacket_sq hX hHpos hcutoffCont
      houterCont hcutoffSupport houterSupport
  have hzero : ∀ x, x ≤ -H → J x = 0 := by
    intro x hx
    exact sourceStationaryPacket_eq_zero_of_le_neg_H hX hHpos
      hcutoffSupport hx
  have htrivial : ∀ x, ‖J x‖ ≤ T * H / X := by
    intro x
    have ht := norm_sourceStationaryPacket_le_trivial_wholeLine
      (X := X) (H := H) (x := x) (beta := beta) (t := t)
      (D0 := D0) (cutoff := cutoff) (outer := outer)
      hX hHpos hcutoffCont houterCont hcutoffInt hD0
      houterSupport houterBound
    simpa [J, T, wholeLineTrivialCoefficient] using ht
  have hvdc : ∀ x, ‖J x‖ ≤ V / Real.sqrt (q * X * E) := by
    intro x
    have hv := norm_sourceStationaryPacket_le_vdc_wholeLine
      (X := X) (H := H) (x := x) (beta := beta) (t := t)
      (Dcut := D1) (Dout := Dout) (cutoff := cutoff)
      (cutoff' := cutoff') (outer := outer) (outer' := outer')
      hX hHpos hbeta houterSupport hcutoffBound houterBound
      hcutoffDeriv houterDeriv hcutoff'Cont houter'Cont
      hcutoff'Int houter'Int hD1 hDout
    simpa [J, V, q, E, wholeLineVdCCoefficient, curvatureFloor] using hv
  have hfar : ∀ x, 4 * H ≤ x → R ≤ |t / (2 * Real.pi) + beta * x| →
      ‖J x‖ ≤ F * (X / H) / |t / (2 * Real.pi) + beta * x| ^ 2 := by
    intro x hx hxFar
    have hf := norm_sourceStationaryPacket_equation84_highCell
      (X := X) (H := H) (x := x) (beta := beta) (t := t)
      (D1 := D1) (D2 := D2) (B1 := B1) (B2 := B2)
      (cutoff := cutoff) (cutoff' := cutoff') (cutoff'' := cutoff'')
      (outer := outer) (outer' := outer') (outer'' := outer'')
      hX hHpos hx (by simpa [R, q, K, outerScaleInflation] using hxFar)
      hcutoffSupport hcutoff'Support houterSupport hcutoffBound houterBound
      houter'Bound houter''Bound hcutoffDeriv hcutoffSecond
      houterDeriv houterSecond hcutoff''Cont houter''Cont
      hcutoff'Int hcutoff''Int hD1 hD2
    simpa [J, F, wholeLineFarCoefficient] using hf
  by_cases hsmall : q * H ^ 2 < X
  · let A : ℝ := (T + F) * H / X
    let B : ℝ := F * (X / H)
    have hA : 0 ≤ A := by unfold A; positivity
    have hB : 0 ≤ B := by unfold B; positivity
    have hqH_le : q * H ≤ X / H := by
      rw [le_div_iff₀ hHpos]
      nlinarith
    have hmax : max (q * H) (K * (X / H)) = K * (X / H) := by
      apply max_eq_right
      exact hqH_le.trans (by
        have hratio : 0 ≤ X / H := (div_pos hX hHpos).le
        nlinarith)
    have hRsmall : R = 4 * K * (X / H) := by
      unfold R
      rw [hmax]
      ring
    have hcentral : ∀ x, ‖J x‖ ≤ A := by
      intro x
      have hTF : T ≤ T + F := le_add_of_nonneg_right hF
      exact (htrivial x).trans (by
        unfold A
        gcongr)
    have hrelation : B / R ^ 2 ≤ A := by
      rw [hRsmall]
      unfold A B
      have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
      have hden : 0 < (4 * K * (X / H)) ^ 2 := by positivity
      have hKF : F ≤ (T + F) * 4 ^ 2 * K ^ 2 := by
        have hTF : F ≤ T + F := by linarith
        have hfac : 1 ≤ 4 ^ 2 * K ^ 2 := by
          nlinarith [sq_nonneg K]
        calc
          F ≤ T + F := hTF
          _ ≤ (T + F) * (4 ^ 2 * K ^ 2) :=
            le_mul_of_one_le_right (by positivity) hfac
          _ = (T + F) * 4 ^ 2 * K ^ 2 := by ring
      apply (div_le_iff₀ hden).2
      field_simp [hX.ne', hHpos.ne', hKpos.ne']
      exact hKF
    have henergy := wholeLine_energy_le_low_add_cauchy
      (H := H) (c := t / (2 * Real.pi)) (beta := beta)
      (R := R) (A := A) (B := B) (J := J)
      hHpos hbeta hR hA hB hzero hcentral hfar hrelation hInt
    have hsmallScale : H ^ 3 / X ^ 2 ≤ H / (q * X) := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hX) (mul_pos hq hX)).2
      have hm := mul_le_mul_of_nonneg_left hsmall.le
        (mul_nonneg hHpos.le hX.le)
      nlinarith [hm]
    have hcoeffNonneg : 0 ≤ 5 + 16 * Real.pi * K := by positivity
    have hsmallCoeff :
        5 * H * A ^ 2 + 4 * Real.pi * A ^ 2 * R / q ≤
          (5 + 16 * Real.pi * K) * (T + F) ^ 2 * H / (q * X) := by
      rw [hRsmall]
      unfold A
      have hsq : 0 ≤ (T + F) ^ 2 := sq_nonneg _
      calc
        5 * H * (((T + F) * H / X) ^ 2) +
            4 * Real.pi * (((T + F) * H / X) ^ 2) *
              (4 * K * (X / H)) / q =
            5 * (T + F) ^ 2 * (H ^ 3 / X ^ 2) +
              16 * Real.pi * K * (T + F) ^ 2 * H / (q * X) := by
          field_simp [hX.ne', hHpos.ne', hq.ne']
          ring
        _ ≤ 5 * (T + F) ^ 2 * (H / (q * X)) +
              16 * Real.pi * K * (T + F) ^ 2 * H / (q * X) := by
          gcongr
        _ = (5 + 16 * Real.pi * K) * (T + F) ^ 2 * H / (q * X) := by ring
    refine henergy.trans (hsmallCoeff.trans ?_)
    unfold wholeLineEquation83Constant
    dsimp only
    change (5 + 16 * Real.pi * K) * (T + F) ^ 2 * H / (q * X) ≤
      ((5 + 16 * Real.pi * K) * ((T + F) ^ 2 + (V + F) ^ 2) / E) *
        H / (q * X)
    have hsum : (T + F) ^ 2 ≤ (T + F) ^ 2 + (V + F) ^ 2 :=
      le_add_of_nonneg_right (sq_nonneg _)
    have hinv : 1 ≤ 1 / E := by
      rw [le_div_iff₀ hE]
      simpa using hEle
    have hscale0 : 0 ≤ (5 + 16 * Real.pi * K) * H / (q * X) := by positivity
    calc
      (5 + 16 * Real.pi * K) * (T + F) ^ 2 * H / (q * X) ≤
          (5 + 16 * Real.pi * K) * ((T + F) ^ 2 + (V + F) ^ 2) *
            H / (q * X) := by gcongr
      _ = ((5 + 16 * Real.pi * K) * ((T + F) ^ 2 + (V + F) ^ 2) *
            H / (q * X)) * 1 := by ring
      _ ≤ ((5 + 16 * Real.pi * K) * ((T + F) ^ 2 + (V + F) ^ 2) *
            H / (q * X)) * (1 / E) := by
        gcongr
      _ = ((5 + 16 * Real.pi * K) * ((T + F) ^ 2 + (V + F) ^ 2) / E) *
            H / (q * X) := by ring
  · have hlarge : X ≤ q * H ^ 2 := le_of_not_gt hsmall
    let A : ℝ := (V + F) / Real.sqrt (q * X * E)
    let B : ℝ := F * (X / H)
    have hsqrt : 0 < Real.sqrt (q * X * E) := by positivity
    have hsqrtSq : Real.sqrt (q * X * E) ^ 2 = q * X * E :=
      Real.sq_sqrt (by positivity)
    have hsqrt_le : Real.sqrt (q * X * E) ≤ q * H := by
      have hsq : Real.sqrt (q * X * E) ^ 2 ≤ (q * H) ^ 2 := by
        rw [hsqrtSq]
        have hqX : q * X ≤ q * (q * H ^ 2) :=
          mul_le_mul_of_nonneg_left hlarge hq.le
        have hqXE : q * X * E ≤ q * X :=
          mul_le_of_le_one_right (by positivity : 0 ≤ q * X) hEle
        calc
          q * X * E ≤ q * X := hqXE
          _ ≤ q * (q * H ^ 2) := hqX
          _ = (q * H) ^ 2 := by ring
      nlinarith [sq_nonneg (Real.sqrt (q * X * E) - q * H)]
    have hA : 0 ≤ A := by unfold A; positivity
    have hB : 0 ≤ B := by unfold B; positivity
    have hmaxLarge : max (q * H) (K * (X / H)) ≤ K * (q * H) := by
      apply max_le
      · exact (le_mul_of_one_le_left (mul_nonneg hq.le hHpos.le) hK)
      · have hxratio : X / H ≤ q * H := by
          rw [div_le_iff₀ hHpos]
          calc
            X ≤ q * H ^ 2 := hlarge
            _ = q * H * H := by ring
        exact mul_le_mul_of_nonneg_left hxratio (by linarith : 0 ≤ K)
    have hRlarge : R ≤ 4 * K * (q * H) := by
      unfold R
      calc
        4 * max (q * H) (K * (X / H)) ≤ 4 * (K * (q * H)) :=
          mul_le_mul_of_nonneg_left hmaxLarge (by norm_num)
        _ = 4 * K * (q * H) := by ring
    have hcentral : ∀ x, ‖J x‖ ≤ A := by
      intro x
      exact (hvdc x).trans (by
        unfold A
        apply div_le_div_of_nonneg_right (le_add_of_nonneg_right hF) hsqrt.le)
    have hrelation : B / R ^ 2 ≤ A := by
      have hRq : 4 * (q * H) ≤ R := by
        unfold R
        exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
      have hden : (4 * (q * H)) ^ 2 ≤ R ^ 2 :=
        pow_le_pow_left₀ (by positivity) hRq 2
      have hfirst : B / R ^ 2 ≤ B / (4 * (q * H)) ^ 2 := by
        exact div_le_div_of_nonneg_left hB (by positivity) hden
      refine hfirst.trans ?_
      unfold A B
      apply (le_div_iff₀ hsqrt).2
      have hXqh : X / H ≤ q * H := by
        rw [div_le_iff₀ hHpos]
        calc
          X ≤ q * H ^ 2 := hlarge
          _ = q * H * H := by ring
      have hFrac : (X / H) / (4 * (q * H)) ^ 2 *
          Real.sqrt (q * X * E) ≤ 1 := by
        have h1 : (X / H) * Real.sqrt (q * X * E) ≤ (q * H) ^ 2 := by
          calc
            (X / H) * Real.sqrt (q * X * E) ≤ (q * H) * (q * H) := by
              gcongr
            _ = (q * H) ^ 2 := by ring
        rw [show (X / H) / (4 * (q * H)) ^ 2 *
            Real.sqrt (q * X * E) =
            ((X / H) * Real.sqrt (q * X * E)) /
              (4 * (q * H)) ^ 2 by ring]
        apply (div_le_iff₀ (by positivity : 0 < (4 * (q * H)) ^ 2)).2
        calc
          (X / H) * Real.sqrt (q * X * E) ≤ (q * H) ^ 2 := h1
          _ ≤ 1 * (4 * (q * H)) ^ 2 := by
            have hbase : q * H ≤ 4 * (q * H) := by
              nlinarith [mul_nonneg hq.le hHpos.le]
            simpa only [one_mul] using
              (pow_le_pow_left₀ (mul_nonneg hq.le hHpos.le) hbase 2)
      calc
        (F * (X / H) / (4 * (q * H)) ^ 2) *
            Real.sqrt (q * X * E) =
            F * (((X / H) / (4 * (q * H)) ^ 2) *
              Real.sqrt (q * X * E)) := by ring
        _ ≤ F * 1 := mul_le_mul_of_nonneg_left hFrac hF
        _ ≤ V + F := by simpa using (le_add_of_nonneg_left hV : F ≤ V + F)
    have henergy := wholeLine_energy_le_low_add_cauchy
      (H := H) (c := t / (2 * Real.pi)) (beta := beta)
      (R := R) (A := A) (B := B) (J := J)
      hHpos hbeta hR hA hB hzero hcentral hfar hrelation hInt
    have hlargeCoeff :
        5 * H * A ^ 2 + 4 * Real.pi * A ^ 2 * R / q ≤
          ((5 + 16 * Real.pi * K) * (V + F) ^ 2 / E) *
            H / (q * X) := by
      unfold A
      have hsqRewrite :
          ((V + F) / Real.sqrt (q * X * E)) ^ 2 =
            (V + F) ^ 2 / (q * X * E) := by
        rw [div_pow, hsqrtSq]
      rw [hsqRewrite]
      calc
        5 * H * ((V + F) ^ 2 / (q * X * E)) +
            4 * Real.pi * ((V + F) ^ 2 / (q * X * E)) * R / q ≤
          5 * H * ((V + F) ^ 2 / (q * X * E)) +
            4 * Real.pi * ((V + F) ^ 2 / (q * X * E)) *
              (4 * K * (q * H)) / q := by
          apply add_le_add le_rfl
          apply div_le_div_of_nonneg_right _ hq.le
          apply mul_le_mul_of_nonneg_left hRlarge
          positivity
        _ = ((5 + 16 * Real.pi * K) * (V + F) ^ 2 / E) *
              H / (q * X) := by
          field_simp [hq.ne', hX.ne', hE.ne']
          ring
    refine henergy.trans (hlargeCoeff.trans ?_)
    unfold wholeLineEquation83Constant
    dsimp only
    change ((5 + 16 * Real.pi * K) * (V + F) ^ 2 / E) * H / (q * X) ≤
      ((5 + 16 * Real.pi * K) * ((T + F) ^ 2 + (V + F) ^ 2) / E) *
        H / (q * X)
    gcongr
    exact le_add_of_nonneg_left (sq_nonneg _)

#print axioms outerScaleInflation_one_le
#print axioms curvatureFloor_pos
#print axioms curvatureFloor_le_one
#print axioms source_packet_energy_equation83_wholeLine

end
end MAPMRTWholeLineEq83Parallel
