import MRTSourceLowerCollarAmplitudeGain
import MRTSourceLowerCollarPhasePartition
import MRTVanDerCorputCore

/-!
# Van der Corput on the resonant endpoint-collar cell

This is the exact specialization of the proved weighted second-derivative/BV
lemma to the collar packet-difference amplitude.  The amplitude derivative is
defined and proved here; no source-facing van der Corput premise is introduced.
-/

namespace MAPMRTSourceLowerCollarVdC

open MeasureTheory Set
open MAPMRTProposition51HardBranch
open MAPMRTCorollary53Source
open MAPMRTVanDerCorput
open MAPMRTVanDerCorputProof
open MAPMRTSourceLowerCollarResonance
open MAPMRTSourceLowerCollarPhasePartition
open MAPMRTSourceLowerCollarAmplitudeGain

noncomputable section

/-- The literal difference of the amplitudes with and without the fixed outer
cutoff. -/
def sourceLowerCollarAmplitudeDifference
    (X H x : ℝ) (cutoff outer : ℝ → ℝ) (w : ℝ) : ℂ :=
  sourcePacketAmplitude X H x cutoff (fun _ ↦ 1) w -
    sourcePacketAmplitude X H x cutoff outer w

/-- Its exact derivative. -/
def sourceLowerCollarAmplitudeDifferenceDeriv
    (X H x : ℝ) (cutoff cutoff' outer outer' : ℝ → ℝ) (w : ℝ) : ℂ :=
  sourcePacketAmplitudeDeriv X H x cutoff cutoff' (fun _ ↦ 1) (fun _ ↦ 0) w -
    sourcePacketAmplitudeDeriv X H x cutoff cutoff' outer outer' w

theorem hasDerivAt_sourceLowerCollarAmplitudeDifference
    {X H x w : ℝ} {cutoff cutoff' outer outer' : ℝ → ℝ}
    (hcutoffDeriv : ∀ z, HasDerivAt cutoff (cutoff' z) z)
    (houterDeriv : ∀ z, HasDerivAt outer (outer' z) z) :
    HasDerivAt (sourceLowerCollarAmplitudeDifference X H x cutoff outer)
      (sourceLowerCollarAmplitudeDifferenceDeriv
        X H x cutoff cutoff' outer outer' w) w := by
  exact (hasDerivAt_sourcePacketAmplitude hcutoffDeriv
    (fun z ↦ hasDerivAt_const z 1)).sub
      (hasDerivAt_sourcePacketAmplitude hcutoffDeriv houterDeriv)

/-- Elementary three-term norm bound for the exact source amplitude
derivative. -/
theorem norm_sourcePacketAmplitudeDeriv_le_terms
    (X H x w : ℝ) (cutoff cutoff' outer outer' : ℝ → ℝ) :
    ‖sourcePacketAmplitudeDeriv X H x cutoff cutoff' outer outer' w‖ ≤
      Real.exp (w / 2) / 2 * |cutoff ((X * Real.exp w - x) / H)| *
          |outer (w / 100)| +
        Real.exp (w / 2) * |cutoff' ((X * Real.exp w - x) / H)| *
          |X * Real.exp w / H| * |outer (w / 100)| +
        Real.exp (w / 2) * |cutoff ((X * Real.exp w - x) / H)| *
          (|outer' (w / 100)| / 100) := by
  unfold sourcePacketAmplitudeDeriv
  calc
    ‖((Real.exp (w / 2) / 2 : ℝ) : ℂ) *
          (cutoff ((X * Real.exp w - x) / H) : ℂ) *
            (outer (w / 100) : ℂ) +
        (Real.exp (w / 2) : ℂ) *
          ((cutoff' ((X * Real.exp w - x) / H) *
            (X * Real.exp w / H) : ℝ) : ℂ) *
            (outer (w / 100) : ℂ) +
        (Real.exp (w / 2) : ℂ) *
          (cutoff ((X * Real.exp w - x) / H) : ℂ) *
            ((outer' (w / 100) / 100 : ℝ) : ℂ)‖ ≤
      (‖((Real.exp (w / 2) / 2 : ℝ) : ℂ) *
          (cutoff ((X * Real.exp w - x) / H) : ℂ) *
            (outer (w / 100) : ℂ)‖ +
        ‖(Real.exp (w / 2) : ℂ) *
          ((cutoff' ((X * Real.exp w - x) / H) *
            (X * Real.exp w / H) : ℝ) : ℂ) *
            (outer (w / 100) : ℂ)‖) +
        ‖(Real.exp (w / 2) : ℂ) *
          (cutoff ((X * Real.exp w - x) / H) : ℂ) *
            ((outer' (w / 100) / 100 : ℝ) : ℂ)‖ := by
      refine (norm_add_le _ _).trans ?_
      gcongr
      exact norm_add_le _ _
    _ = _ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_div,
        abs_of_pos (Real.exp_pos _), abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (by norm_num : (0 : ℝ) < 100)]
      ring

/-- The exact amplitude-difference derivative retains the cutoff boundary
gain throughout the resonant cell. -/
theorem norm_sourceLowerCollarAmplitudeDifferenceDeriv_on_resonanceCell_le
    {X x q w B1 B2 Bout : ℝ}
    {cutoff cutoff' cutoff'' outer outer' : ℝ → ℝ}
    (hX : 0 < X) (hqPos : 0 < q)
    (hxLower : X / 2 ≤ x) (hwUpper : Real.exp w ≤ 2 * q)
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hcutoffSupport : ∀ z, 1 ≤ |z| → cutoff z = 0)
    (hcutoff'Support : ∀ z, 1 ≤ |z| → cutoff' z = 0)
    (hcutoffDeriv : ∀ z, HasDerivAt cutoff (cutoff' z) z)
    (hcutoffSecond : ∀ z, HasDerivAt cutoff' (cutoff'' z) z)
    (hcutoff'Bound : ∀ z, |cutoff' z| ≤ B1)
    (hcutoff''Bound : ∀ z, |cutoff'' z| ≤ B2)
    (houterBound : ∀ z, |outer z| ≤ 1)
    (houter'Bound : ∀ z, |outer' z| ≤ Bout) :
    ‖sourceLowerCollarAmplitudeDifferenceDeriv
        X (X / 2) x cutoff cutoff' outer outer' w‖ ≤
      Real.exp (w / 2) *
        (4 * B1 * q + 32 * B2 * q ^ 2 + B1 * Bout * q / 25) := by
  have hc := abs_cutoff_on_resonanceCell_le_four_mul_derivBound_mul_ratio
    hX hqPos hxLower hwUpper hB1 hcutoffSupport hcutoffDeriv hcutoff'Bound
  have hc' := abs_cutoff_on_resonanceCell_le_four_mul_derivBound_mul_ratio
    hX hqPos hxLower hwUpper hB2 hcutoff'Support hcutoffSecond hcutoff''Bound
  have hscale : |X * Real.exp w / (X / 2)| ≤ 4 * q := by
    rw [abs_of_nonneg (by positivity : 0 ≤ X * Real.exp w / (X / 2))]
    have hden : 0 < X / 2 := by positivity
    rw [div_le_iff₀ hden]
    nlinarith
  have hD0 := norm_sourcePacketAmplitudeDeriv_le_terms
    X (X / 2) x w cutoff cutoff' (fun _ ↦ 1) (fun _ ↦ 0)
  have hD1 := norm_sourcePacketAmplitudeDeriv_le_terms
    X (X / 2) x w cutoff cutoff' outer outer'
  have hD0' :
      ‖sourcePacketAmplitudeDeriv X (X / 2) x cutoff cutoff'
          (fun _ ↦ 1) (fun _ ↦ 0) w‖ ≤
        Real.exp (w / 2) * (2 * B1 * q + 16 * B2 * q ^ 2) := by
    calc
      _ ≤ Real.exp (w / 2) / 2 *
            |cutoff ((X * Real.exp w - x) / (X / 2))| * 1 +
          Real.exp (w / 2) *
            |cutoff' ((X * Real.exp w - x) / (X / 2))| *
              |X * Real.exp w / (X / 2)| * 1 +
          Real.exp (w / 2) *
            |cutoff ((X * Real.exp w - x) / (X / 2))| * (0 / 100) := by
        simpa using hD0
      _ ≤ Real.exp (w / 2) / 2 * (4 * B1 * q) * 1 +
          Real.exp (w / 2) * (4 * B2 * q) * (4 * q) * 1 +
          Real.exp (w / 2) * (4 * B1 * q) * (0 / 100) := by gcongr
      _ = Real.exp (w / 2) * (2 * B1 * q + 16 * B2 * q ^ 2) := by ring
  have hD1' :
      ‖sourcePacketAmplitudeDeriv X (X / 2) x cutoff cutoff' outer outer' w‖ ≤
        Real.exp (w / 2) *
          (2 * B1 * q + 16 * B2 * q ^ 2 + B1 * Bout * q / 25) := by
    calc
      _ ≤ Real.exp (w / 2) / 2 *
            |cutoff ((X * Real.exp w - x) / (X / 2))| *
              |outer (w / 100)| +
          Real.exp (w / 2) *
            |cutoff' ((X * Real.exp w - x) / (X / 2))| *
              |X * Real.exp w / (X / 2)| * |outer (w / 100)| +
          Real.exp (w / 2) *
            |cutoff ((X * Real.exp w - x) / (X / 2))| *
              (|outer' (w / 100)| / 100) := hD1
      _ ≤ Real.exp (w / 2) / 2 * (4 * B1 * q) * 1 +
          Real.exp (w / 2) * (4 * B2 * q) * (4 * q) * 1 +
          Real.exp (w / 2) * (4 * B1 * q) * (Bout / 100) := by
        gcongr
        · exact houterBound _
        · exact houterBound _
        · exact houter'Bound _
      _ = Real.exp (w / 2) *
          (2 * B1 * q + 16 * B2 * q ^ 2 + B1 * Bout * q / 25) := by ring
  unfold sourceLowerCollarAmplitudeDifferenceDeriv
  calc
    _ ≤ ‖sourcePacketAmplitudeDeriv X (X / 2) x cutoff cutoff'
          (fun _ ↦ 1) (fun _ ↦ 0) w‖ +
        ‖sourcePacketAmplitudeDeriv X (X / 2) x cutoff cutoff'
          outer outer' w‖ := norm_sub_le _ _
    _ ≤ Real.exp (w / 2) * (2 * B1 * q + 16 * B2 * q ^ 2) +
        Real.exp (w / 2) *
          (2 * B1 * q + 16 * B2 * q ^ 2 + B1 * Bout * q / 25) :=
      add_le_add hD0' hD1'
    _ = _ := by ring

/-- The full BV budget on the resonant cell, including the boundary gain for
both `cutoff` and `cutoff'`. -/
theorem integral_norm_sourceLowerCollarAmplitudeDifferenceDeriv_on_resonanceCell_le
    {X x q B1 B2 Bout : ℝ}
    {cutoff cutoff' cutoff'' outer outer' : ℝ → ℝ}
    (hX : 0 < X) (hqPos : 0 < q) (hxLower : X / 2 ≤ x)
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hcutoffSupport : ∀ z, 1 ≤ |z| → cutoff z = 0)
    (hcutoff'Support : ∀ z, 1 ≤ |z| → cutoff' z = 0)
    (hcutoffDeriv : ∀ z, HasDerivAt cutoff (cutoff' z) z)
    (hcutoffSecond : ∀ z, HasDerivAt cutoff' (cutoff'' z) z)
    (hcutoff'Bound : ∀ z, |cutoff' z| ≤ B1)
    (hcutoff''Bound : ∀ z, |cutoff'' z| ≤ B2)
    (houterBound : ∀ z, |outer z| ≤ 1)
    (houter'Bound : ∀ z, |outer' z| ≤ Bout) :
    let a := Real.log (q / 2)
    let b := Real.log (2 * q)
    (∫ w : ℝ in a..b,
      ‖sourceLowerCollarAmplitudeDifferenceDeriv
        X (X / 2) x cutoff cutoff' outer outer' w‖) ≤
      (b - a) * Real.exp (b / 2) *
        (4 * B1 * q + 32 * B2 * q ^ 2 + B1 * Bout * q / 25) := by
  dsimp
  let a : ℝ := Real.log (q / 2)
  let b : ℝ := Real.log (2 * q)
  let C : ℝ := Real.exp (b / 2) *
    (4 * B1 * q + 32 * B2 * q ^ 2 + B1 * Bout * q / 25)
  have hqHalf : 0 < q / 2 := by positivity
  have htwoq : 0 < 2 * q := by positivity
  have hab : a ≤ b := by
    unfold a b
    exact Real.log_le_log hqHalf (by linarith)
  have hexpb : Real.exp b = 2 * q := by
    unfold b
    exact Real.exp_log htwoq
  have hC : 0 ≤ C := by
    unfold C
    have hBoutNonneg : 0 ≤ Bout :=
      (abs_nonneg (outer' 0)).trans (houter'Bound 0)
    positivity
  have hpoint : ∀ w ∈ Set.Icc a b,
      ‖sourceLowerCollarAmplitudeDifferenceDeriv
        X (X / 2) x cutoff cutoff' outer outer' w‖ ≤ C := by
    intro w hw
    have hwUpper : Real.exp w ≤ 2 * q := by
      rw [← hexpb]
      exact Real.exp_le_exp.mpr hw.2
    have hd :=
      norm_sourceLowerCollarAmplitudeDifferenceDeriv_on_resonanceCell_le
        hX hqPos hxLower hwUpper hB1 hB2 hcutoffSupport hcutoff'Support
        hcutoffDeriv hcutoffSecond hcutoff'Bound hcutoff''Bound
        houterBound houter'Bound
    have he : Real.exp (w / 2) ≤ Real.exp (b / 2) :=
      Real.exp_le_exp.mpr (by linarith [hw.2])
    unfold C
    exact hd.trans (mul_le_mul_of_nonneg_right he (by
      have hBoutNonneg : 0 ≤ Bout :=
        (abs_nonneg (outer' 0)).trans (houter'Bound 0)
      positivity))
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (C := C) (f := fun w : ℝ ↦
      ‖sourceLowerCollarAmplitudeDifferenceDeriv
        X (X / 2) x cutoff cutoff' outer outer' w‖) (by
      intro w hw
      have hw' : w ∈ Set.uIcc a b := Set.uIoc_subset_uIcc hw
      simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
        hpoint w (by simpa [Set.uIcc_of_le hab] using hw'))
  have hnonneg : 0 ≤ ∫ w : ℝ in a..b,
      ‖sourceLowerCollarAmplitudeDifferenceDeriv
        X (X / 2) x cutoff cutoff' outer outer' w‖ :=
    intervalIntegral.integral_nonneg hab (fun w _ ↦ norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hnorm
  have habs : |b - a| = b - a := abs_of_nonneg (sub_nonneg.mpr hab)
  rw [habs] at hnorm
  unfold C at hnorm
  calc
    _ ≤ Real.exp (b / 2) *
        (4 * B1 * q + 32 * B2 * q ^ 2 + B1 * Bout * q / 25) *
          (b - a) := hnorm
    _ = _ := by ring

/-- The resonant interval in logarithmic coordinates. -/
def lowerCollarResonanceInterval (q : ℝ) : Set ℝ :=
  Set.Icc (Real.log (q / 2)) (Real.log (2 * q))

/-- Weighted second-derivative van der Corput on the exact resonant cell.  The
remaining integral is the literal BV budget of the proved amplitude derivative,
not an external estimate. -/
theorem norm_integral_sourceLowerCollarAmplitudeDifference_on_resonanceCell_le
    {X x beta t B : ℝ} {cutoff cutoff' outer outer' : ℝ → ℝ}
    (hX : 0 < X) (hbeta : beta ≠ 0)
    (hqPos : 0 < lowerCollarResonanceRatio X beta t)
    (hxLower : X / 2 ≤ x) (hB : 0 ≤ B)
    (hcutoffSupport : ∀ z, 1 ≤ |z| → cutoff z = 0)
    (hcutoffDeriv : ∀ z, HasDerivAt cutoff (cutoff' z) z)
    (hcutoff'Bound : ∀ z, |cutoff' z| ≤ B)
    (houterDeriv : ∀ z, HasDerivAt outer (outer' z) z)
    (houterBound : ∀ z, |outer z| ≤ 1)
    (hcutoff'Cont : Continuous cutoff')
    (houter'Cont : Continuous outer') :
    let q := lowerCollarResonanceRatio X beta t
    let a := Real.log (q / 2)
    let b := Real.log (2 * q)
    let M := 8 * B * q * Real.exp (b / 2)
    let m := Real.sqrt (|beta| * X * (q / 2))
    ‖∫ w : ℝ in a..b,
        additivePhase (stationaryPacketPhase X beta t w) *
          sourceLowerCollarAmplitudeDifference
            X (X / 2) x cutoff outer w‖ ≤
      10 * (M + ∫ w : ℝ in a..b,
        ‖sourceLowerCollarAmplitudeDifferenceDeriv
          X (X / 2) x cutoff cutoff' outer outer' w‖) / m := by
  dsimp
  let q : ℝ := lowerCollarResonanceRatio X beta t
  let a : ℝ := Real.log (q / 2)
  let b : ℝ := Real.log (2 * q)
  let M : ℝ := 8 * B * q * Real.exp (b / 2)
  let m : ℝ := Real.sqrt (|beta| * X * (q / 2))
  have hq : 0 < q := hqPos
  have hqHalf : 0 < q / 2 := by positivity
  have htwoq : 0 < 2 * q := by positivity
  have hab : a ≤ b := by
    unfold a b
    exact Real.log_le_log hqHalf (by linarith)
  have hlambda : 0 < |beta| * X * (q / 2) := by
    have hbabs : 0 < |beta| := abs_pos.mpr hbeta
    positivity
  have hm : 0 < m := by unfold m; positivity
  have hM : 0 ≤ M := by unfold M; positivity
  have hexpa : Real.exp a = q / 2 := by
    unfold a
    exact Real.exp_log hqHalf
  have hexpb : Real.exp b = 2 * q := by
    unfold b
    exact Real.exp_log htwoq
  have hphase : ∀ w ∈ Set.Icc a b,
      HasDerivAt (stationaryPacketPhase X beta t)
        (beta * X * Real.exp w + t / (2 * Real.pi)) w := by
    intro w _
    exact hasDerivAt_stationaryPacketPhase X beta t w
  have hphase' : ∀ w ∈ Set.Icc a b,
      HasDerivAt (fun z ↦ beta * X * Real.exp z + t / (2 * Real.pi))
        (beta * X * Real.exp w) w := by
    intro w _
    exact hasDerivAt_stationaryPacketPhase_deriv X beta t w
  have hcurvature : ∀ w ∈ Set.Icc a b,
      m ^ 2 ≤ |beta * X * Real.exp w| := by
    intro w hw
    have hwexp : q / 2 ≤ Real.exp w := by
      rw [← hexpa]
      exact Real.exp_le_exp.mpr hw.1
    have hbase := stationaryPacketPhase_secondDeriv_lower_on_resonanceCell
      hX hwexp
    unfold m
    rw [Real.sq_sqrt hlambda.le]
    exact hbase
  have hsign :
      (∀ w ∈ Set.Icc a b, 0 ≤ beta * X * Real.exp w) ∨
        (∀ w ∈ Set.Icc a b, beta * X * Real.exp w ≤ 0) := by
    rcases le_total 0 beta with hbetaPos | hbetaNeg
    · left
      intro w _
      positivity
    · right
      intro w _
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hbetaNeg hX.le)
        (Real.exp_pos w).le
  have hamp : ∀ w ∈ Set.Icc a b,
      HasDerivAt (sourceLowerCollarAmplitudeDifference
        X (X / 2) x cutoff outer)
        (sourceLowerCollarAmplitudeDifferenceDeriv
          X (X / 2) x cutoff cutoff' outer outer' w) w := by
    intro w _
    exact hasDerivAt_sourceLowerCollarAmplitudeDifference
      hcutoffDeriv houterDeriv
  have hphase''Cont : ContinuousOn (fun w ↦ beta * X * Real.exp w)
      (Set.Icc a b) := by fun_prop
  have hcutoffCont : Continuous cutoff :=
    continuous_iff_continuousAt.mpr (fun z ↦ (hcutoffDeriv z).continuousAt)
  have houterCont : Continuous outer :=
    continuous_iff_continuousAt.mpr (fun z ↦ (houterDeriv z).continuousAt)
  have hamp'Cont : ContinuousOn
      (sourceLowerCollarAmplitudeDifferenceDeriv
        X (X / 2) x cutoff cutoff' outer outer') (Set.Icc a b) := by
    apply Continuous.continuousOn
    unfold sourceLowerCollarAmplitudeDifferenceDeriv sourcePacketAmplitudeDeriv
    fun_prop
  have hampBound : ∀ w ∈ Set.Icc a b,
      ‖sourceLowerCollarAmplitudeDifference X (X / 2) x cutoff outer w‖ ≤ M := by
    intro w hw
    have hwUpper : Real.exp w ≤ 2 * q := by
      rw [← hexpb]
      exact Real.exp_le_exp.mpr hw.2
    have hpoint := norm_sourcePacketAmplitude_difference_on_resonanceCell_le
      hX hq hxLower hwUpper hB hcutoffSupport hcutoffDeriv
      hcutoff'Bound houterBound
    have hexpHalf : Real.exp (w / 2) ≤ Real.exp (b / 2) := by
      exact Real.exp_le_exp.mpr (by linarith [hw.2])
    unfold M
    exact hpoint.trans (mul_le_mul_of_nonneg_left hexpHalf (by positivity))
  exact weightedSecondDerivativeVanDerCorputC1
    hab hm hM hphase hphase' hcurvature hsign hamp
    hphase''Cont hamp'Cont hampBound

/-- Resonant-cell van der Corput with the manuscript amplitude BV calculation
fully discharged for the packet difference. -/
theorem norm_integral_sourceLowerCollarAmplitudeDifference_on_resonanceCell_bv_le
    {X x beta t B1 B2 Bout : ℝ}
    {cutoff cutoff' cutoff'' outer outer' : ℝ → ℝ}
    (hX : 0 < X) (hbeta : beta ≠ 0)
    (hqPos : 0 < lowerCollarResonanceRatio X beta t)
    (hxLower : X / 2 ≤ x)
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hcutoffSupport : ∀ z, 1 ≤ |z| → cutoff z = 0)
    (hcutoff'Support : ∀ z, 1 ≤ |z| → cutoff' z = 0)
    (hcutoffDeriv : ∀ z, HasDerivAt cutoff (cutoff' z) z)
    (hcutoffSecond : ∀ z, HasDerivAt cutoff' (cutoff'' z) z)
    (hcutoff'Bound : ∀ z, |cutoff' z| ≤ B1)
    (hcutoff''Bound : ∀ z, |cutoff'' z| ≤ B2)
    (houterDeriv : ∀ z, HasDerivAt outer (outer' z) z)
    (houterBound : ∀ z, |outer z| ≤ 1)
    (houter'Bound : ∀ z, |outer' z| ≤ Bout)
    (houter'Cont : Continuous outer') :
    let q := lowerCollarResonanceRatio X beta t
    let a := Real.log (q / 2)
    let b := Real.log (2 * q)
    let M := 8 * B1 * q * Real.exp (b / 2)
    let Cbv := Real.exp (b / 2) *
      (4 * B1 * q + 32 * B2 * q ^ 2 + B1 * Bout * q / 25)
    let m := Real.sqrt (|beta| * X * (q / 2))
    ‖∫ w : ℝ in a..b,
        additivePhase (stationaryPacketPhase X beta t w) *
          sourceLowerCollarAmplitudeDifference
            X (X / 2) x cutoff outer w‖ ≤
      10 * (M + (b - a) * Cbv) / m := by
  dsimp
  let q : ℝ := lowerCollarResonanceRatio X beta t
  let a : ℝ := Real.log (q / 2)
  let b : ℝ := Real.log (2 * q)
  let M : ℝ := 8 * B1 * q * Real.exp (b / 2)
  let Cbv : ℝ := Real.exp (b / 2) *
    (4 * B1 * q + 32 * B2 * q ^ 2 + B1 * Bout * q / 25)
  let m : ℝ := Real.sqrt (|beta| * X * (q / 2))
  have hq : 0 < q := hqPos
  have hcutoff'Cont : Continuous cutoff' :=
    continuous_iff_continuousAt.mpr (fun z ↦ (hcutoffSecond z).continuousAt)
  have hvdc :=
    norm_integral_sourceLowerCollarAmplitudeDifference_on_resonanceCell_le
      (X := X) (x := x) (beta := beta) (t := t) (B := B1)
      hX hbeta hqPos hxLower hB1 hcutoffSupport hcutoffDeriv
      hcutoff'Bound houterDeriv houterBound hcutoff'Cont houter'Cont
  have hbv :=
    integral_norm_sourceLowerCollarAmplitudeDifferenceDeriv_on_resonanceCell_le
      (X := X) (x := x) (q := q) (B1 := B1) (B2 := B2) (Bout := Bout)
      hX hq hxLower hB1 hB2 hcutoffSupport hcutoff'Support
      hcutoffDeriv hcutoffSecond hcutoff'Bound hcutoff''Bound
      houterBound houter'Bound
  have hm : 0 < m := by
    unfold m q
    have hbabs : 0 < |beta| := abs_pos.mpr hbeta
    positivity
  change ‖∫ w : ℝ in a..b,
      additivePhase (stationaryPacketPhase X beta t w) *
        sourceLowerCollarAmplitudeDifference X (X / 2) x cutoff outer w‖ ≤
    10 * (M + (b - a) * Cbv) / m
  have hvdc' :
      ‖∫ w : ℝ in a..b,
          additivePhase (stationaryPacketPhase X beta t w) *
            sourceLowerCollarAmplitudeDifference X (X / 2) x cutoff outer w‖ ≤
        10 * (M + ∫ w : ℝ in a..b,
          ‖sourceLowerCollarAmplitudeDifferenceDeriv
            X (X / 2) x cutoff cutoff' outer outer' w‖) / m := by
    simpa [q, a, b, M, m] using hvdc
  have hbv' :
      (∫ w : ℝ in a..b,
        ‖sourceLowerCollarAmplitudeDifferenceDeriv
          X (X / 2) x cutoff cutoff' outer outer' w‖) ≤
        (b - a) * Cbv := by
    simpa [q, a, b, Cbv, mul_assoc] using hbv
  refine hvdc'.trans ?_
  apply div_le_div_of_nonneg_right _ hm.le
  gcongr

/-- The resonant-cell part of the lower-collar packet difference. -/
def sourceLowerCollarResonantPacket
    (X beta t : ℝ) (cutoff outer : ℝ → ℝ) (x : ℝ) : ℂ :=
  let q := lowerCollarResonanceRatio X beta t
  ∫ w : ℝ in Real.log (q / 2)..Real.log (2 * q),
    additivePhase (stationaryPacketPhase X beta t w) *
      sourceLowerCollarAmplitudeDifference X (X / 2) x cutoff outer w

/-- The resonant packet depends continuously on the spatial parameter. -/
theorem continuous_sourceLowerCollarResonantPacket
    {X beta t : ℝ} {cutoff outer : ℝ → ℝ}
    (hcutoff : Continuous cutoff) (houter : Continuous outer) :
    Continuous (sourceLowerCollarResonantPacket X beta t cutoff outer) := by
  unfold sourceLowerCollarResonantPacket
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold sourceLowerCollarAmplitudeDifference sourcePacketAmplitude
  have hadd : Continuous additivePhase :=
    continuous_iff_continuousAt.mpr (fun z ↦
      (hasDerivAt_additivePhase z).continuousAt)
  have hphase : Continuous (stationaryPacketPhase X beta t) :=
    continuous_iff_continuousAt.mpr (fun w ↦
      (hasDerivAt_stationaryPacketPhase X beta t w).continuousAt)
  exact (hadd.comp (hphase.comp continuous_snd)).mul (by fun_prop)

/-- The literal finite-width resonant-cell energy estimate.  Its spatial
width is `2*q*X`; no whole-line or sharp-boundary simplification is used. -/
theorem integral_norm_sq_sourceLowerCollarResonantPacket_on_endpointWindow_le
    {X beta t B1 B2 Bout : ℝ}
    {cutoff cutoff' cutoff'' outer outer' : ℝ → ℝ}
    (hX : 0 < X) (hbeta : beta ≠ 0)
    (hqPos : 0 < lowerCollarResonanceRatio X beta t)
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hcutoffSupport : ∀ z, 1 ≤ |z| → cutoff z = 0)
    (hcutoff'Support : ∀ z, 1 ≤ |z| → cutoff' z = 0)
    (hcutoffDeriv : ∀ z, HasDerivAt cutoff (cutoff' z) z)
    (hcutoffSecond : ∀ z, HasDerivAt cutoff' (cutoff'' z) z)
    (hcutoff'Bound : ∀ z, |cutoff' z| ≤ B1)
    (hcutoff''Bound : ∀ z, |cutoff'' z| ≤ B2)
    (houterDeriv : ∀ z, HasDerivAt outer (outer' z) z)
    (houterBound : ∀ z, |outer z| ≤ 1)
    (houter'Bound : ∀ z, |outer' z| ≤ Bout)
    (houter'Cont : Continuous outer') :
    let q := lowerCollarResonanceRatio X beta t
    let a := Real.log (q / 2)
    let b := Real.log (2 * q)
    let K := 10 *
      (8 * B1 * q * Real.exp (b / 2) +
        (b - a) * (Real.exp (b / 2) *
          (4 * B1 * q + 32 * B2 * q ^ 2 + B1 * Bout * q / 25))) /
        Real.sqrt (|beta| * X * (q / 2))
    (∫ x in Set.Ico (X / 2) (X / 2 + 2 * q * X),
      ‖sourceLowerCollarResonantPacket X beta t cutoff outer x‖ ^ 2) ≤
        2 * q * X * K ^ 2 := by
  dsimp
  let q : ℝ := lowerCollarResonanceRatio X beta t
  let a : ℝ := Real.log (q / 2)
  let b : ℝ := Real.log (2 * q)
  let K : ℝ := 10 *
    (8 * B1 * q * Real.exp (b / 2) +
      (b - a) * (Real.exp (b / 2) *
        (4 * B1 * q + 32 * B2 * q ^ 2 + B1 * Bout * q / 25))) /
      Real.sqrt (|beta| * X * (q / 2))
  have hq : 0 < q := hqPos
  have hcutoffCont : Continuous cutoff :=
    continuous_iff_continuousAt.mpr (fun z ↦ (hcutoffDeriv z).continuousAt)
  have houterCont : Continuous outer :=
    continuous_iff_continuousAt.mpr (fun z ↦ (houterDeriv z).continuousAt)
  have hpacketCont : Continuous
      (sourceLowerCollarResonantPacket X beta t cutoff outer) :=
    continuous_sourceLowerCollarResonantPacket hcutoffCont houterCont
  have henergyInt : IntegrableOn
      (fun x : ℝ ↦
        ‖sourceLowerCollarResonantPacket X beta t cutoff outer x‖ ^ 2)
      (Set.Ico (X / 2) (X / 2 + 2 * q * X)) := by
    have hIcc : IntegrableOn
        (fun x : ℝ ↦
          ‖sourceLowerCollarResonantPacket X beta t cutoff outer x‖ ^ 2)
        (Set.Icc (X / 2) (X / 2 + 2 * q * X)) :=
      (hpacketCont.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hIcc.mono_set Set.Ico_subset_Icc_self
  have hKnonneg : 0 ≤ K := by
    unfold K a b
    have hBoutNonneg : 0 ≤ Bout :=
      (abs_nonneg (outer' 0)).trans (houter'Bound 0)
    have hlog : Real.log (q / 2) ≤ Real.log (2 * q) :=
      Real.log_le_log (by positivity) (by linarith)
    positivity
  have hpoint : ∀ x ∈ Set.Ico (X / 2) (X / 2 + 2 * q * X),
      ‖sourceLowerCollarResonantPacket X beta t cutoff outer x‖ ^ 2 ≤ K ^ 2 := by
    intro x hx
    have hvdc :=
      norm_integral_sourceLowerCollarAmplitudeDifference_on_resonanceCell_bv_le
        (X := X) (x := x) (beta := beta) (t := t)
        (B1 := B1) (B2 := B2) (Bout := Bout)
        hX hbeta hqPos hx.1 hB1 hB2 hcutoffSupport hcutoff'Support
        hcutoffDeriv hcutoffSecond hcutoff'Bound hcutoff''Bound
        houterDeriv houterBound houter'Bound houter'Cont
    have hvdc' :
        ‖sourceLowerCollarResonantPacket X beta t cutoff outer x‖ ≤ K := by
      simpa [sourceLowerCollarResonantPacket, q, a, b, K] using hvdc
    exact pow_le_pow_left₀ (norm_nonneg _) hvdc' 2
  calc
    (∫ x in Set.Ico (X / 2) (X / 2 + 2 * q * X),
        ‖sourceLowerCollarResonantPacket X beta t cutoff outer x‖ ^ 2) ≤
        ∫ _x in Set.Ico (X / 2) (X / 2 + 2 * q * X), K ^ 2 := by
      apply MeasureTheory.integral_mono_ae henergyInt
        (MeasureTheory.integrableOn_const (by
          rw [Real.volume_Ico]
          exact ENNReal.ofReal_ne_top))
      filter_upwards [self_mem_ae_restrict measurableSet_Ico] with x hx
      exact hpoint x hx
    _ = 2 * q * X * K ^ 2 := by
      rw [MeasureTheory.setIntegral_const]
      simp only [Measure.real, Real.volume_Ico]
      rw [ENNReal.toReal_ofReal (by nlinarith [mul_pos hq hX])]
      simp [smul_eq_mul]

end

end MAPMRTSourceLowerCollarVdC

#print axioms MAPMRTSourceLowerCollarVdC.hasDerivAt_sourceLowerCollarAmplitudeDifference
#print axioms MAPMRTSourceLowerCollarVdC.norm_sourcePacketAmplitudeDeriv_le_terms
#print axioms MAPMRTSourceLowerCollarVdC.norm_sourceLowerCollarAmplitudeDifferenceDeriv_on_resonanceCell_le
#print axioms MAPMRTSourceLowerCollarVdC.integral_norm_sourceLowerCollarAmplitudeDifferenceDeriv_on_resonanceCell_le
#print axioms MAPMRTSourceLowerCollarVdC.norm_integral_sourceLowerCollarAmplitudeDifference_on_resonanceCell_le
#print axioms MAPMRTSourceLowerCollarVdC.norm_integral_sourceLowerCollarAmplitudeDifference_on_resonanceCell_bv_le
#print axioms MAPMRTSourceLowerCollarVdC.continuous_sourceLowerCollarResonantPacket
#print axioms MAPMRTSourceLowerCollarVdC.integral_norm_sq_sourceLowerCollarResonantPacket_on_endpointWindow_le
