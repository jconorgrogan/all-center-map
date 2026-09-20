import MRTWholeLineHighCellEquation84
import MRTWholeLinePacketTrivialBound
import MRTWholeLineVanDerCorput
import MRTPacketEnergy

/-!
# Source-faithful whole-line MRT equation (83)

After MRT's legal pre-Cauchy extension the packet is integrated over the whole
`x` line.  This proof splits only at `x = 4H`.  The low cell has literal length
at most `5H`; the high cell uses recentered equation (84).  No artificial
`[X/2,4X]` indicator and no frequency-band hypothesis are introduced.
-/

namespace MAPMRTWholeLinePacketEquation83

set_option maxHeartbeats 800000

open MeasureTheory Set
open MAPMRTCorollary53Source MAPMRTProposition51HardBranch
open MAPMRTWholeLinePacketMemLp MAPMRTWholeLinePacketTrivialBound
open MAPMRTWholeLineVanDerCorput MAPMRTWholeLineHighCellEquation84
open MAPMRTPacketEnergy

noncomputable section

/-- The packet vanishes on the whole left half-line `x ≤ -H`. -/
theorem sourceStationaryPacket_eq_zero_of_le_neg_H
    {X H x beta t : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hx : x ≤ -H) :
    sourceStationaryPacket X H x beta t cutoff outer = 0 := by
  unfold sourceStationaryPacket
  rw [show (∫ w : ℝ,
      additivePhase (stationaryPacketPhase X beta t w) *
        sourcePacketAmplitude X H x cutoff outer w) =
      ∫ _w : ℝ, (0 : ℂ) by
    apply integral_congr_ae
    filter_upwards with w
    have hnum : H ≤ X * Real.exp w - x := by
      have hc : 0 < X * Real.exp w := mul_pos hX (Real.exp_pos w)
      linarith
    have hq : 1 ≤ (X * Real.exp w - x) / H := by
      rw [le_div_iff₀ hH]
      simpa only [one_mul] using hnum
    have habs : 1 ≤ |(X * Real.exp w - x) / H| :=
      hq.trans_eq (abs_of_nonneg (by linarith)).symm
    rw [show sourcePacketAmplitude X H x cutoff outer w = 0 by
      unfold sourcePacketAmplitude
      rw [hcutoffSupport _ habs]
      simp]
    simp]
  simp

/-- A nonnegative integrable function supported in `(-H,4H)` has at most its
pointwise square budget times the literal length `5H`. -/
private theorem integral_Iio_fourH_le_five_mul
    {H M : ℝ} {f : ℝ → ℝ}
    (hH : 0 < H) (hf : Integrable f)
    (hzero : ∀ x, x ≤ -H → f x = 0)
    (hbound : ∀ x, f x ≤ M ^ 2) :
    (∫ x : ℝ in Set.Iio (4 * H), f x) ≤ 5 * H * M ^ 2 := by
  have hind : Set.indicator (Set.Iio (4 * H)) f =
      Set.indicator (Set.Ioo (-H) (4 * H)) f := by
    funext x
    by_cases hx : x ∈ Set.Ioo (-H) (4 * H)
    · have hi : x ∈ Set.Iio (4 * H) := hx.2
      simp [hi, hx]
    · by_cases hi : x ∈ Set.Iio (4 * H)
      · have hxle : x ≤ -H := by
          by_contra hn
          exact hx ⟨lt_of_not_ge hn, hi⟩
        simp [hi, hx, hzero x hxle]
      · simp [hi, hx]
  rw [← integral_indicator measurableSet_Iio, hind,
    integral_indicator measurableSet_Ioo]
  have hmono : (∫ x : ℝ in Set.Ioo (-H) (4 * H), f x) ≤
      ∫ _x : ℝ in Set.Ioo (-H) (4 * H), M ^ 2 := by
    exact integral_mono hf.integrableOn
      (integrableOn_const (by simp [Real.volume_Ioo])) (fun x ↦ hbound x)
  refine hmono.trans_eq ?_
  rw [setIntegral_const]
  have hvol : volume.real (Set.Ioo (-H) (4 * H)) = 5 * H := by
    rw [Measure.real_def, Real.volume_Ioo, ENNReal.toReal_ofReal]
    · ring
    · linarith
  rw [hvol]
  simp only [smul_eq_mul]

/-- Fixed whole-line equation-(83) coefficient. -/
def wholeLineEquation83Constant
    (D0 D1 D2 Dout B1 B2 : ℝ) : ℝ :=
  let E := Real.exp (-100)
  let K := (4 / 3 : ℝ) * Real.exp 100
  let C0 := Real.exp 50 * D0
  let Cv := 10 * Real.exp 50 * (101 + D1 + Dout)
  let Ch := 4 * Real.exp 200 * highCellEquation84BaseConstant D1 D2 B1 B2
  16 * Real.pi * (Cv + Ch) ^ 2 / E + 5 * Cv ^ 2 / E +
    16 * Real.pi * K * (C0 + Ch) ^ 2 + 5 * K * C0 ^ 2

/-- MRT equation (83) for the unrestricted packet occurring after the
source's whole-line extension. -/
theorem source_packet_energy_equation83_wholeLine
    {X H beta eta t D0 D1 D2 Dout B1 B2 : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hH : 1 ≤ H) (hHalf : H ≤ X / 2)
    (hhard : 1 < |beta| * H)
    (hetaPos : 0 < eta) (hetaHard : eta < 1 / 100)
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
      wholeLineEquation83Constant D0 D1 D2 Dout B1 B2 *
        H / (|beta| * X) := by
  let q : ℝ := |beta|
  let E : ℝ := Real.exp (-100)
  let K : ℝ := (4 / 3 : ℝ) * Real.exp 100
  let C0 : ℝ := Real.exp 50 * D0
  let Cv : ℝ := 10 * Real.exp 50 * (101 + D1 + Dout)
  let Ch : ℝ := 4 * Real.exp 200 * highCellEquation84BaseConstant D1 D2 B1 B2
  let C83 : ℝ := 16 * Real.pi * (Cv + Ch) ^ 2 / E + 5 * Cv ^ 2 / E +
    16 * Real.pi * K * (C0 + Ch) ^ 2 + 5 * K * C0 ^ 2
  let J : ℝ → ℂ := fun x ↦ sourceStationaryPacket X H x beta t cutoff outer
  let Jhi : ℝ → ℂ := fun x ↦ Set.indicator (Set.Ici (4 * H)) J x
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hX : 0 < X := by linarith
  have hbeta : beta ≠ 0 := by
    intro hb
    subst beta
    norm_num at hhard
  have hq : 0 < q := by exact abs_pos.mpr hbeta
  have hE : 0 < E := by unfold E; positivity
  have hEle : E ≤ 1 := by
    unfold E
    simpa using Real.exp_le_one_iff.mpr (by norm_num : (-100 : ℝ) ≤ 0)
  have hK : 1 ≤ K := by
    unfold K
    have he : 1 ≤ Real.exp 100 := Real.one_le_exp (by norm_num)
    nlinarith
  have hD0n : 0 ≤ D0 :=
    (integral_nonneg (fun y ↦ abs_nonneg (cutoff y))).trans hD0
  have hD1n : 0 ≤ D1 :=
    (integral_nonneg (fun y ↦ abs_nonneg (cutoff' y))).trans hD1
  have hD2n : 0 ≤ D2 :=
    (integral_nonneg (fun y ↦ abs_nonneg (cutoff'' y))).trans hD2
  have hDoutn : 0 ≤ Dout :=
    (integral_nonneg (fun y ↦ abs_nonneg (outer' y))).trans hDout
  have hB1n : 0 ≤ B1 := (abs_nonneg (outer' 0)).trans (houter'Bound 0)
  have hB2n : 0 ≤ B2 := (abs_nonneg (outer'' 0)).trans (houter''Bound 0)
  have hC0 : 0 ≤ C0 := by unfold C0; positivity
  have hCv : 0 ≤ Cv := by unfold Cv; positivity
  have hCh : 0 ≤ Ch := by
    unfold Ch highCellEquation84BaseConstant
    positivity
  have hcutoffCont : Continuous cutoff :=
    continuous_iff_continuousAt.mpr (fun y ↦ (hcutoffDeriv y).continuousAt)
  have houterCont : Continuous outer :=
    continuous_iff_continuousAt.mpr (fun y ↦ (houterDeriv y).continuousAt)
  have hcutoff'Cont : Continuous cutoff' :=
    continuous_iff_continuousAt.mpr (fun y ↦ (hcutoffSecond y).continuousAt)
  have houter'Cont : Continuous outer' :=
    continuous_iff_continuousAt.mpr (fun y ↦ (houterSecond y).continuousAt)
  have hJInt : Integrable (fun x ↦ ‖J x‖ ^ 2) := by
    exact integrable_norm_sourceStationaryPacket_sq hX hHpos hcutoffCont
      houterCont hcutoffSupport houterSupport
  have hJhiInt : Integrable (fun x ↦ ‖Jhi x‖ ^ 2) := by
    have hi := hJInt.indicator (s := Set.Ici (4 * H)) measurableSet_Ici
    apply hi.congr
    filter_upwards with x
    by_cases hx : x ∈ Set.Ici (4 * H) <;> simp [Jhi, J, hx]
  have hhighSetEq : (∫ x : ℝ, ‖Jhi x‖ ^ 2) =
      ∫ x : ℝ in Set.Ici (4 * H), ‖J x‖ ^ 2 := by
    rw [← integral_indicator measurableSet_Ici]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Set.Ici (4 * H) <;> simp [Jhi, hx]
  have htrivial : ∀ x, ‖J x‖ ≤ C0 * H / X := by
    intro x
    have ht := norm_sourceStationaryPacket_le_trivial_wholeLine
      (X := X) (H := H) (x := x) (beta := beta) (t := t) (D0 := D0)
      hX hHpos hcutoffCont houterCont hcutoffInt hD0
      houterSupport houterBound
    simpa [J, C0] using ht
  have hvdc : ∀ x, ‖J x‖ ≤ Cv /
      Real.sqrt (q * X * E) := by
    intro x
    have hv := norm_sourceStationaryPacket_le_wholeLine_vdc
      (X := X) (H := H) (x := x) (beta := beta) (eta := eta) (t := t)
      (Dcut := D1) (Dout := Dout) hH hHalf hhard hetaPos hetaHard
      houterSupport hcutoffBound houterBound hcutoffDeriv houterDeriv
      hcutoff'Cont houter'Cont hcutoff'Int houter'Int hD1 hDout
    simpa [J, Cv, q, E] using hv
  have hfar : ∀ x, 4 * max (q * H) (K * (X / H)) ≤
      |t / (2 * Real.pi) + beta * x| →
      ‖Jhi x‖ ≤ Ch * (X / H) /
        |t / (2 * Real.pi) + beta * x| ^ 2 := by
    intro x hcenter
    by_cases hx : x ∈ Set.Ici (4 * H)
    · simp only [Jhi, Set.indicator_of_mem hx]
      have hh := norm_sourceStationaryPacket_equation84_highCell
        (X := X) (H := H) (x := x) (beta := beta) (t := t)
        (D1 := D1) (D2 := D2) (B1 := B1) (B2 := B2)
        (cutoff := cutoff) (cutoff' := cutoff') (cutoff'' := cutoff'')
        (outer := outer) (outer' := outer') (outer'' := outer'')
        hX hHpos hx hcenter hcutoffSupport hcutoff'Support houterSupport
        hcutoffBound houterBound houter'Bound houter''Bound
        hcutoffDeriv hcutoffSecond houterDeriv houterSecond
        hcutoff''Cont houter''Cont hcutoff'Int hcutoff''Int hD1 hD2
      simpa [J, Ch, K] using hh
    · simp [Jhi, hx]
      positivity
  have hlowLarge : K * X ≤ q * H ^ 2 →
      (∫ x : ℝ in Set.Iio (4 * H), ‖J x‖ ^ 2) ≤
        (5 * Cv ^ 2 / E) * H / (q * X) := by
    intro hlarge
    let s : ℝ := Real.sqrt (q * X * E)
    have hs : 0 < s := by unfold s; positivity
    have hsSq : s ^ 2 = q * X * E := by
      unfold s
      exact Real.sq_sqrt (by positivity)
    have hlow := integral_Iio_fourH_le_five_mul hHpos hJInt
      (fun x hx ↦ by
        have hz := sourceStationaryPacket_eq_zero_of_le_neg_H
          (X := X) (beta := beta) (t := t) (cutoff := cutoff) (outer := outer)
          hX hHpos hcutoffSupport hx
        simp [J, hz])
      (fun x ↦ by
        have hx := hvdc x
        exact pow_le_pow_left₀ (norm_nonneg _) hx 2)
    refine hlow.trans_eq ?_
    rw [show (Cv / Real.sqrt (q * X * E)) = Cv / s by rfl]
    field_simp [hq.ne', hX.ne', hE.ne', hs.ne']
    rw [hsSq]
    ring
  have hlowSmall : q * H ^ 2 < K * X →
      (∫ x : ℝ in Set.Iio (4 * H), ‖J x‖ ^ 2) ≤
        (5 * K * C0 ^ 2) * H / (q * X) := by
    intro hsmall
    have hlow := integral_Iio_fourH_le_five_mul hHpos hJInt
      (fun x hx ↦ by
        have hz := sourceStationaryPacket_eq_zero_of_le_neg_H
          (X := X) (beta := beta) (t := t) (cutoff := cutoff) (outer := outer)
          hX hHpos hcutoffSupport hx
        simp [J, hz])
      (fun x ↦ pow_le_pow_left₀ (norm_nonneg _) (htrivial x) 2)
    refine hlow.trans ?_
    have hn : 0 ≤ 5 * C0 ^ 2 * H := by positivity
    field_simp [hq.ne', hX.ne']
    nlinarith [mul_lt_mul_of_pos_left hsmall (mul_pos (sq_pos_of_pos hHpos) hq)]
  have hsplit := integral_add_compl (s := Set.Ici (4 * H))
    measurableSet_Ici hJInt
  rw [Set.compl_Ici] at hsplit
  change (∫ x : ℝ, ‖J x‖ ^ 2) ≤ C83 * H / (q * X)
  rw [← hsplit]
  by_cases hlarge : K * X ≤ q * H ^ 2
  · have hRcmp : K * (X / H) ≤ q * H := by
      calc
        K * (X / H) = (K * X) / H := by ring
        _ ≤ (q * H ^ 2) / H := div_le_div_of_nonneg_right hlarge hHpos.le
        _ = q * H := by field_simp [hHpos.ne']
    have hmax : max (q * H) (K * (X / H)) = q * H := max_eq_left hRcmp
    let s : ℝ := Real.sqrt (q * X * E)
    let A : ℝ := (Cv + Ch) / s
    let B : ℝ := Ch * (X / H)
    have hs : 0 < s := by unfold s; positivity
    have hsSq : s ^ 2 = q * X * E := by
      unfold s
      exact Real.sq_sqrt (by positivity)
    have hXle : X ≤ q * H ^ 2 := by
      calc
        X = 1 * X := by ring
        _ ≤ K * X := mul_le_mul_of_nonneg_right hK hX.le
        _ ≤ q * H ^ 2 := hlarge
    have hsle : s ≤ q * H := by
      have hsquare : s ^ 2 ≤ (q * H) ^ 2 := by
        rw [hsSq]
        have hqx : q * X ≤ (q * H) ^ 2 := by
          calc q * X ≤ q * (q * H ^ 2) := mul_le_mul_of_nonneg_left hXle hq.le
               _ = (q * H) ^ 2 := by ring
        exact (mul_le_of_le_one_right (by positivity : 0 ≤ q * X) hEle).trans hqx
      nlinarith [sq_nonneg (s - q * H)]
    have hcentral : ∀ x, ‖Jhi x‖ ≤ A := by
      intro x
      by_cases hx : x ∈ Set.Ici (4 * H)
      · simp only [Jhi, Set.indicator_of_mem hx]
        have hv := hvdc x
        have hplus : Cv / s ≤ (Cv + Ch) / s := by
          apply div_le_div_of_nonneg_right (by linarith) hs.le
        exact hv.trans (by simpa [A, s] using hplus)
      · simp [Jhi, hx, A]
        positivity
    have hfar' : ∀ x, 4 * (q * H) ≤ |t / (2 * Real.pi) + beta * x| →
        ‖Jhi x‖ ≤ B / |t / (2 * Real.pi) + beta * x| ^ 2 := by
      intro x hx
      have := hfar x (by simpa [hmax])
      simpa [B] using this
    have hrelation : B / (4 * (q * H)) ^ 2 ≤ A := by
      have hxs : X * s ≤ q ^ 2 * H ^ 3 := by
        calc X * s ≤ X * (q * H) := by gcongr
             _ ≤ (q * H ^ 2) * (q * H) := by gcongr
             _ = q ^ 2 * H ^ 3 := by ring
      have hbase : B / (4 * (q * H)) ^ 2 ≤ Ch / s := by
        have hmul := mul_le_mul_of_nonneg_left hxs hCh
        have hmul16 : Ch * (X * s) ≤ Ch * (16 * q ^ 2 * H ^ 3) := by
          calc
            Ch * (X * s) ≤ Ch * (q ^ 2 * H ^ 3) := hmul
            _ ≤ Ch * (16 * q ^ 2 * H ^ 3) := by
              apply mul_le_mul_of_nonneg_left _ hCh
              nlinarith [sq_nonneg q, sq_nonneg H]
        have hdiv := div_le_div_of_nonneg_right hmul16 hHpos.le
        unfold B
        apply (div_le_div_iff₀ (sq_pos_of_pos (by positivity)) hs).2
        calc
          Ch * (X / H) * s = Ch * (X * s) / H := by field_simp [hHpos.ne']
          _ ≤ Ch * (16 * q ^ 2 * H ^ 3) / H := hdiv
          _ = Ch * (4 * (q * H)) ^ 2 := by
            field_simp [hHpos.ne']
            norm_num
      exact hbase.trans (by
        unfold A
        apply div_le_div_of_nonneg_right (by linarith) hs.le)
    have henergy := packet_energy_le_of_central_far
      (c := t / (2 * Real.pi)) (beta := beta) (R := 4 * (q * H))
      (A := A) (B := B) (J := Jhi) hbeta (by positivity)
      (by unfold A; positivity) (by unfold B; positivity)
      hcentral hfar' hrelation hJhiInt
    rw [show |beta| = q by rfl] at henergy
    have hhigh : (∫ x : ℝ in Set.Ici (4 * H), ‖J x‖ ^ 2) ≤
        (16 * Real.pi * (Cv + Ch) ^ 2 / E) * H / (q * X) := by
      rw [← hhighSetEq]
      refine henergy.trans_eq ?_
      have hA2 : A ^ 2 = (Cv + Ch) ^ 2 / (q * X * E) := by
        unfold A
        rw [div_pow, hsSq]
      rw [hA2]
      field_simp [hq.ne', hX.ne', hE.ne']
      ring
    have hlow := hlowLarge hlarge
    have hsum := add_le_add hhigh hlow
    have hscale : 0 ≤ H / (q * X) := by positivity
    calc
      (∫ x : ℝ in Set.Ici (4 * H), ‖J x‖ ^ 2) +
          ∫ x : ℝ in Set.Iio (4 * H), ‖J x‖ ^ 2 ≤
          (16 * Real.pi * (Cv + Ch) ^ 2 / E + 5 * Cv ^ 2 / E) *
            H / (q * X) := by
        calc
          _ ≤ (16 * Real.pi * (Cv + Ch) ^ 2 / E) * H / (q * X) +
              (5 * Cv ^ 2 / E) * H / (q * X) := hsum
          _ = _ := by ring
      _ ≤ C83 * H / (q * X) := by
        rw [show (16 * Real.pi * (Cv + Ch) ^ 2 / E + 5 * Cv ^ 2 / E) *
            H / (q * X) =
            (16 * Real.pi * (Cv + Ch) ^ 2 / E + 5 * Cv ^ 2 / E) *
              (H / (q * X)) by ring,
          show C83 * H / (q * X) = C83 * (H / (q * X)) by ring]
        apply mul_le_mul_of_nonneg_right _ hscale
        unfold C83
        have hc : 0 ≤ 16 * Real.pi * K * (C0 + Ch) ^ 2 := by positivity
        have hd : 0 ≤ 5 * K * C0 ^ 2 := by positivity
        linarith
  · have hsmall : q * H ^ 2 < K * X := lt_of_not_ge hlarge
    have hRcmp : q * H ≤ K * (X / H) := by
      rw [show K * (X / H) = (K * X) / H by ring]
      apply (le_div_iff₀ hHpos).2
      nlinarith
    have hmax : max (q * H) (K * (X / H)) = K * (X / H) := max_eq_right hRcmp
    let A : ℝ := (C0 + Ch) * H / X
    let B : ℝ := Ch * (X / H)
    have hcentral : ∀ x, ‖Jhi x‖ ≤ A := by
      intro x
      by_cases hx : x ∈ Set.Ici (4 * H)
      · simp only [Jhi, Set.indicator_of_mem hx]
        have ht := htrivial x
        have hplus : C0 * H / X ≤ (C0 + Ch) * H / X := by
          apply div_le_div_of_nonneg_right _ hX.le
          exact mul_le_mul_of_nonneg_right (by linarith) hHpos.le
        exact ht.trans (by simpa [A] using hplus)
      · simp [Jhi, hx, A]
        positivity
    have hfar' : ∀ x, 4 * (K * (X / H)) ≤
        |t / (2 * Real.pi) + beta * x| →
        ‖Jhi x‖ ≤ B / |t / (2 * Real.pi) + beta * x| ^ 2 := by
      intro x hx
      have := hfar x (by simpa [hmax])
      simpa [B] using this
    have hrelation : B / (4 * (K * (X / H))) ^ 2 ≤ A := by
      have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
      have hbase : B / (4 * (K * (X / H))) ^ 2 ≤ Ch * H / X := by
        unfold B
        field_simp [hKpos.ne', hX.ne', hHpos.ne']
        have hfactor : 1 ≤ 16 * K ^ 2 := by nlinarith [sq_nonneg K]
        have hmul := mul_le_mul_of_nonneg_left hfactor hCh
        nlinarith
      exact hbase.trans (by
        unfold A
        apply div_le_div_of_nonneg_right _ hX.le
        exact mul_le_mul_of_nonneg_right (by linarith) hHpos.le)
    have henergy := packet_energy_le_of_central_far
      (c := t / (2 * Real.pi)) (beta := beta)
      (R := 4 * (K * (X / H))) (A := A) (B := B) (J := Jhi)
      hbeta (by positivity) (by unfold A; positivity) (by unfold B; positivity)
      hcentral hfar' hrelation hJhiInt
    rw [show |beta| = q by rfl] at henergy
    have hhigh : (∫ x : ℝ in Set.Ici (4 * H), ‖J x‖ ^ 2) ≤
        (16 * Real.pi * K * (C0 + Ch) ^ 2) * H / (q * X) := by
      rw [← hhighSetEq]
      refine henergy.trans_eq ?_
      have hA2 : A ^ 2 = (C0 + Ch) ^ 2 * H ^ 2 / X ^ 2 := by
        unfold A
        ring
      rw [hA2]
      field_simp [hq.ne', hX.ne', hHpos.ne']
      ring
    have hlow := hlowSmall hsmall
    have hsum := add_le_add hhigh hlow
    have hscale : 0 ≤ H / (q * X) := by positivity
    calc
      (∫ x : ℝ in Set.Ici (4 * H), ‖J x‖ ^ 2) +
          ∫ x : ℝ in Set.Iio (4 * H), ‖J x‖ ^ 2 ≤
          (16 * Real.pi * K * (C0 + Ch) ^ 2 + 5 * K * C0 ^ 2) *
            H / (q * X) := by
        calc
          _ ≤ (16 * Real.pi * K * (C0 + Ch) ^ 2) * H / (q * X) +
              (5 * K * C0 ^ 2) * H / (q * X) := hsum
          _ = _ := by ring
      _ ≤ C83 * H / (q * X) := by
        rw [show (16 * Real.pi * K * (C0 + Ch) ^ 2 + 5 * K * C0 ^ 2) *
            H / (q * X) =
            (16 * Real.pi * K * (C0 + Ch) ^ 2 + 5 * K * C0 ^ 2) *
              (H / (q * X)) by ring,
          show C83 * H / (q * X) = C83 * (H / (q * X)) by ring]
        apply mul_le_mul_of_nonneg_right _ hscale
        unfold C83
        have ha : 0 ≤ 16 * Real.pi * (Cv + Ch) ^ 2 / E := by positivity
        have hb : 0 ≤ 5 * Cv ^ 2 / E := by positivity
        linarith

#print axioms sourceStationaryPacket_eq_zero_of_le_neg_H
#print axioms source_packet_energy_equation83_wholeLine

end
end MAPMRTWholeLinePacketEquation83
