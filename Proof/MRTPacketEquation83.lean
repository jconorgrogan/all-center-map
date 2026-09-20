import MRTSourcePacketSupport

/-!
# MRT equation (83) from the literal equation-(84) packet bound

This module performs the two `|β|H²` cases immediately below (83).  All
measurability and square-integrability obligations are discharged.  The sole
remaining packet input is exactly the two-integration-by-parts estimate (84),
with its regime-dependent nonstationary radius written as
`4 * max (|β|H) (X/H)`.
-/

namespace MAPMRTPacketEquation83

open MeasureTheory Set
open MAPMRTProposition51HardBranch
open MAPMRTVanDerCorput
open MAPMRTPacketEnergy
open MAPMRTSourcePacketSupport

noncomputable section

/-- An explicit absolute constant large enough for both pointwise packet
bounds used below (83). -/
def packetPointwiseConstant (Dcut Dout : ℝ) : ℝ :=
  800 * Real.exp 50 + 10 * Real.exp 50 * (101 + Dcut + Dout)

theorem packetPointwiseConstant_pos
    {Dcut Dout : ℝ} (hDcut : 0 ≤ Dcut) (hDout : 0 ≤ Dout) :
    0 < packetPointwiseConstant Dcut Dout := by
  unfold packetPointwiseConstant
  have he : 0 < Real.exp 50 := Real.exp_pos 50
  nlinarith

/-- Equation (83), conditional only on the exact equation-(84) estimate.

The packet is restricted to `[X/2,4X]`, the support of the normalized dual
function in (72),(73).  The premise `h84` is precisely the manuscript's two
integrations by parts, with an explicit absolute coefficient and with the two
case thresholds combined as `4 * max (|β|H) (X/H)`. -/
theorem source_packet_energy_equation83_of_equation84
    {X H beta eta t Dcut Dout : ℝ}
    {cutoff cutoff' outerCutoff outerCutoff' : ℝ → ℝ}
    (hH : 1 ≤ H) (hHalf : H ≤ X / 2)
    (hhard : 1 < |beta| * H)
    (hetaPos : 0 < eta) (hetaHard : eta < 1 / 100)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterSupport : ∀ y, 1 ≤ |y| → outerCutoff y = 0)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (houterBound : ∀ y, |outerCutoff y| ≤ 1)
    (hcutoffDeriv : ∀ y, HasDerivAt cutoff (cutoff' y) y)
    (houterDeriv : ∀ y, HasDerivAt outerCutoff (outerCutoff' y) y)
    (hcutoff'Cont : Continuous cutoff')
    (houter'Cont : Continuous outerCutoff')
    (hcutoff'Int : Integrable (fun y ↦ |cutoff' y|))
    (houter'Int : Integrable (fun y ↦ |outerCutoff' y|))
    (hDcut : (∫ y : ℝ, |cutoff' y|) ≤ Dcut)
    (hDout : (∫ y : ℝ, |outerCutoff' y|) ≤ Dout)
    (h84 : ∀ x,
      4 * max (|beta| * H) (X / H) ≤ |t / (2 * Real.pi) + beta * x| →
      ‖sourceRestrictedPacket X H beta t cutoff outerCutoff x‖ ≤
        packetPointwiseConstant Dcut Dout * (X / H) /
          |t / (2 * Real.pi) + beta * x| ^ 2) :
    (∫ x : ℝ,
      ‖sourceRestrictedPacket X H beta t cutoff outerCutoff x‖ ^ 2) ≤
      (16 * Real.pi * packetPointwiseConstant Dcut Dout ^ 2 /
          Real.exp (-100)) * H / (|beta| * X) := by
  let q : ℝ := |beta|
  let E : ℝ := Real.exp (-100)
  let L : ℝ := packetPointwiseConstant Dcut Dout
  let J : ℝ → ℂ := fun x ↦
    sourceRestrictedPacket X H beta t cutoff outerCutoff x
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hX : 0 < X := by linarith
  have hq : 0 < q := by
    unfold q
    have : beta ≠ 0 := by
      intro hb
      subst beta
      norm_num at hhard
    exact abs_pos.mpr this
  have hE : 0 < E := by unfold E; positivity
  have hEle : E ≤ 1 := by
    unfold E
    simpa using Real.exp_le_one_iff.mpr (by norm_num : (-100 : ℝ) ≤ 0)
  have hDcut0 : 0 ≤ Dcut := by
    exact (integral_nonneg (fun y ↦ abs_nonneg (cutoff' y))).trans hDcut
  have hDout0 : 0 ≤ Dout := by
    exact (integral_nonneg (fun y ↦ abs_nonneg (outerCutoff' y))).trans hDout
  have hL : 0 < L := packetPointwiseConstant_pos hDcut0 hDout0
  have hcutoffCont : Continuous cutoff :=
    continuous_iff_continuousAt.mpr (fun y ↦ (hcutoffDeriv y).continuousAt)
  have houterCont : Continuous outerCutoff :=
    continuous_iff_continuousAt.mpr (fun y ↦ (houterDeriv y).continuousAt)
  have hJInt : Integrable (fun x ↦ ‖J x‖ ^ 2) :=
    integrable_norm_sourceRestrictedPacket_sq hcutoffCont houterCont houterSupport
  change (∫ x : ℝ, ‖J x‖ ^ 2) ≤
    (16 * Real.pi * L ^ 2 / E) * H / (q * X)
  by_cases hlarge : X ≤ q * H ^ 2
  · have hRcmp : X / H ≤ q * H := by
      apply (div_le_iff₀ hHpos).2
      nlinarith
    have hmax : max (q * H) (X / H) = q * H := max_eq_left hRcmp
    let s : ℝ := Real.sqrt (q * X * E)
    have hs : 0 < s := by unfold s; positivity
    have hsSq : s ^ 2 = q * X * E := by
      unfold s
      exact Real.sq_sqrt (by positivity)
    have hs_le : s ≤ q * H := by
      have hsq : s ^ 2 ≤ (q * H) ^ 2 := by
        rw [hsSq]
        have hqX : q * X ≤ (q * H) ^ 2 := by
          calc
            q * X ≤ q * (q * H ^ 2) :=
              mul_le_mul_of_nonneg_left hlarge hq.le
            _ = (q * H) ^ 2 := by ring
        exact (mul_le_of_le_one_right (by positivity : 0 ≤ q * X) hEle).trans hqX
      nlinarith [sq_nonneg (s - q * H)]
    have hcentral : ∀ x, ‖J x‖ ≤ L / s := by
      intro x
      by_cases hx : x ∈ Set.Icc (X / 2) (4 * X)
      · simp only [J, sourceRestrictedPacket, Set.indicator_of_mem hx]
        have hvdc := MAPMRTVanDerCorput.norm_sourceStationaryPacket_le
          (X := X) (H := H) (x := x) (beta := beta) (eta := eta) (t := t)
          (Dcut := Dcut) (Dout := Dout) hH hHalf hhard hetaPos hetaHard
          hx.1 hx.2 houterSupport hcutoffBound houterBound hcutoffDeriv
          houterDeriv hcutoff'Cont houter'Cont hcutoff'Int houter'Int hDcut hDout
        have hnum : 10 * Real.exp 50 * (101 + Dcut + Dout) ≤ L := by
          unfold L packetPointwiseConstant
          nlinarith [Real.exp_pos 50]
        refine hvdc.trans ?_
        have hsDef : s = Real.sqrt (|beta| * X * Real.exp (-100)) := by
          rfl
        rw [hsDef]
        exact div_le_div_of_nonneg_right hnum hs.le
      · simp [J, sourceRestrictedPacket, hx]
        positivity
    have hfar : ∀ x, 4 * (q * H) ≤ |t / (2 * Real.pi) + beta * x| →
        ‖J x‖ ≤ (L * (X / H)) /
          |t / (2 * Real.pi) + beta * x| ^ 2 := by
      intro x hx
      exact h84 x (by simpa [q, hmax])
    have hrelationBase : (L * (X / H)) / (q * H) ^ 2 ≤ L / s := by
      apply (div_le_div_iff₀ (sq_pos_of_pos (mul_pos hq hHpos)) hs).2
      have hbase : (X / H) * s ≤ (q * H) ^ 2 := by
        calc
          (X / H) * s ≤ (X / H) * (q * H) := by
            gcongr
          _ = q * X := by field_simp [hHpos.ne']
          _ ≤ (q * H) ^ 2 := by
            calc
              q * X ≤ q * (q * H ^ 2) :=
                mul_le_mul_of_nonneg_left hlarge hq.le
              _ = (q * H) ^ 2 := by ring
      nlinarith [hL.le]
    have hrelation : (L * (X / H)) / (4 * (q * H)) ^ 2 ≤ L / s := by
      have hden : (q * H) ^ 2 ≤ (4 * (q * H)) ^ 2 := by
        nlinarith [sq_nonneg (q * H)]
      exact (div_le_div_of_nonneg_left (by positivity : 0 ≤ L * (X / H))
        (sq_pos_of_pos (mul_pos hq hHpos)) hden).trans hrelationBase
    have henergy := packet_energy_le_of_central_far
      (c := t / (2 * Real.pi)) (beta := beta) (R := 4 * (q * H))
      (A := L / s) (B := L * (X / H)) (J := J)
      (by simpa [q] using hq.ne') (by positivity) (by positivity)
      (by positivity) hcentral hfar hrelation hJInt
    rw [show |beta| = q by rfl] at henergy
    refine henergy.trans_eq ?_
    field_simp [hq.ne', hX.ne', hE.ne', hs.ne', hHpos.ne']
    rw [hsSq]
    ring
  · have hsmall : q * H ^ 2 < X := lt_of_not_ge hlarge
    have hRcmp : q * H ≤ X / H := by
      apply (le_div_iff₀ hHpos).2
      nlinarith
    have hmax : max (q * H) (X / H) = X / H := max_eq_right hRcmp
    have hcentral : ∀ x, ‖J x‖ ≤ L * H / X := by
      intro x
      have htrivial := norm_sourceRestrictedPacket_le_trivial
        (X := X) (H := H) (beta := beta) (t := t) (x := x)
        hH hHalf hcutoffSupport houterSupport hcutoffBound houterBound
      have hconst : 800 * Real.exp 50 ≤ L := by
        unfold L packetPointwiseConstant
        have hsecond : 0 ≤ 10 * Real.exp 50 * (101 + Dcut + Dout) := by
          positivity
        linarith
      exact htrivial.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hconst hHpos.le) hX.le)
    have hfar : ∀ x, 4 * (X / H) ≤ |t / (2 * Real.pi) + beta * x| →
        ‖J x‖ ≤ (L * (X / H)) /
          |t / (2 * Real.pi) + beta * x| ^ 2 := by
      intro x hx
      exact h84 x (by simpa [q, hmax])
    have hrelationBase : (L * (X / H)) / (X / H) ^ 2 ≤ L * H / X := by
      field_simp [hX.ne', hHpos.ne']
      norm_num
    have hrelation : (L * (X / H)) / (4 * (X / H)) ^ 2 ≤ L * H / X := by
      have hden : (X / H) ^ 2 ≤ (4 * (X / H)) ^ 2 := by
        nlinarith [sq_nonneg (X / H)]
      exact (div_le_div_of_nonneg_left (by positivity : 0 ≤ L * (X / H))
        (sq_pos_of_pos (div_pos hX hHpos)) hden).trans hrelationBase
    have henergy := packet_energy_le_of_central_far
      (c := t / (2 * Real.pi)) (beta := beta) (R := 4 * (X / H))
      (A := L * H / X) (B := L * (X / H)) (J := J)
      (by simpa [q] using hq.ne') (by positivity) (by positivity)
      (by positivity) hcentral hfar hrelation hJInt
    have heq : 4 * Real.pi * (L * H / X) ^ 2 * (4 * (X / H)) / |beta| =
        16 * Real.pi * L ^ 2 * H / (|beta| * X) := by
      field_simp [hX.ne', hHpos.ne', (by simpa [q] using hq.ne' : |beta| ≠ 0)]
      norm_num
    rw [heq] at henergy
    refine henergy.trans ?_
    have hinv : 1 ≤ 1 / E := by
      apply (le_div_iff₀ hE).2
      simpa using hEle
    have hnonneg : 0 ≤ 16 * Real.pi * L ^ 2 * H / (|beta| * X) := by positivity
    calc
      16 * Real.pi * L ^ 2 * H / (|beta| * X) =
          (16 * Real.pi * L ^ 2 * H / (|beta| * X)) * 1 := by ring
      _ ≤ (16 * Real.pi * L ^ 2 * H / (|beta| * X)) * (1 / E) :=
        mul_le_mul_of_nonneg_left hinv hnonneg
      _ = (16 * Real.pi * L ^ 2 / E) * H / (|beta| * X) := by ring

#print axioms MAPMRTPacketEquation83.source_packet_energy_equation83_of_equation84

end
end MAPMRTPacketEquation83
