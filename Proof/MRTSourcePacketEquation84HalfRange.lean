import MRTSourcePacketEquation84Bound
import MRTSourcePacketEquation84Collar

/-! Literal half-range assembly of MRT equation (84). -/

namespace MAPMRTSourcePacketEquation84HalfRange

open MeasureTheory Set
open MAPMRTProposition51HardBranch
open MAPMRTSourcePacketEquation84Bound
open MAPMRTSourcePacketEquation84Collar

noncomputable section

/-- Equation (84) throughout the printed MAP range `H ≤ X/2`.  The proof keeps
its two genuinely different windows visible: the sharp cutoff window when
`H≤X/4`, and the outer/cutoff intersection when `X/4<H≤X/2`. -/
theorem norm_sourceStationaryPacket_equation84_halfRange
    {X H x beta t D1 D2 B1 B2 : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hcenter : 4 * max (|beta| * H) (X / H) ≤
      |t / (2 * Real.pi) + beta * x|)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff'Support : ∀ y, 1 ≤ |y| → cutoff' y = 0)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (houter'Support : ∀ y, 1 ≤ |y| → outer' y = 0)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (houterBound : ∀ y, |outer y| ≤ 1)
    (houter'Bound : ∀ y, |outer' y| ≤ B1)
    (houter''Bound : ∀ y, |outer'' y| ≤ B2)
    (hcutoffDeriv : ∀ y, HasDerivAt cutoff (cutoff' y) y)
    (hcutoffSecond : ∀ y, HasDerivAt cutoff' (cutoff'' y) y)
    (houterDeriv : ∀ y, HasDerivAt outer (outer' y) y)
    (houterSecond : ∀ y, HasDerivAt outer' (outer'' y) y)
    (hcutoff''Cont : Continuous cutoff'') (houter''Cont : Continuous outer'')
    (hcutoff'Int : Integrable (fun y ↦ |cutoff' y|))
    (hcutoff''Int : Integrable (fun y ↦ |cutoff'' y|))
    (hD1 : (∫ y : ℝ, |cutoff' y|) ≤ D1)
    (hD2 : (∫ y : ℝ, |cutoff'' y|) ≤ D2) :
    let Csharp := 1500 + 24 * (10 * (1 + B1) * (1 + D1)) +
      4 * (10 + 10 * (1 + B1) * D1 + 20 * D2 + B1 + B2)
    let Ccollar := 150000 + 24 * (300 + 6 * B1 + 3 * D1) +
      4 * (100 + 10 * B1 + B2 + 10 * (1 + B1) * D1 + 14 * D2)
    ‖sourceStationaryPacket X H x beta t cutoff outer‖ ≤
      (Csharp + Ccollar) * (X / H) /
        |t / (2 * Real.pi) + beta * x| ^ 2 := by
  dsimp
  let Csharp := 1500 + 24 * (10 * (1 + B1) * (1 + D1)) +
    4 * (10 + 10 * (1 + B1) * D1 + 20 * D2 + B1 + B2)
  let Ccollar := 150000 + 24 * (300 + 6 * B1 + 3 * D1) +
    4 * (100 + 10 * B1 + B2 + 10 * (1 + B1) * D1 + 14 * D2)
  have hB1 : 0 ≤ B1 := le_trans (abs_nonneg (outer' 0)) (houter'Bound 0)
  have hB2 : 0 ≤ B2 := le_trans (abs_nonneg (outer'' 0)) (houter''Bound 0)
  have hD1n : 0 ≤ D1 := le_trans (integral_nonneg (fun _ ↦ abs_nonneg _)) hD1
  have hD2n : 0 ≤ D2 := le_trans (integral_nonneg (fun _ ↦ abs_nonneg _)) hD2
  have hCs : 0 ≤ Csharp := by unfold Csharp; positivity
  have hCc : 0 ≤ Ccollar := by unfold Ccollar; positivity
  have hscale : 0 ≤ (X / H) / |t / (2 * Real.pi) + beta * x| ^ 2 := by positivity
  by_cases hquarter : H ≤ X / 4
  · have hs := norm_sourceStationaryPacket_equation84_sharp
      hX hH hquarter hxLower hxUpper hcenter hcutoffSupport hcutoff'Support
      hcutoffBound houterBound houter'Bound houter''Bound hcutoffDeriv
      hcutoffSecond houterDeriv houterSecond hcutoff''Cont houter''Cont
      hcutoff'Int hcutoff''Int hD1 hD2
    calc
      ‖sourceStationaryPacket X H x beta t cutoff outer‖ ≤
          Csharp * (X / H) / |t / (2 * Real.pi) + beta * x| ^ 2 := by
        simpa [Csharp] using hs
      _ ≤ (Csharp + Ccollar) * (X / H) /
          |t / (2 * Real.pi) + beta * x| ^ 2 := by
        have hc : Csharp ≤ Csharp + Ccollar := le_add_of_nonneg_right hCc
        calc
          _ = Csharp * ((X / H) / |t / (2 * Real.pi) + beta * x| ^ 2) := by ring
          _ ≤ (Csharp + Ccollar) *
              ((X / H) / |t / (2 * Real.pi) + beta * x| ^ 2) := by gcongr
          _ = _ := by ring
  · have hcollar : X / 4 < H := lt_of_not_ge hquarter
    have hc := norm_sourceStationaryPacket_equation84_collar
      hX hH hcollar hHalf hxLower hxUpper hcenter hcutoffSupport hcutoff'Support
      houterSupport houter'Support hcutoffBound houterBound houter'Bound
      houter''Bound hcutoffDeriv hcutoffSecond houterDeriv houterSecond
      hcutoff''Cont houter''Cont hcutoff'Int hcutoff''Int hD1 hD2
    calc
      ‖sourceStationaryPacket X H x beta t cutoff outer‖ ≤
          Ccollar * (X / H) / |t / (2 * Real.pi) + beta * x| ^ 2 := by
        simpa [Ccollar] using hc
      _ ≤ (Csharp + Ccollar) * (X / H) /
          |t / (2 * Real.pi) + beta * x| ^ 2 := by
        have hc' : Ccollar ≤ Csharp + Ccollar := le_add_of_nonneg_left hCs
        calc
          _ = Ccollar * ((X / H) / |t / (2 * Real.pi) + beta * x| ^ 2) := by ring
          _ ≤ (Csharp + Ccollar) *
              ((X / H) / |t / (2 * Real.pi) + beta * x| ^ 2) := by gcongr
          _ = _ := by ring

#print axioms norm_sourceStationaryPacket_equation84_halfRange

end
end MAPMRTSourcePacketEquation84HalfRange
