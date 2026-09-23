import MRTWholeLinePacketEquation82
import MRTEquation81SourceScale

/-!
# MRT equation (81) from the whole-line packet kernel

This module closes the deterministic step after equation (82): the weighted
packet-correlation bilinear is dominated by the literal equation-(81) kernel,
and the already-certified averaging/Schur estimate gives the source scale.
The remaining upstream obligation is the exact equation-(79) duality identity
that produces this bilinear from the medium Littlewood--Paley piece.
-/

namespace MAPMRTWholeLineEquation81FromEquation82

open MeasureTheory
open MAPMRTPacketEquation82 MAPMRTEquation81Kernel
open MAPMRTEquation81AveragingBilinear MAPMRTEquation81SourceScale

noncomputable section

/-- The nonnegative weighted correlation object on the left of MRT (81). -/
def packetCorrelationBilinear
    (J : ℝ → ℝ → ℂ) (F : ℝ → ENNReal) : ENNReal :=
  ∫⁻ z : ℝ × ℝ,
    F z.1 * F z.2 * ENNReal.ofReal ‖packetCorrelation J z.1 z.2‖
      ∂volume.prod volume

/-- Pointwise equation (82) dominates the complete packet bilinear by the
literal equation-(81) kernel. -/
theorem packetCorrelationBilinear_le_equation81Bilinear
    {R M : ℝ} {J : ℝ → ℝ → ℂ} {F : ℝ → ENNReal}
    (hR : 0 < R) (hM : 0 ≤ M)
    (hcorr : ∀ t t', ‖packetCorrelation J t t'‖ ≤
      M * equation81Kernel R t t') :
    packetCorrelationBilinear J F ≤
      ENNReal.ofReal M * equation81Bilinear R F := by
  unfold packetCorrelationBilinear equation81Bilinear
  calc
    (∫⁻ z : ℝ × ℝ,
      F z.1 * F z.2 * ENNReal.ofReal ‖packetCorrelation J z.1 z.2‖
        ∂volume.prod volume) ≤
      ∫⁻ z : ℝ × ℝ,
        ENNReal.ofReal M *
          (F z.1 * F z.2 * ENNReal.ofReal (equation81Kernel R z.1 z.2))
          ∂volume.prod volume := by
      apply lintegral_mono
      intro z
      have hz := ENNReal.ofReal_le_ofReal (hcorr z.1 z.2)
      calc
        F z.1 * F z.2 * ENNReal.ofReal ‖packetCorrelation J z.1 z.2‖ ≤
            F z.1 * F z.2 *
              ENNReal.ofReal (M * equation81Kernel R z.1 z.2) :=
          mul_le_mul_right hz _
        _ = ENNReal.ofReal M *
            (F z.1 * F z.2 * ENNReal.ofReal (equation81Kernel R z.1 z.2)) := by
          rw [ENNReal.ofReal_mul hM]
          ring
    _ = ENNReal.ofReal M *
        (∫⁻ z : ℝ × ℝ,
          F z.1 * F z.2 * ENNReal.ofReal (equation81Kernel R z.1 z.2)
            ∂volume.prod volume) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Equation (81) at source scale, now consuming the actual packet kernel
rather than an abstract Schur citation. -/
theorem packetCorrelationBilinear_source_scale
    {R M : ℝ} {J : ℝ → ℝ → ℂ} {F : ℝ → ENNReal}
    (hR : 0 < R) (hM : 0 ≤ M) (hF : Measurable F)
    (hAfin : ∀ x, equation81Average R F x ≠ ⊤)
    (hcorr : ∀ t t', ‖packetCorrelation J t t'‖ ≤
      M * equation81Kernel R t t') :
    ENNReal.ofReal R * packetCorrelationBilinear J F ≤
      18 * ENNReal.ofReal M *
        (∫⁻ x : ℝ, (equation81Average R F x) ^ 2) := by
  have hbil := packetCorrelationBilinear_le_equation81Bilinear
    (J := J) (F := F) hR hM hcorr
  have hschur := equation81_source_scale hR hF hAfin
  calc
    ENNReal.ofReal R * packetCorrelationBilinear J F ≤
        ENNReal.ofReal R *
          (ENNReal.ofReal M * equation81Bilinear R F) :=
      mul_le_mul_right hbil _
    _ = ENNReal.ofReal M *
        (ENNReal.ofReal R * equation81Bilinear R F) := by ring
    _ ≤ ENNReal.ofReal M *
        (18 * (∫⁻ x : ℝ, (equation81Average R F x) ^ 2)) :=
      mul_le_mul_right hschur _
    _ = 18 * ENNReal.ofReal M *
        (∫⁻ x : ℝ, (equation81Average R F x) ^ 2) := by ring

#print axioms packetCorrelationBilinear_le_equation81Bilinear
#print axioms packetCorrelationBilinear_source_scale

end
end MAPMRTWholeLineEquation81FromEquation82
