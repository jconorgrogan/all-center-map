import FordMixedLogKusmin
import FordUnitPhaseSign
import FordMixedLogEndpointMargins
import FordMixedKernelFTC
import FordPhaseDifferencing

open scoped BigOperators
noncomputable section
namespace FordLogPhaseLeafBound

open FordMixedReciprocalIntegral FordMixedLogKusmin
open FordMixedLogEndpointMargins FordMixedKernelFTC FordMixedKernelBounds
open FordPhaseDifferencing FordUnitPhaseSign FordUnitPhaseLipschitz

/-- The literal logarithmic phase leaf bound under explicit endpoint margins. -/
theorem norm_sum_phaseDiff_le
    (hs : List ℝ) (hsteps : ∀ h ∈ hs, 0 ≤ h)
    {t x δ : ℝ} (ht : 0 ≤ t) (hx : 0 < x) (hδ : 0 < δ)
    (H : ℕ)
    (hδlo : δ ≤ t * endpointCoeff hs /
      (x + H + 1 + shiftSum hs) ^ (hs.length + 1))
    (hδhi : t * endpointCoeff hs / x ^ (hs.length + 1) ≤
      2 * Real.pi - δ) :
    ‖∑ n ∈ Finset.range H,
      phaseDiff hs (fun y : ℝ => t * Real.log y) (x + n)‖ ≤
      3 * Real.pi / δ := by
  have hmarg := endpoint_margin_pair hs ht hx
    (by positivity : 0 ≤ (H : ℝ)) hsteps hδ hδlo hδhi
  have hlow : δ ≤ incrementSequence hs t x H := by
    simpa [incrementSequence, endpointIncrement] using hmarg.1
  have hupper : incrementSequence hs t x 0 ≤ 2 * Real.pi - δ := by
    simpa [incrementSequence, endpointIncrement] using hmarg.2
  have hphase (n : ℕ) :
      phaseDiff hs (fun y : ℝ => t * Real.log y) (x + n) =
        unitPhase (t * mixedDiff hs Real.log (x + n)) := by
    rw [phaseDiff_eq_unitPhase]
    rw [mixedDiff_const_mul]
  have hsum :
      (∑ n ∈ Finset.range H,
        phaseDiff hs (fun y : ℝ => t * Real.log y) (x + n)) =
      ∑ n ∈ Finset.range H,
        unitPhase (t * mixedDiff hs Real.log (x + n)) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact hphase n
  calc
    ‖∑ n ∈ Finset.range H,
        phaseDiff hs (fun y : ℝ => t * Real.log y) (x + n)‖ =
      ‖∑ n ∈ Finset.range H,
        unitPhase (t * mixedDiff hs Real.log (x + n))‖ := by
          rw [hsum]
    _ = ‖∑ n ∈ Finset.range H,
        phaseSequence hs t x n‖ := by
          simpa [phaseSequence, phaseArgument, mul_assoc] using
            (norm_sum_unitPhase_sign (Finset.range H)
              (fun n : ℕ => t * mixedDiff hs Real.log (x + n)) hs.length).symm
    _ ≤ 3 * Real.pi / δ := norm_sum_phase_le hs hsteps ht hx hδ H hlow hupper

end FordLogPhaseLeafBound

#print axioms FordLogPhaseLeafBound.norm_sum_phaseDiff_le
