import MRTWholeLineEq83ParallelLowCell
import MRTPacketEnergy

/-!
# Whole-line equation-(83) energy split

This is the deterministic integration weld.  It uses a global central packet
bound on the lower cell, and the same central bound plus equation (84) on the
high cell.  The high cell is introduced only as a measurable indicator after
the source's legal whole-line extension.
-/

namespace MAPMRTWholeLineEq83ParallelEnergySplit

open MeasureTheory Set
open MAPMRTPacketEnergy
open MAPMRTWholeLineEq83ParallelLowCell

noncomputable section

def highCellPart (H : ℝ) (J : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Set.Ici (4 * H)).indicator J x

theorem integrable_norm_highCellPart_sq
    {H : ℝ} {J : ℝ → ℂ}
    (hInt : Integrable (fun x ↦ ‖J x‖ ^ 2)) :
    Integrable (fun x ↦ ‖highCellPart H J x‖ ^ 2) := by
  have hi : Integrable ((Set.Ici (4 * H)).indicator
      (fun x ↦ ‖J x‖ ^ 2)) := hInt.indicator measurableSet_Ici
  apply hi.congr
  filter_upwards with x
  by_cases hx : x ∈ Set.Ici (4 * H)
  · simp [highCellPart, hx]
  · simp [highCellPart, hx]

/-- Generic low/high energy weld underlying the unrestricted equation (83). -/
theorem wholeLine_energy_le_low_add_cauchy
    {H c beta R A B : ℝ} {J : ℝ → ℂ}
    (hH : 0 < H) (hbeta : beta ≠ 0)
    (hR : 0 < R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hzero : ∀ x, x ≤ -H → J x = 0)
    (hcentral : ∀ x, ‖J x‖ ≤ A)
    (hfar : ∀ x, 4 * H ≤ x → R ≤ |c + beta * x| →
      ‖J x‖ ≤ B / |c + beta * x| ^ 2)
    (hrelation : B / R ^ 2 ≤ A)
    (hInt : Integrable (fun x ↦ ‖J x‖ ^ 2)) :
    (∫ x : ℝ, ‖J x‖ ^ 2) ≤
      5 * H * A ^ 2 + 4 * Real.pi * A ^ 2 * R / |beta| := by
  let Jh : ℝ → ℂ := highCellPart H J
  have hJhInt : Integrable (fun x ↦ ‖Jh x‖ ^ 2) := by
    exact integrable_norm_highCellPart_sq hInt
  have hJhCentral : ∀ x, ‖Jh x‖ ≤ A := by
    intro x
    by_cases hx : x ∈ Set.Ici (4 * H)
    · simpa [Jh, highCellPart, hx] using hcentral x
    · simp [Jh, highCellPart, hx, hA]
  have hJhFar : ∀ x, R ≤ |c + beta * x| →
      ‖Jh x‖ ≤ B / |c + beta * x| ^ 2 := by
    intro x hxFar
    by_cases hx : x ∈ Set.Ici (4 * H)
    · have hxHigh : 4 * H ≤ x := hx
      simpa [Jh, highCellPart, hx] using hfar x hxHigh hxFar
    · simp [Jh, highCellPart, hx]
      positivity
  have hhigh := packet_energy_le_of_central_far
    (c := c) (beta := beta) (R := R) (A := A) (B := B) (J := Jh)
    hbeta hR hA hB hJhCentral hJhFar hrelation hJhInt
  have hlow := integral_Iio_four_mul_le_five_mul
    hH hA hzero hcentral hInt
  have hsplit := integral_add_compl
    (f := fun x : ℝ ↦ ‖J x‖ ^ 2) (s := Set.Iio (4 * H))
    measurableSet_Iio hInt
  rw [Set.compl_Iio] at hsplit
  have hhighEq :
      (∫ x : ℝ, ‖Jh x‖ ^ 2) =
        ∫ x in Set.Ici (4 * H), ‖J x‖ ^ 2 := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ici]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Set.Ici (4 * H)
    · simp [Jh, highCellPart, hx]
    · simp [Jh, highCellPart, hx]
  rw [hhighEq] at hhigh
  calc
    (∫ x : ℝ, ‖J x‖ ^ 2) =
        (∫ x in Set.Iio (4 * H), ‖J x‖ ^ 2) +
          ∫ x in Set.Ici (4 * H), ‖J x‖ ^ 2 := hsplit.symm
    _ ≤ 5 * H * A ^ 2 + 4 * Real.pi * A ^ 2 * R / |beta| :=
      add_le_add hlow hhigh

#print axioms integrable_norm_highCellPart_sq
#print axioms wholeLine_energy_le_low_add_cauchy

end
end MAPMRTWholeLineEq83ParallelEnergySplit
