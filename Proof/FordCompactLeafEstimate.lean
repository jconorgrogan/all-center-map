import FordCompactGoodShiftMargins
import FordCompactMarginScalar
import FordLogPhaseLeafBound
import FordPhaseTreeRecurrence

noncomputable section
namespace FordCompactLeafEstimate
open FordCompactGoodShiftMargins FordCompactMarginScalar
open FordMixedKernelBounds FordMixedLogEndpointMargins FordPhaseTreeRecurrence
open FordGoodShiftError

/-- Actual terminal logarithmic sum estimate; endpoint margins are derived. -/
theorem phaseSize_le {N H : ℕ} {lam q eps u : ℝ} (hs : List ℕ)
    (hN : 2 ≤ N) (hH : H ≤ N) (hr : 2 ≤ hs.length)
    (heps : 0 ≤ eps) (heq : eps ≤ q) (hq : q ≤ (3 : ℝ) / 4)
    (hlam : 0 ≤ lam)
    (hexpU : lam + (hs.length : ℝ) * q - (hs.length + 1) = -(1 / 2))
    (hexpL : lam + (hs.length : ℝ) * (q - eps) - (hs.length + 1) = -(3 / 4))
    (hgood : ∀ g ∈ hs, g ∈ goodShifts (FordScaleFloor.scale N q) ((N : ℝ) ^ (-eps)))
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hcollar : (hs.length : ℝ) * (N : ℝ) ^ ((3 : ℝ) / 4) ≤ (N : ℝ))
    (hfac : (hs.length.factorial : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1)
    (habsorb : (12 * Real.pi * 8 ^ hs.length) * (N : ℝ) ^ (-(1 / 4 : ℝ)) ≤
      (N : ℝ) ^ (-eps)) :
    phaseSize N H (fun y : ℝ => (N : ℝ) ^ lam * Real.log y) ((N : ℝ) + u) hs ≤
      (N : ℝ) ^ (-eps) := by
  let L := hs.map (fun h : ℕ => (h : ℝ))
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hx : 0 < (N : ℝ) + u := by linarith
  have hsteps : ∀ h ∈ L, 0 ≤ h := by
    intro h hh
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hh
    positivity
  have hm := endpoint_margins (H := H - hs.sum) hs hN hr heps heq hq hlam hexpU hexpL
    hgood hu0 hu1 ((Nat.sub_le H hs.sum).trans hH) hcollar
  have hnum : 0 ≤ (N : ℝ) ^ lam * endpointCoeff L := by
    unfold endpointCoeff
    exact mul_nonneg (Real.rpow_nonneg hNr.le _)
      (mul_nonneg (riseCoeff_pos (by omega : 1 ≤ (1 : ℕ))).le (shiftProd_nonneg hsteps))
  have hup : (N : ℝ) ^ lam * endpointCoeff L /
      ((N : ℝ) + u) ^ (L.length + 1) ≤ 1 := by
    have hden : (N : ℝ) ^ (hs.length + 1) ≤
        ((N : ℝ) + u) ^ (hs.length + 1) :=
      pow_le_pow_left₀ hNr.le (by linarith) _
    have hd : (N : ℝ) ^ lam * endpointCoeff L /
        ((N : ℝ) + u) ^ (hs.length + 1) ≤
        (N : ℝ) ^ lam * endpointCoeff L / (N : ℝ) ^ (hs.length + 1) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      exact mul_le_mul_of_nonneg_left hden hnum
    simpa [L] using hd.trans (hm.2.trans hfac)
  have hb := FordLogPhaseLeafBound.norm_sum_phaseDiff_le L hsteps
    (Real.rpow_nonneg hNr.le lam) hx (margin_pos (r := hs.length) (by omega : 1 ≤ N))
    (H - hs.sum)
    (by simpa [margin, L] using hm.1)
    (endpoint_upper_of_le_one (r := hs.length) (by omega : 1 ≤ N) hup)
  have hd := div_le_div_of_nonneg_right hb hNr.le
  calc
    phaseSize N H (fun y : ℝ => (N : ℝ) ^ lam * Real.log y) ((N : ℝ) + u) hs ≤
        (3 * Real.pi / margin hs.length N) / (N : ℝ) := by
      simpa only [phaseSize, phaseSum, L] using hd
    _ = (12 * Real.pi * 8 ^ hs.length) * (N : ℝ) ^ (-(1 / 4 : ℝ)) :=
      normalized_ratio (by omega)
    _ ≤ (N : ℝ) ^ (-eps) := habsorb

end FordCompactLeafEstimate
#print axioms FordCompactLeafEstimate.phaseSize_le
