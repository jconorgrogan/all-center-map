import MRTPacketEquation82

/-! Source-faithful large-constant off-diagonal interface for equation (82). -/

namespace MAPMRTPacketEquation82LargeThreshold

open MeasureTheory
open MAPMRTPacketEquation82

noncomputable section

/-- The corrected (82) interface.  The two-IBP estimate is only requested past
`L|β|H`; the intermediate band is absorbed by (83) and Cauchy--Schwarz. -/
theorem packet_correlation_equation82_large_threshold
    {X H beta L C83 Coff t t' : ℝ} {J : ℝ → ℝ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hhard : 1 < |beta| * H)
    (hL : 1 ≤ L) (hC83 : 0 ≤ C83) (hCoff : 0 ≤ Coff)
    (hJ : ∀ s, MemLp (J s) 2)
    (h83 : ∀ s, (∫ x : ℝ, ‖J s x‖ ^ 2) ≤
      C83 * H / (|beta| * X))
    (hoff : ∀ s s', L * (|beta| * H) ≤ |s - s'| →
      ‖packetCorrelation J s s'‖ ≤
        Coff * H ^ 2 / (X * |s - s'| ^ 2)) :
    ‖packetCorrelation J t t'‖ ≤
      ((1 + L) ^ 2 * C83 + 4 * Coff) * H / (|beta| * X) /
        (1 + |t - t'| / (|beta| * H)) ^ 2 := by
  let q : ℝ := |beta|
  let R : ℝ := q * H
  let d : ℝ := |t - t'|
  let y : ℝ := d / R
  let S : ℝ := H / (q * X)
  let C : ℝ := (1 + L) ^ 2 * C83 + 4 * Coff
  have hq : 0 < q := by
    unfold q
    have hb : beta ≠ 0 := by
      intro hb
      subst beta
      norm_num at hhard
    exact abs_pos.mpr hb
  have hR : 0 < R := mul_pos hq hH
  have hRone : 1 < R := by simpa [R, q] using hhard
  have hd : 0 ≤ d := by unfold d; positivity
  have hy : 0 ≤ y := by unfold y; positivity
  have hS : 0 < S := by unfold S; positivity
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have hC : 0 ≤ C := by unfold C; positivity
  have hcentral : ‖packetCorrelation J t t'‖ ≤ C83 * S := by
    have hc := norm_packetCorrelation_le_average_energy (hJ t) (hJ t')
    have ht := h83 t
    have ht' := h83 t'
    have havg : ((∫ x : ℝ, ‖J t x‖ ^ 2) +
        (∫ x : ℝ, ‖J t' x‖ ^ 2)) / 2 ≤
        C83 * H / (q * X) := by
      simpa [q] using (show ((∫ x : ℝ, ‖J t x‖ ^ 2) +
          (∫ x : ℝ, ‖J t' x‖ ^ 2)) / 2 ≤
          C83 * H / (|beta| * X) by linarith)
    refine hc.trans ?_
    convert havg using 1 <;> simp [S] <;> ring
  by_cases hfar : L * R ≤ d
  · have hoff' := hoff t t' (by simpa [R, q, d] using hfar)
    have hdpos : 0 < d := lt_of_lt_of_le (mul_pos (lt_of_lt_of_le zero_lt_one hL) hR) hfar
    have hyone : 1 ≤ y := by
      unfold y
      rw [le_div_iff₀ hR]
      exact le_trans (mul_le_mul_of_nonneg_right hL hR.le) hfar
    have hden : 0 < (1 + y) ^ 2 := by positivity
    have hkernel : (1 + y) ^ 2 ≤ 4 * y ^ 2 := by
      nlinarith [sq_nonneg (y - 1)]
    have hfarScale :
        Coff * H ^ 2 / (X * d ^ 2) ≤
          4 * Coff * S / (1 + y) ^ 2 := by
      apply (div_le_div_iff₀ (mul_pos hX (sq_pos_of_pos hdpos)) hden).2
      calc
        Coff * H ^ 2 * (1 + y) ^ 2 ≤
            Coff * H ^ 2 * (4 * y ^ 2) := by gcongr
        _ ≤ (4 * Coff * S) * (X * d ^ 2) := by
          unfold y R S
          field_simp [hq.ne', hH.ne', hX.ne']
          nlinarith [hRone, sq_nonneg d]
    have hcoeff : 4 * Coff * S ≤ C * S := by
      unfold C
      nlinarith [mul_nonneg hC83 hS.le, sq_nonneg (1 + L)]
    have htarget : C * S / (1 + y) ^ 2 =
        ((1 + L) ^ 2 * C83 + 4 * Coff) * H / (|beta| * X) /
          (1 + |t - t'| / (|beta| * H)) ^ 2 := by
      simp only [C, S, q, y, d, R]
      ring
    rw [← htarget]
    exact hoff'.trans (hfarScale.trans
      (div_le_div_of_nonneg_right hcoeff hden.le))
  · have hnear : y < L := by
      unfold y
      rw [div_lt_iff₀ hR]
      nlinarith
    have hden : 0 < (1 + y) ^ 2 := by positivity
    have hkernel : (1 + y) ^ 2 ≤ (1 + L) ^ 2 := by
      nlinarith [sq_nonneg ((1 + L) - (1 + y))]
    apply hcentral.trans
    apply (le_div_iff₀ hden).2
    calc
      C83 * S * (1 + y) ^ 2 ≤ C83 * S * (1 + L) ^ 2 := by gcongr
      _ ≤ C * S := by
        unfold C
        nlinarith [mul_nonneg hCoff hS.le,
          mul_nonneg hC83 hS.le, sq_nonneg (1 + L)]
      _ = ((1 + L) ^ 2 * C83 + 4 * Coff) * H / (|beta| * X) := by
        simp only [C, S, q]
        ring
  
#print axioms packet_correlation_equation82_large_threshold

end
end MAPMRTPacketEquation82LargeThreshold
