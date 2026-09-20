import MRTNonstationaryPhaseInverse
import MRTVanDerCorput

/-! Exact phase separation for the distinct off-diagonal two-IBP argument. -/

namespace MAPMRTOffDiagonalPhase

open MAPMRTProposition51HardBranch

noncomputable section

/-- Phase after the manuscript change `w' = w+h`. -/
def offDiagonalPhase (X beta s s' h w : ℝ) : ℝ :=
  stationaryPacketPhase X beta s w -
    stationaryPacketPhase X beta s' (w + h)

def offDiagonalPhaseDeriv (X beta s s' h w : ℝ) : ℝ :=
  beta * X * (Real.exp w - Real.exp (w + h)) +
    (s - s') / (2 * Real.pi)

def offDiagonalPhaseSecond (X beta h w : ℝ) : ℝ :=
  beta * X * (Real.exp w - Real.exp (w + h))

theorem hasDerivAt_offDiagonalPhase
    (X beta s s' h w : ℝ) :
    HasDerivAt (offDiagonalPhase X beta s s' h)
      (offDiagonalPhaseDeriv X beta s s' h w) w := by
  unfold offDiagonalPhase offDiagonalPhaseDeriv
  convert (hasDerivAt_stationaryPacketPhase X beta s w).sub
    ((hasDerivAt_stationaryPacketPhase X beta s' (w + h)).scomp w
      ((hasDerivAt_id w).add_const h)) using 1 <;> ring

theorem hasDerivAt_offDiagonalPhaseDeriv
    (X beta s s' h w : ℝ) :
    HasDerivAt (offDiagonalPhaseDeriv X beta s s' h)
      (offDiagonalPhaseSecond X beta h w) w := by
  unfold offDiagonalPhaseDeriv offDiagonalPhaseSecond
  convert (((Real.hasDerivAt_exp w).sub
    ((Real.hasDerivAt_exp (w + h)).scomp w
      ((hasDerivAt_id w).add_const h))).const_mul (beta * X)).add_const
        ((s - s') / (2 * Real.pi)) using 1 <;> ring

theorem hasDerivAt_offDiagonalPhaseSecond
    (X beta h w : ℝ) :
    HasDerivAt (offDiagonalPhaseSecond X beta h)
      (offDiagonalPhaseSecond X beta h w) w := by
  unfold offDiagonalPhaseSecond
  convert ((Real.hasDerivAt_exp w).sub
    ((Real.hasDerivAt_exp (w + h)).scomp w
      ((hasDerivAt_id w).add_const h))).const_mul (beta * X) using 1 <;> ring

/-- The two source cutoffs force the two exponential centers to be within
`2H`, independently of the sharp `x` restriction. -/
theorem exp_centers_close_of_cutoff_support
    {X H x w h : ℝ} (hH : 0 < H)
    (hw : |(X * Real.exp w - x) / H| ≤ 1)
    (hwh : |(X * Real.exp (w + h) - x) / H| ≤ 1) :
    |X * Real.exp w - X * Real.exp (w + h)| ≤ 2 * H := by
  have hw' : |X * Real.exp w - x| ≤ H := by
    rw [abs_div, abs_of_pos hH] at hw
    exact (div_le_one hH).mp hw
  have hwh' : |X * Real.exp (w + h) - x| ≤ H := by
    rw [abs_div, abs_of_pos hH] at hwh
    exact (div_le_one hH).mp hwh
  calc
    |X * Real.exp w - X * Real.exp (w + h)| =
        |(X * Real.exp w - x) - (X * Real.exp (w + h) - x)| := by
      congr 1 <;> ring
    _ ≤ |X * Real.exp w - x| + |X * Real.exp (w + h) - x| := abs_sub _ _
    _ ≤ 2 * H := by linarith

/-- The exact large-constant separation needed by two integrations by parts.
The factor `8π` is exposed rather than hidden in the manuscript's `C`. -/
theorem offDiagonalPhaseDeriv_lower
    {X H beta s s' h w : ℝ} (hH : 0 < H)
    (hclose : |X * Real.exp w - X * Real.exp (w + h)| ≤ 2 * H)
    (hsep : 8 * Real.pi * |beta| * H ≤ |s - s'|) :
    |s - s'| / (4 * Real.pi) ≤
      |offDiagonalPhaseDeriv X beta s s' h w| := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpert :
      |beta * X * (Real.exp w - Real.exp (w + h))| ≤ 2 * |beta| * H := by
    have heq : X * (Real.exp w - Real.exp (w + h)) =
        X * Real.exp w - X * Real.exp (w + h) := by ring
    calc
      |beta * X * (Real.exp w - Real.exp (w + h))| =
          |beta| * |X * (Real.exp w - Real.exp (w + h))| := by
        simp only [abs_mul]
        ring
      _ = |beta| * |X * Real.exp w - X * Real.exp (w + h)| := by rw [heq]
      _ ≤ |beta| * (2 * H) :=
        mul_le_mul_of_nonneg_left hclose (abs_nonneg beta)
      _ = 2 * |beta| * H := by ring
  have hpert' :
      |beta * X * (Real.exp w - Real.exp (w + h))| ≤
        |s - s'| / (4 * Real.pi) := by
    apply hpert.trans
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.pi)).2
    nlinarith
  have hlin : |(s - s') / (2 * Real.pi)| =
      |s - s'| / (2 * Real.pi) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  have hrev := abs_sub_abs_le_abs_sub
    ((s - s') / (2 * Real.pi))
    (- beta * X * (Real.exp w - Real.exp (w + h)))
  have hrearrange :
      (s - s') / (2 * Real.pi) -
          (- beta * X * (Real.exp w - Real.exp (w + h))) =
        offDiagonalPhaseDeriv X beta s s' h w := by
    unfold offDiagonalPhaseDeriv
    ring
  have hneg : |- beta * X * (Real.exp w - Real.exp (w + h))| =
      |beta * X * (Real.exp w - Real.exp (w + h))| := by
    rw [show - beta * X * (Real.exp w - Real.exp (w + h)) =
      -(beta * X * (Real.exp w - Real.exp (w + h))) by ring, abs_neg]
  rw [hrearrange, hneg, hlin] at hrev
  have hid : |s - s'| / (2 * Real.pi) - |s - s'| / (4 * Real.pi) =
      |s - s'| / (4 * Real.pi) := by
    field_simp [Real.pi_ne_zero]
    ring
  calc
    |s - s'| / (4 * Real.pi) =
        |s - s'| / (2 * Real.pi) - |s - s'| / (4 * Real.pi) := hid.symm
    _ ≤ |s - s'| / (2 * Real.pi) -
        |beta * X * (Real.exp w - Real.exp (w + h))| :=
      sub_le_sub_left hpert' _
    _ ≤ |offDiagonalPhaseDeriv X beta s s' h w| := hrev

/-- The second and third derivatives have the manuscript size
`O(|β|H)=O(|s-s'|)` on the same support. -/
theorem offDiagonalPhase_higherDerivs_upper
    {X H beta s s' h w : ℝ}
    (hclose : |X * Real.exp w - X * Real.exp (w + h)| ≤ 2 * H)
    (hsep : 8 * Real.pi * |beta| * H ≤ |s - s'|) :
    |offDiagonalPhaseSecond X beta h w| ≤ |s - s'| ∧
      |offDiagonalPhaseSecond X beta h w| ≤ |s - s'| := by
  have hpert : |offDiagonalPhaseSecond X beta h w| ≤ 2 * |beta| * H := by
    unfold offDiagonalPhaseSecond
    have heq : X * (Real.exp w - Real.exp (w + h)) =
        X * Real.exp w - X * Real.exp (w + h) := by ring
    calc
      |beta * X * (Real.exp w - Real.exp (w + h))| =
          |beta| * |X * (Real.exp w - Real.exp (w + h))| := by
        simp only [abs_mul]
        ring
      _ = |beta| * |X * Real.exp w - X * Real.exp (w + h)| := by rw [heq]
      _ ≤ |beta| * (2 * H) :=
        mul_le_mul_of_nonneg_left hclose (abs_nonneg beta)
      _ = 2 * |beta| * H := by ring
  have hpi : 1 ≤ 4 * Real.pi := by nlinarith [Real.pi_gt_three]
  have : 2 * |beta| * H ≤ |s - s'| := by
    have hH0 : 0 ≤ H := by
      nlinarith [abs_nonneg (X * Real.exp w - X * Real.exp (w + h))]
    have hnon : 0 ≤ |beta| * H := mul_nonneg (abs_nonneg beta) hH0
    nlinarith
  exact ⟨hpert.trans this, hpert.trans this⟩

#print axioms offDiagonalPhaseDeriv_lower
#print axioms offDiagonalPhase_higherDerivs_upper

end
end MAPMRTOffDiagonalPhase
