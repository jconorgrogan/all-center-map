import Mathlib

/-!
# Literal scale algebra in Jutila--Heath--Brown Lemma 29.10

The two middle subranges meet at

`K = 4^(1/3) T^(2(1+epsilon)/3)`.

If `A=T^(1+epsilon)` and `M=A/N`, the identity `K^3=4A^2`
shows that `K ≤ N` is exactly the side on which `4M^2 ≤ N`, while
`N ≤ K` sends the comparison length `4M^2` back into the already
controlled range.  These are the scale implications used immediately before
and after equation (29.42).
-/

namespace GuthMaynardLemma2910SourceScale

noncomputable section

def sourceReflectionNumerator (T epsilon : ℝ) : ℝ :=
  Real.rpow T (1 + epsilon)

def sourceCubicThreshold (T epsilon : ℝ) : ℝ :=
  Real.rpow 4 (1 / 3 : ℝ) *
    Real.rpow T (2 * (1 + epsilon) / 3)

theorem sourceCubicThreshold_cube
    {T epsilon : ℝ} (hT : 0 < T) :
    sourceCubicThreshold T epsilon ^ 3 =
      4 * sourceReflectionNumerator T epsilon ^ 2 := by
  unfold sourceCubicThreshold sourceReflectionNumerator
  rw [mul_pow]
  have hfour : Real.rpow 4 (1 / 3 : ℝ) ^ 3 =
      Real.rpow 4 ((1 / 3 : ℝ) * 3) :=
    (Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 4)
      (1 / 3 : ℝ) 3).symm
  have hTthree : Real.rpow T (2 * (1 + epsilon) / 3) ^ 3 =
      Real.rpow T ((2 * (1 + epsilon) / 3) * 3) :=
    (Real.rpow_mul_natCast hT.le (2 * (1 + epsilon) / 3) 3).symm
  have hTtwo : Real.rpow T ((1 + epsilon) * 2) =
      Real.rpow T (1 + epsilon) ^ 2 :=
    Real.rpow_mul_natCast hT.le (1 + epsilon) 2
  calc
    Real.rpow 4 (1 / 3 : ℝ) ^ 3 *
          Real.rpow T (2 * (1 + epsilon) / 3) ^ 3 =
        Real.rpow 4 ((1 / 3 : ℝ) * 3) *
          Real.rpow T ((2 * (1 + epsilon) / 3) * 3) := by
      rw [hfour, hTthree]
    _ = 4 * Real.rpow T ((1 + epsilon) * 2) := by
      congr 1
      · norm_num
      · congr 1 <;> ring
    _ = 4 * Real.rpow T (1 + epsilon) ^ 2 := by
      rw [hTtwo]

theorem sourceCubicThreshold_pos
    {T epsilon : ℝ} (hT : 0 < T) :
    0 < sourceCubicThreshold T epsilon := by
  unfold sourceCubicThreshold
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.rpow_pos_of_pos hT _)

theorem sourceReflectionNumerator_pos
    {T epsilon : ℝ} (hT : 0 < T) :
    0 < sourceReflectionNumerator T epsilon := by
  exact Real.rpow_pos_of_pos hT _

/-- First middle subrange: the reflected square may be powered directly
against the original length. -/
theorem direct_reflected_scale_le
    {A K N : ℝ} (hK : 0 < K) (hN : 0 < N)
    (hcube : K ^ 3 = 4 * A ^ 2) (hKN : K ≤ N) :
    4 * (A / N) ^ 2 ≤ N := by
  have hcubes : K ^ 3 ≤ N ^ 3 := by
    exact pow_le_pow_left₀ hK.le hKN 3
  have hNsq : 0 < N ^ 2 := sq_pos_of_pos hN
  rw [div_pow]
  rw [show 4 * (A ^ 2 / N ^ 2) = (4 * A ^ 2) / N ^ 2 by ring]
  apply (div_le_iff₀ hNsq).2
  rw [← hcube]
  nlinarith

/-- Second middle subrange: the new length `4M^2` lies on the controlled
side of the same cubic threshold. -/
theorem threshold_le_bootstrap_reflected_scale
    {A K N : ℝ} (hK : 0 < K) (hN : 0 < N)
    (hcube : K ^ 3 = 4 * A ^ 2) (hNK : N ≤ K) :
    K ≤ 4 * (A / N) ^ 2 := by
  have hcubes : N ^ 3 ≤ K ^ 3 := by
    exact pow_le_pow_left₀ hN.le hNK 3
  have hNsq : 0 < N ^ 2 := sq_pos_of_pos hN
  rw [div_pow]
  rw [show 4 * (A ^ 2 / N ^ 2) = (4 * A ^ 2) / N ^ 2 by ring]
  apply (le_div_iff₀ hNsq).2
  rw [← hcube]
  have hsquares : N ^ 2 ≤ K ^ 2 :=
    pow_le_pow_left₀ hN.le hNK 2
  have hmul := mul_le_mul_of_nonneg_left hsquares hK.le
  nlinarith

theorem source_direct_reflected_scale_le
    {T epsilon N : ℝ} (hT : 0 < T) (hN : 0 < N)
    (hthreshold : sourceCubicThreshold T epsilon ≤ N) :
    4 * (sourceReflectionNumerator T epsilon / N) ^ 2 ≤ N := by
  exact direct_reflected_scale_le
    (sourceCubicThreshold_pos hT) hN
    (sourceCubicThreshold_cube hT) hthreshold

theorem source_threshold_le_bootstrap_reflected_scale
    {T epsilon N : ℝ} (hT : 0 < T) (hN : 0 < N)
    (hthreshold : N ≤ sourceCubicThreshold T epsilon) :
    sourceCubicThreshold T epsilon ≤
      4 * (sourceReflectionNumerator T epsilon / N) ^ 2 := by
  exact threshold_le_bootstrap_reflected_scale
    (sourceCubicThreshold_pos hT) hN
    (sourceCubicThreshold_cube hT) hthreshold

#print axioms sourceCubicThreshold_cube
#print axioms direct_reflected_scale_le
#print axioms threshold_le_bootstrap_reflected_scale
#print axioms source_direct_reflected_scale_le
#print axioms source_threshold_le_bootstrap_reflected_scale

end

end GuthMaynardLemma2910SourceScale
