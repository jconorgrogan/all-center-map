import GuthMaynardJutilaReflection2941
import GuthMaynardLemma295FloorTruncation

/-!
# Exact scale ledger for the corrected Lemma 29.5 interface

The certified chain uses only the source's equation (29.40),
`M=T^(1+epsilon)/N`, inside `1 <= N <= T^(1+epsilon)`.  These elementary
facts keep the contour estimates tied to that literal scale.
-/

namespace GuthMaynardLemma295ExactMScale

open GuthMaynardJutilaReflection2941

noncomputable section

 theorem sourceReflectionNumerator29_40_pos
    {T epsilon : ℝ} (hT : 0 < T) :
    0 < sourceReflectionNumerator29_40 T epsilon := by
  unfold sourceReflectionNumerator29_40
  exact Real.rpow_pos_of_pos hT _

 theorem reflectedLength29_40_pos
    {T epsilon N : ℝ} (hT : 0 < T) (hN : 0 < N) :
    0 < reflectedLength29_40 T epsilon N := by
  unfold reflectedLength29_40
  exact div_pos (sourceReflectionNumerator29_40_pos hT) hN

 theorem one_le_reflectedLength29_40
    {T epsilon N : ℝ} (hT : 0 < T) (hN : 0 < N)
    (hNcap : N ≤ sourceReflectionNumerator29_40 T epsilon) :
    1 ≤ reflectedLength29_40 T epsilon N := by
  unfold reflectedLength29_40
  exact (le_div_iff₀ hN).2 (by simpa using hNcap)

 theorem reflectedLength29_40_mul_N
    {T epsilon N : ℝ} (hN : N ≠ 0) :
    reflectedLength29_40 T epsilon N * N =
      sourceReflectionNumerator29_40 T epsilon := by
  unfold reflectedLength29_40
  field_simp

 theorem N_mul_reflectedLength29_40
    {T epsilon N : ℝ} (hN : N ≠ 0) :
    N * reflectedLength29_40 T epsilon N =
      sourceReflectionNumerator29_40 T epsilon := by
  rw [mul_comm, reflectedLength29_40_mul_N hN]

 theorem floor_reflectedLength_le
    {T epsilon N : ℝ}
    (hM0 : 0 ≤ reflectedLength29_40 T epsilon N) :
    ((⌊reflectedLength29_40 T epsilon N⌋₊ : ℕ) : ℝ) ≤
      reflectedLength29_40 T epsilon N := by
  exact Nat.floor_le hM0

 theorem floor_reflectedLength_add_one_le_two_mul
    {T epsilon N : ℝ} (hM : 1 ≤ reflectedLength29_40 T epsilon N) :
    ((⌊reflectedLength29_40 T epsilon N⌋₊ + 1 : ℕ) : ℝ) ≤
      2 * reflectedLength29_40 T epsilon N := by
  have hfloor := floor_reflectedLength_le (T := T) (epsilon := epsilon) (N := N)
    (by linarith)
  push_cast
  linarith

end
end GuthMaynardLemma295ExactMScale

#print axioms GuthMaynardLemma295ExactMScale.one_le_reflectedLength29_40
#print axioms GuthMaynardLemma295ExactMScale.N_mul_reflectedLength29_40
#print axioms GuthMaynardLemma295ExactMScale.floor_reflectedLength_add_one_le_two_mul
