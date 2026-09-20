import GuthMaynardS1Tail

/-!
# The exact power ledger for the source `S₁` contribution

This scratch file contains only reusable consequences of the Proposition 5.1
geometry.  It deliberately does not alter the canonical source files.
-/

namespace GuthMaynardS1PowerLedger

open GuthMaynardS1Tail
open scoped Real

noncomputable section

/-- The tail order is literally two less than the vertical order. -/
theorem decayOrder_sub_two (epsilon : ℝ) :
    s1DecayOrder epsilon - 2 = Nat.ceil (20 / epsilon) := by
  unfold s1DecayOrder
  omega

/-- This is the common twenty-power reserve in both source sectors. -/
theorem twenty_le_epsilon_mul_decayOrder_sub_two
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    20 ≤ epsilon * (s1DecayOrder epsilon - 2 : ℕ) := by
  have h := s1FarExponent_le_neg_twelve hepsilon
  linarith

/-- Exact finite exponent before rounding: `N^2=T^(5/3)` and the three
ordinate sums plus cutoff contribute `T^(4+epsilon)`. -/
theorem exact_finite_exponent_le_neg_fourteen
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    17 / 3 + epsilon - epsilon * s1DecayOrder epsilon ≤ -14 := by
  have h := twenty_add_two_epsilon_le_epsilon_mul_s1DecayOrder hepsilon
  linarith

/-- Exact far exponent after `j=q+2`: cancellation of the cutoff leaves
`N*T^5*T^(-epsilon*q)=T^(35/6-epsilon*q)`. -/
theorem exact_far_exponent_le_neg_fourteen
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    35 / 6 - epsilon * (s1DecayOrder epsilon - 2 : ℕ) ≤ -14 := by
  have h := twenty_le_epsilon_mul_decayOrder_sub_two hepsilon
  linarith

/-- In the Guth--Maynard geometry, `T` is at least one. -/
theorem one_le_sourceT
    {N T : ℝ} (hN : 1 ≤ N)
    (hT : T = Real.rpow N (6 / 5 : ℝ)) :
    1 ≤ T := by
  rw [hT]
  exact Real.one_le_rpow hN (by norm_num)

/-- The source separation scale is no larger than `N`.  The upper bound
`epsilon ≤ 1/2` is stronger than necessary but is the printed range. -/
theorem sourceSeparation_le_N
    {N T epsilon : ℝ} (hN : 1 ≤ N)
    (hT : T = Real.rpow N (6 / 5 : ℝ))
    (hepsilonHalf : epsilon ≤ 1 / 2) :
    Real.rpow T epsilon ≤ N := by
  have hN0 : 0 ≤ N := hN.trans' (by norm_num)
  have hexp : (6 / 5 : ℝ) * epsilon ≤ 1 := by linarith
  rw [hT]
  calc
    Real.rpow (Real.rpow N (6 / 5 : ℝ)) epsilon =
        Real.rpow N ((6 / 5 : ℝ) * epsilon) :=
      (Real.rpow_mul hN0 (6 / 5 : ℝ) epsilon).symm
    _ ≤ Real.rpow N 1 := Real.rpow_le_rpow_of_exponent_le hN hexp
    _ = N := Real.rpow_one N

/-- `N ≤ T` for `T=N^(6/5)`. -/
theorem sourceN_le_T
    {N T : ℝ} (hN : 1 ≤ N)
    (hT : T = Real.rpow N (6 / 5 : ℝ)) :
    N ≤ T := by
  rw [hT]
  calc
    N = Real.rpow N 1 := (Real.rpow_one N).symm
    _ ≤ Real.rpow N (6 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN (by norm_num)

/-- The literal cutoff lies between one and `T^2/N`. -/
theorem sourceCutoff_bounds
    {N T epsilon B : ℝ} (hN : 1 ≤ N)
    (hTdef : T = Real.rpow N (6 / 5 : ℝ))
    (hepsilon0 : 0 ≤ epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hBdef : B = Real.rpow T (1 + epsilon) / N) :
    1 ≤ B ∧ B ≤ T ^ 2 / N := by
  have hTone := one_le_sourceT hN hTdef
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hNleT := sourceN_le_T hN hTdef
  have hTlePow : T ≤ Real.rpow T (1 + epsilon) := by
    calc
      T = Real.rpow T 1 := (Real.rpow_one T).symm
      _ ≤ Real.rpow T (1 + epsilon) :=
        Real.rpow_le_rpow_of_exponent_le hTone (by linarith)
  have hPowUpper : Real.rpow T (1 + epsilon) ≤ T ^ 2 := by
    calc
      Real.rpow T (1 + epsilon) ≤ Real.rpow T (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hTone (by linarith)
      _ = T ^ 2 := Real.rpow_natCast T 2
  rw [hBdef]
  constructor
  · rw [le_div_iff₀ hNpos]
    simpa only [one_mul] using hNleT.trans hTlePow
  · exact div_le_div_of_nonneg_right hPowUpper hNpos.le

/-- Exact conversion of the separation denominator to one `T`-power. -/
theorem sourceSeparation_pow
    {T epsilon : ℝ} (hT : 0 ≤ T) (j : ℕ) :
    (Real.rpow T epsilon) ^ j =
      Real.rpow T (epsilon * j) := by
  calc
    (Real.rpow T epsilon) ^ j =
        Real.rpow (Real.rpow T epsilon) (j : ℝ) :=
      (Real.rpow_natCast _ _).symm
    _ = Real.rpow T (epsilon * j) :=
      (Real.rpow_mul hT epsilon j).symm

/-- The selected tail denominator contains at least `T^20`. -/
theorem sourceTailDenominator_ge_twenty
    {T epsilon : ℝ} (hT : 1 ≤ T) (hepsilon : 0 < epsilon) :
    T ^ 20 ≤ (Real.rpow T epsilon) ^ (s1DecayOrder epsilon - 2) := by
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  rw [sourceSeparation_pow hT0]
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hT
    (twenty_le_epsilon_mul_decayOrder_sub_two hepsilon)

/-- The vertical denominator has the same twenty-power reserve. -/
theorem sourceVerticalDenominator_ge_twenty
    {T epsilon : ℝ} (hT : 1 ≤ T) (hepsilon : 0 < epsilon) :
    T ^ 20 ≤ (Real.rpow T epsilon) ^ s1DecayOrder epsilon := by
  have horder : s1DecayOrder epsilon - 2 ≤ s1DecayOrder epsilon :=
    Nat.sub_le _ _
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  exact (sourceTailDenominator_ge_twenty hT hepsilon).trans
    (pow_le_pow_right₀ (Real.one_le_rpow hT hepsilon.le) horder)

/-- The diagonal `N^{-j}` is at least as strong as the separation decay. -/
theorem sourceDiagonalDenominator_ge_twenty
    {N T epsilon : ℝ} (hN : 1 ≤ N)
    (hTdef : T = Real.rpow N (6 / 5 : ℝ))
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2) :
    T ^ 20 ≤ N ^ s1DecayOrder epsilon := by
  have hTone := one_le_sourceT hN hTdef
  have hT0 : 0 ≤ T := le_trans (by norm_num) hTone
  refine (sourceVerticalDenominator_ge_twenty hTone hepsilon).trans ?_
  exact pow_le_pow_left₀ (Real.rpow_nonneg hT0 epsilon)
    (sourceSeparation_le_N hN hTdef hepsilonHalf)
    (s1DecayOrder epsilon)

/-- The literal outer factor `3`, the bound `W.card ≤ 2T`, and the cutoff
cardinality bound `M.card ≤ 5B` cost at most `120*T^7`.  This deliberately
uses the round exponent seven, matching the source exponent budget. -/
theorem finite_prefactor_le_one_twenty_mul_pow_seven
    {N T B Wc Mc : ℝ} (hN : 1 ≤ N) (hT : 1 ≤ T)
    (hNT : N ≤ T) (hB : B ≤ T ^ 2 / N)
    (hWc0 : 0 ≤ Wc) (hWc : Wc ≤ 2 * T)
    (hMc0 : 0 ≤ Mc) (hMc : Mc ≤ 5 * B) :
    3 * N ^ 3 * (Wc ^ 3 * Mc) ≤ 120 * T ^ 7 := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  have hB0 : 0 ≤ B := by
    have : 0 ≤ 5 * B := hMc0.trans hMc
    linarith
  have hWpow : Wc ^ 3 ≤ (2 * T) ^ 3 :=
    pow_le_pow_left₀ hWc0 hWc 3
  have hNpow : N ^ 2 ≤ T ^ 2 :=
    pow_le_pow_left₀ (le_trans (by norm_num) hN) hNT 2
  have hNB : N * B ≤ T ^ 2 := by
    have := (le_div_iff₀ hNpos).mp hB
    nlinarith
  have hcore : N ^ 3 * B * T ^ 3 ≤ T ^ 7 := by
    calc
      N ^ 3 * B * T ^ 3 = (N ^ 2) * (N * B) * T ^ 3 := by ring
      _ ≤ (T ^ 2) * (T ^ 2) * T ^ 3 := by gcongr
      _ = T ^ 7 := by ring
  calc
    3 * N ^ 3 * (Wc ^ 3 * Mc) ≤
        3 * N ^ 3 * ((2 * T) ^ 3 * (5 * B)) := by gcongr
    _ = 120 * (N ^ 3 * B * T ^ 3) := by ring
    _ ≤ 120 * T ^ 7 := by gcongr

/-- Finite off-diagonal prefactor after division by the vertical denominator. -/
theorem finite_prefactor_over_vertical_le
    {N T B Wc Mc epsilon : ℝ} (hN : 1 ≤ N) (hT : 1 ≤ T)
    (hNT : N ≤ T) (hB : B ≤ T ^ 2 / N)
    (hWc0 : 0 ≤ Wc) (hWc : Wc ≤ 2 * T)
    (hMc0 : 0 ≤ Mc) (hMc : Mc ≤ 5 * B)
    (hepsilon : 0 < epsilon) :
    (3 * N ^ 3 * (Wc ^ 3 * Mc)) /
        (Real.rpow T epsilon) ^ s1DecayOrder epsilon ≤
      120 / T ^ 13 := by
  have hpref := finite_prefactor_le_one_twenty_mul_pow_seven
    hN hT hNT hB hWc0 hWc hMc0 hMc
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hdenpos : 0 < (Real.rpow T epsilon) ^ s1DecayOrder epsilon := by
    exact pow_pos (Real.rpow_pos_of_pos hTpos epsilon) _
  have hden := sourceVerticalDenominator_ge_twenty hT hepsilon
  calc
    (3 * N ^ 3 * (Wc ^ 3 * Mc)) /
          (Real.rpow T epsilon) ^ s1DecayOrder epsilon ≤
        (120 * T ^ 7) /
          (Real.rpow T epsilon) ^ s1DecayOrder epsilon :=
      div_le_div_of_nonneg_right hpref hdenpos.le
    _ ≤ (120 * T ^ 7) / T ^ 20 := by
      exact div_le_div_of_nonneg_left (by positivity) (pow_pos hTpos _) hden
    _ = 120 / T ^ 13 := by
      field_simp

/-- Finite diagonal prefactor after division by `N^j`. -/
theorem finite_prefactor_over_diagonal_le
    {N T B Wc Mc epsilon : ℝ} (hN : 1 ≤ N) (hT : 1 ≤ T)
    (hNT : N ≤ T) (hB : B ≤ T ^ 2 / N)
    (hWc0 : 0 ≤ Wc) (hWc : Wc ≤ 2 * T)
    (hMc0 : 0 ≤ Mc) (hMc : Mc ≤ 5 * B)
    (hTdef : T = Real.rpow N (6 / 5 : ℝ))
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2) :
    (3 * N ^ 3 * (Wc ^ 3 * Mc)) / N ^ s1DecayOrder epsilon ≤
      120 / T ^ 13 := by
  have hpref := finite_prefactor_le_one_twenty_mul_pow_seven
    hN hT hNT hB hWc0 hWc hMc0 hMc
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hden := sourceDiagonalDenominator_ge_twenty
    hN hTdef hepsilon hepsilonHalf
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  calc
    (3 * N ^ 3 * (Wc ^ 3 * Mc)) / N ^ s1DecayOrder epsilon ≤
        (120 * T ^ 7) / N ^ s1DecayOrder epsilon := by
      exact div_le_div_of_nonneg_right hpref (pow_nonneg hNpos.le _)
    _ ≤ (120 * T ^ 7) / T ^ 20 := by
      exact div_le_div_of_nonneg_left (by positivity) (pow_pos hTpos _) hden
    _ = 120 / T ^ 13 := by
      field_simp

/-- A denominator reserve lemma in the exact quotient form needed after the
finite-sector cardinalities have been reduced to a `T^7` numerator. -/
theorem seven_over_vertical_le_inv_thirteen
    {T epsilon : ℝ} (hT : 1 ≤ T) (hepsilon : 0 < epsilon) :
    T ^ 7 / (Real.rpow T epsilon) ^ s1DecayOrder epsilon ≤
      1 / T ^ 13 := by
  have hden := sourceVerticalDenominator_ge_twenty hT hepsilon
  have hpos : 0 < T ^ 20 := pow_pos (lt_of_lt_of_le zero_lt_one hT) _
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  calc
    T ^ 7 / (Real.rpow T epsilon) ^ s1DecayOrder epsilon ≤
        T ^ 7 / T ^ 20 :=
      div_le_div_of_nonneg_left (pow_nonneg hT0 _) hpos hden
    _ = 1 / T ^ 13 := by
      field_simp

/-- The corresponding tail quotient; this is the printed `T^-12` reserve. -/
theorem eight_over_tail_le_inv_twelve
    {T epsilon : ℝ} (hT : 1 ≤ T) (hepsilon : 0 < epsilon) :
    T ^ 8 / (Real.rpow T epsilon) ^ (s1DecayOrder epsilon - 2) ≤
      1 / T ^ 12 := by
  have hden := sourceTailDenominator_ge_twenty hT hepsilon
  have hpos : 0 < T ^ 20 := pow_pos (lt_of_lt_of_le zero_lt_one hT) _
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  calc
    T ^ 8 / (Real.rpow T epsilon) ^ (s1DecayOrder epsilon - 2) ≤
        T ^ 8 / T ^ 20 :=
      div_le_div_of_nonneg_left (pow_nonneg hT0 _) hpos hden
    _ = 1 / T ^ 12 := by
      field_simp

/-- Multiplicative form used after the far-tail algebra has exposed its fixed
seminorm constant. -/
theorem fixed_mul_eight_over_tail_le
    {C T epsilon : ℝ} (hC : 0 ≤ C) (hT : 1 ≤ T)
    (hepsilon : 0 < epsilon) :
    C * (T ^ 8 /
        (Real.rpow T epsilon) ^ (s1DecayOrder epsilon - 2)) ≤
      C / T ^ 12 := by
  calc
    C * (T ^ 8 /
        (Real.rpow T epsilon) ^ (s1DecayOrder epsilon - 2)) ≤
        C * (1 / T ^ 12) := by
      exact mul_le_mul_of_nonneg_left
        (eight_over_tail_le_inv_twelve hT hepsilon) hC
    _ = C / T ^ 12 := by ring

/-- Any nonnegative fixed source constant is absorbed by the four-power gap
between the certified `T^-14` scale and the printed `T^-10` target. -/
theorem fixed_over_fourteen_le_inv_ten
    {C T : ℝ} (hT : 1 ≤ T) (hCT : C ≤ T ^ 4) :
    C / T ^ 14 ≤ 1 / T ^ 10 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  calc
    C / T ^ 14 ≤ T ^ 4 / T ^ 14 :=
      div_le_div_of_nonneg_right hCT (pow_nonneg hTpos.le _)
    _ = 1 / T ^ 10 := by
      field_simp

/-- The exact relation `q+2=j` used to normalize the far summand. -/
theorem tailOrder_add_two (epsilon : ℝ) :
    s1DecayOrder epsilon - 2 + 2 = s1DecayOrder epsilon := by
  unfold s1DecayOrder
  omega

end
end GuthMaynardS1PowerLedger

#print axioms GuthMaynardS1PowerLedger.sourceDiagonalDenominator_ge_twenty
#print axioms GuthMaynardS1PowerLedger.exact_finite_exponent_le_neg_fourteen
#print axioms GuthMaynardS1PowerLedger.exact_far_exponent_le_neg_fourteen
#print axioms GuthMaynardS1PowerLedger.finite_prefactor_over_vertical_le
#print axioms GuthMaynardS1PowerLedger.finite_prefactor_over_diagonal_le
#print axioms GuthMaynardS1PowerLedger.seven_over_vertical_le_inv_thirteen
#print axioms GuthMaynardS1PowerLedger.eight_over_tail_le_inv_twelve
#print axioms GuthMaynardS1PowerLedger.fixed_mul_eight_over_tail_le
#print axioms GuthMaynardS1PowerLedger.fixed_over_fourteen_le_inv_ten
