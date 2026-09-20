import GuthMaynardLemma295DualTail

/-!
# Choosing the deep-left contour depth in Lemma 29.5

The source moves to `sigma = -1/2-2n`.  This file makes the choice of `n`
explicit and proves that the lower scale `U T^epsilon`, with
`U >= T^delta`, contributes any requested power saving.
-/

namespace GuthMaynardLemma295TailExponentLedger

open GuthMaynardLemma295DualTail

noncomputable section

def lemma295TailDepth (delta epsilon A : ℝ) : ℕ :=
  Nat.ceil (A / (delta + epsilon))

def lemma295TailDepthStrong (epsilon A : ℝ) : ℕ :=
  Nat.ceil ((A + 5) / (2 * epsilon))

/-- Depth choice that absorbs the coarse residual `T^5` left by the uniform
horizontal/vertical theta polynomial. -/
theorem tailDepthStrong_exponent_le
    {epsilon A : ℝ} (hepsilon : 0 < epsilon) :
    5 + epsilon * deepLeftSigma (lemma295TailDepthStrong epsilon A) ≤
      -A := by
  have hden : 0 < 2 * epsilon := by positivity
  have hratio : (A + 5) / (2 * epsilon) ≤
      (lemma295TailDepthStrong epsilon A : ℝ) := Nat.le_ceil _
  have hmul : A + 5 ≤
      (2 * epsilon) * (lemma295TailDepthStrong epsilon A : ℝ) := by
    simpa [mul_comm] using (div_le_iff₀ hden).mp hratio
  unfold deepLeftSigma
  nlinarith

theorem tailDepth_exponent_le
    {delta epsilon A : ℝ}
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) (hA : 0 < A) :
    (delta + epsilon) * deepLeftSigma (lemma295TailDepth delta epsilon A) ≤
      -A := by
  have hsum : 0 < delta + epsilon := by linarith
  have hratio : A / (delta + epsilon) ≤
      (lemma295TailDepth delta epsilon A : ℝ) := by
    exact Nat.le_ceil _
  have hAn : A ≤ (delta + epsilon) *
      (lemma295TailDepth delta epsilon A : ℝ) := by
    simpa [mul_comm] using (div_le_iff₀ hsum).mp hratio
  unfold deepLeftSigma
  nlinarith [mul_pos hsum (show (0 : ℝ) < 1 / 2 by norm_num)]

theorem sourceScale_deepLeft_rpow_le
    {T U delta epsilon A : ℝ}
    (hT : 1 ≤ T) (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (hA : 0 < A) (hU : Real.rpow T delta ≤ U) :
    Real.rpow (U * Real.rpow T epsilon)
        (deepLeftSigma (lemma295TailDepth delta epsilon A)) ≤
      Real.rpow T (-A) := by
  let n := lemma295TailDepth delta epsilon A
  let sigma := deepLeftSigma n
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hTdelta0 : 0 ≤ Real.rpow T delta := Real.rpow_nonneg hTpos.le _
  have hTepsilon0 : 0 ≤ Real.rpow T epsilon := Real.rpow_nonneg hTpos.le _
  have hU0 : 0 ≤ U := hTdelta0.trans hU
  have hsigma : sigma < 0 := by
    dsimp [sigma, deepLeftSigma]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hscale : Real.rpow T (delta + epsilon) ≤
      U * Real.rpow T epsilon := by
    calc
      Real.rpow T (delta + epsilon) =
          Real.rpow T delta * Real.rpow T epsilon :=
        Real.rpow_add hTpos delta epsilon
      _ ≤ U * Real.rpow T epsilon :=
        mul_le_mul_of_nonneg_right hU hTepsilon0
  have hreverse :
      Real.rpow (U * Real.rpow T epsilon) sigma ≤
        Real.rpow (Real.rpow T (delta + epsilon)) sigma := by
    exact Real.rpow_le_rpow_of_nonpos
      (Real.rpow_pos_of_pos hTpos _)
      hscale hsigma.le
  have hcompose :
      Real.rpow (Real.rpow T (delta + epsilon)) sigma =
        Real.rpow T ((delta + epsilon) * sigma) := by
    exact (Real.rpow_mul hTpos.le (delta + epsilon) sigma).symm
  have hexponent : (delta + epsilon) * sigma ≤ -A := by
    simpa [sigma, n] using tailDepth_exponent_le hdelta hepsilon hA
  calc
    Real.rpow (U * Real.rpow T epsilon) sigma ≤
        Real.rpow (Real.rpow T (delta + epsilon)) sigma := hreverse
    _ = Real.rpow T ((delta + epsilon) * sigma) := hcompose
    _ ≤ Real.rpow T (-A) :=
      Real.rpow_le_rpow_of_exponent_le hT hexponent

/-- The complete coarse power ledger used after integrating the theta
polynomial: its degree `2n+5` cancels against the `U^sigma` tail scale up to
the fixed residual `U^(9/2)`, absorbed by `T^5`. -/
theorem thetaPolynomial_mul_sourceScale_le
    {T U epsilon A : ℝ}
    (hT : 1 ≤ T) (hU : 1 ≤ U) (hUT : U ≤ T)
    (hepsilon : 0 < epsilon) :
    Real.rpow U
        ((2 * lemma295TailDepthStrong epsilon A + 5 : ℕ) : ℝ) *
      Real.rpow (U * Real.rpow T epsilon)
        (deepLeftSigma (lemma295TailDepthStrong epsilon A)) ≤
      Real.rpow T (-A) := by
  let n := lemma295TailDepthStrong epsilon A
  let sigma := deepLeftSigma n
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hTepspos : 0 < Real.rpow T epsilon := Real.rpow_pos_of_pos hTpos _
  have hsplit :
      Real.rpow (U * Real.rpow T epsilon) sigma =
        Real.rpow U sigma * Real.rpow (Real.rpow T epsilon) sigma :=
    Real.mul_rpow hUpos.le hTepspos.le
  have hTcompose :
      Real.rpow (Real.rpow T epsilon) sigma =
        Real.rpow T (epsilon * sigma) :=
    (Real.rpow_mul hTpos.le epsilon sigma).symm
  have hUcombine :
      Real.rpow U (((2 * n + 5 : ℕ) : ℝ)) * Real.rpow U sigma =
        Real.rpow U (9 / 2 : ℝ) := by
    calc
      Real.rpow U (((2 * n + 5 : ℕ) : ℝ)) * Real.rpow U sigma =
          Real.rpow U ((((2 * n + 5 : ℕ) : ℝ)) + sigma) :=
        (Real.rpow_add hUpos _ _).symm
      _ = Real.rpow U (9 / 2 : ℝ) := by
        congr 1
        dsimp [sigma, deepLeftSigma]
        push_cast
        ring
  have hUhalf : Real.rpow U (9 / 2 : ℝ) ≤ Real.rpow U 5 :=
    Real.rpow_le_rpow_of_exponent_le hU (by norm_num)
  have hUpowT : Real.rpow U 5 ≤ Real.rpow T 5 :=
    Real.rpow_le_rpow hUpos.le hUT (by norm_num)
  have hTepow : 0 ≤ Real.rpow T (epsilon * sigma) :=
    Real.rpow_nonneg hTpos.le _
  have hexponent : 5 + epsilon * sigma ≤ -A := by
    simpa [sigma, n] using tailDepthStrong_exponent_le (A := A) hepsilon
  calc
    Real.rpow U (((2 * n + 5 : ℕ) : ℝ)) *
        Real.rpow (U * Real.rpow T epsilon) sigma =
      Real.rpow U (((2 * n + 5 : ℕ) : ℝ)) *
        (Real.rpow U sigma * Real.rpow T (epsilon * sigma)) := by
          rw [hsplit, hTcompose]
    _ = Real.rpow U (9 / 2 : ℝ) * Real.rpow T (epsilon * sigma) := by
      rw [← mul_assoc, hUcombine]
    _ ≤ Real.rpow T 5 * Real.rpow T (epsilon * sigma) := by
      gcongr
      exact hUhalf.trans hUpowT
    _ = Real.rpow T (5 + epsilon * sigma) :=
      (Real.rpow_add hTpos 5 (epsilon * sigma)).symm
    _ ≤ Real.rpow T (-A) :=
      Real.rpow_le_rpow_of_exponent_le hT hexponent

end

end GuthMaynardLemma295TailExponentLedger

#print axioms GuthMaynardLemma295TailExponentLedger.tailDepth_exponent_le
#print axioms GuthMaynardLemma295TailExponentLedger.sourceScale_deepLeft_rpow_le
#print axioms GuthMaynardLemma295TailExponentLedger.tailDepthStrong_exponent_le
#print axioms GuthMaynardLemma295TailExponentLedger.thetaPolynomial_mul_sourceScale_le
