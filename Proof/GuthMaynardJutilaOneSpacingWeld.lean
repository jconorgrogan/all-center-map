import GuthMaynardJutilaSpacingPartition

/-!
# The deterministic one-spacing weld after Lemma 29.10

The source restates the `T^delta`-separated Lemma 29.10 as the one-separated
Lemma 29.26.  After the exact coloring/energy partition, this file performs
the remaining cardinality and exponent ledger.  Choosing `delta ≤ eta/4`
pays the square of the color count inside the requested `T^eta` loss.
-/

namespace GuthMaynardJutilaOneSpacingWeld

open scoped BigOperators
open CGLProofDAG
open GuthMaynardJutilaSpacingPartition
open GuthMaynardLengthComparison

noncomputable section

def jutilaThreeTermShape (T M : ℝ) (W : Finset ℝ) : ℝ :=
  (W.card : ℝ) * M +
    Real.rpow (W.card : ℝ) (5 / 4 : ℝ) * Real.rpow T (1 / 2 : ℝ) +
    (W.card : ℝ) ^ 2

theorem colorFiber_subset
    {m : ℕ} (color : ℝ → Fin m) (W : Finset ℝ) (i : Fin m) :
    colorFiber color W i ⊆ W := Finset.filter_subset _ _

theorem jutilaThreeTermShape_nonneg
    {T M : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M) (W : Finset ℝ) :
    0 ≤ jutilaThreeTermShape T M W := by
  unfold jutilaThreeTermShape
  have hcard : 0 ≤ (W.card : ℝ) := by positivity
  have hcardPow : 0 ≤ Real.rpow (W.card : ℝ) (5 / 4 : ℝ) :=
    Real.rpow_nonneg hcard _
  have hTpow : 0 ≤ Real.rpow T (1 / 2 : ℝ) := Real.rpow_nonneg hT _
  exact add_nonneg
    (add_nonneg (mul_nonneg hcard hM) (mul_nonneg hcardPow hTpow))
    (sq_nonneg (W.card : ℝ))

theorem jutilaThreeTermShape_mono
    {T M : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M)
    {A B : Finset ℝ} (hAB : A ⊆ B) :
    jutilaThreeTermShape T M A ≤ jutilaThreeTermShape T M B := by
  have hcardNat : A.card ≤ B.card := Finset.card_le_card hAB
  have hcard : (A.card : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hcardNat
  have hA0 : 0 ≤ (A.card : ℝ) := by positivity
  have hB0 : 0 ≤ (B.card : ℝ) := by positivity
  have hpow : Real.rpow (A.card : ℝ) (5 / 4 : ℝ) ≤
      Real.rpow (B.card : ℝ) (5 / 4 : ℝ) :=
    Real.rpow_le_rpow hA0 hcard (by norm_num)
  unfold jutilaThreeTermShape
  have hTpow : 0 ≤ Real.rpow T (1 / 2 : ℝ) := Real.rpow_nonneg hT _
  nlinarith [mul_le_mul_of_nonneg_right hcard hM,
    mul_le_mul_of_nonneg_right hpow hTpow,
    pow_le_pow_left₀ hA0 hcard 2]

theorem sum_colorFiber_shapes_le
    {m : ℕ} (color : ℝ → Fin m)
    {T M : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M) (W : Finset ℝ) :
    (∑ i : Fin m, jutilaThreeTermShape T M (colorFiber color W i)) ≤
      (m : ℝ) * jutilaThreeTermShape T M W := by
  calc
    (∑ i : Fin m, jutilaThreeTermShape T M (colorFiber color W i)) ≤
        ∑ _i : Fin m, jutilaThreeTermShape T M W := by
      apply Finset.sum_le_sum
      intro i hi
      exact jutilaThreeTermShape_mono hT hM (colorFiber_subset color W i)
    _ = (m : ℝ) * jutilaThreeTermShape T M W := by simp

/-- If Lemma 29.10 is available on every long-spaced color, its one-spaced
form follows with explicit constant `9C`.  No analytic estimate is used in
this theorem. -/
theorem oneSeparated_jutila_of_powerSeparated_fibers
    {T M delta eta C : ℝ} {W : Finset ℝ}
    (hT : 1 ≤ T) (hM : 0 ≤ M) (hdelta : 0 ≤ delta)
    (heta : 0 ≤ eta) (hdeltaEta : delta ≤ eta / 4)
    (hC : 0 ≤ C) (hsep : OneSeparated W)
    (hfiberBound : ∀ i : Fin (powerSpacingColorCount T delta),
      jutilaSecondMoment M
          (colorFiber (powerSpacingColor T delta) W i) ≤
        C * Real.rpow T (eta / 2) *
          jutilaThreeTermShape T M
            (colorFiber (powerSpacingColor T delta) W i)) :
    jutilaSecondMoment M W ≤
      9 * C * Real.rpow T eta * jutilaThreeTermShape T M W := by
  let q : ℝ := powerSpacingColorCount T delta
  have hq := powerSpacingColorCount_cast_le hT hdelta
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hshape0 : 0 ≤ jutilaThreeTermShape T M W :=
    jutilaThreeTermShape_nonneg (le_trans zero_le_one hT) hM W
  have hsumShape := sum_colorFiber_shapes_le
    (powerSpacingColor T delta) (le_trans zero_le_one hT) hM W
  have hpartition := jutilaSecondMoment_le_powerSpacingColor_sum M T delta W
  have hsumBound :
      (∑ i : Fin (powerSpacingColorCount T delta),
        jutilaSecondMoment M
          (colorFiber (powerSpacingColor T delta) W i)) ≤
      C * Real.rpow T (eta / 2) *
        (q * jutilaThreeTermShape T M W) := by
    calc
      _ ≤ ∑ i : Fin (powerSpacingColorCount T delta),
          C * Real.rpow T (eta / 2) *
            jutilaThreeTermShape T M
              (colorFiber (powerSpacingColor T delta) W i) :=
        Finset.sum_le_sum (fun i hi => hfiberBound i)
      _ = C * Real.rpow T (eta / 2) *
          ∑ i : Fin (powerSpacingColorCount T delta),
            jutilaThreeTermShape T M
              (colorFiber (powerSpacingColor T delta) W i) := by
        rw [Finset.mul_sum]
      _ ≤ C * Real.rpow T (eta / 2) *
          (q * jutilaThreeTermShape T M W) := by
        exact mul_le_mul_of_nonneg_left hsumShape
          (mul_nonneg hC (Real.rpow_nonneg (le_trans zero_le_one hT) _))
  have hqSq : q ^ 2 ≤ 9 * Real.rpow T (2 * delta) := by
    have hpow0 : 0 ≤ Real.rpow T delta :=
      Real.rpow_nonneg (le_trans zero_le_one hT) _
    have hsquare := pow_le_pow_left₀ hq0 hq 2
    calc
      q ^ 2 ≤ (3 * Real.rpow T delta) ^ 2 := hsquare
      _ = 9 * Real.rpow T (2 * delta) := by
        rw [mul_pow]
        norm_num
        rw [show 2 * delta = delta * (2 : ℕ) by ring,
          Real.rpow_mul_natCast (le_trans zero_le_one hT)]
  have hexponent : eta / 2 + 2 * delta ≤ eta := by linarith
  have hrpowExp : Real.rpow T (eta / 2 + 2 * delta) ≤ Real.rpow T eta :=
    Real.rpow_le_rpow_of_exponent_le hT hexponent
  calc
    jutilaSecondMoment M W ≤ q *
        ∑ i : Fin (powerSpacingColorCount T delta),
          jutilaSecondMoment M
            (colorFiber (powerSpacingColor T delta) W i) := by
      simpa [q] using hpartition
    _ ≤ q * (C * Real.rpow T (eta / 2) *
        (q * jutilaThreeTermShape T M W)) :=
      mul_le_mul_of_nonneg_left hsumBound hq0
    _ = C * (q ^ 2) * Real.rpow T (eta / 2) *
        jutilaThreeTermShape T M W := by ring
    _ ≤ C * (9 * Real.rpow T (2 * delta)) *
        Real.rpow T (eta / 2) * jutilaThreeTermShape T M W := by
      apply mul_le_mul_of_nonneg_right _ hshape0
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hqSq hC)
        (Real.rpow_nonneg (le_trans zero_le_one hT) _)
    _ = 9 * C * Real.rpow T (eta / 2 + 2 * delta) *
        jutilaThreeTermShape T M W := by
      have hadd : Real.rpow T (eta / 2 + 2 * delta) =
          Real.rpow T (eta / 2) * Real.rpow T (2 * delta) :=
        Real.rpow_add (lt_of_lt_of_le zero_lt_one hT) _ _
      rw [hadd]
      ring
    _ ≤ 9 * C * Real.rpow T eta * jutilaThreeTermShape T M W := by
      gcongr

end

end GuthMaynardJutilaOneSpacingWeld

#print axioms GuthMaynardJutilaOneSpacingWeld.oneSeparated_jutila_of_powerSeparated_fibers
