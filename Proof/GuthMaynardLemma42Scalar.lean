import GuthMaynardSectionFourPoisson
import Mathlib.Algebra.Order.Chebyshev

/-!
# Guth--Maynard Lemma 4.2: scalar core

This file formalizes the load-bearing algebra in the proof of Lemma 4.2.
The variables `a`, `b`, `c` are respectively `x₁²`, `∑_{i≥2}xᵢ²`, and
`∑_{i≥2}xᵢ⁶`; `k` is the number of singular values.  Hölder supplies
`b³ ≤ k² c`.  The conclusion is exactly the maximum inequality on the
last displayed line of the source proof, before taking sixth roots.
-/

namespace GuthMaynardLemma42Scalar

open scoped BigOperators

private theorem large_coordinate_defect
    {a b c k : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hk : 0 < k)
    (hholder : b ^ 3 ≤ k ^ 2 * c)
    (hlarge : 2 * (a + b) < k * a) :
    a ^ 3 ≤ 4 * ((a ^ 3 + c) - (a + b) ^ 3 / k ^ 2) := by
  have hk2 : 0 < k ^ 2 := sq_pos_of_pos hk
  rw [show 4 * ((a ^ 3 + c) - (a + b) ^ 3 / k ^ 2) =
      4 * (a ^ 3 + c) - 4 * (a + b) ^ 3 / k ^ 2 by ring]
  rw [le_sub_iff_add_le]
  field_simp [ne_of_gt hk2]
  have hs : (2 * (a + b)) ^ 2 ≤ (k * a) ^ 2 := by nlinarith
  have hquad : 4 * (a + b) ^ 2 ≤ k ^ 2 * a ^ 2 := by nlinarith
  have hmul : 4 * a * (a + b) ^ 2 ≤ k ^ 2 * a ^ 3 := by
    calc
      4 * a * (a + b) ^ 2 = a * (4 * (a + b) ^ 2) := by ring
      _ ≤ a * (k ^ 2 * a ^ 2) := mul_le_mul_of_nonneg_left hquad ha
      _ = k ^ 2 * a ^ 3 := by ring
  nlinarith [mul_nonneg ha (sq_nonneg (a + b)),
    mul_nonneg hb (sq_nonneg b),
    mul_nonneg (sq_nonneg k) (mul_nonneg ha (sq_nonneg a))]

/-- Exact polynomial maximum inequality in the proof of source Lemma 4.2. -/
theorem lemma42_scalar_maximum
    {a b c k : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hk : 0 < k)
    (hholder : b ^ 3 ≤ k ^ 2 * c) :
    a ^ 3 ≤ max
      (4 * ((a ^ 3 + c) - (a + b) ^ 3 / k ^ 2))
      (8 * (a + b) ^ 3 / k ^ 3) := by
  by_cases hsmall : k * a ≤ 2 * (a + b)
  · apply le_trans ?_ (le_max_right _ _)
    have hka : 0 ≤ k * a := mul_nonneg hk.le ha
    have hcub := pow_le_pow_left₀ hka hsmall 3
    have hk3 : 0 < k ^ 3 := pow_pos hk 3
    rw [show (k * a) ^ 3 = k ^ 3 * a ^ 3 by ring,
      show (2 * (a + b)) ^ 3 = 8 * (a + b) ^ 3 by ring] at hcub
    exact (le_div_iff₀ hk3).2 (by simpa [mul_comm] using hcub)
  · apply le_trans (large_coordinate_defect ha hb hk hholder (lt_of_not_ge hsmall))
      (le_max_left _ _)

/-- The Hölder/Jensen input used by Lemma 4.2, with the source's deliberately
weaker denominator `k²` rather than `(k-1)²`. -/
theorem holder_erase_with_total_card
    {I : Type*} [Fintype I] [DecidableEq I]
    (x : I → ℝ) (i₀ : I) :
    (∑ i ∈ (Finset.univ.erase i₀), x i ^ 2) ^ 3 ≤
      (Fintype.card I : ℝ) ^ 2 *
        ∑ i ∈ (Finset.univ.erase i₀), x i ^ 6 := by
  let s : Finset I := Finset.univ.erase i₀
  have hpow := pow_sum_le_card_mul_sum_pow
    (s := s) (f := fun i => x i ^ 2) (fun i hi => sq_nonneg (x i)) 2
  have hcard : (s.card : ℝ) ^ 2 ≤ (Fintype.card I : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg s.card)
      (by exact_mod_cast s.card_le_univ) 2
  calc
    (∑ i ∈ s, x i ^ 2) ^ 3 ≤
        (s.card : ℝ) ^ 2 * ∑ i ∈ s, (x i ^ 2) ^ 3 := hpow
    _ ≤ (Fintype.card I : ℝ) ^ 2 * ∑ i ∈ s, (x i ^ 2) ^ 3 := by
      gcongr
    _ = (Fintype.card I : ℝ) ^ 2 * ∑ i ∈ s, x i ^ 6 := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Finite-family form of the exact maximum inequality in Lemma 4.2. -/
theorem lemma42_finite_maximum
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (x : I → ℝ) (i₀ : I) :
    x i₀ ^ 6 ≤
      max
        (4 * ((∑ i, x i ^ 6) - (∑ i, x i ^ 2) ^ 3 /
          (Fintype.card I : ℝ) ^ 2))
        (8 * (∑ i, x i ^ 2) ^ 3 / (Fintype.card I : ℝ) ^ 3) := by
  let b := ∑ i ∈ (Finset.univ.erase i₀), x i ^ 2
  let c := ∑ i ∈ (Finset.univ.erase i₀), x i ^ 6
  have hk : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos
  have hb : 0 ≤ b := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hh : b ^ 3 ≤ (Fintype.card I : ℝ) ^ 2 * c := by
    exact holder_erase_with_total_card x i₀
  have h := lemma42_scalar_maximum (sq_nonneg (x i₀)) hb hk hh
  have hsum2 : x i₀ ^ 2 + b = ∑ i, x i ^ 2 := by
    rw [show (∑ i, x i ^ 2) = x i₀ ^ 2 + ∑ i ∈ Finset.univ.erase i₀, x i ^ 2 by
      rw [← Finset.add_sum_erase Finset.univ (fun i => x i ^ 2) (Finset.mem_univ i₀)]]
  have hsum6 : (x i₀ ^ 2) ^ 3 + c = ∑ i, x i ^ 6 := by
    rw [show (∑ i, x i ^ 6) = x i₀ ^ 6 + ∑ i ∈ Finset.univ.erase i₀, x i ^ 6 by
      rw [← Finset.add_sum_erase Finset.univ (fun i => x i ^ 6) (Finset.mem_univ i₀)]]
    congr 1
    ring
  rw [hsum2, hsum6] at h
  convert h using 1 <;> ring

/-- Literal scalar inequality (4.3), including the sixth- and square-root
conversion.  This is the complete numerical heart of Lemma 4.2. -/
theorem lemma42_equation4_3
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) (i₀ : I) :
    x i₀ ≤
      2 * ((∑ i, x i ^ 6) - (∑ i, x i ^ 2) ^ 3 /
        (Fintype.card I : ℝ) ^ 2) ^ (1 / 6 : ℝ) +
      2 * Real.sqrt ((∑ i, x i ^ 2) / (Fintype.card I : ℝ)) := by
  let S₂ : ℝ := ∑ i, x i ^ 2
  let S₆ : ℝ := ∑ i, x i ^ 6
  let k : ℝ := Fintype.card I
  let D : ℝ := S₆ - S₂ ^ 3 / k ^ 2
  let A : ℝ := S₂ / k
  have hk : 0 < k := by
    dsimp [k]
    exact_mod_cast Fintype.card_pos
  have hS₂ : 0 ≤ S₂ := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hA : 0 ≤ A := div_nonneg hS₂ hk.le
  have hjensen : S₂ ^ 3 / k ^ 2 ≤ S₆ := by
    have h := pow_sum_div_card_le_sum_pow
      (s := (Finset.univ : Finset I)) (f := fun i => x i ^ 2)
      (fun i hi => sq_nonneg (x i)) 2
    change S₂ ^ 3 / k ^ 2 ≤ ∑ i, (x i ^ 2) ^ 3 at h
    refine h.trans_eq ?_
    dsimp [S₆]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hD : 0 ≤ D := sub_nonneg.mpr hjensen
  have hmax := lemma42_finite_maximum x i₀
  change x i₀ ^ 6 ≤ max (4 * D) (8 * S₂ ^ 3 / k ^ 3) at hmax
  rw [le_max_iff] at hmax
  rcases hmax with hdefect | havg
  · have hpow : x i₀ ^ 6 ≤ (2 * D ^ (1 / 6 : ℝ)) ^ 6 := by
      have hroot : (D ^ (1 / 6 : ℝ)) ^ (6 : ℕ) = D := by
        convert Real.rpow_inv_natCast_pow hD (by norm_num : (6 : ℕ) ≠ 0) using 1 <;>
          norm_num
      calc
        x i₀ ^ 6 ≤ 4 * D := hdefect
        _ ≤ 64 * D := by nlinarith
        _ = (2 * D ^ (1 / 6 : ℝ)) ^ 6 := by
          rw [mul_pow, hroot]
          norm_num
    have hxroot : x i₀ ≤ 2 * D ^ (1 / 6 : ℝ) :=
      (pow_le_pow_iff_left₀ (hx i₀)
        (mul_nonneg (by norm_num) (Real.rpow_nonneg hD _)) (by norm_num : (6 : ℕ) ≠ 0)).mp hpow
    change x i₀ ≤ 2 * D ^ (1 / 6 : ℝ) + 2 * Real.sqrt A
    exact hxroot.trans (le_add_of_nonneg_right (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
  · have havg' : x i₀ ^ 6 ≤ 8 * A ^ 3 := by
      convert havg using 1
      dsimp [A]
      field_simp [ne_of_gt hk]
    have hpow : x i₀ ^ 6 ≤ (2 * Real.sqrt A) ^ 6 := by
      calc
        x i₀ ^ 6 ≤ 8 * A ^ 3 := havg'
        _ ≤ 64 * A ^ 3 := by nlinarith [pow_nonneg hA 3]
        _ = (2 * Real.sqrt A) ^ 6 := by
          rw [show (2 * Real.sqrt A) ^ 6 = 64 * (Real.sqrt A ^ 2) ^ 3 by ring,
            Real.sq_sqrt hA]
    have hxroot : x i₀ ≤ 2 * Real.sqrt A :=
      (pow_le_pow_iff_left₀ (hx i₀)
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (by norm_num : (6 : ℕ) ≠ 0)).mp hpow
    change x i₀ ≤ 2 * D ^ (1 / 6 : ℝ) + 2 * Real.sqrt A
    exact hxroot.trans (le_add_of_nonneg_left
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hD _)))

end GuthMaynardLemma42Scalar

#print axioms GuthMaynardLemma42Scalar.lemma42_scalar_maximum
#print axioms GuthMaynardLemma42Scalar.lemma42_finite_maximum
#print axioms GuthMaynardLemma42Scalar.lemma42_equation4_3
