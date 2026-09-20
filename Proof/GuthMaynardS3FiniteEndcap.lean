import GuthMaynardAffineCrudeBound
import GuthMaynardSourceDyadicRanges
import GuthMaynardAffineSmoothingNorms

open scoped BigOperators Real
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

private theorem card_sourcePositiveDyadicRange_cast_le_two_mul
    {M : ℕ} (hM : 1 ≤ M) :
    ((sourcePositiveDyadicRange M).card : ℝ) ≤ 2 * (M : ℝ) := by
  rw [sourcePositiveDyadicRange]
  have hcard := Int.card_Icc (M : ℤ) (2 * M : ℤ)
  have hnonneg : (0 : ℤ) ≤ (2 * M : ℤ) + 1 - (M : ℤ) := by omega
  have hcast :
      ((((2 * M : ℤ) + 1 - (M : ℤ)).toNat : ℕ) : ℝ) =
        ((2 * M : ℤ) + 1 - (M : ℤ) : ℤ) := by
    exact_mod_cast (Int.toNat_of_nonneg hnonneg)
  rw [hcard, hcast]
  push_cast
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  linarith

private theorem card_sourceCenteredRange_16_mul_cast_le
    {M : ℕ} (hM : 1 ≤ M) :
    ((sourceCenteredRange (16 * M)).card : ℝ) ≤ 33 * (M : ℝ) := by
  rw [sourceCenteredRange]
  change
    (((Finset.Icc (-(16 * (M : ℤ))) (16 * (M : ℤ))).card : ℕ) : ℝ) ≤
      33 * (M : ℝ)
  have hcard := Int.card_Icc (-(16 * M : ℤ)) (16 * M : ℤ)
  have hnonneg :
      (0 : ℤ) ≤ (16 * M : ℤ) + 1 - (-(16 * M : ℤ)) := by omega
  have hcast :
      ((((16 * M : ℤ) + 1 - (-(16 * M : ℤ))).toNat : ℕ) : ℝ) =
        ((16 * M : ℤ) + 1 - (-(16 * M : ℤ)) : ℤ) := by
    exact_mod_cast (Int.toNat_of_nonneg hnonneg)
  rw [hcard, hcast]
  push_cast
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  linarith

/-- Literal finite affine endcap controlled by the source L2 mass. -/
theorem sourcePositiveCentered_endcap_energy_le
    {T S F : ℝ} {M : ℕ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S F f) (hM : 1 ≤ M) :
    sourceFiniteAffineEnergy (sourcePositiveDyadicRange M)
        (sourcePositiveDyadicRange M) (sourceCenteredRange (16 * M)) f ≤
      34848 * (M : ℝ) ^ 6 * (∫ u : ℝ, f u ^ 2) := by
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hm1 : ∀ m ∈ sourcePositiveDyadicRange M, m ≠ 0 :=
    fun m hm => sourcePositiveDyadicRange_ne_zero hMpos hm
  have hm2 := hm1
  have hcard1 := card_sourcePositiveDyadicRange_cast_le_two_mul hM
  have hcard2 := hcard1
  have hcard3 := card_sourceCenteredRange_16_mul_cast_le hM
  have hratio :
      ∀ m1 ∈ sourcePositiveDyadicRange M,
        ∀ m2 ∈ sourcePositiveDyadicRange M,
          |(m2 : ℝ) / (m1 : ℝ)| ≤ 2 := by
    intro m1 hm1mem m2 hm2mem
    have hm1bounds := sourcePositiveDyadicRange_abs_bounds hMpos hm1mem
    have hm2bounds := sourcePositiveDyadicRange_abs_bounds hMpos hm2mem
    have hm1den : 0 < |(m1 : ℝ)| := by
      exact abs_pos.mpr (by exact_mod_cast hm1 m1 hm1mem)
    have hMreal : 0 < (M : ℝ) := by exact_mod_cast hMpos
    rw [abs_div]
    calc
      |(m2 : ℝ)| / |(m1 : ℝ)| ≤
          (2 * (M : ℝ)) / |(m1 : ℝ)| :=
        div_le_div_of_nonneg_right hm2bounds.2 (abs_nonneg _)
      _ ≤ (2 * (M : ℝ)) / (M : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hMreal hm1bounds.1
      _ = 2 := by field_simp
  have hbase := sourceFiniteAffineEnergy_crude_card
    (sourcePositiveDyadicRange M) (sourcePositiveDyadicRange M)
      (sourceCenteredRange (16 * M)) f hf.squareIntegrable hm1 hm2
      (by norm_num : (0 : ℝ) ≤ 2) hratio
  let K : ℝ :=
    ((sourcePositiveDyadicRange M).card *
      (sourcePositiveDyadicRange M).card *
      (sourceCenteredRange (16 * M)).card : ℕ)
  have hK : K ≤ 132 * (M : ℝ) ^ 3 := by
    dsimp [K]
    push_cast
    have hc1 : 0 ≤ ((sourcePositiveDyadicRange M).card : ℝ) := by positivity
    have hc2 : 0 ≤ ((sourcePositiveDyadicRange M).card : ℝ) := by positivity
    have hc3 : 0 ≤ ((sourceCenteredRange (16 * M)).card : ℝ) := by positivity
    calc
      (sourcePositiveDyadicRange M).card *
          (sourcePositiveDyadicRange M).card *
          (sourceCenteredRange (16 * M)).card ≤
          (2 * (M : ℝ)) * (2 * (M : ℝ)) * (33 * (M : ℝ)) :=
        mul_le_mul
          (mul_le_mul hcard1 hcard2 hc2 (by positivity))
          hcard3 hc3 (by positivity)
      _ = 132 * (M : ℝ) ^ 3 := by ring
  have hK0 : 0 ≤ K := by positivity
  have hKsq : K ^ 2 ≤ (132 * (M : ℝ) ^ 3) ^ 2 :=
    pow_le_pow_left₀ hK0 hK 2
  have hI0 : 0 ≤ ∫ u : ℝ, f u ^ 2 :=
    integral_nonneg fun u => sq_nonneg (f u)
  calc
    sourceFiniteAffineEnergy (sourcePositiveDyadicRange M)
        (sourcePositiveDyadicRange M) (sourceCenteredRange (16 * M)) f ≤
        K ^ 2 * 2 * (∫ u : ℝ, f u ^ 2) := by
      simpa only [K] using hbase
    _ ≤ (132 * (M : ℝ) ^ 3) ^ 2 * 2 *
        (∫ u : ℝ, f u ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hKsq (by norm_num)) hI0
    _ = 34848 * (M : ℝ) ^ 6 * (∫ u : ℝ, f u ^ 2) := by ring

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.sourcePositiveCentered_endcap_energy_le
