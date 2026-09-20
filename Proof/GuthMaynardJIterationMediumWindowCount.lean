import GuthMaynardJIterationMediumPairCount

open scoped Real

noncomputable section
namespace GuthMaynardJIteration

/-! Literal integer-window scalar choice in source TeX 1585. -/

theorem card_sourceIntegerWindow_cast_le
    (xi W : ℝ) (hW : 0 ≤ W) :
    ((sourceIntegerWindow xi W).card : ℝ) ≤ 2 * W + 3 := by
  rw [card_sourceIntegerWindow]
  let n : ℤ := ⌈xi + W⌉ + 1 - ⌊xi - W⌋
  have horderR : ((⌊xi - W⌋ : ℤ) : ℝ) ≤ ((⌈xi + W⌉ : ℤ) : ℝ) := by
    have hx : xi - W ≤ xi + W := by linarith
    exact (Int.floor_le _).trans (hx.trans (Int.le_ceil _))
  have horder : (⌊xi - W⌋ : ℤ) ≤ ⌈xi + W⌉ := by exact_mod_cast horderR
  have hn : 0 ≤ n := by dsimp only [n]; omega
  have hncast : (n.toNat : ℝ) = (n : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hn)
  rw [show (⌈xi + W⌉ + 1 - ⌊xi - W⌋).toNat = n.toNat by rfl, hncast]
  have hceil := Int.ceil_lt_add_one (xi + W)
  have hfloor := Int.sub_one_lt_floor (xi - W)
  dsimp only [n]
  push_cast
  linarith

/-- Exact source scale `1+M1/M3` for the integer product window.  The two
constant requirements expose the localization width loss `c1*B`. -/
theorem card_sourceIntegerWindow_le_sourceScale
    (xi : ℝ) {M1 M3 B c1 Lwindow : ℝ}
    (hM1 : 0 ≤ M1) (hM3 : 0 < M3) (hB : 0 ≤ B) (hc1 : 0 ≤ c1)
    (hthree : 3 ≤ Lwindow) (hwidth : 2 * c1 * B ≤ Lwindow) :
    ((sourceIntegerWindow xi (c1 * M1 / M3 * B)).card : ℝ) ≤
      Lwindow * (1 + M1 / M3) := by
  have hratio : 0 ≤ M1 / M3 := div_nonneg hM1 hM3.le
  have hW : 0 ≤ c1 * M1 / M3 * B := by positivity
  refine (card_sourceIntegerWindow_cast_le xi _ hW).trans ?_
  calc
    2 * (c1 * M1 / M3 * B) + 3 =
        (2 * c1 * B) * (M1 / M3) + 3 := by ring
    _ ≤ Lwindow * (M1 / M3) + Lwindow := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hwidth hratio) hthree
    _ = Lwindow * (1 + M1 / M3) := by ring

theorem sourceMediumRadius_le_dyadicWindow
    {m1Range : Finset ℤ} {M1 M3 B c1 : ℝ}
    (hM3 : 0 < M3) (hB : 0 ≤ B)
    (hm1hi : ∀ m1 ∈ m1Range, |(m1 : ℝ)| ≤ c1 * M1) :
    ∀ m1 ∈ m1Range,
      (|(m1 : ℝ)| / M3) * B ≤ c1 * M1 / M3 * B := by
  intro m1 hm1
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (hm1hi m1 hm1) hM3.le) hB

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.card_sourceIntegerWindow_cast_le
#print axioms GuthMaynardJIteration.card_sourceIntegerWindow_le_sourceScale
#print axioms GuthMaynardJIteration.sourceMediumRadius_le_dyadicWindow
