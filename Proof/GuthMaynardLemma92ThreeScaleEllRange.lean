import GuthMaynardLemma92LargeEllRange

/-!
# Literal first-Poisson ell cover with independent `M₁` and `M₃`

The localization radius is `|m₁| B / M₃`, so the cover is
`|ell| <= T^6/M₁ + B/M₃`.  This must remain separate from the second-Poisson
scale `M₂` used by the later detector.
-/

open scoped Real

noncomputable section
namespace GuthMaynardJIteration

/-- Source-faithful first-Poisson cover with the numerator and affine scales
kept independent. -/
def sourceLemma92ThreeScaleEllRange
    (M1 M3 : ℕ) (T B : ℝ) : Finset ℤ :=
  sourceIntegerWindow 0
    (T ^ 6 / (M1 : ℝ) + B / (M3 : ℝ))

/-- Every localized first-Poisson index through frequency `T^6` lies in the
independent-scale cover. -/
theorem mem_sourceLemma92ThreeScaleEllRange_of_localized
    {M1 M3 : ℕ} (hM1 : 0 < M1) (hM3 : 0 < M3)
    {T B xi : ℝ} (_hT : 0 ≤ T) (_hB : 0 ≤ B)
    {m1 ell : ℤ} (hm1 : m1 ∈ sourceSignedDyadicRange M1)
    (hxi : |xi| ≤ T ^ 6)
    (hell : |xi - (m1 : ℝ) * (ell : ℝ)| <
      (|(m1 : ℝ)| / (M3 : ℝ)) * B) :
    ell ∈ sourceLemma92ThreeScaleEllRange M1 M3 T B := by
  have hM1real : 0 < (M1 : ℝ) := Nat.cast_pos.mpr hM1
  have hM3real : 0 < (M3 : ℝ) := Nat.cast_pos.mpr hM3
  have hmlo : (M1 : ℝ) ≤ |(m1 : ℝ)| :=
    (sourceSignedDyadicRange_abs_bounds hM1 hm1).1
  have hmpos : 0 < |(m1 : ℝ)| := hM1real.trans_le hmlo
  have hprod : |(m1 : ℝ)| * |(ell : ℝ)| <
      T ^ 6 + (|(m1 : ℝ)| / (M3 : ℝ)) * B := by
    calc
      |(m1 : ℝ)| * |(ell : ℝ)| =
          |(m1 : ℝ) * (ell : ℝ)| := (abs_mul _ _).symm
      _ = |xi - (xi - (m1 : ℝ) * (ell : ℝ))| := by ring_nf
      _ ≤ |xi| + |xi - (m1 : ℝ) * (ell : ℝ)| := abs_sub _ _
      _ < T ^ 6 + (|(m1 : ℝ)| / (M3 : ℝ)) * B :=
        add_lt_add_of_le_of_lt hxi hell
  have hellDiv : |(ell : ℝ)| <
      (T ^ 6 + (|(m1 : ℝ)| / (M3 : ℝ)) * B) /
        |(m1 : ℝ)| :=
    (lt_div_iff₀ hmpos).2 (by simpa [mul_comm] using hprod)
  have hsplit :
      (T ^ 6 + (|(m1 : ℝ)| / (M3 : ℝ)) * B) /
          |(m1 : ℝ)| =
        T ^ 6 / |(m1 : ℝ)| + B / (M3 : ℝ) := by
    field_simp [hM3real.ne', hmpos.ne']
  rw [hsplit] at hellDiv
  have hpow0 : 0 ≤ T ^ 6 := by positivity
  have hfirst : T ^ 6 / |(m1 : ℝ)| ≤ T ^ 6 / (M1 : ℝ) :=
    div_le_div_of_nonneg_left hpow0 hM1real hmlo
  apply mem_sourceIntegerWindow_zero_of_abs_le
  exact hellDiv.le.trans (add_le_add hfirst le_rfl)

/-- Exact cardinality bound before any dyadic simplification. -/
theorem card_sourceLemma92ThreeScaleEllRange_cast_le
    {M1 M3 : ℕ} (hM1 : 0 < M1) (hM3 : 0 < M3)
    {T B : ℝ} (_hT : 0 ≤ T) (hB : 0 ≤ B) :
    ((sourceLemma92ThreeScaleEllRange M1 M3 T B).card : ℝ) ≤
      2 * (T ^ 6 / (M1 : ℝ) + B / (M3 : ℝ)) + 3 := by
  unfold sourceLemma92ThreeScaleEllRange
  exact card_sourceIntegerWindow_cast_le 0
    (T ^ 6 / (M1 : ℝ) + B / (M3 : ℝ)) (by positivity)

/-- Uniform source bound for the independent-scale cover. -/
theorem card_sourceLemma92ThreeScaleEllRange_cast_le_seven_time_six
    {M1 M3 : ℕ} (hM1 : 0 < M1) (hM3 : 0 < M3)
    {T B : ℝ} (hT : 1 ≤ T) (hB : 0 ≤ B) (hBT : B ≤ T ^ 6) :
    ((sourceLemma92ThreeScaleEllRange M1 M3 T B).card : ℝ) ≤
      7 * T ^ 6 := by
  have hM1one : 1 ≤ (M1 : ℝ) := by exact_mod_cast hM1
  have hM3one : 1 ≤ (M3 : ℝ) := by exact_mod_cast hM3
  have hT0 : 0 ≤ T := by linarith
  have hT6 : 1 ≤ T ^ 6 := by
    simpa using (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hT 6)
  have hfirst : T ^ 6 / (M1 : ℝ) ≤ T ^ 6 :=
    div_le_self (by positivity) hM1one
  have hsecond : B / (M3 : ℝ) ≤ T ^ 6 :=
    (div_le_self hB hM3one).trans hBT
  calc
    ((sourceLemma92ThreeScaleEllRange M1 M3 T B).card : ℝ) ≤
        2 * (T ^ 6 / (M1 : ℝ) + B / (M3 : ℝ)) + 3 :=
      card_sourceLemma92ThreeScaleEllRange_cast_le hM1 hM3 hT0 hB
    _ ≤ 2 * (T ^ 6 + T ^ 6) + 3 := by linarith
    _ ≤ 7 * T ^ 6 := by linarith

#print axioms GuthMaynardJIteration.mem_sourceLemma92ThreeScaleEllRange_of_localized
#print axioms GuthMaynardJIteration.card_sourceLemma92ThreeScaleEllRange_cast_le
#print axioms GuthMaynardJIteration.card_sourceLemma92ThreeScaleEllRange_cast_le_seven_time_six

end GuthMaynardJIteration
