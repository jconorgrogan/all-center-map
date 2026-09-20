import GuthMaynardSourceDyadicRanges
import GuthMaynardJIterationMediumWindowCount
import GuthMaynardJIterationSigmaII

/-!
# Literal large ell range for the first Poisson cover

The first Poisson localization is used for frequencies through `T^6`, so its
finite ell range is much larger than the later `Sigma_II` detector range.  This
module supplies the exact support window and cardinality bound.
-/

open scoped Real

noncomputable section
namespace GuthMaynardJIteration

def sourceLemma92LargeEllRange (M : ℕ) (T B : ℝ) : Finset ℤ :=
  sourceIntegerWindow 0 ((T ^ 6 + B) / (M : ℝ))

/-- Every first-Poisson index contributing below `T^6` lies in the literal
large ell range. -/
theorem mem_sourceLemma92LargeEllRange_of_localized
    {M : ℕ} (hM : 0 < M) {T B xi : ℝ}
    (_hT : 0 ≤ T) (_hB : 0 ≤ B)
    {m1 ell : ℤ} (hm1 : m1 ∈ sourceSignedDyadicRange M)
    (hxi : |xi| ≤ T ^ 6)
    (hell : |xi - (m1 : ℝ) * (ell : ℝ)| <
      (|(m1 : ℝ)| / (M : ℝ)) * B) :
    ell ∈ sourceLemma92LargeEllRange M T B := by
  have hMreal : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hmlo : (M : ℝ) ≤ |(m1 : ℝ)| :=
    (sourceSignedDyadicRange_abs_bounds hM hm1).1
  have hmpos : 0 < |(m1 : ℝ)| := hMreal.trans_le hmlo
  have hprod : |(m1 : ℝ)| * |(ell : ℝ)| <
      T ^ 6 + (|(m1 : ℝ)| / (M : ℝ)) * B := by
    calc
      |(m1 : ℝ)| * |(ell : ℝ)| =
          |(m1 : ℝ) * (ell : ℝ)| := (abs_mul _ _).symm
      _ = |xi - (xi - (m1 : ℝ) * (ell : ℝ))| := by ring_nf
      _ ≤ |xi| + |xi - (m1 : ℝ) * (ell : ℝ)| := abs_sub _ _
      _ < T ^ 6 + (|(m1 : ℝ)| / (M : ℝ)) * B :=
        add_lt_add_of_le_of_lt hxi hell
  have hellDiv : |(ell : ℝ)| <
      (T ^ 6 + (|(m1 : ℝ)| / (M : ℝ)) * B) /
        |(m1 : ℝ)| := (lt_div_iff₀ hmpos).2 (by
          simpa [mul_comm] using hprod)
  have hsplit :
      (T ^ 6 + (|(m1 : ℝ)| / (M : ℝ)) * B) /
          |(m1 : ℝ)| =
        T ^ 6 / |(m1 : ℝ)| + B / (M : ℝ) := by
    field_simp [hMreal.ne', hmpos.ne']
  rw [hsplit] at hellDiv
  have hpow0 : 0 ≤ T ^ 6 := by positivity
  have hfirst : T ^ 6 / |(m1 : ℝ)| ≤ T ^ 6 / (M : ℝ) :=
    div_le_div_of_nonneg_left hpow0 hMreal hmlo
  apply mem_sourceIntegerWindow_zero_of_abs_le
  have : |(ell : ℝ)| ≤ T ^ 6 / (M : ℝ) + B / (M : ℝ) :=
    hellDiv.le.trans (add_le_add hfirst le_rfl)
  simpa [sourceLemma92LargeEllRange, add_div] using this

/-- Exact cardinality bound for the large first-Poisson ell range. -/
theorem card_sourceLemma92LargeEllRange_cast_le
    {M : ℕ} (hM : 0 < M) {T B : ℝ} (_hT : 0 ≤ T) (hB : 0 ≤ B) :
    ((sourceLemma92LargeEllRange M T B).card : ℝ) ≤
      2 * ((T ^ 6 + B) / (M : ℝ)) + 3 := by
  unfold sourceLemma92LargeEllRange
  exact card_sourceIntegerWindow_cast_le 0 ((T ^ 6 + B) / (M : ℝ))
    (by positivity)

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.mem_sourceLemma92LargeEllRange_of_localized
#print axioms GuthMaynardJIteration.card_sourceLemma92LargeEllRange_cast_le
