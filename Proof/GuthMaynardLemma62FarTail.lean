import GuthMaynardSectionThreeCutoffDerivativeBudget
import Mathlib.Analysis.SumIntegralComparisons

/-!
# The far-frequency truncation in Guth--Maynard Lemma 6.2

The source discards `|m|` larger than `T₀^(1+o(1))/N` using Lemma 4.3(1).
This file records the finite-tail estimate before any asymptotic choice of
the cutoff.  In particular, the arbitrary derivative order remains visible;
that freedom is what permits the advertised `T⁻¹⁰⁰` remainder.
-/

namespace GuthMaynardLemma62FarTail

open Real Complex Set MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap
open GuthMaynardSectionThreeCutoffDerivativeBudget

noncomputable section

/-- Integral-test bound for a finite segment of the literal `p`-series
tail.  The right side is independent of the upper endpoint `K`. -/
theorem finite_nat_rpow_tail_le
    {M K j : ℕ} (hM : 1 ≤ M) (hj : 2 ≤ j) :
    (∑ i ∈ Finset.range K,
        ((M + (i + 1 : ℕ) : ℕ) : ℝ) ^ (-(j : ℝ))) ≤
      (M : ℝ) ^ (1 - (j : ℝ)) / ((j : ℝ) - 1) := by
  let f : ℝ → ℝ := fun x => x ^ (-(j : ℝ))
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have hanti : AntitoneOn f
      (Set.Icc (M : ℝ) ((M : ℝ) + K)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hMpos.trans_le hx.1) hxy
      (neg_nonpos.mpr (Nat.cast_nonneg j))
  have hsum := hanti.sum_le_integral
  have hjNe : -(j : ℝ) ≠ -1 := by
    have hjR : (2 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  have hzero : (0 : ℝ) ∉ Set.uIcc (M : ℝ) ((M : ℝ) + K) := by
    rw [Set.uIcc_of_le (le_add_of_nonneg_right (Nat.cast_nonneg K))]
    intro hz
    exact (not_le_of_gt hMpos) hz.1
  rw [integral_rpow (Or.inr ⟨hjNe, hzero⟩)] at hsum
  have hdenPos : 0 < (j : ℝ) - 1 := by
    have hjR : (2 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  have hupperNonneg :
      0 ≤ ((M : ℝ) + K) ^ (-(j : ℝ) + 1) := Real.rpow_nonneg (by positivity) _
  have hrewrite : -(j : ℝ) + 1 = 1 - (j : ℝ) := by ring
  calc
    (∑ i ∈ Finset.range K,
        ((M + (i + 1 : ℕ) : ℕ) : ℝ) ^ (-(j : ℝ))) ≤
      (((M : ℝ) + K) ^ (-(j : ℝ) + 1) -
          (M : ℝ) ^ (-(j : ℝ) + 1)) / (-(j : ℝ) + 1) := by
        simpa [f, Nat.cast_add] using hsum
    _ ≤ (M : ℝ) ^ (1 - (j : ℝ)) / ((j : ℝ) - 1) := by
      rw [hrewrite]
      have hdenNe : (j : ℝ) - 1 ≠ 0 := hdenPos.ne'
      rw [show 1 - (j : ℝ) = -((j : ℝ) - 1) by ring]
      have hupperNonneg' :
          0 ≤ ((M : ℝ) + K) ^ (-((j : ℝ) - 1)) :=
        Real.rpow_nonneg (by positivity) _
      have heq :
          (((M : ℝ) + K) ^ (-((j : ℝ) - 1)) -
              (M : ℝ) ^ (-((j : ℝ) - 1))) / (-((j : ℝ) - 1)) =
            ((M : ℝ) ^ (-((j : ℝ) - 1)) -
              ((M : ℝ) + K) ^ (-((j : ℝ) - 1))) / ((j : ℝ) - 1) := by
        field_simp [hdenNe]
        ring
      rw [heq]
      exact (div_le_div_iff_of_pos_right hdenPos).2
        (sub_le_self _ hupperNonneg')

def sectionThreeFourierCoefficient (t xi : ℝ) : ℂ :=
  (𝓕 (sectionThreeOscillatorySchwartz t) : 𝓢(ℝ, ℂ)) xi

/-- Exact Fourier-integral formula for the source coefficient
`\widehat h_t(ξ)`, with mathlib's `2π` normalization exposed. -/
theorem sectionThreeFourierCoefficient_eq_integral
    (t xi : ℝ) :
    sectionThreeFourierCoefficient t xi =
      ∫ u : ℝ,
        Complex.exp (((-2 * Real.pi * u * xi : ℝ) : ℂ) * Complex.I) *
          sectionThreeOscillatory t u := by
  unfold sectionThreeFourierCoefficient
  have hcoe := congrFun
    (SchwartzMap.fourier_coe (sectionThreeOscillatorySchwartz t)) xi
  rw [hcoe]
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  simp only [smul_eq_mul]
  rw [sectionThreeOscillatorySchwartz_apply]

theorem norm_sectionThreeFourierCoefficient_signed_nat_le
    (t : ℝ) (j m : ℕ) {N : ℝ} (hN : 0 < N) (hm : 0 < m)
    (sign : ℝ) (hsign : |sign| = 1) :
    ‖sectionThreeFourierCoefficient t (sign * (m : ℝ) * N)‖ ≤
      (lemma43DerivativeConstant j * (1 + |t|) ^ j *
          N ^ (-(j : ℝ))) * (m : ℝ) ^ (-(j : ℝ)) := by
  have hxi : sign * (m : ℝ) * N ≠ 0 := by
    have hsignNe : sign ≠ 0 := by
      intro hz
      simp [hz] at hsign
    positivity
  have hfourier := lemma43_part_one_sectionThreeOscillatory t j hxi
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have habs : |sign * (m : ℝ) * N| = (m : ℝ) * N := by
    calc
      |sign * (m : ℝ) * N| = |sign| * |(m : ℝ)| * |N| := by
        rw [abs_mul, abs_mul]
      _ = (m : ℝ) * N := by rw [hsign, abs_of_pos hmR, abs_of_pos hN]; ring
  unfold sectionThreeFourierCoefficient
  calc
    ‖(𝓕 (sectionThreeOscillatorySchwartz t) : 𝓢(ℝ, ℂ))
        (sign * (m : ℝ) * N)‖ ≤
      (lemma43DerivativeConstant j * (1 + |t|) ^ j) /
        |sign * (m : ℝ) * N| ^ j := hfourier
    _ = (lemma43DerivativeConstant j * (1 + |t|) ^ j *
          N ^ (-(j : ℝ))) * (m : ℝ) ^ (-(j : ℝ)) := by
      rw [habs, mul_pow]
      rw [Real.rpow_neg hN.le, Real.rpow_natCast,
        Real.rpow_neg (by positivity : (0 : ℝ) ≤ m), Real.rpow_natCast]
      field_simp [hN.ne', (show (m : ℝ) ≠ 0 by positivity)]

/-- Positive or negative far frequencies have the same finite-tail bound.
The sign parameter is retained so the negative branch cannot disappear from
the eventual AFE assembly. -/
theorem finite_signed_fourier_tail_le
    (t : ℝ) {N : ℝ} (hN : 0 < N) {M K j : ℕ}
    (hM : 1 ≤ M) (hj : 2 ≤ j) (sign : ℝ) (hsign : |sign| = 1) :
    (∑ i ∈ Finset.range K,
        ‖sectionThreeFourierCoefficient t
          (sign * ((M + (i + 1 : ℕ) : ℕ) : ℝ) * N)‖) ≤
      (lemma43DerivativeConstant j * (1 + |t|) ^ j *
          N ^ (-(j : ℝ))) *
        ((M : ℝ) ^ (1 - (j : ℝ)) / ((j : ℝ) - 1)) := by
  let A : ℝ := lemma43DerivativeConstant j * (1 + |t|) ^ j *
    N ^ (-(j : ℝ))
  have hA : 0 ≤ A := by
    unfold A
    exact mul_nonneg
      (mul_nonneg (lemma43DerivativeConstant_nonneg j) (by positivity))
      (Real.rpow_nonneg hN.le _)
  calc
    (∑ i ∈ Finset.range K,
        ‖sectionThreeFourierCoefficient t
          (sign * ((M + (i + 1 : ℕ) : ℕ) : ℝ) * N)‖) ≤
      ∑ i ∈ Finset.range K,
        A * ((M + (i + 1 : ℕ) : ℕ) : ℝ) ^ (-(j : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_sectionThreeFourierCoefficient_signed_nat_le
        t j (M + (i + 1)) hN (by omega) sign hsign
    _ = A * ∑ i ∈ Finset.range K,
        ((M + (i + 1 : ℕ) : ℕ) : ℝ) ^ (-(j : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ A * ((M : ℝ) ^ (1 - (j : ℝ)) / ((j : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left (finite_nat_rpow_tail_le hM hj) hA
    _ = (lemma43DerivativeConstant j * (1 + |t|) ^ j *
          N ^ (-(j : ℝ))) *
        ((M : ℝ) ^ (1 - (j : ℝ)) / ((j : ℝ) - 1)) := rfl

theorem finite_twoSided_fourier_tail_le
    (t : ℝ) {N : ℝ} (hN : 0 < N) {M K j : ℕ}
    (hM : 1 ≤ M) (hj : 2 ≤ j) :
    (∑ i ∈ Finset.range K,
        ‖sectionThreeFourierCoefficient t
          (((M + (i + 1 : ℕ) : ℕ) : ℝ) * N)‖) +
      (∑ i ∈ Finset.range K,
        ‖sectionThreeFourierCoefficient t
          (-(((M + (i + 1 : ℕ) : ℕ) : ℝ) * N))‖) ≤
      2 * ((lemma43DerivativeConstant j * (1 + |t|) ^ j *
          N ^ (-(j : ℝ))) *
        ((M : ℝ) ^ (1 - (j : ℝ)) / ((j : ℝ) - 1))) := by
  have hpos := finite_signed_fourier_tail_le t hN (K := K) hM hj 1 (by simp)
  have hneg := finite_signed_fourier_tail_le t hN (K := K) hM hj (-1) (by simp)
  have hpos' :
      (∑ i ∈ Finset.range K,
        ‖sectionThreeFourierCoefficient t
          (((M + (i + 1 : ℕ) : ℕ) : ℝ) * N)‖) ≤
        (lemma43DerivativeConstant j * (1 + |t|) ^ j *
          N ^ (-(j : ℝ))) *
        ((M : ℝ) ^ (1 - (j : ℝ)) / ((j : ℝ) - 1)) := by
    simpa only [one_mul] using hpos
  have hnegForm :
      (∑ i ∈ Finset.range K,
        ‖sectionThreeFourierCoefficient t
          (-(((M + (i + 1 : ℕ) : ℕ) : ℝ) * N))‖) =
      ∑ i ∈ Finset.range K,
        ‖sectionThreeFourierCoefficient t
          ((-1 : ℝ) * ((M + (i + 1 : ℕ) : ℕ) : ℝ) * N)‖ := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    ring
  calc
    (∑ i ∈ Finset.range K,
        ‖sectionThreeFourierCoefficient t
          (((M + (i + 1 : ℕ) : ℕ) : ℝ) * N)‖) +
      (∑ i ∈ Finset.range K,
        ‖sectionThreeFourierCoefficient t
          (-(((M + (i + 1 : ℕ) : ℕ) : ℝ) * N))‖) =
      (∑ i ∈ Finset.range K,
        ‖sectionThreeFourierCoefficient t
          (((M + (i + 1 : ℕ) : ℕ) : ℝ) * N)‖) +
      (∑ i ∈ Finset.range K,
        ‖sectionThreeFourierCoefficient t
          ((-1 : ℝ) * ((M + (i + 1 : ℕ) : ℕ) : ℝ) * N)‖) := by
        rw [hnegForm]
    _ ≤
      ((lemma43DerivativeConstant j * (1 + |t|) ^ j *
          N ^ (-(j : ℝ))) *
        ((M : ℝ) ^ (1 - (j : ℝ)) / ((j : ℝ) - 1))) +
      ((lemma43DerivativeConstant j * (1 + |t|) ^ j *
          N ^ (-(j : ℝ))) *
        ((M : ℝ) ^ (1 - (j : ℝ)) / ((j : ℝ) - 1))) :=
          add_le_add hpos' hneg
    _ = 2 * ((lemma43DerivativeConstant j * (1 + |t|) ^ j *
          N ^ (-(j : ℝ))) *
        ((M : ℝ) ^ (1 - (j : ℝ)) / ((j : ℝ) - 1))) := by ring

end

end GuthMaynardLemma62FarTail

#print axioms GuthMaynardLemma62FarTail.finite_nat_rpow_tail_le
#print axioms GuthMaynardLemma62FarTail.sectionThreeFourierCoefficient_eq_integral
#print axioms GuthMaynardLemma62FarTail.finite_signed_fourier_tail_le
#print axioms GuthMaynardLemma62FarTail.finite_twoSided_fourier_tail_le
