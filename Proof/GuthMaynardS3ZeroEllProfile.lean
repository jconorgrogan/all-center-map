import GuthMaynardS3ZeroEllSupport
import GuthMaynardS3LiteralLemma92RegionII

open scoped BigOperators Real FourierTransform
open MeasureTheory

noncomputable section
namespace GuthMaynardS3ZeroEllProfile

open GuthMaynardJIteration
open GuthMaynardS3ZeroEllSupport

theorem card_sourceSignedDyadicRange_cast_le_four_mul
    {M : ℕ} (hM : 1 ≤ M) :
    ((sourceSignedDyadicRange M).card : ℝ) ≤ 4 * (M : ℝ) := by
  have hneg : Disjoint (Finset.Icc (-(2 * M : ℤ)) (-(M : ℤ)))
      (Finset.Icc (M : ℤ) (2 * M : ℤ)) := by
    rw [Finset.disjoint_left]
    intro m hmneg hmpos
    rw [Finset.mem_Icc] at hmneg hmpos
    omega
  rw [sourceSignedDyadicRange, Finset.card_union_of_disjoint hneg]
  have hcardNeg := Int.card_Icc (-(2 * M : ℤ)) (-(M : ℤ))
  have hcardPos := Int.card_Icc (M : ℤ) (2 * M : ℤ)
  have hnonnegNeg : (0 : ℤ) ≤ -(M : ℤ) + 1 - (-(2 * M : ℤ)) := by omega
  have hnonnegPos : (0 : ℤ) ≤ (2 * M : ℤ) + 1 - (M : ℤ) := by omega
  have hcastNeg :
      ((((-(M : ℤ) + 1 - (-(2 * M : ℤ))).toNat : ℕ) : ℝ)) =
        (-(M : ℤ) + 1 - (-(2 * M : ℤ)) : ℤ) := by
    exact_mod_cast (Int.toNat_of_nonneg hnonnegNeg)
  have hcastPos :
      ((((2 * M : ℤ) + 1 - (M : ℤ)).toNat : ℕ) : ℝ) =
        ((2 * M : ℤ) + 1 - (M : ℤ) : ℤ) := by
    exact_mod_cast (Int.toNat_of_nonneg hnonnegPos)
  rw [hcardNeg, hcardPos]
  have hsumcast :
      ((((-(M : ℤ) + 1 - (-(2 * M : ℤ))).toNat +
        ((2 * M : ℤ) + 1 - (M : ℤ)).toNat : ℕ) : ℝ)) =
        (-(M : ℤ) + 1 - (-(2 * M : ℤ)) : ℝ) +
          ((2 * M : ℤ) + 1 - (M : ℤ) : ℝ) := by
    push_cast
    rw [hcastNeg, hcastPos]
    ring_nf
    norm_num
    ring
  rw [hsumcast]
  push_cast
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  linarith

theorem card_sourcePositiveDyadicRange_cast_le_three_mul
    {M : ℕ} (hM : 1 ≤ M) :
    ((sourcePositiveDyadicRange M).card : ℝ) ≤ 3 * (M : ℝ) := by
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

/-- The literal L1 Fourier majorant supplied by the admissible source profile. -/
theorem profile_fourier_l1_bound
    {T S F : ℝ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S F f) :
    ∀ z : ℝ,
      ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) z‖ ≤
        ∫ u : ℝ, ‖(f u : ℂ)‖ := by
  set_option maxHeartbeats 800000 in
    
  intro z
  have hraw := VectorFourier.norm_fourierIntegral_le_integral_norm
    𝐞 volume (innerₗ ℝ) (fun u : ℝ => (f u : ℂ)) z
  change ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) z‖ ≤
    ∫ u : ℝ, ‖(f u : ℂ)‖ at hraw
  exact hraw

/-- The unit source bump supplies the exact `Kψ=1` bound and is continuous. -/
theorem unit_bump_fourier_bound :
    (∀ z : ℝ,
      ‖FourierTransform.fourier
        (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ)) z‖ ≤
          sourceBumpFourierConstant 1 zero_lt_one 0) ∧
    Continuous (FourierTransform.fourier
      (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))) := by
  refine ⟨?_, ?_⟩
  · intro z
    simpa only [pow_zero, div_one] using
      (sourceBump_fourier_decay 1 zero_lt_one 0 z)
  · exact VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (innerSL ℝ).continuous₂
      ((sourceBump 1 zero_lt_one).integrable.ofReal)

/-- Concrete corrected-inner L1 bound for the actual positive dyadic `m₂` range. -/
theorem profile_corrected_inner_le
    {T S F : ℝ} {M1 M2 : ℕ} {m1 : ℤ} {m2Range : Finset ℤ}
    {f : ℝ → ℝ} (hf : SourceAdmissibleProfile T S F f)
    (hM1nat : 1 ≤ M1) (hM2nat : 1 ≤ M2)
    (hm1 : m1 ∈ sourceSignedDyadicRange M1)
    (hm2card : (m2Range.card : ℝ) ≤ 3 * (M2 : ℝ))
    (hm2hi : ∀ m2 ∈ m2Range, |(m2 : ℝ)| ≤ 2 * (M2 : ℝ))
    (hM1 : 1 ≤ (M1 : ℝ)) (hM2 : 0 ≤ (M2 : ℝ)) {xi : ℝ} :
    ‖sourceCorrectedM2FourierInner m2Range
      (FourierTransform.fourier (fun u : ℝ => (f u : ℂ))) m1 xi‖ ≤
      6 * (M2 : ℝ) ^ 2 / (M1 : ℝ) *
        (∫ u : ℝ, ‖(f u : ℂ)‖) := by
  have hm1lo : (M1 : ℝ) ≤ |(m1 : ℝ)| :=
    (sourceSignedDyadicRange_abs_bounds hM1nat hm1).1
  have hm1ne : (m1 : ℝ) ≠ 0 := by
    exact_mod_cast sourceSignedDyadicRange_ne_zero hM1nat hm1
  have hden : 0 < |(m1 : ℝ)| := abs_pos.mpr hm1ne
  have hfourier := profile_fourier_l1_bound hf
  calc
    ‖sourceCorrectedM2FourierInner m2Range
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ))) m1 xi‖ ≤
        ∑ m2 ∈ m2Range,
          ‖(((|(m2 : ℝ) / (m1 : ℝ)| : ℝ) : ℂ) *
            FourierTransform.fourier (fun u : ℝ => (f u : ℂ))
              (((m2 : ℝ) / (m1 : ℝ)) * xi))‖ := by
      unfold sourceCorrectedM2FourierInner
      exact norm_sum_le _ _
    _ ≤ ∑ _m2 ∈ m2Range,
        (2 * (M2 : ℝ) / (M1 : ℝ)) *
          (∫ u : ℝ, ‖(f u : ℂ)‖) := by
      apply Finset.sum_le_sum
      intro m2 hm2
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hratio : |(m2 : ℝ) / (m1 : ℝ)| ≤
          2 * (M2 : ℝ) / (M1 : ℝ) := by
        rw [abs_div]
        calc
          |(m2 : ℝ)| / |(m1 : ℝ)| ≤
              (2 * (M2 : ℝ)) / |(m1 : ℝ)| :=
            div_le_div_of_nonneg_right (hm2hi m2 hm2) hden.le
          _ ≤ (2 * (M2 : ℝ)) / (M1 : ℝ) := by
            gcongr
      have hterm := hfourier (((m2 : ℝ) / (m1 : ℝ)) * xi)
      rw [abs_abs]
      calc
        |(m2 : ℝ) / (m1 : ℝ)| *
              ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ))
                (((m2 : ℝ) / (m1 : ℝ)) * xi)‖ ≤
            (2 * (M2 : ℝ) / (M1 : ℝ)) *
              ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ))
                (((m2 : ℝ) / (m1 : ℝ)) * xi)‖ :=
          mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
        _ ≤ (2 * (M2 : ℝ) / (M1 : ℝ)) *
              (∫ u : ℝ, ‖(f u : ℂ)‖) :=
          mul_le_mul_of_nonneg_left hterm (by positivity)
    _ ≤ (m2Range.card : ℝ) *
        ((2 * (M2 : ℝ) / (M1 : ℝ)) *
          (∫ u : ℝ, ‖(f u : ℂ)‖)) := by
      simpa [nsmul_eq_mul] using
        (Finset.sum_le_card_nsmul m2Range
          (fun _m2 : ℤ => (2 * (M2 : ℝ) / (M1 : ℝ)) *
            (∫ u : ℝ, ‖(f u : ℂ)‖)) _ (fun _ _ => le_rfl))
    _ ≤ 6 * (M2 : ℝ) ^ 2 / (M1 : ℝ) *
        (∫ u : ℝ, ‖(f u : ℂ)‖) := by
      have hL1 : 0 ≤ ∫ u : ℝ, ‖(f u : ℂ)‖ := integral_nonneg fun _ => norm_nonneg _
      have hA : 0 ≤ (2 * (M2 : ℝ) / (M1 : ℝ)) *
          (∫ u : ℝ, ‖(f u : ℂ)‖) := by positivity
      calc
        (m2Range.card : ℝ) *
            ((2 * (M2 : ℝ) / (M1 : ℝ)) *
              (∫ u : ℝ, ‖(f u : ℂ)‖)) ≤
            (3 * (M2 : ℝ)) *
              ((2 * (M2 : ℝ) / (M1 : ℝ)) *
                (∫ u : ℝ, ‖(f u : ℂ)‖)) := by
          exact mul_le_mul_of_nonneg_right hm2card hA
        _ = 6 * (M2 : ℝ) ^ 2 / (M1 : ℝ) *
            (∫ u : ℝ, ‖(f u : ℂ)‖) := by ring

/-- Actual zero-ell producer for the literal signed/positive dyadic ranges.
The Fourier loss is the profile's L1 mass, so the energy bound retains its
square rather than replacing it by a coarse source-scale surrogate. -/
theorem actualZeroEllProfile
    {T S F : ℝ} {f : ℝ → ℝ} (hf : SourceAdmissibleProfile T S F f)
    {M M3 B : ℝ} {M1 M2 : ℕ} (ellRange : Finset ℤ)
    (hM : 0 ≤ M) (hM1 : 1 ≤ M1) (hM2 : 1 ≤ M2)
    (hM3 : 0 < M3) (hM1M : (M1 : ℝ) ≤ M)
    (hM2M : (M2 : ℝ) ≤ M) (hM3M : M3 ≤ M) (hB : 0 ≤ B) :
    (∫ xi : ℝ, ‖sourceMediumZeroEllSum
      (sourceSignedDyadicRange M1) ellRange
      (sourcePositiveDyadicRange M2)
      (FourierTransform.fourier
        (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ)))
      (FourierTransform.fourier (fun u : ℝ => (f u : ℂ))) M3 B xi‖ ^ 2) ≤
      2304 * (sourceBumpFourierConstant 1 zero_lt_one 0) ^ 2 * B * M ^ 6 *
        (∫ u : ℝ, ‖(f u : ℂ)‖) ^ 2 := by
  let m1Range : Finset ℤ := sourceSignedDyadicRange M1
  let m2Range : Finset ℤ := sourcePositiveDyadicRange M2
  let Funit : ℝ → ℂ := fun x : ℝ =>
    FourierTransform.fourier (fun y : ℝ => (sourceBump 1 zero_lt_one y : ℂ)) x
  let fhat : ℝ → ℂ := fun u : ℝ =>
    FourierTransform.fourier (fun y : ℝ => (f y : ℂ)) u
  have hM1pos : 0 < (M1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM1)
  have hM2pos : 0 < (M2 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM2)
  have hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0 := by
    intro m1 hm
    exact sourceSignedDyadicRange_ne_zero
      (lt_of_lt_of_le Nat.zero_lt_one hM1) hm
  have hm1hi : ∀ m1 ∈ m1Range, |(m1 : ℝ)| ≤ 2 * (M1 : ℝ) := by
    intro m1 hm
    exact (sourceSignedDyadicRange_abs_bounds
      (lt_of_lt_of_le Nat.zero_lt_one hM1) hm).2
  have hcard1 : (m1Range.card : ℝ) ≤ 4 * (M1 : ℝ) := by
    exact card_sourceSignedDyadicRange_cast_le_four_mul hM1
  have hm2card : (m2Range.card : ℝ) ≤ 3 * (M2 : ℝ) := by
    exact card_sourcePositiveDyadicRange_cast_le_three_mul hM2
  have hm2hi : ∀ m2 ∈ m2Range, |(m2 : ℝ)| ≤ 2 * (M2 : ℝ) := by
    intro m2 hm
    exact (sourcePositiveDyadicRange_abs_bounds
      (lt_of_lt_of_le Nat.zero_lt_one hM2) hm).2
  have hunit := unit_bump_fourier_bound
  have hF : ∀ z, ‖Funit z‖ ≤ sourceBumpFourierConstant 1 zero_lt_one 0 := by
    intro z
    exact hunit.1 z
  have hfhat : Continuous fhat := by
    dsimp [fhat]
    exact continuous_fourier_of_integrable f hf.integrable
  have hFcont : Continuous Funit := by
    exact hunit.2
  have hzeroEq : (fun xi : ℝ =>
      sourceMediumZeroEllSum m1Range ellRange m2Range Funit fhat M3 B xi) =
      (fun xi : ℝ => sourceFirstPoissonLocalizedPairSum m1Range
        (ellRange.filter (fun e : ℤ => e = 0)) m2Range Funit fhat M3 B xi) := by
    funext xi
    unfold sourceMediumZeroEllSum sourceFirstPoissonLocalizedPairSum
      sourceMediumLocalizedPairs
    have hprod : m1Range ×ˢ (ellRange.filter (fun e : ℤ => e = 0)) =
        (m1Range ×ˢ ellRange).filter (fun p : ℤ × ℤ => p.2 = 0) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨hp1, ⟨hp2, hpzero⟩⟩
        exact ⟨⟨hp1, hp2⟩, hpzero⟩
      · rintro ⟨⟨hp1, hp2⟩, hpzero⟩
        exact ⟨hp1, ⟨hp2, hpzero⟩⟩
    rw [hprod]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hlocal : |xi - (p.1 : ℝ) * (p.2 : ℝ)| <
        |(p.1 : ℝ)| / M3 * B <;>
      by_cases hzero : p.2 = 0 <;>
      simp [hlocal, hzero]
  have hint : Integrable (fun xi : ℝ =>
      ‖sourceMediumZeroEllSum m1Range ellRange m2Range Funit fhat M3 B xi‖ ^ 2) := by
    have hnormEq : (fun xi : ℝ =>
        ‖sourceMediumZeroEllSum m1Range ellRange m2Range Funit fhat M3 B xi‖ ^ 2) =
        (fun xi : ℝ =>
          ‖sourceFirstPoissonLocalizedPairSum m1Range
            (ellRange.filter (fun e : ℤ => e = 0)) m2Range Funit fhat M3 B xi‖ ^ 2) := by
      funext xi
      exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (congrFun hzeroEq xi)
    rw [hnormEq]
    exact integrable_norm_sq_sourceFirstPoissonLocalizedPairSum m1Range
      (ellRange.filter (fun e : ℤ => e = 0)) m2Range Funit fhat
      hFcont hfhat hM3 hB
  have hinner : ∀ (xi : ℝ) (p : ℤ × ℤ),
      p ∈ (sourceMediumLocalizedPairs m1Range ellRange M3 B xi).filter
        (fun p : ℤ × ℤ => p.2 = 0) →
      ‖sourceCorrectedM2FourierInner m2Range fhat p.1 xi‖ ≤
        6 * (M2 : ℝ) ^ 2 / (M1 : ℝ) *
          (∫ u : ℝ, ‖(f u : ℂ)‖) := by
    intro xi p hp
    have hpbase := (Finset.mem_filter.mp hp).1
    have hpmem := (mem_sourceMediumLocalizedPairs_iff.mp hpbase).1
    exact profile_corrected_inner_le hf hM1 hM2 hpmem hm2card hm2hi
      (by exact_mod_cast hM1) (by positivity)
  have hcore := integral_norm_sq_sourceMediumZeroEllSum_le
    m1Range ellRange m2Range Funit fhat
    hM hM1pos (by positivity) hM3 hM1M hM2M hM3M hB
    (sourceBumpFourierConstant_nonneg 1 zero_lt_one 0)
    (integral_nonneg fun _ => norm_nonneg _)
    hm1 hm1hi hcard1 hF hinner hint
  simpa [m1Range, m2Range, Funit, fhat] using hcore

end GuthMaynardS3ZeroEllProfile

#print axioms GuthMaynardS3ZeroEllProfile.profile_fourier_l1_bound
#print axioms GuthMaynardS3ZeroEllProfile.unit_bump_fourier_bound
#print axioms GuthMaynardS3ZeroEllProfile.profile_corrected_inner_le
#print axioms GuthMaynardS3ZeroEllProfile.actualZeroEllProfile
