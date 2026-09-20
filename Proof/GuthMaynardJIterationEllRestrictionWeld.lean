import GuthMaynardJIterationSourceEllRestriction
import GuthMaynardLemma92EllWindowSupport
import GuthMaynardSourceDyadicRanges

/-!
# Weld from the large first-Poisson ell range to the short Sigma-II range

The medium-frequency first Poisson cover may require a large finite `ell`
range.  Fourier decay first restricts `Sigma_II` to `|ell| < T/M`; on this
retained range the radius-one source bump is exactly one, and the range embeds
in the support-driven `sourceBumpEllRange`.  This is the missing comparison
between the two different ell ranges in the source proof.
-/

open scoped BigOperators Real FourierTransform
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-- The retained part of a large constant-weight `Sigma_II` is dominated by
the literal radius-one bump `Sigma_II` used by the second-Poisson producer. -/
theorem sigmaIIEllRetainedFinite_const_one_le_sourceBump
    (ellRange m2Range : Finset ℤ) (fhat : ℝ → ℂ)
    {M : ℕ} (hM : 0 < M) {T Ctau : ℝ}
    (hT : 0 < T) (hCtau : 0 ≤ Ctau) :
    sigmaIIEllRetainedFinite ellRange m2Range (T / (M : ℝ))
        (fun _ => 1) fhat (M : ℝ) T (M : ℝ) Ctau ≤
      sigmaIIFinite (sourceBumpEllRange M T 1) m2Range
        (fun x => sourceBump 1 zero_lt_one x) fhat
        (M : ℝ) T (M : ℝ) Ctau := by
  have hMreal : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  let retained := ellRange.filter fun ell : ℤ =>
    |(ell : ℝ)| < T / (M : ℝ)
  have hsubset : retained ⊆ sourceBumpEllRange M T 1 := by
    intro ell hell
    have hell' := (Finset.mem_filter.mp hell).2
    apply mem_sourceIntegerWindow_zero_of_abs_le
    have hratio : 0 < T / (M : ℝ) := div_pos hT hMreal
    have : |(ell : ℝ)| ≤ 2 * 1 * T / (M : ℝ) := by
      calc
        |(ell : ℝ)| ≤ T / (M : ℝ) := hell'.le
        _ ≤ 2 * 1 * T / (M : ℝ) := by
          rw [show 2 * 1 * T / (M : ℝ) = 2 * (T / (M : ℝ)) by ring]
          linarith
    simpa only [sourceBumpEllRange] using this
  have hplateau : ∀ ell ∈ retained,
      sourceBump 1 zero_lt_one ((M : ℝ) * (ell : ℝ) / T) = 1 := by
    intro ell hell
    have hell' := (Finset.mem_filter.mp hell).2
    apply sourceBump_eq_one_of_abs_le
    have hscaled :
        |(M : ℝ) * (ell : ℝ) / T| =
          (M : ℝ) * |(ell : ℝ)| / T := by
      rw [abs_div, abs_mul, abs_of_pos hMreal, abs_of_pos hT]
    rw [hscaled]
    have hmul : (M : ℝ) * |(ell : ℝ)| < T := by
      simpa [mul_comm] using (lt_div_iff₀ hMreal).mp hell'
    exact ((div_lt_one hT).2 hmul).le
  unfold sigmaIIEllRetainedFinite sigmaIIFinite
  change (∑ ell ∈ retained,
      (1 : ℝ) * ∫ tau in -Ctau..Ctau,
        ‖∑ m2 ∈ m2Range,
          sigmaIIFourierSummand (M : ℝ) fhat ell m2 tau‖ ^ 2) ≤ _
  calc
    (∑ ell ∈ retained,
        (1 : ℝ) * ∫ tau in -Ctau..Ctau,
          ‖∑ m2 ∈ m2Range,
            sigmaIIFourierSummand (M : ℝ) fhat ell m2 tau‖ ^ 2) =
      ∑ ell ∈ retained,
        sourceBump 1 zero_lt_one ((M : ℝ) * (ell : ℝ) / T) *
          ∫ tau in -Ctau..Ctau,
            ‖∑ m2 ∈ m2Range,
              sigmaIIFourierSummand (M : ℝ) fhat ell m2 tau‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro ell hell
        rw [hplateau ell hell]
    _ ≤ ∑ ell ∈ sourceBumpEllRange M T 1,
        sourceBump 1 zero_lt_one ((M : ℝ) * (ell : ℝ) / T) *
          ∫ tau in -Ctau..Ctau,
            ‖∑ m2 ∈ m2Range,
              sigmaIIFourierSummand (M : ℝ) fhat ell m2 tau‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro ell hellSmall hellNotRetained
        exact mul_nonneg (sourceBump_nonneg 1 zero_lt_one _)
          (intervalIntegral.integral_nonneg (by linarith) fun tau htau =>
            sq_nonneg _)

/-- Variable-radius version used for the source's subpower ell cutoff. -/
theorem sigmaIIEllRetainedFinite_const_one_le_sourceBump_radius
    (ellRange m2Range : Finset ℤ) (fhat : ℝ → ℂ)
    {M : ℕ} (hM : 0 < M) {T Ctau R : ℝ}
    (hT : 0 < T) (hCtau : 0 ≤ Ctau) (hR : 0 < R) :
    sigmaIIEllRetainedFinite ellRange m2Range
        (R * T / (M : ℝ)) (fun _ => 1) fhat
        (M : ℝ) T (M : ℝ) Ctau ≤
      sigmaIIFinite (sourceBumpEllRange M T R) m2Range
        (fun x => sourceBump R hR x) fhat
        (M : ℝ) T (M : ℝ) Ctau := by
  have hMreal : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  let retained := ellRange.filter fun ell : ℤ =>
    |(ell : ℝ)| < R * T / (M : ℝ)
  have hsubset : retained ⊆ sourceBumpEllRange M T R := by
    intro ell hell
    have hell' := (Finset.mem_filter.mp hell).2
    apply mem_sourceIntegerWindow_zero_of_abs_le
    have hratio : 0 < R * T / (M : ℝ) := by positivity
    have : |(ell : ℝ)| ≤ 2 * R * T / (M : ℝ) := by
      calc
        |(ell : ℝ)| ≤ R * T / (M : ℝ) := hell'.le
        _ ≤ 2 * R * T / (M : ℝ) := by
          rw [show 2 * R * T / (M : ℝ) =
            2 * (R * T / (M : ℝ)) by ring]
          linarith
    simpa only [sourceBumpEllRange] using this
  have hplateau : ∀ ell ∈ retained,
      sourceBump R hR ((M : ℝ) * (ell : ℝ) / T) = 1 := by
    intro ell hell
    have hell' := (Finset.mem_filter.mp hell).2
    apply sourceBump_eq_one_of_abs_le
    have hscaled :
        |(M : ℝ) * (ell : ℝ) / T| =
          (M : ℝ) * |(ell : ℝ)| / T := by
      rw [abs_div, abs_mul, abs_of_pos hMreal, abs_of_pos hT]
    rw [hscaled]
    have hmul : (M : ℝ) * |(ell : ℝ)| < R * T := by
      have := (lt_div_iff₀ hMreal).mp hell'
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    exact ((div_lt_iff₀ hT).2 hmul).le
  unfold sigmaIIEllRetainedFinite sigmaIIFinite
  change (∑ ell ∈ retained,
      (1 : ℝ) * ∫ tau in -Ctau..Ctau,
        ‖∑ m2 ∈ m2Range,
          sigmaIIFourierSummand (M : ℝ) fhat ell m2 tau‖ ^ 2) ≤ _
  calc
    (∑ ell ∈ retained,
        (1 : ℝ) * ∫ tau in -Ctau..Ctau,
          ‖∑ m2 ∈ m2Range,
            sigmaIIFourierSummand (M : ℝ) fhat ell m2 tau‖ ^ 2) =
      ∑ ell ∈ retained,
        sourceBump R hR ((M : ℝ) * (ell : ℝ) / T) *
          ∫ tau in -Ctau..Ctau,
            ‖∑ m2 ∈ m2Range,
              sigmaIIFourierSummand (M : ℝ) fhat ell m2 tau‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro ell hell
        rw [hplateau ell hell]
    _ ≤ ∑ ell ∈ sourceBumpEllRange M T R,
        sourceBump R hR ((M : ℝ) * (ell : ℝ) / T) *
          ∫ tau in -Ctau..Ctau,
            ‖∑ m2 ∈ m2Range,
              sigmaIIFourierSummand (M : ℝ) fhat ell m2 tau‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro ell hellSmall hellNotRetained
        exact mul_nonneg (sourceBump_nonneg R hR _)
          (intervalIntegral.integral_nonneg (by linarith) fun tau htau =>
            sq_nonneg _)

/-- Full source-facing ell restriction.  A large first-Poisson cover with
constant weight splits into the literal short bump `Sigma_II` and an explicit
Fourier-decay tail.  No common ell-range fiction remains. -/
theorem sigmaIIFinite_const_one_le_sourceBump_add_ellTail
    (ellRange mRange : Finset ℤ) (fhat : ℝ → ℂ)
    {M : ℕ} (hM : 0 < M) (hmRange : mRange ⊆ sourcePositiveDyadicRange M)
    {T S eta C B : ℝ} (j : ℕ)
    (hT : 0 < T) (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hB0 : 0 ≤ B) (hBT : B < T)
    (hbound : ∀ z : ℝ, z ≠ 0 →
      ‖fhat z‖ ≤ C * T ^ eta * (T / |z|) ^ j * S) :
    sigmaIIFinite ellRange mRange (fun _ => 1) fhat
        (M : ℝ) T (M : ℝ) B ≤
      sigmaIIFinite (sourceBumpEllRange M T 1) mRange
          (fun x => sourceBump 1 zero_lt_one x) fhat
          (M : ℝ) T (M : ℝ) B +
        (ellRange.card : ℝ) * 1 * (2 * B) *
          (((4 * (M : ℝ) + 3) * (2 * (M : ℝ)) *
            (C * T ^ eta *
              (T / ((M : ℝ) *
                (T / (M : ℝ) - B / (M : ℝ)))) ^ j * S)) ^ 2) := by
  have hMreal : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hN2 : (mRange.card : ℝ) ≤ 4 * (M : ℝ) + 3 := by
    calc
      (mRange.card : ℝ) ≤ ((sourcePositiveDyadicRange M).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hmRange
      _ ≤ 4 * (M : ℝ) + 3 := card_sourcePositiveDyadicRange_cast_le M
  have hNell :
      ((ellRange.filter fun ell : ℤ =>
        ¬ |(ell : ℝ)| < T / (M : ℝ)).card : ℝ) ≤
        (ellRange.card : ℝ) := by
    have hcard := Finset.card_filter_le ellRange
      (fun ell : ℤ => ¬ |(ell : ℝ)| < T / (M : ℝ))
    exact_mod_cast hcard
  have hfreq : 0 < (M : ℝ) *
      (T / (M : ℝ) - B / (M : ℝ)) := by
    have hgap : 0 < T / (M : ℝ) - B / (M : ℝ) := by
      rw [← sub_div]
      positivity
    positivity
  have hmlo : ∀ m ∈ mRange, (M : ℝ) ≤ |(m : ℝ)| := by
    intro m hm
    exact (sourcePositiveDyadicRange_abs_bounds hM (hmRange hm)).1
  have hmhi : ∀ m ∈ mRange, |(m : ℝ)| ≤ 2 * (M : ℝ) := by
    intro m hm
    simpa using (sourcePositiveDyadicRange_abs_bounds hM (hmRange hm)).2
  have htail := sigmaIIEllTailFinite_le
    ellRange mRange (fun _ => 1) fhat
    (T := T) (S := S) (eta := eta) (C := C)
    (M2 := (M : ℝ)) (M3 := (M : ℝ)) (M2lo := (M : ℝ))
    (M2hi := 2 * (M : ℝ)) (N2 := 4 * (M : ℝ) + 3)
    (L := T / (M : ℝ)) (Ctau := B) (P2 := 1)
    (Nell := (ellRange.card : ℝ)) j hT.le hS hC hMreal
    hMreal.le (by positivity : (0 : ℝ) ≤ 2 * (M : ℝ)) hN2 hB0
    (by norm_num : (0 : ℝ) ≤ 1) hNell hfreq hmlo hmhi
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) hbound
  have hretained := sigmaIIEllRetainedFinite_const_one_le_sourceBump
    ellRange mRange fhat hM hT hB0
  rw [sigmaIIFinite_eq_ellRetained_add_tail ellRange mRange
    (T / (M : ℝ)) (fun _ => 1) fhat (M : ℝ) T (M : ℝ) B]
  exact add_le_add hretained htail

/-- Variable-radius source ell restriction.  Taking `R=T^κ` moves the
discarded frequencies to size `T^(1+κ)` and exposes the saving
`(T/(R*T-B))^j` needed for a genuine power tail. -/
theorem sigmaIIFinite_const_one_le_sourceBump_radius_add_ellTail
    (ellRange mRange : Finset ℤ) (fhat : ℝ → ℂ)
    {M : ℕ} (hM : 0 < M) (hmRange : mRange ⊆ sourcePositiveDyadicRange M)
    {T S eta C B R : ℝ} (j : ℕ)
    (hT : 0 < T) (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hB0 : 0 ≤ B) (hR : 0 < R) (hBRT : B < R * T)
    (hbound : ∀ z : ℝ, z ≠ 0 →
      ‖fhat z‖ ≤ C * T ^ eta * (T / |z|) ^ j * S) :
    sigmaIIFinite ellRange mRange (fun _ => 1) fhat
        (M : ℝ) T (M : ℝ) B ≤
      sigmaIIFinite (sourceBumpEllRange M T R) mRange
          (fun x => sourceBump R hR x) fhat
          (M : ℝ) T (M : ℝ) B +
        (ellRange.card : ℝ) * 1 * (2 * B) *
          (((4 * (M : ℝ) + 3) * (2 * (M : ℝ)) *
            (C * T ^ eta *
              (T / ((M : ℝ) *
                (R * T / (M : ℝ) - B / (M : ℝ)))) ^ j * S)) ^ 2) := by
  have hMreal : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hN2 : (mRange.card : ℝ) ≤ 4 * (M : ℝ) + 3 := by
    calc
      (mRange.card : ℝ) ≤ ((sourcePositiveDyadicRange M).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hmRange
      _ ≤ 4 * (M : ℝ) + 3 := card_sourcePositiveDyadicRange_cast_le M
  have hNell :
      ((ellRange.filter fun ell : ℤ =>
        ¬ |(ell : ℝ)| < R * T / (M : ℝ)).card : ℝ) ≤
        (ellRange.card : ℝ) := by
    have hcard := Finset.card_filter_le ellRange
      (fun ell : ℤ => ¬ |(ell : ℝ)| < R * T / (M : ℝ))
    exact_mod_cast hcard
  have hfreq : 0 < (M : ℝ) *
      (R * T / (M : ℝ) - B / (M : ℝ)) := by
    have hgap : 0 < R * T / (M : ℝ) - B / (M : ℝ) := by
      rw [← sub_div]
      positivity
    positivity
  have hmlo : ∀ m ∈ mRange, (M : ℝ) ≤ |(m : ℝ)| := by
    intro m hm
    exact (sourcePositiveDyadicRange_abs_bounds hM (hmRange hm)).1
  have hmhi : ∀ m ∈ mRange, |(m : ℝ)| ≤ 2 * (M : ℝ) := by
    intro m hm
    simpa using (sourcePositiveDyadicRange_abs_bounds hM (hmRange hm)).2
  have htail := sigmaIIEllTailFinite_le
    ellRange mRange (fun _ => 1) fhat
    (T := T) (S := S) (eta := eta) (C := C)
    (M2 := (M : ℝ)) (M3 := (M : ℝ)) (M2lo := (M : ℝ))
    (M2hi := 2 * (M : ℝ)) (N2 := 4 * (M : ℝ) + 3)
    (L := R * T / (M : ℝ)) (Ctau := B) (P2 := 1)
    (Nell := (ellRange.card : ℝ)) j hT.le hS hC hMreal
    hMreal.le (by positivity : (0 : ℝ) ≤ 2 * (M : ℝ)) hN2 hB0
    (by norm_num : (0 : ℝ) ≤ 1) hNell hfreq hmlo hmhi
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) hbound
  have hretained := sigmaIIEllRetainedFinite_const_one_le_sourceBump_radius
    ellRange mRange fhat hM hT hB0 hR
  rw [sigmaIIFinite_eq_ellRetained_add_tail ellRange mRange
    (R * T / (M : ℝ)) (fun _ => 1) fhat (M : ℝ) T (M : ℝ) B]
  exact add_le_add hretained htail

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.sigmaIIEllRetainedFinite_const_one_le_sourceBump
#print axioms GuthMaynardJIteration.sigmaIIFinite_const_one_le_sourceBump_add_ellTail
#print axioms GuthMaynardJIteration.sigmaIIEllRetainedFinite_const_one_le_sourceBump_radius
#print axioms GuthMaynardJIteration.sigmaIIFinite_const_one_le_sourceBump_radius_add_ellTail
