import GuthMaynardJIterationAffineEnergy
import GuthMaynardJIterationAffineConfigs
import GuthMaynardJIterationMediumWindowCount
import GuthMaynardJIterationBumpWeld
import GuthMaynardJIterationPlancherel

/-!
# Canonical finite dyadic ranges for Guth--Maynard Section 9

The source repeatedly uses `|m₁| ∼ M₁`, `m₂ ∼ M₂`, and `|m₃| ≪ M₃`.
This file gives those ranges literal finite integer definitions and proves the
nonvanishing, size, ratio, and cardinality facts needed by the existing
Fourier/Poisson DAG.  No analytic estimate occurs here.
-/

open scoped BigOperators Real SchwartzMap

noncomputable section
namespace GuthMaynardJIteration

def sourcePositiveDyadicRange (M : ℕ) : Finset ℤ :=
  Finset.Icc (M : ℤ) (2 * M : ℤ)

def sourceSignedDyadicRange (M : ℕ) : Finset ℤ :=
  Finset.Icc (-(2 * M : ℤ)) (-(M : ℤ)) ∪
    Finset.Icc (M : ℤ) (2 * M : ℤ)

def sourceCenteredRange (M : ℕ) : Finset ℤ :=
  Finset.Icc (-(M : ℤ)) (M : ℤ)

theorem mem_sourcePositiveDyadicRange_iff {M : ℕ} {m : ℤ} :
    m ∈ sourcePositiveDyadicRange M ↔ (M : ℤ) ≤ m ∧ m ≤ (2 * M : ℤ) := by
  simp [sourcePositiveDyadicRange]

theorem mem_sourceSignedDyadicRange_iff {M : ℕ} {m : ℤ} :
    m ∈ sourceSignedDyadicRange M ↔
      (-(2 * M : ℤ) ≤ m ∧ m ≤ -(M : ℤ)) ∨
        ((M : ℤ) ≤ m ∧ m ≤ (2 * M : ℤ)) := by
  simp [sourceSignedDyadicRange]

theorem mem_sourceCenteredRange_iff {M : ℕ} {m : ℤ} :
    m ∈ sourceCenteredRange M ↔ -(M : ℤ) ≤ m ∧ m ≤ (M : ℤ) := by
  simp [sourceCenteredRange]

theorem sourcePositiveDyadicRange_pos {M : ℕ} (hM : 0 < M)
    {m : ℤ} (hm : m ∈ sourcePositiveDyadicRange M) : 0 < m := by
  rw [mem_sourcePositiveDyadicRange_iff] at hm
  exact lt_of_lt_of_le (by exact_mod_cast hM) hm.1

theorem sourcePositiveDyadicRange_ne_zero {M : ℕ} (hM : 0 < M)
    {m : ℤ} (hm : m ∈ sourcePositiveDyadicRange M) : m ≠ 0 :=
  (sourcePositiveDyadicRange_pos hM hm).ne'

theorem sourcePositiveDyadicRange_abs_bounds {M : ℕ} (hM : 0 < M)
    {m : ℤ} (hm : m ∈ sourcePositiveDyadicRange M) :
    (M : ℝ) ≤ |(m : ℝ)| ∧ |(m : ℝ)| ≤ (2 * M : ℝ) := by
  have hpos := sourcePositiveDyadicRange_pos hM hm
  rw [mem_sourcePositiveDyadicRange_iff] at hm
  rw [abs_of_pos (by exact_mod_cast hpos)]
  constructor
  · exact_mod_cast hm.1
  · exact_mod_cast hm.2

theorem sourceSignedDyadicRange_abs_bounds {M : ℕ} (hM : 0 < M)
    {m : ℤ} (hm : m ∈ sourceSignedDyadicRange M) :
    (M : ℝ) ≤ |(m : ℝ)| ∧ |(m : ℝ)| ≤ (2 * M : ℝ) := by
  rw [mem_sourceSignedDyadicRange_iff] at hm
  rcases hm with hm | hm
  · have hmneg : m < 0 := by omega
    rw [abs_of_neg (by exact_mod_cast hmneg)]
    constructor
    · have : (M : ℤ) ≤ -m := by omega
      exact_mod_cast this
    · have : -m ≤ (2 * M : ℤ) := by omega
      exact_mod_cast this
  · have hmpos : 0 < m := lt_of_lt_of_le (by exact_mod_cast hM) hm.1
    rw [abs_of_pos (by exact_mod_cast hmpos)]
    constructor
    · exact_mod_cast hm.1
    · exact_mod_cast hm.2

theorem sourceSignedDyadicRange_ne_zero {M : ℕ} (hM : 0 < M)
    {m : ℤ} (hm : m ∈ sourceSignedDyadicRange M) : m ≠ 0 := by
  have hlo := (sourceSignedDyadicRange_abs_bounds hM hm).1
  intro hz
  subst m
  norm_num at hlo
  exact (Nat.cast_pos.mpr hM).ne' hlo

theorem sourceCenteredRange_abs_le {M : ℕ} {m : ℤ}
    (hm : m ∈ sourceCenteredRange M) : |(m : ℝ)| ≤ (M : ℝ) := by
  rw [mem_sourceCenteredRange_iff] at hm
  exact abs_le.mpr (by
    constructor
    · exact_mod_cast hm.1
    · exact_mod_cast hm.2)

theorem sourceCenteredRange_ratio_abs_le_one {M : ℕ} (hM : 0 < M)
    {m : ℤ} (hm : m ∈ sourceCenteredRange M) :
    |(m : ℝ) / (M : ℝ)| ≤ 1 := by
  have hMabs : |(M : ℝ)| = (M : ℝ) := abs_of_pos (Nat.cast_pos.mpr hM)
  rw [abs_div, hMabs]
  exact (div_le_one (Nat.cast_pos.mpr hM)).2 (sourceCenteredRange_abs_le hm)

theorem sourceSignedDyadicRange_subset_window (M : ℕ) :
    sourceSignedDyadicRange M ⊆ sourceIntegerWindow 0 (2 * M : ℝ) := by
  intro m hm
  apply mem_sourceIntegerWindow_zero_of_abs_le
  rw [mem_sourceSignedDyadicRange_iff] at hm
  rcases hm with hm | hm
  · rw [abs_of_nonpos]
    · have : -m ≤ (2 * M : ℤ) := by omega
      exact_mod_cast this
    · have hM0 : (0 : ℤ) ≤ (M : ℤ) := by exact_mod_cast Nat.zero_le M
      have : m ≤ 0 := by omega
      exact_mod_cast this
  · rw [abs_of_nonneg]
    · exact_mod_cast hm.2
    · have hM0 : (0 : ℤ) ≤ (M : ℤ) := by exact_mod_cast Nat.zero_le M
      have : 0 ≤ m := by omega
      exact_mod_cast this

theorem sourcePositiveDyadicRange_subset_window (M : ℕ) :
    sourcePositiveDyadicRange M ⊆ sourceIntegerWindow 0 (2 * M : ℝ) := by
  intro m hm
  apply mem_sourceIntegerWindow_zero_of_abs_le
  rw [mem_sourcePositiveDyadicRange_iff] at hm
  have hm0 : 0 ≤ m := hm.1.trans' (by simp)
  rw [abs_of_nonneg (by exact_mod_cast hm0)]
  exact_mod_cast hm.2

theorem sourceCenteredRange_subset_window (M : ℕ) :
    sourceCenteredRange M ⊆ sourceIntegerWindow 0 (M : ℝ) := by
  intro m hm
  exact mem_sourceIntegerWindow_zero_of_abs_le (sourceCenteredRange_abs_le hm)

theorem sourceSignedDyadicRange_subset_masterWindow {Mi M : ℕ} (hMi : Mi ≤ M) :
    sourceSignedDyadicRange Mi ⊆ sourceIntegerWindow 0 (2 * M : ℝ) := by
  intro m hm
  apply mem_sourceIntegerWindow_zero_of_abs_le
  have hupper : |(m : ℝ)| ≤ (2 * Mi : ℝ) := by
    rw [mem_sourceSignedDyadicRange_iff] at hm
    rcases hm with hm | hm
    · rw [abs_of_nonpos]
      · have : -m ≤ (2 * Mi : ℤ) := by omega
        exact_mod_cast this
      · have hMi0 : (0 : ℤ) ≤ (Mi : ℤ) := by exact_mod_cast Nat.zero_le Mi
        have : m ≤ 0 := by omega
        exact_mod_cast this
    · rw [abs_of_nonneg]
      · exact_mod_cast hm.2
      · have hMi0 : (0 : ℤ) ≤ (Mi : ℤ) := by exact_mod_cast Nat.zero_le Mi
        have : 0 ≤ m := by omega
        exact_mod_cast this
  have hscale : (2 * Mi : ℝ) ≤ (2 * M : ℝ) := by exact_mod_cast Nat.mul_le_mul_left 2 hMi
  exact hupper.trans hscale

theorem sourcePositiveDyadicRange_subset_masterWindow {Mi M : ℕ} (hMi : Mi ≤ M) :
    sourcePositiveDyadicRange Mi ⊆ sourceIntegerWindow 0 (2 * M : ℝ) := by
  intro m hm
  apply mem_sourceIntegerWindow_zero_of_abs_le
  rw [mem_sourcePositiveDyadicRange_iff] at hm
  have hm0 : (0 : ℤ) ≤ m := by
    have hMi0 : (0 : ℤ) ≤ (Mi : ℤ) := by exact_mod_cast Nat.zero_le Mi
    omega
  rw [abs_of_nonneg (by exact_mod_cast hm0)]
  have hmReal : (m : ℝ) ≤ (2 * Mi : ℝ) := by exact_mod_cast hm.2
  have hscale : (2 * Mi : ℝ) ≤ (2 * M : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_left 2 hMi
  exact hmReal.trans hscale

theorem sourceCenteredRange_subset_masterWindow {Mi M : ℕ} (hMi : Mi ≤ M) :
    sourceCenteredRange Mi ⊆ sourceIntegerWindow 0 (M : ℝ) := by
  intro m hm
  apply mem_sourceIntegerWindow_zero_of_abs_le
  exact (sourceCenteredRange_abs_le hm).trans (by exact_mod_cast hMi)

/-- Every literal dyadic branch with all three scales at most `M` is an
admissible member of one common finite configuration family. -/
theorem sourceDyadicConfig_mem_master
    {M1 M2 M3 M : ℕ} (hM1 : M1 ≤ M) (hM2 : M2 ≤ M) (hM3 : M3 ≤ M) :
    (sourceSignedDyadicRange M1, sourcePositiveDyadicRange M2,
        sourceCenteredRange M3) ∈
      sourceAffineConfigs (sourceIntegerWindow 0 (2 * M : ℝ))
        (sourceIntegerWindow 0 (M : ℝ)) := by
  rw [mem_sourceAffineConfigs_iff]
  exact ⟨sourceSignedDyadicRange_subset_masterWindow hM1,
    sourcePositiveDyadicRange_subset_masterWindow hM2,
    sourceCenteredRange_subset_masterWindow hM3⟩

theorem sourceDyadicEnergy_le_masterJ
    (f : ℝ → ℝ) {M1 M2 M3 M : ℕ}
    (hM1 : M1 ≤ M) (hM2 : M2 ≤ M) (hM3 : M3 ≤ M) :
    sourceFiniteAffineEnergy (sourceSignedDyadicRange M1)
        (sourcePositiveDyadicRange M2) (sourceCenteredRange M3) f ≤
      sourceAffineJ
        (sourceAffineConfigs (sourceIntegerWindow 0 (2 * M : ℝ))
          (sourceIntegerWindow 0 (M : ℝ))) f := by
  exact sourceFiniteAffineEnergy_le_canonicalJ
    (sourceIntegerWindow 0 (2 * M : ℝ)) (sourceIntegerWindow 0 (M : ℝ)) f
    (sourceSignedDyadicRange_subset_masterWindow hM1)
    (sourcePositiveDyadicRange_subset_masterWindow hM2)
    (sourceCenteredRange_subset_masterWindow hM3)

/-- Literal dyadic specialization of the exact `(9.2)` Plancherel weld. -/
theorem sourceDyadicEnergy_eq_fourierIntegral_sourceBump
    (f : ℝ → ℝ) (fSchwartz : 𝓢(ℝ, ℂ))
    {M1 M2 M3 : ℕ} (hM1 : 0 < M1) (hM2 : 0 < M2) (hM3 : 0 < M3)
    (hf : ∀ u : ℝ, fSchwartz u = (f u : ℂ)) :
    sourceFiniteAffineEnergy (sourceSignedDyadicRange M1)
        (sourcePositiveDyadicRange M2) (sourceCenteredRange M3) f =
      ∫ xi : ℝ,
        ‖FourierTransform.fourier
          (sourceGFinite (sourceSignedDyadicRange M1)
            (sourcePositiveDyadicRange M2) (sourceCenteredRange M3)
            (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
            (fun u : ℝ => fSchwartz u) (M3 : ℝ)) xi‖ ^ 2 := by
  let R1 := sourceSignedDyadicRange M1
  let R2 := sourcePositiveDyadicRange M2
  let R3 := sourceCenteredRange M3
  let psi1 : ℝ → ℂ := fun x => (sourceBump 1 zero_lt_one x : ℂ)
  have hm1 : ∀ m ∈ R1, m ≠ 0 :=
    fun _ hm => sourceSignedDyadicRange_ne_zero hM1 hm
  have hm2 : ∀ m ∈ R2, m ≠ 0 :=
    fun _ hm => sourcePositiveDyadicRange_ne_zero hM2 hm
  have hm3 : ∀ m ∈ R3, |(m : ℝ) / (M3 : ℝ)| ≤ (1 : ℝ) :=
    fun _ hm => sourceCenteredRange_ratio_abs_le_one hM3 hm
  have hsource :
      sourceGFinite R1 R2 R3 psi1 (fun u : ℝ => fSchwartz u) (M3 : ℝ) =
        sourceGFinite R1 R2 R3 psi1 (fun u : ℝ => (f u : ℂ)) (M3 : ℝ) := by
    funext u
    unfold sourceGFinite sourceGSummand
    apply Finset.sum_congr rfl
    intro m1 hm1mem
    apply Finset.sum_congr rfl
    intro m2 hm2mem
    apply Finset.sum_congr rfl
    intro m3 hm3mem
    exact congrArg (fun z : ℂ => psi1 ((m3 : ℝ) / (M3 : ℝ)) * z)
      (hf (((m1 : ℝ) * u + (m3 : ℝ)) / (m2 : ℝ)))
  calc
    sourceFiniteAffineEnergy R1 R2 R3 f =
        ∫ u : ℝ, ‖sourceGFinite R1 R2 R3 psi1
          (fun x : ℝ => (f x : ℂ)) (M3 : ℝ) u‖ ^ 2 :=
      sourceFiniteAffineEnergy_eq_integral_norm_sourceGFinite_sourceBump
        R1 R2 R3 f zero_lt_one hm3
    _ = ∫ u : ℝ, ‖sourceGFinite R1 R2 R3 psi1
          (fun x : ℝ => fSchwartz x) (M3 : ℝ) u‖ ^ 2 := by rw [hsource]
    _ = ∫ xi : ℝ, ‖FourierTransform.fourier
          (sourceGFinite R1 R2 R3 psi1
            (fun x : ℝ => fSchwartz x) (M3 : ℝ)) xi‖ ^ 2 :=
      (integral_norm_sq_fourier_sourceGFinite R1 R2 R3 psi1 fSchwartz
        (M3 : ℝ) hm1 hm2).symm

theorem card_sourceSignedDyadicRange_cast_le (M : ℕ) :
    ((sourceSignedDyadicRange M).card : ℝ) ≤ 4 * M + 3 := by
  calc
    ((sourceSignedDyadicRange M).card : ℝ) ≤
        ((sourceIntegerWindow 0 (2 * M : ℝ)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (sourceSignedDyadicRange_subset_window M)
    _ ≤ 2 * (2 * M : ℝ) + 3 :=
      card_sourceIntegerWindow_cast_le 0 (2 * M : ℝ) (by positivity)
    _ = 4 * M + 3 := by push_cast; ring

theorem card_sourcePositiveDyadicRange_cast_le (M : ℕ) :
    ((sourcePositiveDyadicRange M).card : ℝ) ≤ 4 * M + 3 := by
  calc
    ((sourcePositiveDyadicRange M).card : ℝ) ≤
        ((sourceIntegerWindow 0 (2 * M : ℝ)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (sourcePositiveDyadicRange_subset_window M)
    _ ≤ 2 * (2 * M : ℝ) + 3 :=
      card_sourceIntegerWindow_cast_le 0 (2 * M : ℝ) (by positivity)
    _ = 4 * M + 3 := by push_cast; ring

theorem card_sourceCenteredRange_cast_le (M : ℕ) :
    ((sourceCenteredRange M).card : ℝ) ≤ 2 * M + 3 := by
  calc
    ((sourceCenteredRange M).card : ℝ) ≤
        ((sourceIntegerWindow 0 (M : ℝ)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (sourceCenteredRange_subset_window M)
    _ ≤ 2 * (M : ℝ) + 3 :=
      card_sourceIntegerWindow_cast_le 0 (M : ℝ) (by positivity)
    _ = 2 * M + 3 := by norm_num

theorem sourceDyadic_ratio_bounds {M1 M2 : ℕ} (hM1 : 0 < M1) (hM2 : 0 < M2)
    {m1 m2 : ℤ} (hm1 : m1 ∈ sourceSignedDyadicRange M1)
    (hm2 : m2 ∈ sourcePositiveDyadicRange M2) :
    (M2 : ℝ) / (2 * M1 : ℝ) ≤ |(m2 : ℝ) / (m1 : ℝ)| ∧
      |(m2 : ℝ) / (m1 : ℝ)| ≤ (2 * M2 : ℝ) / (M1 : ℝ) := by
  have h1 := sourceSignedDyadicRange_abs_bounds hM1 hm1
  have h2 := sourcePositiveDyadicRange_abs_bounds hM2 hm2
  have hM1R : 0 < (M1 : ℝ) := Nat.cast_pos.mpr hM1
  have h2M1R : 0 < (2 * M1 : ℝ) := by positivity
  have hm1abs : 0 < |(m1 : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast sourceSignedDyadicRange_ne_zero hM1 hm1
  rw [abs_div]
  constructor
  · calc
      (M2 : ℝ) / (2 * M1 : ℝ) ≤ |(m2 : ℝ)| / (2 * M1 : ℝ) :=
        div_le_div_of_nonneg_right h2.1 h2M1R.le
      _ ≤ |(m2 : ℝ)| / |(m1 : ℝ)| :=
        div_le_div_of_nonneg_left (abs_nonneg _) hm1abs h1.2
  · calc
      |(m2 : ℝ)| / |(m1 : ℝ)| ≤ (2 * M2 : ℝ) / |(m1 : ℝ)| :=
        div_le_div_of_nonneg_right h2.2 hm1abs.le
      _ ≤ (2 * M2 : ℝ) / (M1 : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hM1R h1.1

/-! ## Literal polynomial scale bounds for source region III -/

theorem card_sourceSignedDyadicRange_cast_le_seven_mul_time
    {M : ℕ} {T : ℝ} (hT : 1 ≤ T) (hM : (M : ℝ) ≤ T) :
    ((sourceSignedDyadicRange M).card : ℝ) ≤ 7 * T := by
  have hcard := card_sourceSignedDyadicRange_cast_le M
  have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  nlinarith

theorem card_sourcePositiveDyadicRange_cast_le_seven_mul_time
    {M : ℕ} {T : ℝ} (hT : 1 ≤ T) (hM : (M : ℝ) ≤ T) :
    ((sourcePositiveDyadicRange M).card : ℝ) ≤ 7 * T := by
  have hcard := card_sourcePositiveDyadicRange_cast_le M
  have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  nlinarith

theorem card_sourceCenteredRange_cast_le_five_mul_time
    {M : ℕ} {T : ℝ} (hT : 1 ≤ T) (hM : (M : ℝ) ≤ T) :
    ((sourceCenteredRange M).card : ℝ) ≤ 5 * T := by
  have hcard := card_sourceCenteredRange_cast_le M
  have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  nlinarith

/-- The literal dyadic ratio has the upper scale `2*T` whenever the second
dyadic length is at most `T`. -/
theorem sourceDyadic_ratio_upper_le_two_mul_time
    {M1 M2 : ℕ} (hM1 : 0 < M1) (hM2 : 0 < M2)
    {T : ℝ} (hM2T : (M2 : ℝ) ≤ T)
    {m1 m2 : ℤ} (hm1 : m1 ∈ sourceSignedDyadicRange M1)
    (hm2 : m2 ∈ sourcePositiveDyadicRange M2) :
    |(m2 : ℝ) / (m1 : ℝ)| ≤ 2 * T := by
  have hraw := (sourceDyadic_ratio_bounds hM1 hM2 hm1 hm2).2
  have hM1one : (1 : ℝ) ≤ (M1 : ℝ) := by exact_mod_cast hM1
  calc
    |(m2 : ℝ) / (m1 : ℝ)| ≤ (2 * M2 : ℝ) / (M1 : ℝ) := hraw
    _ ≤ (2 * M2 : ℝ) := div_le_self (by positivity) hM1one
    _ ≤ 2 * T := by exact mul_le_mul_of_nonneg_left hM2T (by norm_num)

/-- Exact reciprocal lower-ratio budget used by the region-III envelope.
The source ranges actually cost only `2*T^2`; the target keeps the looser
`2*T^5` budget used by the global adapter. -/
theorem sourceDyadic_reciprocal_ratio_le_two_mul_time_pow_five
    {M1 M2 : ℕ} (hM1 : 0 < M1) (hM2 : 0 < M2)
    {T : ℝ} (hT : 1 ≤ T) (hM1T : (M1 : ℝ) ≤ T) :
    T / ((M2 : ℝ) / (2 * M1 : ℝ)) ≤ 2 * T ^ 5 := by
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hM1R : 0 < (M1 : ℝ) := Nat.cast_pos.mpr hM1
  have hM2R : 0 < (M2 : ℝ) := Nat.cast_pos.mpr hM2
  have hM2one : (1 : ℝ) ≤ (M2 : ℝ) := by exact_mod_cast hM2
  calc
    T / ((M2 : ℝ) / (2 * M1 : ℝ)) =
        (2 * T * (M1 : ℝ)) / (M2 : ℝ) := by
      field_simp [hM1R.ne', hM2R.ne']
    _ ≤ 2 * T * (M1 : ℝ) := div_le_self (by positivity) hM2one
    _ ≤ 2 * T * T := by
      exact mul_le_mul_of_nonneg_left hM1T (mul_nonneg (by norm_num) hT0)
    _ = 2 * T ^ 2 := by ring
    _ ≤ 2 * T ^ 5 := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hT (show 2 ≤ 5 by omega)) (by norm_num)

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.sourcePositiveDyadicRange_ne_zero
#print axioms GuthMaynardJIteration.sourceSignedDyadicRange_ne_zero
#print axioms GuthMaynardJIteration.sourceCenteredRange_ratio_abs_le_one
#print axioms GuthMaynardJIteration.sourceDyadic_ratio_bounds
#print axioms GuthMaynardJIteration.sourceDyadicConfig_mem_master
#print axioms GuthMaynardJIteration.sourceDyadicEnergy_le_masterJ
#print axioms GuthMaynardJIteration.sourceDyadicEnergy_eq_fourierIntegral_sourceBump
#print axioms GuthMaynardJIteration.card_sourceSignedDyadicRange_cast_le
#print axioms GuthMaynardJIteration.card_sourcePositiveDyadicRange_cast_le
#print axioms GuthMaynardJIteration.card_sourceCenteredRange_cast_le
#print axioms GuthMaynardJIteration.card_sourceSignedDyadicRange_cast_le_seven_mul_time
#print axioms GuthMaynardJIteration.card_sourcePositiveDyadicRange_cast_le_seven_mul_time
#print axioms GuthMaynardJIteration.card_sourceCenteredRange_cast_le_five_mul_time
#print axioms GuthMaynardJIteration.sourceDyadic_ratio_upper_le_two_mul_time
#print axioms GuthMaynardJIteration.sourceDyadic_reciprocal_ratio_le_two_mul_time_pow_five
