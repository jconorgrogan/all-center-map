import GuthMaynardSectionThreeCutoffDerivativeBudget

/-!
# Guth--Maynard Proposition 5.1: the analytic `S₁` source

The `S₁` terms in Guth--Maynard are the cubic-trace frequencies for which
exactly one of `m₁,m₂,m₃` is nonzero.  Their proof uses both halves of Lemma
4.3: vertical decay at frequency zero for the two zero-frequency factors,
and horizontal Fourier decay for the remaining nonzero frequency.

The horizontal half was already certified by
`lemma43_part_one_sectionThreeOscillatory`.  This file closes the missing
vertical half for the literal Section 3 cutoff, by identifying the
zero-frequency Fourier transform exactly with the cutoff Mellin transform.
It then records the three pointwise estimates used in Proposition 5.1.  No
large-value theorem, Heath--Brown estimate, or `S₃` input is used here.
-/

namespace GuthMaynardS1Source

open Real Complex Set MeasureTheory
open scoped FourierTransform SchwartzMap
open GuthMaynardSectionThreeCutoff
open GuthMaynardSectionThreeCutoffDerivativeBudget

noncomputable section

/-- The literal Fourier coefficient `\widehat h_t(ξ)` from source (4.4), for
the concrete legal Section 3 cutoff. -/
def sourceHhat (t xi : ℝ) : ℂ :=
  (𝓕 (sectionThreeOscillatorySchwartz t) : 𝓢(ℝ, ℂ)) xi

/-- At zero Fourier frequency the source kernel is exactly the Mellin
transform on `Re(s)=1`.  This is the missing bridge needed to obtain Lemma
4.3(2) from the already-certified Mellin rapid-decay theorem. -/
theorem sourceHhat_zero_eq_mellin (t : ℝ) :
    sourceHhat t 0 =
      mellin sectionThreeCutoff ((1 : ℂ) + t * Complex.I) := by
  rw [sourceHhat]
  change FourierTransform.fourier
    (fun x : ℝ => sectionThreeOscillatorySchwartz t x) 0 = _
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [sectionThreeOscillatorySchwartz_apply]
  unfold sectionThreeOscillatory mellin
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  by_cases hx : 0 < x
  · simp only [mul_zero, ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
    simp only [Set.mem_Ioi, hx, Set.indicator_of_mem]
    rw [show ((1 : ℂ) + t * Complex.I) - 1 =
      Complex.I * (t : ℂ) by ring]
    ring
  · have hsupp : sectionThreeCutoff x = 0 := by
      apply sectionThreeCutoff_supported
      simp only [Set.mem_Icc, not_and_or, not_le]
      exact Or.inl (by linarith)
    simp [show x ∉ Set.Ioi (0 : ℝ) by exact hx, hsupp]

/-- Exact arbitrary-order vertical decay at zero frequency.  This is the
literal estimate invoked in source (5.1), with the fixed Schwartz seminorm
left visible instead of asymptotic notation. -/
theorem absScaledPow_mul_norm_sourceHhat_zero_le
    (t : ℝ) (j : ℕ) :
    |t / (2 * Real.pi)| ^ j * ‖sourceHhat t 0‖ ≤
      SchwartzMap.seminorm ℂ j 0
        (𝓕 (GuthMaynardMellinRapidDecay.mellinLogLiftSchwartz
          sectionThreeCutoff
          (GuthMaynardMellinRapidDecay.mellinLogLift_hasCompactSupport
            (by norm_num) (by norm_num) sectionThreeCutoff_supported)
          (GuthMaynardMellinRapidDecay.mellinLogLift_contDiff
            sectionThreeCutoff_contDiff)) : 𝓢(ℝ, ℂ)) := by
  rw [sourceHhat_zero_eq_mellin]
  exact sectionThreeCutoff_mellin_rapidDecay j t

/-- Quotient form of the vertical decay when `t ≠ 0`. -/
theorem norm_sourceHhat_zero_le_div
    (t : ℝ) (j : ℕ) (ht : t ≠ 0) :
    ‖sourceHhat t 0‖ ≤
      SchwartzMap.seminorm ℂ j 0
          (𝓕 (GuthMaynardMellinRapidDecay.mellinLogLiftSchwartz
            sectionThreeCutoff
            (GuthMaynardMellinRapidDecay.mellinLogLift_hasCompactSupport
              (by norm_num) (by norm_num) sectionThreeCutoff_supported)
            (GuthMaynardMellinRapidDecay.mellinLogLift_contDiff
              sectionThreeCutoff_contDiff)) : 𝓢(ℝ, ℂ)) /
        |t / (2 * Real.pi)| ^ j := by
  apply (le_div_iff₀ (by positivity : 0 < |t / (2 * Real.pi)| ^ j)).2
  simpa [mul_comm] using
    absScaledPow_mul_norm_sourceHhat_zero_le t j

/-- Horizontal decay for the nonzero `mN` frequency, now exposed in the
same `sourceHhat` notation as the vertical estimate. -/
theorem norm_sourceHhat_le_horizontal
    (t : ℝ) (j : ℕ) {xi : ℝ} (hxi : xi ≠ 0) :
    ‖sourceHhat t xi‖ ≤
      (lemma43DerivativeConstant j * (1 + |t|) ^ j) / |xi| ^ j := by
  exact lemma43_part_one_sectionThreeOscillatory t j hxi

/-- Uniform bound for either of the two factors not assigned the rapid
decay.  It is Lemma 4.3(1) with derivative order zero, proved directly so it
also covers `xi=0`. -/
theorem norm_sourceHhat_le_fixed (t xi : ℝ) :
    ‖sourceHhat t xi‖ ≤ lemma43DerivativeConstant 0 := by
  have hfourier :=
    GuthMaynardLemma43FourierIBP.absPow_mul_norm_fourier_le_integral_iteratedDerivative
      (sectionThreeOscillatorySchwartz t) 0 xi
  have hbudget :=
    integral_norm_iteratedDeriv_sectionThreeOscillatory_le t 0
  rw [show sourceHhat t xi =
      (𝓕 (sectionThreeOscillatorySchwartz t) : 𝓢(ℝ, ℂ)) xi from rfl]
  simpa using hfourier.trans hbudget

/-- One orientation of the `S₁` cubic kernel: only the third frequency is
nonzero.  The other two orientations are cyclic permutations. -/
def sourceS1KernelThird (N : ℕ) (t₁ t₂ t₃ : ℝ) (m : ℤ) : ℂ :=
  sourceHhat (t₁ - t₂) 0 * sourceHhat (t₂ - t₃) 0 *
    sourceHhat (t₃ - t₁) ((m : ℝ) * N)

/-- Finite truncation of one orientation of the absolute `S₁` mass.  The
source has three cyclic orientations; their equality follows by relabeling
the three ordinate variables. -/
def sourceS1ThirdFiniteMass
    (N : ℕ) (W : Finset ℝ) (M : Finset ℤ) : ℝ :=
  ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, ∑ m ∈ M,
    ‖sourceS1KernelThird N t₁ t₂ t₃ m‖

/-- Exact finite cardinality assembly used repeatedly after splitting the
`S₁` ranges.  It turns any uniform pointwise kernel bound into the literal
four-fold sum bound, with no asymptotic convention hidden. -/
theorem sourceS1ThirdFiniteMass_le_card
    {N : ℕ} {W : Finset ℝ} {M : Finset ℤ} {B : ℝ}
    (hpoint : ∀ t₁ ∈ W, ∀ t₂ ∈ W, ∀ t₃ ∈ W, ∀ m ∈ M,
      ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ ≤ B) :
    sourceS1ThirdFiniteMass N W M ≤
      (W.card : ℝ) ^ 3 * (M.card : ℝ) * B := by
  unfold sourceS1ThirdFiniteMass
  calc
    (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, ∑ m ∈ M,
        ‖sourceS1KernelThird N t₁ t₂ t₃ m‖) ≤
      ∑ _t₁ ∈ W, ∑ _t₂ ∈ W, ∑ _t₃ ∈ W, ∑ _m ∈ M, B := by
        apply Finset.sum_le_sum
        intro t₁ ht₁
        apply Finset.sum_le_sum
        intro t₂ ht₂
        apply Finset.sum_le_sum
        intro t₃ ht₃
        apply Finset.sum_le_sum
        intro m hm
        exact hpoint t₁ ht₁ t₂ ht₂ t₃ ht₃ m hm
    _ = (W.card : ℝ) ^ 3 * (M.card : ℝ) * B := by
      simp
      ring

def sourceS1ThirdFiniteFirstGapMass
    (N : ℕ) (W : Finset ℝ) (M : Finset ℤ) : ℝ :=
  ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, ∑ m ∈ M,
    if t₁ ≠ t₂ then ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ else 0

def sourceS1ThirdFiniteSecondGapMass
    (N : ℕ) (W : Finset ℝ) (M : Finset ℤ) : ℝ :=
  ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, ∑ m ∈ M,
    if t₁ = t₂ ∧ t₂ ≠ t₃ then
      ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ else 0

def sourceS1ThirdFiniteDiagonalMass
    (N : ℕ) (W : Finset ℝ) (M : Finset ℤ) : ℝ :=
  ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, ∑ m ∈ M,
    if t₁ = t₂ ∧ t₂ = t₃ then
      ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ else 0

/-- Exact, disjoint finite-triple partition in Proposition 5.1. -/
theorem sourceS1ThirdFiniteMass_partition
    (N : ℕ) (W : Finset ℝ) (M : Finset ℤ) :
    sourceS1ThirdFiniteMass N W M =
      sourceS1ThirdFiniteFirstGapMass N W M +
      sourceS1ThirdFiniteSecondGapMass N W M +
      sourceS1ThirdFiniteDiagonalMass N W M := by
  unfold sourceS1ThirdFiniteMass sourceS1ThirdFiniteFirstGapMass
    sourceS1ThirdFiniteSecondGapMass sourceS1ThirdFiniteDiagonalMass
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t₁ ht₁
  apply Finset.sum_congr rfl
  intro t₂ ht₂
  apply Finset.sum_congr rfl
  intro t₃ ht₃
  apply Finset.sum_congr rfl
  intro m hm
  by_cases h₁₂ : t₁ = t₂
  · by_cases h₂₃ : t₂ = t₃
    · simp [h₁₂, h₂₃]
    · simp [h₁₂, h₂₃]
  · simp [h₁₂]

/-- The `t₁ != t₂` part of the finite `m` range in Proposition 5.1.  This
is the exact three-factor deterministic assembly after source (5.1). -/
theorem norm_sourceS1KernelThird_le_of_first_gap
    {N : ℕ} {t₁ t₂ t₃ R : ℝ} {m : ℤ} (j : ℕ)
    (hgap : R ≤ |t₁ - t₂|) (hR : 0 < R) :
    ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ ≤
      (SchwartzMap.seminorm ℂ j 0
          (𝓕 (GuthMaynardMellinRapidDecay.mellinLogLiftSchwartz
            sectionThreeCutoff
            (GuthMaynardMellinRapidDecay.mellinLogLift_hasCompactSupport
              (by norm_num) (by norm_num) sectionThreeCutoff_supported)
            (GuthMaynardMellinRapidDecay.mellinLogLift_contDiff
              sectionThreeCutoff_contDiff)) : 𝓢(ℝ, ℂ)) /
        |(t₁ - t₂) / (2 * Real.pi)| ^ j) *
      lemma43DerivativeConstant 0 ^ 2 := by
  unfold sourceS1KernelThird
  rw [norm_mul, norm_mul]
  have hdec := norm_sourceHhat_zero_le_div (t₁ - t₂) j (by
    intro hzero
    have hz : |t₁ - t₂| = 0 := by rw [hzero, abs_zero]
    linarith)
  have hsecond := norm_sourceHhat_le_fixed (t₂ - t₃) 0
  have hthird := norm_sourceHhat_le_fixed (t₃ - t₁) ((m : ℝ) * N)
  calc
    ‖sourceHhat (t₁ - t₂) 0‖ *
          ‖sourceHhat (t₂ - t₃) 0‖ *
          ‖sourceHhat (t₃ - t₁) ((m : ℝ) * N)‖ ≤
        (SchwartzMap.seminorm ℂ j 0
            (𝓕 (GuthMaynardMellinRapidDecay.mellinLogLiftSchwartz
              sectionThreeCutoff
              (GuthMaynardMellinRapidDecay.mellinLogLift_hasCompactSupport
                (by norm_num) (by norm_num) sectionThreeCutoff_supported)
              (GuthMaynardMellinRapidDecay.mellinLogLift_contDiff
                sectionThreeCutoff_contDiff)) : 𝓢(ℝ, ℂ)) /
          |(t₁ - t₂) / (2 * Real.pi)| ^ j) *
          lemma43DerivativeConstant 0 * lemma43DerivativeConstant 0 := by
      calc
        _ ≤ (SchwartzMap.seminorm ℂ j 0
              (𝓕 (GuthMaynardMellinRapidDecay.mellinLogLiftSchwartz
                sectionThreeCutoff
                (GuthMaynardMellinRapidDecay.mellinLogLift_hasCompactSupport
                  (by norm_num) (by norm_num) sectionThreeCutoff_supported)
                (GuthMaynardMellinRapidDecay.mellinLogLift_contDiff
                  sectionThreeCutoff_contDiff)) : 𝓢(ℝ, ℂ)) /
            |(t₁ - t₂) / (2 * Real.pi)| ^ j) *
            lemma43DerivativeConstant 0 *
              ‖sourceHhat (t₃ - t₁) ((m : ℝ) * N)‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul hdec hsecond (norm_nonneg _) (by positivity)
        _ ≤ _ := by
          exact mul_le_mul_of_nonneg_left hthird
            (mul_nonneg (by positivity)
              (lemma43DerivativeConstant_nonneg 0))
    _ = _ := by ring

/-- The symmetric `t₂ != t₃` part of the finite range in Proposition 5.1. -/
theorem norm_sourceS1KernelThird_le_of_second_gap
    {N : ℕ} {t₁ t₂ t₃ R : ℝ} {m : ℤ} (j : ℕ)
    (hgap : R ≤ |t₂ - t₃|) (hR : 0 < R) :
    ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ ≤
      lemma43DerivativeConstant 0 *
        (SchwartzMap.seminorm ℂ j 0
            (𝓕 (GuthMaynardMellinRapidDecay.mellinLogLiftSchwartz
              sectionThreeCutoff
              (GuthMaynardMellinRapidDecay.mellinLogLift_hasCompactSupport
                (by norm_num) (by norm_num) sectionThreeCutoff_supported)
              (GuthMaynardMellinRapidDecay.mellinLogLift_contDiff
                sectionThreeCutoff_contDiff)) : 𝓢(ℝ, ℂ)) /
          |(t₂ - t₃) / (2 * Real.pi)| ^ j) *
        lemma43DerivativeConstant 0 := by
  unfold sourceS1KernelThird
  rw [norm_mul, norm_mul]
  have hfirst := norm_sourceHhat_le_fixed (t₁ - t₂) 0
  have hdec := norm_sourceHhat_zero_le_div (t₂ - t₃) j (by
    intro hzero
    have hz : |t₂ - t₃| = 0 := by rw [hzero, abs_zero]
    linarith)
  have hthird := norm_sourceHhat_le_fixed (t₃ - t₁) ((m : ℝ) * N)
  calc
    ‖sourceHhat (t₁ - t₂) 0‖ * ‖sourceHhat (t₂ - t₃) 0‖ *
        ‖sourceHhat (t₃ - t₁) ((m : ℝ) * N)‖ ≤
      lemma43DerivativeConstant 0 *
        (SchwartzMap.seminorm ℂ j 0
            (𝓕 (GuthMaynardMellinRapidDecay.mellinLogLiftSchwartz
              sectionThreeCutoff
              (GuthMaynardMellinRapidDecay.mellinLogLift_hasCompactSupport
                (by norm_num) (by norm_num) sectionThreeCutoff_supported)
              (GuthMaynardMellinRapidDecay.mellinLogLift_contDiff
                sectionThreeCutoff_contDiff)) : 𝓢(ℝ, ℂ)) /
          |(t₂ - t₃) / (2 * Real.pi)| ^ j) *
          ‖sourceHhat (t₃ - t₁) ((m : ℝ) * N)‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul hfirst hdec (norm_nonneg _)
          (lemma43DerivativeConstant_nonneg 0)
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left hthird
        (mul_nonneg (lemma43DerivativeConstant_nonneg 0) (by positivity))

/-- The far-`m` kernel before summing its absolutely convergent integer tail.
This is the deterministic three-factor assembly of source (5.4). -/
theorem norm_sourceS1KernelThird_le_far
    {N : ℕ} {t₁ t₂ t₃ T : ℝ} {m : ℤ} (j : ℕ)
    (hm : m ≠ 0) (hN : 0 < N) (hheight : |t₃ - t₁| ≤ T) :
    ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ ≤
      lemma43DerivativeConstant 0 ^ 2 *
        ((lemma43DerivativeConstant j * (1 + T) ^ j) /
          |(m : ℝ) * N| ^ j) := by
  unfold sourceS1KernelThird
  rw [norm_mul, norm_mul]
  have hfirst := norm_sourceHhat_le_fixed (t₁ - t₂) 0
  have hsecond := norm_sourceHhat_le_fixed (t₂ - t₃) 0
  have hxi : (m : ℝ) * (N : ℝ) ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.mpr hm) (Nat.cast_ne_zero.mpr hN.ne')
  have hhorizontal := norm_sourceHhat_le_horizontal (t₃ - t₁) j hxi
  have hj : (1 + |t₃ - t₁|) ^ j ≤ (1 + T) ^ j :=
    pow_le_pow_left₀ (by positivity) (by linarith) j
  have hthird : ‖sourceHhat (t₃ - t₁) ((m : ℝ) * N)‖ ≤
      (lemma43DerivativeConstant j * (1 + T) ^ j) /
        |(m : ℝ) * N| ^ j := by
    exact hhorizontal.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hj (lemma43DerivativeConstant_nonneg j))
      (by positivity))
  calc
    ‖sourceHhat (t₁ - t₂) 0‖ * ‖sourceHhat (t₂ - t₃) 0‖ *
        ‖sourceHhat (t₃ - t₁) ((m : ℝ) * N)‖ ≤
      lemma43DerivativeConstant 0 * lemma43DerivativeConstant 0 *
        ‖sourceHhat (t₃ - t₁) ((m : ℝ) * N)‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul hfirst hsecond (norm_nonneg _)
        (lemma43DerivativeConstant_nonneg 0)
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left hthird
        (mul_nonneg (lemma43DerivativeConstant_nonneg 0)
          (lemma43DerivativeConstant_nonneg 0))
    _ = _ := by ring

/-- The full-diagonal part of Proposition 5.1, assembled from source (5.3).
The two zero-frequency factors cost only the fixed order-zero constant. -/
theorem norm_sourceS1KernelThird_diagonal_le
    {N : ℕ} {t : ℝ} {m : ℤ} (hm : m ≠ 0) (hN : 0 < N) (j : ℕ) :
    ‖sourceS1KernelThird N t t t m‖ ≤
      lemma43DerivativeConstant 0 ^ 2 *
        (lemma43DerivativeConstant j / |(m : ℝ) * N| ^ j) := by
  unfold sourceS1KernelThird
  simp only [sub_self, norm_mul]
  have hzero := norm_sourceHhat_le_fixed 0 0
  have hfreq : ‖sourceHhat 0 ((m : ℝ) * N)‖ ≤
      lemma43DerivativeConstant j / |(m : ℝ) * N| ^ j := by
    have hxi : (m : ℝ) * (N : ℝ) ≠ 0 :=
      mul_ne_zero (Int.cast_ne_zero.mpr hm) (Nat.cast_ne_zero.mpr hN.ne')
    simpa using norm_sourceHhat_le_horizontal 0 j hxi
  calc
    ‖sourceHhat 0 0‖ * ‖sourceHhat 0 0‖ *
        ‖sourceHhat 0 ((m : ℝ) * N)‖ ≤
      lemma43DerivativeConstant 0 * lemma43DerivativeConstant 0 *
        (lemma43DerivativeConstant j / |(m : ℝ) * N| ^ j) := by
      calc
        _ ≤ lemma43DerivativeConstant 0 * lemma43DerivativeConstant 0 *
            ‖sourceHhat 0 ((m : ℝ) * N)‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul hzero hzero (norm_nonneg _)
            (lemma43DerivativeConstant_nonneg 0)
        _ ≤ _ := by
          exact mul_le_mul_of_nonneg_left hfreq
            (mul_nonneg (lemma43DerivativeConstant_nonneg 0)
              (lemma43DerivativeConstant_nonneg 0))
    _ = _ := by ring

/-- Source (5.1): separation of two distinct ordinates turns either
zero-frequency factor into a rapidly decaying one. -/
theorem source_equation5_1
    {t u R : ℝ} (j : ℕ) (hsep : R ≤ |t - u|) (hR : 0 < R) :
    ‖sourceHhat (t - u) 0‖ ≤
      SchwartzMap.seminorm ℂ j 0
          (𝓕 (GuthMaynardMellinRapidDecay.mellinLogLiftSchwartz
            sectionThreeCutoff
            (GuthMaynardMellinRapidDecay.mellinLogLift_hasCompactSupport
              (by norm_num) (by norm_num) sectionThreeCutoff_supported)
            (GuthMaynardMellinRapidDecay.mellinLogLift_contDiff
              sectionThreeCutoff_contDiff)) : 𝓢(ℝ, ℂ)) /
        |(t - u) / (2 * Real.pi)| ^ j := by
  apply norm_sourceHhat_zero_le_div
  intro htu
  have hz : |t - u| = 0 := by rw [htu, abs_zero]
  linarith

/-- Source (5.3): on the full diagonal, the remaining nonzero frequency is
controlled by the horizontal half of Lemma 4.3. -/
theorem source_equation5_3
    {m : ℤ} (hm : m ≠ 0) {N : ℕ} (hN : 0 < N) (j : ℕ) :
    ‖sourceHhat 0 ((m : ℝ) * N)‖ ≤
      lemma43DerivativeConstant j / |(m : ℝ) * N| ^ j := by
  have hxi : (m : ℝ) * (N : ℝ) ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.mpr hm) (Nat.cast_ne_zero.mpr hN.ne')
  simpa using norm_sourceHhat_le_horizontal 0 j hxi

/-- Source (5.4), before selecting the paper's large numerical derivative
order: bounded ordinate differences and a large nonzero frequency give the
exact ratio whose high powers make the infinite `m` tail negligible. -/
theorem source_equation5_4_raw
    {t u T : ℝ} (ht : |t - u| ≤ T) (j : ℕ)
    {m : ℤ} (hm : m ≠ 0) {N : ℕ} (hN : 0 < N) :
    ‖sourceHhat (t - u) ((m : ℝ) * N)‖ ≤
      (lemma43DerivativeConstant j * (1 + T) ^ j) /
        |(m : ℝ) * N| ^ j := by
  have hxi : (m : ℝ) * (N : ℝ) ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.mpr hm) (Nat.cast_ne_zero.mpr hN.ne')
  have hbase : 1 + |t - u| ≤ 1 + T := by linarith
  have hj : (1 + |t - u|) ^ j ≤ (1 + T) ^ j :=
    pow_le_pow_left₀ (by positivity) hbase j
  calc
    ‖sourceHhat (t - u) ((m : ℝ) * N)‖ ≤
        (lemma43DerivativeConstant j * (1 + |t - u|) ^ j) /
          |(m : ℝ) * N| ^ j :=
      norm_sourceHhat_le_horizontal (t - u) j hxi
    _ ≤ (lemma43DerivativeConstant j * (1 + T) ^ j) /
          |(m : ℝ) * N| ^ j := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hj
        (lemma43DerivativeConstant_nonneg j)

end

end GuthMaynardS1Source

#print axioms GuthMaynardS1Source.sourceHhat_zero_eq_mellin
#print axioms GuthMaynardS1Source.absScaledPow_mul_norm_sourceHhat_zero_le
#print axioms GuthMaynardS1Source.norm_sourceHhat_zero_le_div
#print axioms GuthMaynardS1Source.norm_sourceHhat_le_fixed
#print axioms GuthMaynardS1Source.source_equation5_1
#print axioms GuthMaynardS1Source.source_equation5_3
#print axioms GuthMaynardS1Source.source_equation5_4_raw
#print axioms GuthMaynardS1Source.norm_sourceS1KernelThird_le_of_first_gap
#print axioms GuthMaynardS1Source.norm_sourceS1KernelThird_le_of_second_gap
#print axioms GuthMaynardS1Source.norm_sourceS1KernelThird_le_far
#print axioms GuthMaynardS1Source.norm_sourceS1KernelThird_diagonal_le
