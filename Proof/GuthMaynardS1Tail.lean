import GuthMaynardS1Source
import GuthMaynardJIterationTail

/-! # Explicit integer-tail summation for Guth--Maynard `S₁` -/

namespace GuthMaynardS1Tail

open scoped BigOperators Real FourierTransform SchwartzMap
open GuthMaynardS1Source GuthMaynardJIteration
open GuthMaynardSectionThreeCutoffDerivativeBudget

noncomputable section

/-- A nonzero integer has real absolute value at least one. -/
theorem one_le_abs_intCast {m : ℤ} (hm : m ≠ 0) :
    (1 : ℝ) ≤ |(m : ℝ)| := by
  exact_mod_cast Int.one_le_abs hm

/-- Convert the source's pure power tail to the shifted decay tail whose
sum was already certified in the Poisson bookkeeping. -/
theorem inv_abs_int_pow_le_scaledShiftedDecayTail
    (q : ℕ) {B : ℝ} (hB : 0 < B) {m : ℤ}
    (hmB : B ≤ |(m : ℝ)|) :
    1 / |(m : ℝ)| ^ (q + 2) ≤
      2 ^ (q + 2) * scaledShiftedDecayTail q 1 B 0 m := by
  have hm : m ≠ 0 := by
    intro hm0
    subst m
    norm_num at hmB
    linarith
  have hm1 := one_le_abs_intCast hm
  have hbase : 1 + |(m : ℝ)| ≤ 2 * |(m : ℝ)| := by linarith
  have hpow : (1 + |(m : ℝ)|) ^ (q + 2) ≤
      (2 * |(m : ℝ)|) ^ (q + 2) :=
    pow_le_pow_left₀ (by positivity) hbase (q + 2)
  rw [scaledShiftedDecayTail]
  simp only [sub_zero, div_one]
  rw [if_pos hmB]
  have hden : 0 < |(m : ℝ)| ^ (q + 2) := by positivity
  have hshift : 0 < (1 + |(m : ℝ)|) ^ (q + 2) := by positivity
  rw [show 2 ^ (q + 2) * (1 / (1 + |(m : ℝ)|) ^ (q + 2)) =
    2 ^ (q + 2) / (1 + |(m : ℝ)|) ^ (q + 2) by ring]
  rw [div_le_div_iff₀ hden hshift]
  simpa [mul_pow] using hpow

theorem summable_far_power
    (q : ℕ) {B : ℝ} (hB : 0 < B) :
    Summable (fun m : ℤ => if B ≤ |(m : ℝ)| then
      1 / |(m : ℝ)| ^ (q + 2) else 0) := by
  let f : ℤ → ℝ := fun m => if B ≤ |(m : ℝ)| then
    1 / |(m : ℝ)| ^ (q + 2) else 0
  let g : ℤ → ℝ := fun m =>
    2 ^ (q + 2) * scaledShiftedDecayTail q 1 B 0 m
  have hg : Summable g :=
    (summable_scaledShiftedDecayTail q (A := (1 : ℝ))
      (B := B) (by norm_num) hB 0).mul_left _
  apply hg.of_nonneg_of_le
  · intro m
    split_ifs <;> positivity
  · intro m
    dsimp [f, g]
    split_ifs with hm
    · exact inv_abs_int_pow_le_scaledShiftedDecayTail q hB hm
    · exact mul_nonneg (by positivity) (by
        unfold scaledShiftedDecayTail
        split_ifs <;> positivity)

/-- The exact summed far-tail bound.  The decay exponent is `q+2`; after
paying `2^(q+2)` the surviving threshold saving is `B^-q`. -/
theorem tsum_far_power_le
    (q : ℕ) {B : ℝ} (hB : 0 < B) :
    (∑' m : ℤ, if B ≤ |(m : ℝ)| then
        1 / |(m : ℝ)| ^ (q + 2) else 0) ≤
      2 ^ (q + 2) *
        ((1 / B ^ q) * integerQuadraticMass) := by
  let f : ℤ → ℝ := fun m => if B ≤ |(m : ℝ)| then
    1 / |(m : ℝ)| ^ (q + 2) else 0
  let g : ℤ → ℝ := fun m =>
    2 ^ (q + 2) * scaledShiftedDecayTail q 1 B 0 m
  have hg0 : ∀ m, 0 ≤ g m := by
    intro m
    dsimp [g, scaledShiftedDecayTail]
    split_ifs <;> positivity
  have hfg : ∀ m, f m ≤ g m := by
    intro m
    dsimp [f]
    split_ifs with hm
    · exact inv_abs_int_pow_le_scaledShiftedDecayTail q hB hm
    · exact hg0 m
  have htail := tsum_scaledShiftedDecayTail_le q
    (A := (1 : ℝ)) (B := B) (by norm_num) hB 0
  have hgsum : Summable g :=
    (summable_scaledShiftedDecayTail q (A := (1 : ℝ))
      (B := B) (by norm_num) hB 0).mul_left _
  have hf0 : ∀ m, 0 ≤ f m := by
    intro m
    dsimp [f]
    split_ifs <;> positivity
  have hfsum : Summable f := hgsum.of_nonneg_of_le hf0 hfg
  change (∑' m : ℤ, f m) ≤ _
  calc
    (∑' m : ℤ, f m) ≤ ∑' m : ℤ, g m :=
      hfsum.tsum_le_tsum hfg hgsum
    _ = 2 ^ (q + 2) *
        (∑' m : ℤ, scaledShiftedDecayTail q 1 B 0 m) := by
      rw [(summable_scaledShiftedDecayTail q (A := (1 : ℝ))
        (B := B) (by norm_num) hB 0).tsum_mul_left]
    _ ≤ 2 ^ (q + 2) *
        ((1 / B ^ q) *
          ((1 + |(0 : ℝ)| / 1) ^ 2 * max 1 ((1 : ℝ) ^ 2) *
            integerQuadraticMass)) := by
      gcongr
    _ = 2 ^ (q + 2) * ((1 / B ^ q) * integerQuadraticMass) := by
      norm_num

/-- Increasing the positive integer scale can only improve a pure inverse
power of a nonzero integer frequency. -/
theorem inv_abs_int_mul_nat_pow_le
    {m : ℤ} (hm : m ≠ 0) {N : ℕ} (hN : 0 < N) (j : ℕ) :
    1 / |(m : ℝ) * (N : ℝ)| ^ j ≤ 1 / |(m : ℝ)| ^ j := by
  have hmpos : 0 < |(m : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hm)
  have hNc : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have habs : |(m : ℝ) * (N : ℝ)| = |(m : ℝ)| * (N : ℝ) := by
    rw [abs_mul, (abs_of_nonneg (Nat.cast_nonneg N) : |(N : ℝ)| = _)]
  have hle : |(m : ℝ)| ≤ |(m : ℝ) * (N : ℝ)| := by
    rw [habs]
    nlinarith [abs_nonneg (m : ℝ)]
  exact one_div_le_one_div_of_le (pow_pos hmpos j)
    (pow_le_pow_left₀ (abs_nonneg _) hle j)

/-- Exact factorization retaining the decisive `N^-j` saving. -/
theorem inv_abs_int_mul_nat_pow_eq
    {m : ℤ} (hm : m ≠ 0) {N : ℕ} (hN : 0 < N) (j : ℕ) :
    1 / |(m : ℝ) * (N : ℝ)| ^ j =
      (1 / (N : ℝ) ^ j) * (1 / |(m : ℝ)| ^ j) := by
  have hm0 : |(m : ℝ)| ≠ 0 := abs_ne_zero.mpr (Int.cast_ne_zero.mpr hm)
  have hNc : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [abs_mul,
    show |(N : ℝ)| = (N : ℝ) from abs_of_nonneg (Nat.cast_nonneg N),
    mul_pow]
  field_simp

/-- Literal far-frequency `m` summation for one ordinate triple in `S₁`.
This is the exact analytic-to-series weld missing after source (5.4). -/
theorem tsum_sourceS1KernelThird_far_le
    {N : ℕ} (hN : 0 < N) {t₁ t₂ t₃ T B : ℝ}
    (hT : 0 ≤ T) (hB : 0 < B) (hheight : |t₃ - t₁| ≤ T)
    (q : ℕ) :
    (∑' m : ℤ, if B ≤ |(m : ℝ)| then
        ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ else 0) ≤
      (lemma43DerivativeConstant 0 ^ 2 *
          (lemma43DerivativeConstant (q + 2) * (1 + T) ^ (q + 2))) *
        ((1 / (N : ℝ) ^ (q + 2)) *
          (2 ^ (q + 2) * ((1 / B ^ q) * integerQuadraticMass))) := by
  let K₀ : ℝ := lemma43DerivativeConstant 0 ^ 2 *
    (lemma43DerivativeConstant (q + 2) * (1 + T) ^ (q + 2))
  let K : ℝ := K₀ * (1 / (N : ℝ) ^ (q + 2))
  let f : ℤ → ℝ := fun m => if B ≤ |(m : ℝ)| then
    ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ else 0
  let g : ℤ → ℝ := fun m => K *
    (if B ≤ |(m : ℝ)| then 1 / |(m : ℝ)| ^ (q + 2) else 0)
  have hK₀ : 0 ≤ K₀ := by
    dsimp [K₀]
    exact mul_nonneg (sq_nonneg _)
      (mul_nonneg (lemma43DerivativeConstant_nonneg (q + 2))
        (pow_nonneg (by linarith) _))
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg hK₀ (by positivity)
  have hfg : ∀ m, f m ≤ g m := by
    intro m
    dsimp [f, g]
    split_ifs with hmB
    · have hm : m ≠ 0 := by
        intro hm0
        subst m
        norm_num at hmB
        linarith
      have hraw := norm_sourceS1KernelThird_le_far
        (t₁ := t₁) (t₂ := t₂) (t₃ := t₃) (T := T)
        (q + 2) hm hN hheight
      have hscale := inv_abs_int_mul_nat_pow_eq hm hN (q + 2)
      calc
        ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ ≤
            lemma43DerivativeConstant 0 ^ 2 *
              ((lemma43DerivativeConstant (q + 2) * (1 + T) ^ (q + 2)) /
                |(m : ℝ) * N| ^ (q + 2)) := hraw
        _ = K₀ * (1 / |(m : ℝ) * N| ^ (q + 2)) := by
          dsimp [K₀]
          ring
        _ = K * (1 / |(m : ℝ)| ^ (q + 2)) := by
          rw [hscale]
          dsimp [K]
          ring
    · norm_num
  have hpure := summable_far_power q hB
  have hgsum : Summable g := hpure.mul_left K
  have hf0 : ∀ m, 0 ≤ f m := by
    intro m
    dsimp [f]
    split_ifs <;> positivity
  have hfsum : Summable f := hgsum.of_nonneg_of_le hf0 hfg
  change (∑' m : ℤ, f m) ≤ _
  calc
    (∑' m : ℤ, f m) ≤ ∑' m : ℤ, g m :=
      hfsum.tsum_le_tsum hfg hgsum
    _ = K * (∑' m : ℤ, if B ≤ |(m : ℝ)| then
          1 / |(m : ℝ)| ^ (q + 2) else 0) := by
      rw [hpure.tsum_mul_left]
    _ ≤ K * (2 ^ (q + 2) *
        ((1 / B ^ q) * integerQuadraticMass)) := by
      exact mul_le_mul_of_nonneg_left (tsum_far_power_le q hB) hK
    _ = _ := by
      dsimp [K, K₀]
      ring

/-- Absolute summability of every far-frequency sector, proved from the same
source kernel majorant rather than inferred from a finite numerical bound. -/
theorem summable_sourceS1KernelThird_far
    {N : ℕ} (hN : 0 < N) {t₁ t₂ t₃ T B : ℝ}
    (hT : 0 ≤ T) (hB : 0 < B) (hheight : |t₃ - t₁| ≤ T) :
    Summable (fun m : ℤ => if B ≤ |(m : ℝ)| then
      ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ else 0) := by
  let K₀ : ℝ := lemma43DerivativeConstant 0 ^ 2 *
    (lemma43DerivativeConstant 2 * (1 + T) ^ 2)
  let K : ℝ := K₀ * (1 / (N : ℝ) ^ 2)
  let f : ℤ → ℝ := fun m => if B ≤ |(m : ℝ)| then
    ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ else 0
  let g : ℤ → ℝ := fun m => K *
    (if B ≤ |(m : ℝ)| then 1 / |(m : ℝ)| ^ 2 else 0)
  have hK₀ : 0 ≤ K₀ := by
    dsimp [K₀]
    exact mul_nonneg (sq_nonneg _)
      (mul_nonneg (lemma43DerivativeConstant_nonneg 2)
        (pow_nonneg (by linarith) _))
  have hK : 0 ≤ K := mul_nonneg hK₀ (by positivity)
  have hfg : ∀ m, f m ≤ g m := by
    intro m
    dsimp [f, g]
    split_ifs with hmB
    · have hm : m ≠ 0 := by
        intro hm0
        subst m
        norm_num at hmB
        linarith
      have hraw := norm_sourceS1KernelThird_le_far
        (t₁ := t₁) (t₂ := t₂) (t₃ := t₃) (T := T) 2 hm hN hheight
      have hscale := inv_abs_int_mul_nat_pow_eq hm hN 2
      calc
        ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ ≤
            lemma43DerivativeConstant 0 ^ 2 *
              ((lemma43DerivativeConstant 2 * (1 + T) ^ 2) /
                |(m : ℝ) * N| ^ 2) := hraw
        _ = K₀ * (1 / |(m : ℝ) * N| ^ 2) := by
          dsimp [K₀]
          ring
        _ = K * (1 / |(m : ℝ)| ^ 2) := by
          rw [hscale]
          dsimp [K]
          ring
    · norm_num
  have hg : Summable g := (summable_far_power 0 hB).mul_left K
  have hf0 : ∀ m, 0 ≤ f m := by
    intro m
    dsimp [f]
    split_ifs <;> positivity
  exact hg.of_nonneg_of_le hf0 hfg

/-- The full far-frequency contribution for one of the three cyclic `S₁`
orientations, after summing all ordinate triples. -/
def sourceS1ThirdFarMass
    (N : ℕ) (W : Finset ℝ) (B : ℝ) : ℝ :=
  ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
    ∑' m : ℤ, if B ≤ |(m : ℝ)| then
      ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ else 0

theorem sourceS1ThirdFarMass_le
    {N : ℕ} (hN : 0 < N) {W : Finset ℝ} {T B : ℝ}
    (hT : 0 ≤ T) (hB : 0 < B)
    (hdiameter : ∀ t ∈ W, ∀ u ∈ W, |t - u| ≤ T)
    (q : ℕ) :
    sourceS1ThirdFarMass N W B ≤
      (W.card : ℝ) ^ 3 *
        ((lemma43DerivativeConstant 0 ^ 2 *
            (lemma43DerivativeConstant (q + 2) * (1 + T) ^ (q + 2))) *
          ((1 / (N : ℝ) ^ (q + 2)) *
            (2 ^ (q + 2) * ((1 / B ^ q) * integerQuadraticMass)))) := by
  unfold sourceS1ThirdFarMass
  calc
    (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
      ∑' m : ℤ, if B ≤ |(m : ℝ)| then
        ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ else 0) ≤
      ∑ _t₁ ∈ W, ∑ _t₂ ∈ W, ∑ _t₃ ∈ W,
        ((lemma43DerivativeConstant 0 ^ 2 *
            (lemma43DerivativeConstant (q + 2) * (1 + T) ^ (q + 2))) *
          ((1 / (N : ℝ) ^ (q + 2)) *
            (2 ^ (q + 2) * ((1 / B ^ q) * integerQuadraticMass)))) := by
      apply Finset.sum_le_sum
      intro t₁ ht₁
      apply Finset.sum_le_sum
      intro t₂ ht₂
      apply Finset.sum_le_sum
      intro t₃ ht₃
      exact tsum_sourceS1KernelThird_far_le hN hT hB
        (hdiameter t₃ ht₃ t₁ ht₁) q
    _ = _ := by
      simp
      ring

/-! ## The derivative order that yields the printed `T^-10` -/

/-- One explicit source-legal derivative order.  The extra two derivatives
are exactly those retained in the quadratic summable envelope. -/
def s1DecayOrder (epsilon : ℝ) : ℕ :=
  Nat.ceil (20 / epsilon) + 2

theorem twenty_add_two_epsilon_le_epsilon_mul_s1DecayOrder
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    20 + 2 * epsilon ≤ epsilon * s1DecayOrder epsilon := by
  have hceil : 20 / epsilon ≤ (Nat.ceil (20 / epsilon) : ℝ) :=
    Nat.le_ceil _
  have hmul := mul_le_mul_of_nonneg_left hceil hepsilon.le
  have hcancel : epsilon * (20 / epsilon) = 20 := by
    field_simp
  rw [hcancel] at hmul
  unfold s1DecayOrder
  push_cast
  linarith

/-- Crude finite-range bookkeeping costs at most `T^(7+epsilon)`; the
chosen vertical-decay order leaves exponent at most `-13` for
`0<epsilon≤1`, hence more than the printed `T^-10`. -/
theorem s1FiniteExponent_le_neg_thirteen
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    7 + epsilon - epsilon * s1DecayOrder epsilon ≤ -13 := by
  have h := twenty_add_two_epsilon_le_epsilon_mul_s1DecayOrder hepsilon
  linarith

/-- After summing the far integer tail, the crude outer cardinalities cost
`T^8`; the surviving threshold power is again at most `T^-12`. -/
theorem s1FarExponent_le_neg_twelve
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    8 - epsilon * (s1DecayOrder epsilon - 2 : ℕ) ≤ -12 := by
  have hceil : 20 / epsilon ≤ (Nat.ceil (20 / epsilon) : ℝ) :=
    Nat.le_ceil _
  have hmul := mul_le_mul_of_nonneg_left hceil hepsilon.le
  have hcancel : epsilon * (20 / epsilon) = 20 := by
    field_simp
  rw [hcancel] at hmul
  have horder : s1DecayOrder epsilon - 2 = Nat.ceil (20 / epsilon) := by
    unfold s1DecayOrder
    omega
  rw [horder]
  linarith

/-! ## Exact finite partition -/

/-- The bounded nonzero integer frequencies in Proposition 5.1. -/
def s1FiniteMRange (B : ℝ) : Finset ℤ :=
  (Finset.Icc (-(Nat.ceil B : ℤ)) (Nat.ceil B : ℤ)).erase 0

theorem card_s1FiniteMRange_le (B : ℝ) :
    (s1FiniteMRange B).card ≤ 2 * Nat.ceil B + 1 := by
  calc
    (s1FiniteMRange B).card ≤
        (Finset.Icc (-(Nat.ceil B : ℤ)) (Nat.ceil B : ℤ)).card :=
      Finset.card_erase_le
    _ = 2 * Nat.ceil B + 1 := by
      rw [Int.card_Icc]
      simp
      omega

theorem mem_s1FiniteMRange_ne_zero
    {B : ℝ} {m : ℤ} (hm : m ∈ s1FiniteMRange B) : m ≠ 0 := by
  exact (Finset.mem_erase.mp hm).1

theorem mem_s1FiniteMRange_of_abs_lt
    {B : ℝ} (hB : 0 < B) {m : ℤ} (hm : m ≠ 0)
    (hmB : |(m : ℝ)| < B) : m ∈ s1FiniteMRange B := by
  apply Finset.mem_erase.mpr
  refine ⟨hm, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
  · have hceil : B ≤ (Nat.ceil B : ℝ) := Nat.le_ceil B
    have habs : |(m : ℝ)| ≤ (Nat.ceil B : ℝ) := hmB.le.trans hceil
    have hlower : -((Nat.ceil B : ℝ)) ≤ (m : ℝ) := by
      linarith [neg_abs_le (m : ℝ)]
    exact_mod_cast hlower
  · have hceil : B ≤ (Nat.ceil B : ℝ) := Nat.le_ceil B
    have habs : |(m : ℝ)| ≤ (Nat.ceil B : ℝ) := hmB.le.trans hceil
    have hupper : (m : ℝ) ≤ (Nat.ceil B : ℝ) :=
      (le_abs_self (m : ℝ)).trans habs
    exact_mod_cast hupper

/-! ## Quantitative bounds for the three finite triple sectors -/

/-- The literal fixed seminorm in the vertical half of source Lemma 4.3. -/
def s1VerticalConstant (j : ℕ) : ℝ :=
  SchwartzMap.seminorm ℂ j 0
    (𝓕 (GuthMaynardMellinRapidDecay.mellinLogLiftSchwartz
      GuthMaynardSectionThreeCutoff.sectionThreeCutoff
      (GuthMaynardMellinRapidDecay.mellinLogLift_hasCompactSupport
        (by norm_num) (by norm_num)
        GuthMaynardSectionThreeCutoff.sectionThreeCutoff_supported)
      (GuthMaynardMellinRapidDecay.mellinLogLift_contDiff
        GuthMaynardSectionThreeCutoff.sectionThreeCutoff_contDiff)) :
      𝓢(ℝ, ℂ))

theorem s1VerticalConstant_nonneg (j : ℕ) :
    0 ≤ s1VerticalConstant j := by
  unfold s1VerticalConstant
  positivity

/-- Replacing an actual separated gap by the common source gap `R` loses
only the displayed factor `(R/(2*pi))^-j`. -/
theorem vertical_quotient_le_common_gap
    {d R : ℝ} (j : ℕ) (hR : 0 < R) (hgap : R ≤ |d|) :
    s1VerticalConstant j / |d / (2 * Real.pi)| ^ j ≤
      s1VerticalConstant j / (R / (2 * Real.pi)) ^ j := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have habs : |d / (2 * Real.pi)| = |d| / (2 * Real.pi) := by
    rw [abs_div, abs_of_pos hpi]
  have hbase : R / (2 * Real.pi) ≤ |d / (2 * Real.pi)| := by
    rw [habs]
    exact div_le_div_of_nonneg_right hgap hpi.le
  have hsmall : 0 < (R / (2 * Real.pi)) ^ j := by positivity
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ R / (2 * Real.pi)) hbase j
  exact div_le_div_of_nonneg_left (s1VerticalConstant_nonneg j) hsmall hpow

/-- The first off-diagonal sector, with every source constant and finite
cardinality still visible. -/
theorem sourceS1ThirdFiniteFirstGapMass_le
    {N : ℕ} {W : Finset ℝ} {M : Finset ℤ} {R : ℝ}
    (hR : 0 < R)
    (hsep : ∀ t₁ ∈ W, ∀ t₂ ∈ W, t₁ ≠ t₂ → R ≤ |t₁ - t₂|)
    (j : ℕ) :
    sourceS1ThirdFiniteFirstGapMass N W M ≤
      (W.card : ℝ) ^ 3 * (M.card : ℝ) *
        ((s1VerticalConstant j / (R / (2 * Real.pi)) ^ j) *
          lemma43DerivativeConstant 0 ^ 2) := by
  unfold sourceS1ThirdFiniteFirstGapMass
  calc
    _ ≤ ∑ _t₁ ∈ W, ∑ _t₂ ∈ W, ∑ _t₃ ∈ W, ∑ _m ∈ M,
        ((s1VerticalConstant j / (R / (2 * Real.pi)) ^ j) *
          lemma43DerivativeConstant 0 ^ 2) := by
      apply Finset.sum_le_sum
      intro t₁ ht₁
      apply Finset.sum_le_sum
      intro t₂ ht₂
      apply Finset.sum_le_sum
      intro t₃ ht₃
      apply Finset.sum_le_sum
      intro m hm
      split_ifs with hne
      · calc
          ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ ≤
              (s1VerticalConstant j / |(t₁ - t₂) / (2 * Real.pi)| ^ j) *
                lemma43DerivativeConstant 0 ^ 2 := by
            simpa [s1VerticalConstant] using
              norm_sourceS1KernelThird_le_of_first_gap
                (t₁ := t₁) (t₂ := t₂) (t₃ := t₃) (R := R) j
                (hsep t₁ ht₁ t₂ ht₂ hne) hR
          _ ≤ _ := by
            exact mul_le_mul_of_nonneg_right
              (vertical_quotient_le_common_gap j hR
                (hsep t₁ ht₁ t₂ ht₂ hne)) (sq_nonneg _)
      · exact mul_nonneg
          (div_nonneg (s1VerticalConstant_nonneg j)
            (pow_nonneg (div_nonneg hR.le (by positivity)) j))
          (sq_nonneg _)
    _ = _ := by simp; ring

/-- The second off-diagonal sector. -/
theorem sourceS1ThirdFiniteSecondGapMass_le
    {N : ℕ} {W : Finset ℝ} {M : Finset ℤ} {R : ℝ}
    (hR : 0 < R)
    (hsep : ∀ t₁ ∈ W, ∀ t₂ ∈ W, t₁ ≠ t₂ → R ≤ |t₁ - t₂|)
    (j : ℕ) :
    sourceS1ThirdFiniteSecondGapMass N W M ≤
      (W.card : ℝ) ^ 3 * (M.card : ℝ) *
        (lemma43DerivativeConstant 0 *
          (s1VerticalConstant j / (R / (2 * Real.pi)) ^ j) *
          lemma43DerivativeConstant 0) := by
  unfold sourceS1ThirdFiniteSecondGapMass
  calc
    _ ≤ ∑ _t₁ ∈ W, ∑ _t₂ ∈ W, ∑ _t₃ ∈ W, ∑ _m ∈ M,
        (lemma43DerivativeConstant 0 *
          (s1VerticalConstant j / (R / (2 * Real.pi)) ^ j) *
          lemma43DerivativeConstant 0) := by
      apply Finset.sum_le_sum
      intro t₁ ht₁
      apply Finset.sum_le_sum
      intro t₂ ht₂
      apply Finset.sum_le_sum
      intro t₃ ht₃
      apply Finset.sum_le_sum
      intro m hm
      split_ifs with hcase
      · rcases hcase with ⟨heq, hne⟩
        calc
          ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ ≤
              lemma43DerivativeConstant 0 *
                (s1VerticalConstant j / |(t₂ - t₃) / (2 * Real.pi)| ^ j) *
                lemma43DerivativeConstant 0 := by
            simpa [s1VerticalConstant] using
              norm_sourceS1KernelThird_le_of_second_gap
                (t₁ := t₁) (t₂ := t₂) (t₃ := t₃) (R := R) j
                (hsep t₂ ht₂ t₃ ht₃ hne) hR
          _ ≤ _ := by
            have hD := lemma43DerivativeConstant_nonneg 0
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left
                (vertical_quotient_le_common_gap j hR
                  (hsep t₂ ht₂ t₃ ht₃ hne)) hD) hD
      · exact mul_nonneg
          (mul_nonneg (lemma43DerivativeConstant_nonneg 0)
            (div_nonneg (s1VerticalConstant_nonneg j)
              (pow_nonneg (div_nonneg hR.le (by positivity)) j)))
          (lemma43DerivativeConstant_nonneg 0)
    _ = _ := by simp; ring

/-- The fully diagonal sector uses horizontal Fourier decay and the fact that
the finite source range erases `m=0`. -/
theorem sourceS1ThirdFiniteDiagonalMass_le
    {N : ℕ} (hN : 0 < N) {W : Finset ℝ} {M : Finset ℤ}
    (hm0 : ∀ m ∈ M, m ≠ 0) (j : ℕ) :
    sourceS1ThirdFiniteDiagonalMass N W M ≤
      (W.card : ℝ) ^ 3 * (M.card : ℝ) *
        (lemma43DerivativeConstant 0 ^ 2 * lemma43DerivativeConstant j) := by
  unfold sourceS1ThirdFiniteDiagonalMass
  calc
    _ ≤ ∑ _t₁ ∈ W, ∑ _t₂ ∈ W, ∑ _t₃ ∈ W, ∑ _m ∈ M,
        (lemma43DerivativeConstant 0 ^ 2 * lemma43DerivativeConstant j) := by
      apply Finset.sum_le_sum
      intro t₁ ht₁
      apply Finset.sum_le_sum
      intro t₂ ht₂
      apply Finset.sum_le_sum
      intro t₃ ht₃
      apply Finset.sum_le_sum
      intro m hm
      split_ifs with hdiag
      · rcases hdiag with ⟨h12, h23⟩
        subst t₂
        subst t₃
        have hraw := norm_sourceS1KernelThird_diagonal_le
          (N := N) (t := t₁) (m := m) (hm0 m hm) hN j
        have hscale := inv_abs_int_mul_nat_pow_le (hm0 m hm) hN j
        have hmone := one_le_abs_intCast (hm0 m hm)
        have hmpow : (1 : ℝ) ≤ |(m : ℝ)| ^ j := by
          simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hmone j
        have hinv : 1 / |(m : ℝ)| ^ j ≤ (1 : ℝ) := by
          rw [div_le_one (by positivity : 0 < |(m : ℝ)| ^ j)]
          exact hmpow
        have hscaleOne : 1 / |(m : ℝ) * (N : ℝ)| ^ j ≤ (1 : ℝ) :=
          hscale.trans hinv
        calc
          ‖sourceS1KernelThird N t₁ t₁ t₁ m‖ ≤
              lemma43DerivativeConstant 0 ^ 2 *
                (lemma43DerivativeConstant j / |(m : ℝ) * N| ^ j) := hraw
          _ ≤ lemma43DerivativeConstant 0 ^ 2 *
                (lemma43DerivativeConstant j * 1) := by
            gcongr
            simpa [div_eq_mul_inv] using
              mul_le_mul_of_nonneg_left hscaleOne
                (lemma43DerivativeConstant_nonneg j)
          _ = _ := by ring
      · exact mul_nonneg (sq_nonneg _)
          (lemma43DerivativeConstant_nonneg j)
    _ = _ := by simp; ring

/-- Exact finite-sector assembly after the disjoint triple partition. -/
theorem sourceS1ThirdFiniteMass_le_partition_bound
    {N : ℕ} (hN : 0 < N) {W : Finset ℝ} {M : Finset ℤ} {R : ℝ}
    (hR : 0 < R)
    (hsep : ∀ t₁ ∈ W, ∀ t₂ ∈ W, t₁ ≠ t₂ → R ≤ |t₁ - t₂|)
    (hm0 : ∀ m ∈ M, m ≠ 0) (j : ℕ) :
    sourceS1ThirdFiniteMass N W M ≤
      (W.card : ℝ) ^ 3 * (M.card : ℝ) *
        ((s1VerticalConstant j / (R / (2 * Real.pi)) ^ j) *
            lemma43DerivativeConstant 0 ^ 2) +
      (W.card : ℝ) ^ 3 * (M.card : ℝ) *
        (lemma43DerivativeConstant 0 *
          (s1VerticalConstant j / (R / (2 * Real.pi)) ^ j) *
          lemma43DerivativeConstant 0) +
      (W.card : ℝ) ^ 3 * (M.card : ℝ) *
        (lemma43DerivativeConstant 0 ^ 2 * lemma43DerivativeConstant j) := by
  rw [sourceS1ThirdFiniteMass_partition]
  exact add_le_add
    (add_le_add
      (sourceS1ThirdFiniteFirstGapMass_le hR hsep j)
      (sourceS1ThirdFiniteSecondGapMass_le hR hsep j))
    (sourceS1ThirdFiniteDiagonalMass_le hN hm0 j)

/-- One cyclic orientation after the source split at `B`: the bounded
nonzero integers plus the absolutely convergent far tail. -/
def sourceS1ThirdSplitMass
    (N : ℕ) (W : Finset ℝ) (B : ℝ) : ℝ :=
  sourceS1ThirdFiniteMass N W (s1FiniteMRange B) +
    sourceS1ThirdFarMass N W B

/-- The literal one-orientation `S₁` mass, summing every nonzero integer
frequency exactly once. -/
def sourceS1ThirdTotalMass
    (N : ℕ) (W : Finset ℝ) : ℝ :=
  ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
    ∑' m : ℤ, if m ≠ 0 then
      ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ else 0

/-- Every nonzero integer frequency is covered by either the bounded range or
the far tail.  Overlap at the cutoff is harmless because all summands are
nonnegative. -/
theorem sourceS1ThirdTotalMass_le_split
    {N : ℕ} (hN : 0 < N) {W : Finset ℝ} {T B : ℝ}
    (hT : 0 ≤ T) (hB : 0 < B)
    (hdiameter : ∀ t ∈ W, ∀ u ∈ W, |t - u| ≤ T) :
    sourceS1ThirdTotalMass N W ≤ sourceS1ThirdSplitMass N W B := by
  unfold sourceS1ThirdTotalMass sourceS1ThirdSplitMass
    sourceS1ThirdFiniteMass sourceS1ThirdFarMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t₁ ht₁
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t₂ ht₂
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t₃ ht₃
  let f : ℤ → ℝ := fun m => if m ≠ 0 then
    ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ else 0
  let g : ℤ → ℝ := fun m => if m ∈ s1FiniteMRange B then
    ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ else 0
  let h : ℤ → ℝ := fun m => if B ≤ |(m : ℝ)| then
    ‖sourceS1KernelThird N t₁ t₂ t₃ m‖ else 0
  have hh : Summable h := by
    exact summable_sourceS1KernelThird_far hN hT hB
      (hdiameter t₃ ht₃ t₁ ht₁)
  have hg : Summable g := by
    apply summable_of_ne_finset_zero (s := s1FiniteMRange B)
    intro m hm
    simp [g, hm]
  have hf : Summable f := by
    have hfarOne := summable_sourceS1KernelThird_far
      (t₁ := t₁) (t₂ := t₂) (t₃ := t₃) (T := T) (B := (1 : ℝ))
      hN hT (by norm_num) (hdiameter t₃ ht₃ t₁ ht₁)
    convert hfarOne using 1
    funext m
    by_cases hm : m = 0
    · simp [f, hm]
    · simp [f, hm, one_le_abs_intCast hm]
  have hpoint : ∀ m, f m ≤ g m + h m := by
    intro m
    by_cases hm : m = 0
    · simp [f, g, h, hm]
      positivity
    · by_cases hfar : B ≤ |(m : ℝ)|
      · simp [f, g, h, hm, hfar]
        positivity
      · have hmem := mem_s1FiniteMRange_of_abs_lt hB hm
          (lt_of_not_ge hfar)
        simp [f, g, h, hm, hfar, hmem]
  calc
    (∑' m : ℤ, f m) ≤ ∑' m : ℤ, (g m + h m) :=
      hf.tsum_le_tsum hpoint (hg.add hh)
    _ = (∑' m : ℤ, g m) + ∑' m : ℤ, h m :=
      hg.tsum_add hh
    _ = (∑ m ∈ s1FiniteMRange B,
          ‖sourceS1KernelThird N t₁ t₂ t₃ m‖) + ∑' m : ℤ, h m := by
      congr 1
      rw [tsum_eq_sum (s := s1FiniteMRange B)]
      · simp [g]
      · intro m hm
        simp [g, hm]

/-- The literal `3*N^3` symmetry factor in Proposition 5.1. -/
def sourceS1SplitContribution
    (N : ℕ) (W : Finset ℝ) (B : ℝ) : ℝ :=
  3 * (N : ℝ) ^ 3 * sourceS1ThirdSplitMass N W B

/-- The literal three-orientation absolute `S₁` contribution before the
source cutoff split. -/
def sourceS1TotalContribution (N : ℕ) (W : Finset ℝ) : ℝ :=
  3 * (N : ℝ) ^ 3 * sourceS1ThirdTotalMass N W

theorem sourceS1TotalContribution_le_split
    {N : ℕ} (hN : 0 < N) {W : Finset ℝ} {T B : ℝ}
    (hT : 0 ≤ T) (hB : 0 < B)
    (hdiameter : ∀ t ∈ W, ∀ u ∈ W, |t - u| ≤ T) :
    sourceS1TotalContribution N W ≤ sourceS1SplitContribution N W B := by
  unfold sourceS1TotalContribution sourceS1SplitContribution
  exact mul_le_mul_of_nonneg_left
    (sourceS1ThirdTotalMass_le_split hN hT hB hdiameter) (by positivity)

/-- Zero-assumption, constant-explicit endpoint of the `S₁` source chain.
It combines the finite triple partition, the integer tail, and all three
cyclic orientations.  No large-value or pair-moment hypothesis occurs. -/
theorem sourceS1SplitContribution_le
    {N : ℕ} (hN : 0 < N) {W : Finset ℝ} {T R B : ℝ}
    (hT : 0 ≤ T) (hR : 0 < R) (hB : 0 < B)
    (hsep : ∀ t₁ ∈ W, ∀ t₂ ∈ W, t₁ ≠ t₂ → R ≤ |t₁ - t₂|)
    (hdiameter : ∀ t ∈ W, ∀ u ∈ W, |t - u| ≤ T)
    (j q : ℕ) :
    sourceS1SplitContribution N W B ≤
      3 * (N : ℝ) ^ 3 *
        (((W.card : ℝ) ^ 3 * ((s1FiniteMRange B).card : ℝ) *
              ((s1VerticalConstant j / (R / (2 * Real.pi)) ^ j) *
                lemma43DerivativeConstant 0 ^ 2) +
            (W.card : ℝ) ^ 3 * ((s1FiniteMRange B).card : ℝ) *
              (lemma43DerivativeConstant 0 *
                (s1VerticalConstant j / (R / (2 * Real.pi)) ^ j) *
                lemma43DerivativeConstant 0) +
            (W.card : ℝ) ^ 3 * ((s1FiniteMRange B).card : ℝ) *
              (lemma43DerivativeConstant 0 ^ 2 * lemma43DerivativeConstant j)) +
          (W.card : ℝ) ^ 3 *
            ((lemma43DerivativeConstant 0 ^ 2 *
                (lemma43DerivativeConstant (q + 2) * (1 + T) ^ (q + 2))) *
              ((1 / (N : ℝ) ^ (q + 2)) *
                (2 ^ (q + 2) *
                  ((1 / B ^ q) * integerQuadraticMass))))) := by
  unfold sourceS1SplitContribution sourceS1ThirdSplitMass
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add
    (sourceS1ThirdFiniteMass_le_partition_bound hN hR hsep
      (fun m hm => mem_s1FiniteMRange_ne_zero hm) j)
    (sourceS1ThirdFarMass_le hN hT hB hdiameter q)

/-- Exact published `S₁` input bound: literal all-nonzero-frequency mass,
three cyclic orientations, and the source cutoff split, with no assumptions
standing for Proposition 5.1. -/
theorem sourceS1TotalContribution_le
    {N : ℕ} (hN : 0 < N) {W : Finset ℝ} {T R B : ℝ}
    (hT : 0 ≤ T) (hR : 0 < R) (hB : 0 < B)
    (hsep : ∀ t₁ ∈ W, ∀ t₂ ∈ W, t₁ ≠ t₂ → R ≤ |t₁ - t₂|)
    (hdiameter : ∀ t ∈ W, ∀ u ∈ W, |t - u| ≤ T)
    (j q : ℕ) :
    sourceS1TotalContribution N W ≤
      3 * (N : ℝ) ^ 3 *
        (((W.card : ℝ) ^ 3 * ((s1FiniteMRange B).card : ℝ) *
              ((s1VerticalConstant j / (R / (2 * Real.pi)) ^ j) *
                lemma43DerivativeConstant 0 ^ 2) +
            (W.card : ℝ) ^ 3 * ((s1FiniteMRange B).card : ℝ) *
              (lemma43DerivativeConstant 0 *
                (s1VerticalConstant j / (R / (2 * Real.pi)) ^ j) *
                lemma43DerivativeConstant 0) +
            (W.card : ℝ) ^ 3 * ((s1FiniteMRange B).card : ℝ) *
              (lemma43DerivativeConstant 0 ^ 2 * lemma43DerivativeConstant j)) +
          (W.card : ℝ) ^ 3 *
            ((lemma43DerivativeConstant 0 ^ 2 *
                (lemma43DerivativeConstant (q + 2) * (1 + T) ^ (q + 2))) *
              ((1 / (N : ℝ) ^ (q + 2)) *
                (2 ^ (q + 2) *
                  ((1 / B ^ q) * integerQuadraticMass))))) := by
  exact (sourceS1TotalContribution_le_split hN hT hB hdiameter).trans
    (sourceS1SplitContribution_le hN hT hR hB hsep hdiameter j q)

/-- The ordinate-triple partition used after truncating `m`: one of the two
zero-frequency factors is off diagonal, or the triple is fully diagonal. -/
theorem firstGap_or_secondGap_or_diagonal (t₁ t₂ t₃ : ℝ) :
    t₁ ≠ t₂ ∨ t₂ ≠ t₃ ∨ (t₁ = t₂ ∧ t₂ = t₃) := by
  by_cases h₁₂ : t₁ = t₂
  · by_cases h₂₃ : t₂ = t₃
    · exact Or.inr (Or.inr ⟨h₁₂, h₂₃⟩)
    · exact Or.inr (Or.inl h₂₃)
  · exact Or.inl h₁₂

/-- Zero-assumption exponent budget for the equation-(12.1) assembly.  Once
the pointwise kernels are welded through their finite sums, both resulting
powers beat `-10` using one explicit common derivative order. -/
theorem exists_s1DecayOrder_exponent_budget
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ j : ℕ, 2 ≤ j ∧
      7 + epsilon - epsilon * j ≤ -13 ∧
      8 - epsilon * (j - 2 : ℕ) ≤ -12 := by
  refine ⟨s1DecayOrder epsilon, ?_,
    s1FiniteExponent_le_neg_thirteen hepsilon,
    s1FarExponent_le_neg_twelve hepsilon⟩
  unfold s1DecayOrder
  omega

/-- Any fixed source seminorm/cardinality constant is absorbed by the two
spare powers between the certified `-12` tail and the published `-10`
claim. -/
theorem fixedConstant_powTwelve_absorbed_by_powTen
    (C : ℝ) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      C / T ^ 12 ≤ 1 / T ^ 10 := by
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro T hT
  have hTone : 1 ≤ T := (le_max_left 1 C).trans hT
  have hTC : C ≤ T := (le_max_right 1 C).trans hT
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTone
  have hT2 : T ≤ T ^ 2 := by nlinarith
  have hCT2 : C ≤ T ^ 2 := hTC.trans hT2
  rw [div_le_div_iff₀ (pow_pos hTpos 12) (pow_pos hTpos 10)]
  calc
    C * T ^ 10 ≤ T ^ 2 * T ^ 10 :=
      mul_le_mul_of_nonneg_right hCT2 (by positivity)
    _ = 1 * T ^ 12 := by ring

end

end GuthMaynardS1Tail

#print axioms GuthMaynardS1Tail.inv_abs_int_pow_le_scaledShiftedDecayTail
#print axioms GuthMaynardS1Tail.tsum_far_power_le
#print axioms GuthMaynardS1Tail.tsum_sourceS1KernelThird_far_le
#print axioms GuthMaynardS1Tail.sourceS1ThirdFarMass_le
#print axioms GuthMaynardS1Tail.inv_abs_int_mul_nat_pow_eq
#print axioms GuthMaynardS1Tail.sourceS1ThirdFiniteFirstGapMass_le
#print axioms GuthMaynardS1Tail.sourceS1ThirdFiniteSecondGapMass_le
#print axioms GuthMaynardS1Tail.sourceS1ThirdFiniteDiagonalMass_le
#print axioms GuthMaynardS1Tail.sourceS1ThirdFiniteMass_le_partition_bound
#print axioms GuthMaynardS1Tail.sourceS1SplitContribution_le
#print axioms GuthMaynardS1Tail.twenty_add_two_epsilon_le_epsilon_mul_s1DecayOrder
#print axioms GuthMaynardS1Tail.s1FiniteExponent_le_neg_thirteen
#print axioms GuthMaynardS1Tail.s1FarExponent_le_neg_twelve
#print axioms GuthMaynardS1Tail.card_s1FiniteMRange_le
#print axioms GuthMaynardS1Tail.firstGap_or_secondGap_or_diagonal
#print axioms GuthMaynardS1Tail.exists_s1DecayOrder_exponent_budget
#print axioms GuthMaynardS1Tail.fixedConstant_powTwelve_absorbed_by_powTen
