import HarmonicFrontend

/-!
# Floor-tight arithmetic collars for the MAP mixed mean

The existing harmonic frontend uses ceiling-valued collars as safe finite
envelopes.  Those envelopes are too wide for the paper's final `U` and `T`
normalizations when the real collar is below one.  This module keeps the
literal logarithmic-frequency survivor set and proves floor-tight natural
distance bounds.  It also proves the exact sub-unit emptiness statements used
by the zero and nonzero determinant sectors.
-/

noncomputable section

namespace MAPMixedMeanFloor

open DeterminantCountWeld MixedMeanFrontend MAPMixedHarmonic

/-- The sharp natural short-index collar at the paper's `u` scale. -/
def shortFloorCollar (M : ℕ) (U : ℝ) : ℕ :=
  min M ⌊Real.pi * (M : ℝ) / U⌋₊

/-- The sharp natural product collar at the paper's `t` scale. -/
def productFloorCollar (M N : ℕ) (T : ℝ) : ℕ :=
  ⌊2 * Real.pi * (M : ℝ) * (N : ℝ) / T⌋₊

/-- The exact simultaneous Fourier survivor set.  No arithmetic enlargement
is made in this definition. -/
def exactFrequencySurvivors (M N : ℕ) (T U : ℝ) : Finset LiteralTuple :=
  frequencyTuples M N (Real.pi / (2 * U)) (Real.pi / (2 * T))

/-- The floor-tight arithmetic collar into which the exact survivors map. -/
def floorCollarTuples (M N : ℕ) (T U : ℝ) : Finset LiteralTuple :=
  (dyadicTupleBox M N).filter fun q =>
    q.1.1.dist q.1.2 ≤ shortFloorCollar M U ∧
      (q.1.1 * q.2.1).dist (q.1.2 * q.2.2) ≤
        productFloorCollar M N T

/-- Exact survivors with unequal short indices. -/
def unequalShortFrequencySurvivors (M N : ℕ) (T U : ℝ) : Finset LiteralTuple :=
  (exactFrequencySurvivors M N T U).filter fun q => q.1.1 ≠ q.1.2

/-! ## Real distance bounds before flooring -/

/-- The literal short logarithmic band gives the sharp real distance bound
`dist(m₁,m₂) ≤ pi*M/U`. -/
theorem shortFrequency_dist_real_le
    {M m₁ m₂ : ℕ} {U : ℝ}
    (hm₁ : m₁ ∈ dyadic M) (hm₂ : m₂ ∈ dyadic M)
    (hfreq : |Real.log m₂ - Real.log m₁| ≤ Real.pi / (2 * U)) :
    (m₁.dist m₂ : ℝ) ≤ Real.pi * (M : ℝ) / U := by
  have hm₁nat : 0 < m₁ := by
    simp only [dyadic, Finset.mem_Ioc] at hm₁
    omega
  have hm₂nat : 0 < m₂ := by
    simp only [dyadic, Finset.mem_Ioc] at hm₂
    omega
  have hm₁pos : 0 < (m₁ : ℝ) := by exact_mod_cast hm₁nat
  have hm₂pos : 0 < (m₂ : ℝ) := by exact_mod_cast hm₂nat
  have hreal := abs_sub_le_max_mul_abs_log_sub hm₁pos hm₂pos
  have hmax : max (m₁ : ℝ) m₂ ≤ 2 * M := by
    simp only [dyadic, Finset.mem_Ioc] at hm₁ hm₂
    norm_cast
    omega
  rw [natCast_dist_eq_abs]
  calc
    |(m₁ : ℝ) - m₂| ≤
        max (m₁ : ℝ) m₂ * |Real.log m₁ - Real.log m₂| := hreal
    _ = max (m₁ : ℝ) m₂ * |Real.log m₂ - Real.log m₁| := by
      rw [abs_sub_comm]
    _ ≤ (2 * M : ℝ) * (Real.pi / (2 * U)) :=
      mul_le_mul hmax hfreq (abs_nonneg _) (by positivity)
    _ = Real.pi * (M : ℝ) / U := by ring

/-- The literal joint logarithmic band gives the sharp real product-distance
bound `dist(m₁*n₁,m₂*n₂) ≤ 2*pi*M*N/T`. -/
theorem jointFrequency_productDist_real_le
    {M N : ℕ} {q : LiteralTuple} {T : ℝ}
    (hq : q ∈ dyadicTupleBox M N)
    (hfreq : |jointFrequency q| ≤ Real.pi / (2 * T)) :
    ((q.1.1 * q.2.1).dist (q.1.2 * q.2.2) : ℝ) ≤
      2 * Real.pi * (M : ℝ) * (N : ℝ) / T := by
  rcases q with ⟨⟨m₁, m₂⟩, ⟨n₁, n₂⟩⟩
  simp [dyadicTupleBox] at hq
  rcases hq with ⟨⟨hm₁, hm₂⟩, hn₁, hn₂⟩
  have hm₁pos : 0 < m₁ := by
    simp only [dyadic, Finset.mem_Ioc] at hm₁
    omega
  have hm₂pos : 0 < m₂ := by
    simp only [dyadic, Finset.mem_Ioc] at hm₂
    omega
  have hn₁pos : 0 < n₁ := by
    simp only [dyadic, Finset.mem_Ioc] at hn₁
    omega
  have hn₂pos : 0 < n₂ := by
    simp only [dyadic, Finset.mem_Ioc] at hn₂
    omega
  have hp₁ : 0 < (m₁ * n₁ : ℝ) := by
    exact_mod_cast Nat.mul_pos hm₁pos hn₁pos
  have hp₂ : 0 < (m₂ * n₂ : ℝ) := by
    exact_mod_cast Nat.mul_pos hm₂pos hn₂pos
  have hreal := abs_sub_le_max_mul_abs_log_sub hp₁ hp₂
  have hm₁upper : m₁ ≤ 2 * M := by
    have h := hm₁
    simp only [dyadic, Finset.mem_Ioc] at h
    exact h.2
  have hm₂upper : m₂ ≤ 2 * M := by
    have h := hm₂
    simp only [dyadic, Finset.mem_Ioc] at h
    exact h.2
  have hn₁upper : n₁ ≤ 2 * N := by
    have h := hn₁
    simp only [dyadic, Finset.mem_Ioc] at h
    exact h.2
  have hn₂upper : n₂ ≤ 2 * N := by
    have h := hn₂
    simp only [dyadic, Finset.mem_Ioc] at h
    exact h.2
  have hmax : max (m₁ * n₁ : ℕ) (m₂ * n₂) ≤ 4 * M * N := by
    rw [max_le_iff]
    constructor
    · calc
        m₁ * n₁ ≤ (2 * M) * (2 * N) := Nat.mul_le_mul hm₁upper hn₁upper
        _ = 4 * M * N := by ring
    · calc
        m₂ * n₂ ≤ (2 * M) * (2 * N) := Nat.mul_le_mul hm₂upper hn₂upper
        _ = 4 * M * N := by ring
  have hjoint :
      jointFrequency ((m₁, m₂), (n₁, n₂)) =
        Real.log (m₂ * n₂) - Real.log (m₁ * n₁) :=
    jointFrequency_eq_log_products hm₁pos hm₂pos hn₁pos hn₂pos
  rw [natCast_dist_eq_abs]
  calc
    |((m₁ * n₁ : ℕ) : ℝ) - (m₂ * n₂ : ℕ)| ≤
        max ((m₁ * n₁ : ℕ) : ℝ) (m₂ * n₂ : ℕ) *
          |Real.log (m₁ * n₁) - Real.log (m₂ * n₂)| := by
      simpa only [Nat.cast_mul] using hreal
    _ = max ((m₁ * n₁ : ℕ) : ℝ) (m₂ * n₂ : ℕ) *
        |jointFrequency ((m₁, m₂), (n₁, n₂))| := by
      rw [hjoint, abs_sub_comm]
    _ ≤ (4 * M * N : ℝ) * (Real.pi / (2 * T)) := by
      apply mul_le_mul _ hfreq (abs_nonneg _) (by positivity)
      exact_mod_cast hmax
    _ = 2 * Real.pi * (M : ℝ) * (N : ℝ) / T := by ring

/-! ## Floor-tight natural interfaces -/

theorem shortFrequency_to_floorCollar
    {M m₁ m₂ : ℕ} {U : ℝ}
    (_hU : 0 < U)
    (hm₁ : m₁ ∈ dyadic M) (hm₂ : m₂ ∈ dyadic M)
    (hfreq : |Real.log m₂ - Real.log m₁| ≤ Real.pi / (2 * U)) :
    m₁.dist m₂ ≤ shortFloorCollar M U := by
  rw [shortFloorCollar, le_min_iff]
  exact ⟨dyadic_dist_le_base hm₁ hm₂,
    Nat.le_floor (shortFrequency_dist_real_le hm₁ hm₂ hfreq)⟩

theorem jointFrequency_to_productFloorCollar
    {M N : ℕ} {q : LiteralTuple} {T : ℝ}
    (_hT : 0 < T)
    (hq : q ∈ dyadicTupleBox M N)
    (hfreq : |jointFrequency q| ≤ Real.pi / (2 * T)) :
    (q.1.1 * q.2.1).dist (q.1.2 * q.2.2) ≤
      productFloorCollar M N T := by
  exact Nat.le_floor (jointFrequency_productDist_real_le hq hfreq)

/-- The floor collars retain the paper's real upper bounds; these are the
inequalities needed after multiplying by `TU/(MN)`. -/
theorem shortFloorCollar_cast_le
    (M : ℕ) {U : ℝ} (hU : 0 < U) :
    (shortFloorCollar M U : ℝ) ≤ Real.pi * (M : ℝ) / U := by
  unfold shortFloorCollar
  have hmin : min M ⌊Real.pi * (M : ℝ) / U⌋₊ ≤
      ⌊Real.pi * (M : ℝ) / U⌋₊ := min_le_right _ _
  calc
    ((min M ⌊Real.pi * (M : ℝ) / U⌋₊ : ℕ) : ℝ) ≤
        (⌊Real.pi * (M : ℝ) / U⌋₊ : ℝ) := by
      exact_mod_cast hmin
    _ ≤ Real.pi * (M : ℝ) / U := Nat.floor_le (by positivity)

theorem productFloorCollar_cast_le
    (M N : ℕ) {T : ℝ} (hT : 0 < T) :
    (productFloorCollar M N T : ℝ) ≤
      2 * Real.pi * (M : ℝ) * (N : ℝ) / T := by
  unfold productFloorCollar
  exact Nat.floor_le (by positivity)

/-- Every exact two-frequency survivor lies in the floor-tight arithmetic
collar. -/
theorem exactFrequencySurvivors_subset_floorCollarTuples
    (M N : ℕ) {T U : ℝ} (hT : 0 < T) (hU : 0 < U) :
    exactFrequencySurvivors M N T U ⊆ floorCollarTuples M N T U := by
  intro q hq
  simp only [exactFrequencySurvivors, frequencyTuples, Finset.mem_filter] at hq
  rcases hq with ⟨hbox, hshort, hjoint⟩
  have hboxParts := hbox
  simp [dyadicTupleBox] at hboxParts
  exact Finset.mem_filter.mpr ⟨hbox,
    shortFrequency_to_floorCollar hU hboxParts.1.1 hboxParts.1.2 hshort,
    jointFrequency_to_productFloorCollar hT hbox hjoint⟩

theorem exactFrequencySurvivor_mem_floorCollars
    {M N : ℕ} {T U : ℝ} (hT : 0 < T) (hU : 0 < U)
    {q : LiteralTuple} (hq : q ∈ exactFrequencySurvivors M N T U) :
    q.1.1.dist q.1.2 ≤ shortFloorCollar M U ∧
      (q.1.1 * q.2.1).dist (q.1.2 * q.2.2) ≤
        productFloorCollar M N T := by
  have hmem := exactFrequencySurvivors_subset_floorCollarTuples M N hT hU hq
  exact (Finset.mem_filter.mp hmem).2

/-! ## Exact sub-unit emptiness -/

theorem shortFloorCollar_eq_zero_of_lt_one
    (M : ℕ) {U : ℝ}
    (hsmall : Real.pi * (M : ℝ) / U < 1) :
    shortFloorCollar M U = 0 := by
  rw [shortFloorCollar, Nat.floor_eq_zero.mpr hsmall]
  simp

theorem productFloorCollar_eq_zero_of_lt_one
    (M N : ℕ) {T : ℝ}
    (hsmall : 2 * Real.pi * (M : ℝ) * (N : ℝ) / T < 1) :
    productFloorCollar M N T = 0 := by
  exact Nat.floor_eq_zero.mpr hsmall

/-- If the real short collar is below one, every exact survivor has equal
short indices. -/
theorem unequalShortFrequencySurvivors_eq_empty_of_short_lt_one
    (M N : ℕ) {T U : ℝ} (hT : 0 < T) (hU : 0 < U)
    (hsmall : Real.pi * (M : ℝ) / U < 1) :
    unequalShortFrequencySurvivors M N T U = ∅ := by
  unfold unequalShortFrequencySurvivors
  rw [Finset.filter_eq_empty_iff]
  intro q hq hne
  have hdist := (exactFrequencySurvivor_mem_floorCollars hT hU hq).1
  rw [shortFloorCollar_eq_zero_of_lt_one M hsmall] at hdist
  exact hne (Nat.eq_of_dist_eq_zero (Nat.eq_zero_of_le_zero hdist))

/-- The positive determinant survivor sector is empty when the exact real
product collar is below one. -/
theorem positiveFrequencySector_eq_empty_of_product_lt_one
    (M N : ℕ) {T U : ℝ} (hT : 0 < T) (hU : 0 < U)
    (hsmall : 2 * Real.pi * (M : ℝ) * (N : ℝ) / T < 1) :
    positiveFrequencySector M N (Real.pi / (2 * U))
        (Real.pi / (2 * T)) = ∅ := by
  unfold positiveFrequencySector
  rw [Finset.filter_eq_empty_iff]
  intro q hq hsector
  have hqExact : q ∈ exactFrequencySurvivors M N T U := hq
  have hdist := (exactFrequencySurvivor_mem_floorCollars hT hU hqExact).2
  rw [productFloorCollar_eq_zero_of_lt_one M N hsmall] at hdist
  have hproductZero : (q.1.1 * q.2.1).dist (q.1.2 * q.2.2) = 0 :=
    Nat.eq_zero_of_le_zero hdist
  have hdetZero : determinant q = 0 := by
    rw [← Int.natAbs_eq_zero, determinant_natAbs_eq_product_dist]
    exact hproductZero
  exact (ne_of_gt hsector.2) hdetZero

/-- The negative determinant survivor sector is empty when the exact real
product collar is below one. -/
theorem negativeFrequencySector_eq_empty_of_product_lt_one
    (M N : ℕ) {T U : ℝ} (hT : 0 < T) (hU : 0 < U)
    (hsmall : 2 * Real.pi * (M : ℝ) * (N : ℝ) / T < 1) :
    negativeFrequencySector M N (Real.pi / (2 * U))
        (Real.pi / (2 * T)) = ∅ := by
  unfold negativeFrequencySector
  rw [Finset.filter_eq_empty_iff]
  intro q hq hsector
  have hqExact : q ∈ exactFrequencySurvivors M N T U := hq
  have hdist := (exactFrequencySurvivor_mem_floorCollars hT hU hqExact).2
  rw [productFloorCollar_eq_zero_of_lt_one M N hsmall] at hdist
  have hproductZero : (q.1.1 * q.2.1).dist (q.1.2 * q.2.2) = 0 :=
    Nat.eq_zero_of_le_zero hdist
  have hdetZero : determinant q = 0 := by
    rw [← Int.natAbs_eq_zero, determinant_natAbs_eq_product_dist]
    exact hproductZero
  exact (ne_of_lt hsector.2) hdetZero

end MAPMixedMeanFloor
