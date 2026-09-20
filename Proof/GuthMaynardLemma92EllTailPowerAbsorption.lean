import GuthMaynardLemma92EllTailBudget
import GuthMaynardLemma92UnequalScaleLargeEllWeld
import GuthMaynardLemma92ThreeScaleEllRange

open scoped Real

noncomputable section
namespace GuthMaynardJIteration

/-! # Final scalar absorption of the Lemma 9.2 ell tail -/

/-- The elementary identity which makes the detector saving explicit after
squaring: `(2/R)^(2j)=4^j/R^(2j)`. -/
theorem two_div_pow_sq_eq_four_pow_div
    {R : ℝ} (j : ℕ) :
    ((2 / R) ^ j) ^ 2 = (4 : ℝ) ^ j / R ^ (2 * j) := by
  calc
    ((2 / R) ^ j) ^ 2 =
        ((2 : ℝ) ^ j * (2 : ℝ) ^ j) / (R ^ j * R ^ j) := by
          rw [pow_two, div_pow]
          ring
    _ = ((2 * 2 : ℝ) ^ j) / R ^ (j + j) := by
          rw [mul_pow, pow_add]
    _ = (4 : ℝ) ^ j / R ^ (2 * j) := by
          congr 2 <;> ring

/-- Every visible polynomial/cardinality factor in the discarded-ell envelope
is bounded by an explicit monomial.  No asymptotic notation is used. -/
theorem sourceLemma92EllTailPolynomialEnvelope_le
    {M : ℕ} {T S eta C delta R : ℝ} (j : ℕ)
    (hT : 1 ≤ T) (hS0 : 0 ≤ S) (hS1 : S ≤ 1)
    (hC : 0 ≤ C) (hR : 0 < R)
    (hMhi : (M : ℝ) ≤ T ^ 4) :
    (7 * T ^ 6) * (2 * Real.rpow T delta) *
        (((7 * (M : ℝ)) * (2 * (M : ℝ)) *
          (C * Real.rpow T eta * (2 / R) ^ j * S)) ^ 2) ≤
      2744 * C ^ 2 * (4 : ℝ) ^ j * T ^ 6 * Real.rpow T delta *
        (T ^ 4) ^ 4 * (Real.rpow T eta) ^ 2 / R ^ (2 * j) := by
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  have hTdelta : 0 ≤ Real.rpow T delta := Real.rpow_nonneg hT0 delta
  have hTeta : 0 ≤ Real.rpow T eta := Real.rpow_nonneg hT0 eta
  have hratio : 0 ≤ 2 / R := by positivity
  have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  calc
    (7 * T ^ 6) * (2 * Real.rpow T delta) *
        (((7 * (M : ℝ)) * (2 * (M : ℝ)) *
          (C * Real.rpow T eta * (2 / R) ^ j * S)) ^ 2) ≤
      (7 * T ^ 6) * (2 * Real.rpow T delta) *
        (((7 * T ^ 4) * (2 * T ^ 4) *
          (C * Real.rpow T eta * (2 / R) ^ j * 1)) ^ 2) := by
            gcongr
    _ = 2744 * C ^ 2 * T ^ 6 * Real.rpow T delta * (T ^ 4) ^ 4 *
        (Real.rpow T eta) ^ 2 * (((2 / R) ^ j) ^ 2) := by ring
    _ = 2744 * C ^ 2 * (4 : ℝ) ^ j * T ^ 6 * Real.rpow T delta *
        (T ^ 4) ^ 4 * (Real.rpow T eta) ^ 2 / R ^ (2 * j) := by
      rw [two_div_pow_sq_eq_four_pow_div]
      ring


/-- With `R=T^kappa`, the explicit polynomial envelope is exactly one base-`T`
monomial times the fixed Fourier-seminorm constant. -/
theorem sourceLemma92EllTailMonomial_eq
    {T C kappa eta delta : ℝ} (j : ℕ) (hT : 0 < T) :
    2744 * C ^ 2 * (4 : ℝ) ^ j * T ^ 6 * Real.rpow T delta *
        (T ^ 4) ^ 4 * (Real.rpow T eta) ^ 2 /
          (Real.rpow T kappa) ^ (2 * j) =
      2744 * C ^ 2 * (4 : ℝ) ^ j *
        Real.rpow T (22 + delta + 2 * eta - 2 * kappa * (j : ℝ)) := by
  have hT0 : 0 ≤ T := hT.le
  have h6 : T ^ (6 : ℕ) = Real.rpow T (6 : ℝ) := by
    exact (Real.rpow_natCast T 6).symm
  have h16 : (T ^ (4 : ℕ)) ^ (4 : ℕ) = Real.rpow T (16 : ℝ) := by
    rw [← pow_mul]
    norm_num
  have heta2 : (Real.rpow T eta) ^ (2 : ℕ) =
      Real.rpow T (eta * 2) :=
    (Real.rpow_mul_natCast hT0 eta 2).symm
  have hkpow : (Real.rpow T kappa) ^ (2 * j) =
      Real.rpow T (kappa * (2 * (j : ℝ))) := by
    calc
      (Real.rpow T kappa) ^ (2 * j) =
          Real.rpow T (kappa * ((2 * j : ℕ) : ℝ)) :=
        (Real.rpow_mul_natCast hT0 kappa (2 * j)).symm
      _ = Real.rpow T (kappa * (2 * (j : ℝ))) := by
        congr 2
        push_cast
        ring
  rw [h6, h16, heta2, hkpow]
  have h1 : Real.rpow T (6 : ℝ) * Real.rpow T delta =
      Real.rpow T (6 + delta) :=
    (Real.rpow_add hT (6 : ℝ) delta).symm
  have h2 : Real.rpow T (6 + delta) * Real.rpow T (16 : ℝ) =
      Real.rpow T (6 + delta + 16) :=
    (Real.rpow_add hT (6 + delta) (16 : ℝ)).symm
  have h3 : Real.rpow T (6 + delta + 16) * Real.rpow T (eta * 2) =
      Real.rpow T (6 + delta + 16 + eta * 2) :=
    (Real.rpow_add hT (6 + delta + 16) (eta * 2)).symm
  have hnum : Real.rpow T (6 : ℝ) * Real.rpow T delta *
      Real.rpow T (16 : ℝ) * Real.rpow T (eta * 2) =
      Real.rpow T (22 + delta + 2 * eta) := by
    rw [h1, h2, h3]
    congr 1 <;> ring
  rw [show
    2744 * C ^ 2 * (4 : ℝ) ^ j * Real.rpow T (6 : ℝ) *
        Real.rpow T delta * Real.rpow T (16 : ℝ) *
        Real.rpow T (eta * 2) /
        Real.rpow T (kappa * (2 * (j : ℝ))) =
      2744 * C ^ 2 * (4 : ℝ) ^ j *
        ((Real.rpow T (6 : ℝ) * Real.rpow T delta *
          Real.rpow T (16 : ℝ) * Real.rpow T (eta * 2)) /
          Real.rpow T (kappa * (2 * (j : ℝ)))) by ring]
  rw [hnum]
  have hsub :
      Real.rpow T (22 + delta + 2 * eta - kappa * (2 * (j : ℝ))) =
        Real.rpow T (22 + delta + 2 * eta) /
          Real.rpow T (kappa * (2 * (j : ℝ))) :=
    Real.rpow_sub hT (22 + delta + 2 * eta)
      (kappa * (2 * (j : ℝ)))
  calc
    2744 * C ^ 2 * (4 : ℝ) ^ j *
        (Real.rpow T (22 + delta + 2 * eta) /
          Real.rpow T (kappa * (2 * (j : ℝ)))) =
      2744 * C ^ 2 * (4 : ℝ) ^ j *
        Real.rpow T (22 + delta + 2 * eta -
          kappa * (2 * (j : ℝ))) := by rw [hsub]
    _ = 2744 * C ^ 2 * (4 : ℝ) ^ j *
        Real.rpow T (22 + delta + 2 * eta - 2 * kappa * (j : ℝ)) := by
      congr 2
      ring


/-- Once the fixed Fourier constant is charged to one power of `T`, the
chosen detector moment absorbs the complete `T^22` polynomial loss and the
advertised further `T^100`. -/
theorem sourceLemma92EllTailMonomial_le_time_neg100
    {T C kappa eta delta : ℝ} (j : ℕ)
    (hT : 1 ≤ T)
    (hconstant : 2744 * C ^ 2 * (4 : ℝ) ^ j ≤ T)
    (hexponent : 123 + delta + 2 * eta ≤ 2 * kappa * (j : ℝ)) :
    2744 * C ^ 2 * (4 : ℝ) ^ j *
        Real.rpow T (22 + delta + 2 * eta - 2 * kappa * (j : ℝ)) ≤
      T⁻¹ ^ 100 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hT0 : 0 ≤ T := hTpos.le
  let e : ℝ := 22 + delta + 2 * eta - 2 * kappa * (j : ℝ)
  have he : 1 + e ≤ -100 := by
    dsimp only [e]
    linarith
  calc
    2744 * C ^ 2 * (4 : ℝ) ^ j * Real.rpow T e ≤
        T * Real.rpow T e :=
      mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hT0 e)
    _ = Real.rpow T 1 * Real.rpow T e := by
      have hone : Real.rpow T 1 = T := Real.rpow_one T
      rw [hone]
    _ = Real.rpow T (1 + e) := by
      exact (Real.rpow_add hTpos 1 e).symm
    _ ≤ Real.rpow T (-100 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hT he
    _ = T⁻¹ ^ 100 := by
      have hneg : Real.rpow T (-100 : ℝ) =
          (Real.rpow T (100 : ℝ))⁻¹ := Real.rpow_neg hT0 100
      have hnat : Real.rpow T (100 : ℝ) = T ^ (100 : ℕ) :=
        Real.rpow_natCast T 100
      rw [hneg, hnat]
      exact (inv_pow T 100).symm

/-- Any positive detector exponent admits a finite Fourier moment that beats
all visible polynomial losses in the ell tail. -/
theorem exists_sourceLemma92EllTail_decayOrder
    {kappa : ℝ} (hkappa : 0 < kappa) (eta delta : ℝ) :
    ∃ j : ℕ, 123 + delta + 2 * eta ≤ 2 * kappa * (j : ℝ) := by
  obtain ⟨j, hj⟩ := exists_nat_gt ((123 + delta + 2 * eta) / (2 * kappa))
  refine ⟨j, ?_⟩
  have hden : 0 < 2 * kappa := by positivity
  have hj' : (123 + delta + 2 * eta) / (2 * kappa) < (j : ℝ) := by
    exact_mod_cast hj
  exact (le_of_lt ((div_lt_iff₀ hden).mp hj')).trans_eq (by ring)

/-- The fixed seminorm constant is absorbed after one explicit threshold. -/
theorem exists_sourceLemma92EllTail_fixedConstant_threshold
    (C : ℝ) (j : ℕ) :
    ∃ T0 : ℝ, 1 ≤ T0 ∧ ∀ T : ℝ, T0 ≤ T →
      2744 * C ^ 2 * (4 : ℝ) ^ j ≤ T := by
  refine ⟨max 1 (2744 * C ^ 2 * (4 : ℝ) ^ j), le_max_left _ _, ?_⟩
  intro T hT
  exact (le_max_right _ _).trans hT

/-- Literal completion of the first-Poisson discarded-ell tail.  Its only
large-`T` premise is the explicit threshold for the fixed Fourier seminorm. -/
theorem sourceLemma92EllTailCostRadius_largeRange_le_time_neg100
    {M : ℕ} (hM : 0 < M) {T S eta C delta kappa : ℝ} (j : ℕ)
    (hT : 1 ≤ T) (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (hC : 0 ≤ C)
    (hMhi : (M : ℝ) ≤ T ^ 4)
    (hB6 : Real.rpow T delta ≤ T ^ 6)
    (hhalf : 2 * Real.rpow T delta ≤ Real.rpow T kappa * T)
    (hconstant : 2744 * C ^ 2 * (4 : ℝ) ^ j ≤ T)
    (hexponent : 123 + delta + 2 * eta ≤ 2 * kappa * (j : ℝ)) :
    sourceLemma92EllTailCostRadius
        (sourceLemma92LargeEllRange M T (Real.rpow T delta)) M
        T S eta C delta (Real.rpow T kappa) j ≤ T⁻¹ ^ 100 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hRpos : 0 < Real.rpow T kappa := Real.rpow_pos_of_pos hTpos kappa
  calc
    sourceLemma92EllTailCostRadius
        (sourceLemma92LargeEllRange M T (Real.rpow T delta)) M
        T S eta C delta (Real.rpow T kappa) j ≤
      (7 * T ^ 6) * (2 * Real.rpow T delta) *
        (((7 * (M : ℝ)) * (2 * (M : ℝ)) *
          (C * Real.rpow T eta *
            (2 / Real.rpow T kappa) ^ j * S)) ^ 2) :=
      sourceLemma92EllTailCostRadius_largeRange_le hM j hT hS0 hC
        hB6 hRpos hhalf
    _ ≤ 2744 * C ^ 2 * (4 : ℝ) ^ j * T ^ 6 *
        Real.rpow T delta * (T ^ 4) ^ 4 *
          (Real.rpow T eta) ^ 2 /
            (Real.rpow T kappa) ^ (2 * j) :=
      sourceLemma92EllTailPolynomialEnvelope_le j hT hS0 hS1 hC hRpos hMhi
    _ = 2744 * C ^ 2 * (4 : ℝ) ^ j *
        Real.rpow T (22 + delta + 2 * eta - 2 * kappa * (j : ℝ)) :=
      sourceLemma92EllTailMonomial_eq j hTpos
    _ ≤ T⁻¹ ^ 100 :=
      sourceLemma92EllTailMonomial_le_time_neg100 j hT hconstant hexponent


/-- If the affine scale is at least the second-Poisson scale, the literal
unequal-scale frequency denominator retains the same `2/R` saving. -/
theorem sourceLemma92_ellTail_ratio_unequal_le_two_div_radius
    {M : ℕ} (hM : 0 < M) {M3 T B R : ℝ}
    (hM3 : 0 < M3) (hscale : (M : ℝ) ≤ M3)
    (hT : 0 < T) (hB : 0 ≤ B) (hR : 0 < R)
    (hhalf : 2 * B ≤ R * T) :
    T / ((M : ℝ) *
        (R * T / (M : ℝ) - B / M3)) ≤ 2 / R := by
  have hMreal : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hratioScale : (M : ℝ) / M3 ≤ 1 := (div_le_one hM3).2 hscale
  have hMB : (M : ℝ) * B / M3 ≤ B := by
    calc
      (M : ℝ) * B / M3 = ((M : ℝ) / M3) * B := by ring
      _ ≤ 1 * B := mul_le_mul_of_nonneg_right hratioScale hB
      _ = B := one_mul B
  have hden : (M : ℝ) *
      (R * T / (M : ℝ) - B / M3) =
        R * T - (M : ℝ) * B / M3 := by
    field_simp [hMreal.ne', hM3.ne']
  have hgap : 0 < R * T - B := by nlinarith
  have hdenLower : R * T - B ≤ R * T - (M : ℝ) * B / M3 := by
    linarith
  have hbase := sourceLemma92_ellTail_ratio_le_two_div_radius
    hM hT hB hR hhalf
  rw [sourceLemma92_ellTail_frequencyGap_eq hM] at hbase
  rw [hden]
  exact (div_le_div_of_nonneg_left hT.le hgap hdenLower).trans hbase

/-- The full three-scale application does not need the artificial ordering
`M₂ ≤ M₃`.  It is enough that `M₂ ≤ T`, `M₃ ≥ 1`, and the
detector radius pays twice the smoothing width.  Then
`M₂ B / M₃ ≤ T B ≤ RT/2`, so the same `2/R` saving survives. -/
theorem sourceLemma92_ellTail_ratio_unequal_le_two_div_radius_of_scale_le_time
    {M : ℕ} (hM : 0 < M) {M3 T B R : ℝ}
    (hM3one : 1 ≤ M3) (hT : 1 ≤ T) (hMT : (M : ℝ) ≤ T)
    (hB : 0 ≤ B) (hR : 0 < R) (hhalf : 2 * B ≤ R) :
    T / ((M : ℝ) *
        (R * T / (M : ℝ) - B / M3)) ≤ 2 / R := by
  have hMpos : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hM3pos : 0 < M3 := lt_of_lt_of_le zero_lt_one hM3one
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hdivM : (M : ℝ) / M3 ≤ (M : ℝ) :=
    div_le_self hMpos.le hM3one
  have hMB : (M : ℝ) * B / M3 ≤ T * B := by
    calc
      (M : ℝ) * B / M3 = ((M : ℝ) / M3) * B := by ring
      _ ≤ (M : ℝ) * B := mul_le_mul_of_nonneg_right hdivM hB
      _ ≤ T * B := mul_le_mul_of_nonneg_right hMT hB
  have hTB : 2 * (T * B) ≤ R * T := by
    have := mul_le_mul_of_nonneg_right hhalf hTpos.le
    nlinarith
  have hdenEq : (M : ℝ) *
      (R * T / (M : ℝ) - B / M3) =
        R * T - (M : ℝ) * B / M3 := by
    field_simp [hMpos.ne', hM3pos.ne']
  rw [hdenEq]
  have hdenpos : 0 < R * T - (M : ℝ) * B / M3 := by
    nlinarith
  rw [div_le_div_iff₀ hdenpos hR]
  nlinarith

/-- Complete unequal-scale ell-tail envelope under the source ordering
`M₂≤M₃`. -/
theorem sourceLemma92EllTailCostRadiusUnequal_largeRange_le
    {M : ℕ} (hM : 0 < M) {M3 T S eta C delta R : ℝ} (j : ℕ)
    (hM3 : 0 < M3) (hscale : (M : ℝ) ≤ M3)
    (hT : 1 ≤ T) (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hB6 : T ^ delta ≤ T ^ 6) (hR : 0 < R)
    (hhalf : 2 * T ^ delta ≤ R * T) :
    sourceLemma92EllTailCostRadiusUnequal
        (sourceLemma92LargeEllRange M T (T ^ delta)) M M3
        T S eta C delta R j ≤
      (7 * T ^ 6) * (2 * T ^ delta) *
        (((7 * (M : ℝ)) * (2 * (M : ℝ)) *
          (C * T ^ eta * (2 / R) ^ j * S)) ^ 2) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hB0 : 0 ≤ T ^ delta := Real.rpow_nonneg hTpos.le delta
  have hcard := card_sourceLemma92LargeEllRange_cast_le_seven_time_six
    hM hT hB0 hB6
  have hMone : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  have hmcard : 4 * (M : ℝ) + 3 ≤ 7 * (M : ℝ) := by nlinarith
  have hratio := sourceLemma92_ellTail_ratio_unequal_le_two_div_radius
    hM hM3 hscale hTpos hB0 hR hhalf
  have hdenpos : 0 < (M : ℝ) *
      (R * T / (M : ℝ) - T ^ delta / M3) := by
    have hMB : (M : ℝ) * T ^ delta / M3 ≤
        T ^ delta := by
      have hs : (M : ℝ) / M3 ≤ 1 := (div_le_one hM3).2 hscale
      calc
        (M : ℝ) * T ^ delta / M3 =
            ((M : ℝ) / M3) * T ^ delta := by ring
        _ ≤ 1 * T ^ delta :=
          mul_le_mul_of_nonneg_right hs hB0
        _ = T ^ delta := one_mul _
    have hRTgap : 0 < R * T - T ^ delta := by nlinarith
    have hMreal : (M : ℝ) ≠ 0 := (Nat.cast_pos.mpr hM).ne'
    field_simp [hMreal, hM3.ne']
    nlinarith
  have hpow :
      (T / ((M : ℝ) *
        (R * T / (M : ℝ) - T ^ delta / M3))) ^ j ≤
          (2 / R) ^ j :=
    pow_le_pow_left₀ (by positivity) hratio j
  unfold sourceLemma92EllTailCostRadiusUnequal
  gcongr

/-- Final literal unequal-scale tail absorption used by the full Proposition
9.1 supremum. -/
theorem sourceLemma92EllTailCostRadiusUnequal_largeRange_le_time_neg100
    {M : ℕ} (hM : 0 < M) {M3 T S eta C delta kappa : ℝ} (j : ℕ)
    (hM3 : 0 < M3) (hscale : (M : ℝ) ≤ M3)
    (hT : 1 ≤ T) (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (hC : 0 ≤ C)
    (hMhi : (M : ℝ) ≤ T ^ 4)
    (hB6 : Real.rpow T delta ≤ T ^ 6)
    (hhalf : 2 * Real.rpow T delta ≤ Real.rpow T kappa * T)
    (hconstant : 2744 * C ^ 2 * (4 : ℝ) ^ j ≤ T)
    (hexponent : 123 + delta + 2 * eta ≤ 2 * kappa * (j : ℝ)) :
    sourceLemma92EllTailCostRadiusUnequal
        (sourceLemma92LargeEllRange M T (Real.rpow T delta)) M M3
        T S eta C delta (Real.rpow T kappa) j ≤ T⁻¹ ^ 100 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hRpos : 0 < Real.rpow T kappa := Real.rpow_pos_of_pos hTpos kappa
  calc
    sourceLemma92EllTailCostRadiusUnequal
        (sourceLemma92LargeEllRange M T (Real.rpow T delta)) M M3
        T S eta C delta (Real.rpow T kappa) j ≤
      (7 * T ^ 6) * (2 * Real.rpow T delta) *
        (((7 * (M : ℝ)) * (2 * (M : ℝ)) *
          (C * Real.rpow T eta *
            (2 / Real.rpow T kappa) ^ j * S)) ^ 2) :=
      sourceLemma92EllTailCostRadiusUnequal_largeRange_le hM j hM3 hscale
        hT hS0 hC hB6 hRpos hhalf
    _ ≤ 2744 * C ^ 2 * (4 : ℝ) ^ j * T ^ 6 *
        Real.rpow T delta * (T ^ 4) ^ 4 *
          (Real.rpow T eta) ^ 2 /
            (Real.rpow T kappa) ^ (2 * j) :=
      sourceLemma92EllTailPolynomialEnvelope_le j hT hS0 hS1 hC hRpos hMhi
    _ = 2744 * C ^ 2 * (4 : ℝ) ^ j *
        Real.rpow T (22 + delta + 2 * eta - 2 * kappa * (j : ℝ)) :=
      sourceLemma92EllTailMonomial_eq j hTpos
    _ ≤ T⁻¹ ^ 100 :=
      sourceLemma92EllTailMonomial_le_time_neg100 j hT hconstant hexponent

/-- The unequal-scale ell-tail estimate only needs a cardinality budget for
the first-Poisson cover.  This version keeps that cover abstract, so its
`M₁,M₃` geometry does not get silently identified with the second-Poisson
scale `M₂=M`. -/
theorem sourceLemma92EllTailCostRadiusUnequal_le_of_card
    (ellRange : Finset ℤ) {M : ℕ} (hM : 0 < M)
    {M3 T S eta C delta R : ℝ} (j : ℕ)
    (hM3 : 0 < M3) (hscale : (M : ℝ) ≤ M3)
    (hT : 1 ≤ T) (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hcard : (ellRange.card : ℝ) ≤ 7 * T ^ 6)
    (hR : 0 < R) (hhalf : 2 * T ^ delta ≤ R * T) :
    sourceLemma92EllTailCostRadiusUnequal ellRange M M3
        T S eta C delta R j ≤
      (7 * T ^ 6) * (2 * T ^ delta) *
        (((7 * (M : ℝ)) * (2 * (M : ℝ)) *
          (C * T ^ eta * (2 / R) ^ j * S)) ^ 2) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hB0 : 0 ≤ T ^ delta := Real.rpow_nonneg hTpos.le delta
  have hMone : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  have hmcard : 4 * (M : ℝ) + 3 ≤ 7 * (M : ℝ) := by nlinarith
  have hratio := sourceLemma92_ellTail_ratio_unequal_le_two_div_radius
    hM hM3 hscale hTpos hB0 hR hhalf
  have hdenpos : 0 < (M : ℝ) *
      (R * T / (M : ℝ) - T ^ delta / M3) := by
    have hMB : (M : ℝ) * T ^ delta / M3 ≤ T ^ delta := by
      have hs : (M : ℝ) / M3 ≤ 1 := (div_le_one hM3).2 hscale
      calc
        (M : ℝ) * T ^ delta / M3 =
            ((M : ℝ) / M3) * T ^ delta := by ring
        _ ≤ 1 * T ^ delta := mul_le_mul_of_nonneg_right hs hB0
        _ = T ^ delta := one_mul _
    have hRTgap : 0 < R * T - T ^ delta := by nlinarith
    have hMreal : (M : ℝ) ≠ 0 := (Nat.cast_pos.mpr hM).ne'
    field_simp [hMreal, hM3.ne']
    nlinarith
  have hratio0 : 0 ≤ T / ((M : ℝ) *
      (R * T / (M : ℝ) - T ^ delta / M3)) :=
    div_nonneg hTpos.le hdenpos.le
  have hpow :
      (T / ((M : ℝ) *
        (R * T / (M : ℝ) - T ^ delta / M3))) ^ j ≤
          (2 / R) ^ j :=
    pow_le_pow_left₀ hratio0 hratio j
  unfold sourceLemma92EllTailCostRadiusUnequal
  gcongr

/-- Abstract-cardinality envelope in the application-faithful scale regime
`M₂ ≤ T`, `M₃ ≥ 1`.  This is the unequal-scale replacement for the
earlier `M₂ ≤ M₃` interface. -/
theorem sourceLemma92EllTailCostRadiusUnequal_le_of_card_of_scale_le_time
    (ellRange : Finset ℤ) {M : ℕ} (hM : 0 < M)
    {M3 T S eta C delta R : ℝ} (j : ℕ)
    (hM3one : 1 ≤ M3) (hT : 1 ≤ T) (hMT : (M : ℝ) ≤ T)
    (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hcard : (ellRange.card : ℝ) ≤ 7 * T ^ 6)
    (hR : 0 < R) (hhalf : 2 * T ^ delta ≤ R) :
    sourceLemma92EllTailCostRadiusUnequal ellRange M M3
        T S eta C delta R j ≤
      (7 * T ^ 6) * (2 * T ^ delta) *
        (((7 * (M : ℝ)) * (2 * (M : ℝ)) *
          (C * T ^ eta * (2 / R) ^ j * S)) ^ 2) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hB0 : 0 ≤ T ^ delta := Real.rpow_nonneg hTpos.le delta
  have hMone : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  have hmcard : 4 * (M : ℝ) + 3 ≤ 7 * (M : ℝ) := by nlinarith
  have hratio :=
    sourceLemma92_ellTail_ratio_unequal_le_two_div_radius_of_scale_le_time
      hM hM3one hT hMT hB0 hR hhalf
  have hM3pos : 0 < M3 := lt_of_lt_of_le zero_lt_one hM3one
  have hdenpos : 0 < (M : ℝ) *
      (R * T / (M : ℝ) - T ^ delta / M3) := by
    have hMpos : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
    have hdivM : (M : ℝ) / M3 ≤ (M : ℝ) :=
      div_le_self hMpos.le hM3one
    have hMB : (M : ℝ) * T ^ delta / M3 ≤ T * T ^ delta := by
      calc
        (M : ℝ) * T ^ delta / M3 =
            ((M : ℝ) / M3) * T ^ delta := by ring
        _ ≤ (M : ℝ) * T ^ delta :=
          mul_le_mul_of_nonneg_right hdivM hB0
        _ ≤ T * T ^ delta := mul_le_mul_of_nonneg_right hMT hB0
    have hTB : 2 * (T * T ^ delta) ≤ R * T := by
      have := mul_le_mul_of_nonneg_right hhalf hTpos.le
      nlinarith
    have hdenEq : (M : ℝ) *
        (R * T / (M : ℝ) - T ^ delta / M3) =
          R * T - (M : ℝ) * T ^ delta / M3 := by
      field_simp [hMpos.ne', hM3pos.ne']
    rw [hdenEq]
    nlinarith
  have hratio0 : 0 ≤ T / ((M : ℝ) *
      (R * T / (M : ℝ) - T ^ delta / M3)) :=
    div_nonneg hTpos.le hdenpos.le
  have hpow :
      (T / ((M : ℝ) *
        (R * T / (M : ℝ) - T ^ delta / M3))) ^ j ≤
          (2 / R) ^ j :=
    pow_le_pow_left₀ hratio0 hratio j
  unfold sourceLemma92EllTailCostRadiusUnequal
  gcongr

/-- Abstract-cardinality completion of the unequal-scale discarded-ell tail.
The final power saving is independent of how the first-Poisson ell cover was
constructed. -/
theorem sourceLemma92EllTailCostRadiusUnequal_le_time_neg100_of_card
    (ellRange : Finset ℤ) {M : ℕ} (hM : 0 < M)
    {M3 T S eta C delta kappa : ℝ} (j : ℕ)
    (hM3 : 0 < M3) (hscale : (M : ℝ) ≤ M3)
    (hT : 1 ≤ T) (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (hC : 0 ≤ C)
    (hMhi : (M : ℝ) ≤ T ^ 4)
    (hcard : (ellRange.card : ℝ) ≤ 7 * T ^ 6)
    (hhalf : 2 * Real.rpow T delta ≤ Real.rpow T kappa * T)
    (hconstant : 2744 * C ^ 2 * (4 : ℝ) ^ j ≤ T)
    (hexponent : 123 + delta + 2 * eta ≤ 2 * kappa * (j : ℝ)) :
    sourceLemma92EllTailCostRadiusUnequal ellRange M M3
        T S eta C delta (Real.rpow T kappa) j ≤ T⁻¹ ^ 100 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hRpos : 0 < Real.rpow T kappa := Real.rpow_pos_of_pos hTpos kappa
  calc
    sourceLemma92EllTailCostRadiusUnequal ellRange M M3
        T S eta C delta (Real.rpow T kappa) j ≤
      (7 * T ^ 6) * (2 * Real.rpow T delta) *
        (((7 * (M : ℝ)) * (2 * (M : ℝ)) *
          (C * Real.rpow T eta *
            (2 / Real.rpow T kappa) ^ j * S)) ^ 2) :=
      sourceLemma92EllTailCostRadiusUnequal_le_of_card ellRange hM j
        hM3 hscale hT hS0 hC hcard hRpos hhalf
    _ ≤ 2744 * C ^ 2 * (4 : ℝ) ^ j * T ^ 6 *
        Real.rpow T delta * (T ^ 4) ^ 4 *
          (Real.rpow T eta) ^ 2 /
            (Real.rpow T kappa) ^ (2 * j) :=
      sourceLemma92EllTailPolynomialEnvelope_le j hT hS0 hS1 hC hRpos hMhi
    _ = 2744 * C ^ 2 * (4 : ℝ) ^ j *
        Real.rpow T (22 + delta + 2 * eta - 2 * kappa * (j : ℝ)) :=
      sourceLemma92EllTailMonomial_eq j hTpos
    _ ≤ T⁻¹ ^ 100 :=
      sourceLemma92EllTailMonomial_le_time_neg100 j hT hconstant hexponent

/-- Final `T^-100` absorption with no comparison between `M₂` and `M₃`.
The stronger detector-width condition `2T^delta ≤ T^kappa` is compatible
with the epsilon ledger by choosing `delta < kappa`. -/
theorem sourceLemma92EllTailCostRadiusUnequal_le_time_neg100_of_card_of_scale_le_time
    (ellRange : Finset ℤ) {M : ℕ} (hM : 0 < M)
    {M3 T S eta C delta kappa : ℝ} (j : ℕ)
    (hM3one : 1 ≤ M3) (hT : 1 ≤ T) (hMT : (M : ℝ) ≤ T)
    (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (hC : 0 ≤ C)
    (hMhi : (M : ℝ) ≤ T ^ 4)
    (hcard : (ellRange.card : ℝ) ≤ 7 * T ^ 6)
    (hhalf : 2 * Real.rpow T delta ≤ Real.rpow T kappa)
    (hconstant : 2744 * C ^ 2 * (4 : ℝ) ^ j ≤ T)
    (hexponent : 123 + delta + 2 * eta ≤ 2 * kappa * (j : ℝ)) :
    sourceLemma92EllTailCostRadiusUnequal ellRange M M3
        T S eta C delta (Real.rpow T kappa) j ≤ T⁻¹ ^ 100 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hRpos : 0 < Real.rpow T kappa := Real.rpow_pos_of_pos hTpos kappa
  calc
    sourceLemma92EllTailCostRadiusUnequal ellRange M M3
        T S eta C delta (Real.rpow T kappa) j ≤
      (7 * T ^ 6) * (2 * Real.rpow T delta) *
        (((7 * (M : ℝ)) * (2 * (M : ℝ)) *
          (C * Real.rpow T eta *
            (2 / Real.rpow T kappa) ^ j * S)) ^ 2) :=
      sourceLemma92EllTailCostRadiusUnequal_le_of_card_of_scale_le_time
        ellRange hM j hM3one hT hMT hS0 hC hcard hRpos hhalf
    _ ≤ 2744 * C ^ 2 * (4 : ℝ) ^ j * T ^ 6 *
        Real.rpow T delta * (T ^ 4) ^ 4 *
          (Real.rpow T eta) ^ 2 /
            (Real.rpow T kappa) ^ (2 * j) :=
      sourceLemma92EllTailPolynomialEnvelope_le j hT hS0 hS1 hC hRpos hMhi
    _ = 2744 * C ^ 2 * (4 : ℝ) ^ j *
        Real.rpow T (22 + delta + 2 * eta - 2 * kappa * (j : ℝ)) :=
      sourceLemma92EllTailMonomial_eq j hTpos
    _ ≤ T⁻¹ ^ 100 :=
      sourceLemma92EllTailMonomial_le_time_neg100 j hT hconstant hexponent

/-- Literal three-scale tail for arbitrary unequal dyadic scales below `T`. -/
theorem sourceLemma92ThreeScaleEllTail_le_time_neg100_of_scale_le_time
    {M1 M2 M3 : ℕ} (hM1 : 0 < M1) (hM2 : 0 < M2) (hM3 : 0 < M3)
    {T S eta C delta kappa : ℝ} (j : ℕ)
    (hT : 1 ≤ T) (hM2T : (M2 : ℝ) ≤ T)
    (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (hC : 0 ≤ C)
    (hM2hi : (M2 : ℝ) ≤ T ^ 4)
    (hB6 : Real.rpow T delta ≤ T ^ 6)
    (hhalf : 2 * Real.rpow T delta ≤ Real.rpow T kappa)
    (hconstant : 2744 * C ^ 2 * (4 : ℝ) ^ j ≤ T)
    (hexponent : 123 + delta + 2 * eta ≤ 2 * kappa * (j : ℝ)) :
    sourceLemma92EllTailCostRadiusUnequal
        (sourceLemma92ThreeScaleEllRange M1 M3 T (Real.rpow T delta))
        M2 (M3 : ℝ) T S eta C delta (Real.rpow T kappa) j ≤
      T⁻¹ ^ 100 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hB0 : 0 ≤ Real.rpow T delta := Real.rpow_nonneg hTpos.le delta
  have hcard := card_sourceLemma92ThreeScaleEllRange_cast_le_seven_time_six
    hM1 hM3 hT hB0 hB6
  have hM3one : (1 : ℝ) ≤ (M3 : ℝ) := by exact_mod_cast hM3
  exact
    sourceLemma92EllTailCostRadiusUnequal_le_time_neg100_of_card_of_scale_le_time
      (sourceLemma92ThreeScaleEllRange M1 M3 T (Real.rpow T delta))
      hM2 j hM3one hT hM2T hS0 hS1 hC hM2hi hcard hhalf
      hconstant hexponent

/-- Literal three-scale completion: `M₁` builds the first-Poisson ell cover,
`M₂` controls the second-Poisson detector, and `M₃` remains the affine scale.
Only the source ordering `M₂≤M₃` is used. -/
theorem sourceLemma92ThreeScaleEllTail_le_time_neg100
    {M1 M2 M3 : ℕ} (hM1 : 0 < M1) (hM2 : 0 < M2) (hM3 : 0 < M3)
    {T S eta C delta kappa : ℝ} (j : ℕ)
    (hscale : (M2 : ℝ) ≤ (M3 : ℝ))
    (hT : 1 ≤ T) (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (hC : 0 ≤ C)
    (hM2hi : (M2 : ℝ) ≤ T ^ 4)
    (hB6 : Real.rpow T delta ≤ T ^ 6)
    (hhalf : 2 * Real.rpow T delta ≤ Real.rpow T kappa * T)
    (hconstant : 2744 * C ^ 2 * (4 : ℝ) ^ j ≤ T)
    (hexponent : 123 + delta + 2 * eta ≤ 2 * kappa * (j : ℝ)) :
    sourceLemma92EllTailCostRadiusUnequal
        (sourceLemma92ThreeScaleEllRange M1 M3 T (Real.rpow T delta))
        M2 (M3 : ℝ) T S eta C delta (Real.rpow T kappa) j ≤
      T⁻¹ ^ 100 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hB0 : 0 ≤ Real.rpow T delta := Real.rpow_nonneg hTpos.le delta
  have hcard := card_sourceLemma92ThreeScaleEllRange_cast_le_seven_time_six
    hM1 hM3 hT hB0 hB6
  exact sourceLemma92EllTailCostRadiusUnequal_le_time_neg100_of_card
    (sourceLemma92ThreeScaleEllRange M1 M3 T (Real.rpow T delta))
    hM2 j (Nat.cast_pos.mpr hM3) hscale hT hS0 hS1 hC hM2hi hcard
    hhalf hconstant hexponent

#print axioms GuthMaynardJIteration.sourceLemma92_ellTail_ratio_unequal_le_two_div_radius
#print axioms GuthMaynardJIteration.sourceLemma92EllTailCostRadiusUnequal_largeRange_le
#print axioms GuthMaynardJIteration.sourceLemma92EllTailCostRadiusUnequal_largeRange_le_time_neg100
#print axioms GuthMaynardJIteration.sourceLemma92EllTailCostRadiusUnequal_le_of_card
#print axioms GuthMaynardJIteration.sourceLemma92EllTailCostRadiusUnequal_le_time_neg100_of_card
#print axioms GuthMaynardJIteration.sourceLemma92ThreeScaleEllTail_le_time_neg100
#print axioms GuthMaynardJIteration.sourceLemma92EllTailMonomial_le_time_neg100
#print axioms GuthMaynardJIteration.exists_sourceLemma92EllTail_decayOrder
#print axioms GuthMaynardJIteration.exists_sourceLemma92EllTail_fixedConstant_threshold
#print axioms GuthMaynardJIteration.sourceLemma92EllTailCostRadius_largeRange_le_time_neg100
#print axioms GuthMaynardJIteration.sourceLemma92EllTailMonomial_eq
#print axioms GuthMaynardJIteration.two_div_pow_sq_eq_four_pow_div
#print axioms GuthMaynardJIteration.sourceLemma92EllTailPolynomialEnvelope_le

end GuthMaynardJIteration
