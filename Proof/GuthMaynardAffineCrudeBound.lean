import GuthMaynardJIterationAffineEnergy
import GuthMaynardJIterationDeterministic
import GuthMaynardJIterationMediumRegionIntegration

open MeasureTheory
open scoped BigOperators Real

noncomputable section
namespace GuthMaynardJIteration

/-!
# The crude base estimate in Guth--Maynard Proposition 9.1

This is the source's base case for the downward epsilon induction: finite
Cauchy--Schwarz followed by the exact affine Jacobian.
-/

/-- Flatten the three nested source ranges into one product range. -/
theorem sourceFiniteAffineSum_eq_product
    (m1Range m2Range jRange : Finset ℤ) (f : ℝ → ℝ) (u : ℝ) :
    sourceFiniteAffineSum m1Range m2Range jRange f u =
      ∑ p ∈ m1Range ×ˢ (m2Range ×ˢ jRange),
        f (((p.1 : ℝ) * u + (p.2.2 : ℝ)) / (p.2.1 : ℝ)) := by
  unfold sourceFiniteAffineSum
  rw [Finset.sum_product]
  simp_rw [Finset.sum_product]

theorem continuous_sourceFiniteAffineSum
    (m1Range m2Range jRange : Finset ℤ) (f : ℝ → ℝ)
    (hf : Continuous f) :
    Continuous (sourceFiniteAffineSum m1Range m2Range jRange f) := by
  unfold sourceFiniteAffineSum
  fun_prop

/-- Pointwise finite Cauchy--Schwarz with the exact product cardinality. -/
theorem sourceFiniteAffineSum_sq_le
    (m1Range m2Range jRange : Finset ℤ) (f : ℝ → ℝ) (u : ℝ) :
    sourceFiniteAffineSum m1Range m2Range jRange f u ^ 2 ≤
      ((m1Range.card * m2Range.card * jRange.card : ℕ) : ℝ) *
        ∑ p ∈ m1Range ×ˢ (m2Range ×ˢ jRange),
          f (((p.1 : ℝ) * u + (p.2.2 : ℝ)) / (p.2.1 : ℝ)) ^ 2 := by
  let ranges : Finset (ℤ × (ℤ × ℤ)) :=
    m1Range ×ˢ (m2Range ×ˢ jRange)
  let term : (ℤ × (ℤ × ℤ)) → ℝ := fun p =>
    f (((p.1 : ℝ) * u + (p.2.2 : ℝ)) / (p.2.1 : ℝ))
  have hcs := norm_finset_sum_sq_le_card_mul_sum_norm_sq ranges term
  have hsum : sourceFiniteAffineSum m1Range m2Range jRange f u =
      ∑ p ∈ ranges, term p := by
    exact sourceFiniteAffineSum_eq_product m1Range m2Range jRange f u
  rw [← hsum] at hcs
  simp only [Real.norm_eq_abs, sq_abs, ranges, term,
    Finset.card_product, Nat.cast_mul] at hcs
  convert hcs using 1 <;> push_cast <;> ring

/-- Exact integral of one affine square, including the absolute Jacobian. -/
theorem integral_sq_affine_ratio
    (f : ℝ → ℝ) {m1 m2 j : ℤ} (hm1 : m1 ≠ 0) (hm2 : m2 ≠ 0) :
    (∫ u : ℝ, f (((m1 : ℝ) * u + (j : ℝ)) / (m2 : ℝ)) ^ 2) =
      |(m2 : ℝ) / (m1 : ℝ)| * ∫ x : ℝ, f x ^ 2 := by
  have hm1R : (m1 : ℝ) ≠ 0 := by exact_mod_cast hm1
  have hm2R : (m2 : ℝ) ≠ 0 := by exact_mod_cast hm2
  let F : ℝ → ℝ := fun x => f x ^ 2
  have hchange := integral_affine_change_real F
    ((m1 : ℝ) / (m2 : ℝ)) ((j : ℝ) / (m2 : ℝ))
  have hfun : (fun u : ℝ =>
      f (((m1 : ℝ) * u + (j : ℝ)) / (m2 : ℝ)) ^ 2) =
      (fun u : ℝ => F ((j : ℝ) / (m2 : ℝ) +
        ((m1 : ℝ) / (m2 : ℝ)) * u)) := by
    funext u
    dsimp only [F]
    congr 2
    field_simp [hm2R]
    ring
  rw [hfun, hchange]
  congr 2
  · congr 1
    field_simp [hm1R, hm2R]

/-- Integrability of one affine square follows from `f in L2`. -/
theorem integrable_sq_affine_ratio
    (f : ℝ → ℝ) (hf2 : Integrable (fun x : ℝ => f x ^ 2))
    {m1 m2 j : ℤ} (hm1 : m1 ≠ 0) (hm2 : m2 ≠ 0) :
    Integrable (fun u : ℝ =>
      f (((m1 : ℝ) * u + (j : ℝ)) / (m2 : ℝ)) ^ 2) := by
  have hm1R : (m1 : ℝ) ≠ 0 := by exact_mod_cast hm1
  have hm2R : (m2 : ℝ) ≠ 0 := by exact_mod_cast hm2
  have ha : (m1 : ℝ) / (m2 : ℝ) ≠ 0 := div_ne_zero hm1R hm2R
  have h := (hf2.comp_add_left ((j : ℝ) / (m2 : ℝ))).comp_mul_left' ha
  convert h using 1
  funext u
  congr 2
  field_simp [hm2R]
  ring

/-- The square of the complete finite affine sum is integrable for a
continuous `L²` profile.  This discharges the `ha2` premise in the canonical
Lemma 9.2 energy producer. -/
theorem integrable_sq_sourceFiniteAffineSum
    (m1Range m2Range jRange : Finset ℤ) (f : ℝ → ℝ)
    (hfCont : Continuous f)
    (hf2 : Integrable (fun x : ℝ => f x ^ 2))
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0) :
    Integrable (fun u : ℝ =>
      sourceFiniteAffineSum m1Range m2Range jRange f u ^ 2) := by
  let ranges : Finset (ℤ × (ℤ × ℤ)) :=
    m1Range ×ˢ (m2Range ×ˢ jRange)
  let G : (ℤ × (ℤ × ℤ)) → ℝ → ℝ := fun p u =>
    f (((p.1 : ℝ) * u + (p.2.2 : ℝ)) / (p.2.1 : ℝ)) ^ 2
  have hG : ∀ p ∈ ranges, Integrable (G p) := by
    intro p hp
    have hp' := Finset.mem_product.mp hp
    have hp'' := Finset.mem_product.mp hp'.2
    exact integrable_sq_affine_ratio f hf2
      (hm1 p.1 hp'.1) (hm2 p.2.1 hp''.1)
  have hmajor : Integrable (fun u : ℝ =>
      ((m1Range.card * m2Range.card * jRange.card : ℕ) : ℝ) *
        ∑ p ∈ ranges, G p u) :=
    (integrable_finsetSum ranges hG).const_mul _
  apply hmajor.mono'
    ((continuous_sourceFiniteAffineSum m1Range m2Range jRange f hfCont).pow 2).aestronglyMeasurable
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa only [ranges, G] using
    sourceFiniteAffineSum_sq_le m1Range m2Range jRange f u

/-- Crude finite-branch energy bound.  The ratio factor is still exact; dyadic
range bounds can replace it by an absolute constant in the source application. -/
theorem sourceFiniteAffineEnergy_crude
    (m1Range m2Range jRange : Finset ℤ) (f : ℝ → ℝ)
    (hf2 : Integrable (fun x : ℝ => f x ^ 2))
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0) :
    sourceFiniteAffineEnergy m1Range m2Range jRange f ≤
      ((m1Range.card * m2Range.card * jRange.card : ℕ) : ℝ) *
        ∑ p ∈ m1Range ×ˢ (m2Range ×ˢ jRange),
          |(p.2.1 : ℝ) / (p.1 : ℝ)| * ∫ x : ℝ, f x ^ 2 := by
  unfold sourceFiniteAffineEnergy
  let ranges : Finset (ℤ × (ℤ × ℤ)) :=
    m1Range ×ˢ (m2Range ×ˢ jRange)
  let G : (ℤ × (ℤ × ℤ)) → ℝ → ℝ := fun p u =>
    f (((p.1 : ℝ) * u + (p.2.2 : ℝ)) / (p.2.1 : ℝ)) ^ 2
  have hG : ∀ p ∈ ranges, Integrable (G p) := by
    intro p hp
    have hp' := Finset.mem_product.mp hp
    have hp'' := Finset.mem_product.mp hp'.2
    exact integrable_sq_affine_ratio f hf2
      (hm1 p.1 hp'.1) (hm2 p.2.1 hp''.1)
  have hsum : Integrable (fun u : ℝ =>
      ((m1Range.card * m2Range.card * jRange.card : ℕ) : ℝ) *
        ∑ p ∈ ranges, G p u) :=
    (integrable_finsetSum ranges hG).const_mul _
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun u => sq_nonneg _)
    hsum
    (Filter.Eventually.of_forall fun u => by
      simpa only [ranges, G] using
        sourceFiniteAffineSum_sq_le m1Range m2Range jRange f u)
  calc
    (∫ u : ℝ, sourceFiniteAffineSum m1Range m2Range jRange f u ^ 2) ≤
        ∫ u : ℝ,
          ((m1Range.card * m2Range.card * jRange.card : ℕ) : ℝ) *
            ∑ p ∈ ranges, G p u := hmono
    _ = ((m1Range.card * m2Range.card * jRange.card : ℕ) : ℝ) *
        ∑ p ∈ ranges, ∫ u : ℝ, G p u := by
      rw [integral_const_mul, integral_finsetSum ranges hG]
    _ = ((m1Range.card * m2Range.card * jRange.card : ℕ) : ℝ) *
        ∑ p ∈ m1Range ×ˢ (m2Range ×ˢ jRange),
          |(p.2.1 : ℝ) / (p.1 : ℝ)| * ∫ x : ℝ, f x ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      have hp' := Finset.mem_product.mp hp
      have hp'' := Finset.mem_product.mp hp'.2
      exact integral_sq_affine_ratio f (hm1 p.1 hp'.1)
        (hm2 p.2.1 hp''.1)

/-- Cardinality form of the crude estimate. -/
theorem sourceFiniteAffineEnergy_crude_card
    (m1Range m2Range jRange : Finset ℤ) (f : ℝ → ℝ)
    (hf2 : Integrable (fun x : ℝ => f x ^ 2))
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hratio : ∀ m1 ∈ m1Range, ∀ m2 ∈ m2Range,
      |(m2 : ℝ) / (m1 : ℝ)| ≤ C) :
    sourceFiniteAffineEnergy m1Range m2Range jRange f ≤
      (((m1Range.card * m2Range.card * jRange.card : ℕ) : ℝ) ^ 2) *
        C * ∫ x : ℝ, f x ^ 2 := by
  let K : ℝ := ((m1Range.card * m2Range.card * jRange.card : ℕ) : ℝ)
  let I : ℝ := ∫ x : ℝ, f x ^ 2
  have hI0 : 0 ≤ I := integral_nonneg fun x => sq_nonneg (f x)
  have hsum :
      (∑ p ∈ m1Range ×ˢ (m2Range ×ˢ jRange),
          |(p.2.1 : ℝ) / (p.1 : ℝ)| * I) ≤ K * (C * I) := by
    calc
      (∑ p ∈ m1Range ×ˢ (m2Range ×ˢ jRange),
          |(p.2.1 : ℝ) / (p.1 : ℝ)| * I) ≤
          ∑ _p ∈ m1Range ×ˢ (m2Range ×ˢ jRange), C * I := by
        gcongr with p hp
        have hp' := Finset.mem_product.mp hp
        have hp'' := Finset.mem_product.mp hp'.2
        exact hratio p.1 hp'.1 p.2.1 hp''.1
      _ = K * (C * I) := by
        simp only [Finset.sum_const, Finset.card_product, nsmul_eq_mul,
          Nat.cast_mul, K]
        ring
  have hbase := sourceFiniteAffineEnergy_crude m1Range m2Range jRange f
    hf2 hm1 hm2
  calc
    sourceFiniteAffineEnergy m1Range m2Range jRange f ≤
        K * ∑ p ∈ m1Range ×ˢ (m2Range ×ˢ jRange),
          |(p.2.1 : ℝ) / (p.1 : ℝ)| * I := by
      simpa only [K, I] using hbase
    _ ≤ K * (K * (C * I)) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = K ^ 2 * C * I := by ring
    _ = (((m1Range.card * m2Range.card * jRange.card : ℕ) : ℝ) ^ 2) *
        C * ∫ x : ℝ, f x ^ 2 := rfl

/-- The literal `M^6 * ||f||_2^2` scaling in the crude base case. -/
theorem sourceFiniteAffineEnergy_crude_M_six
    (m1Range m2Range jRange : Finset ℤ) (f : ℝ → ℝ)
    (hf2 : Integrable (fun x : ℝ => f x ^ 2))
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0)
    {M C : ℝ} (hM0 : 0 ≤ M) (hC0 : 0 ≤ C)
    (hcard1 : (m1Range.card : ℝ) ≤ M)
    (hcard2 : (m2Range.card : ℝ) ≤ M)
    (hcard3 : (jRange.card : ℝ) ≤ M)
    (hratio : ∀ m1 ∈ m1Range, ∀ m2 ∈ m2Range,
      |(m2 : ℝ) / (m1 : ℝ)| ≤ C) :
    sourceFiniteAffineEnergy m1Range m2Range jRange f ≤
      M ^ 6 * C * ∫ x : ℝ, f x ^ 2 := by
  have hbase := sourceFiniteAffineEnergy_crude_card m1Range m2Range jRange f
    hf2 hm1 hm2 hC0 hratio
  have hK : ((m1Range.card * m2Range.card * jRange.card : ℕ) : ℝ) ≤
      M ^ 3 := by
    push_cast
    have hc1 : 0 ≤ (m1Range.card : ℝ) := by positivity
    have hc2 : 0 ≤ (m2Range.card : ℝ) := by positivity
    have hc3 : 0 ≤ (jRange.card : ℝ) := by positivity
    calc
      (m1Range.card : ℝ) * (m2Range.card : ℝ) * (jRange.card : ℝ) ≤
          (M * M) * (jRange.card : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hcard1 hcard2 hc2 hM0) hc3
      _ ≤ (M * M) * M :=
        mul_le_mul_of_nonneg_left hcard3 (mul_nonneg hM0 hM0)
      _ = M ^ 3 := by ring
  have hK0 : 0 ≤ ((m1Range.card * m2Range.card * jRange.card : ℕ) : ℝ) :=
    by positivity
  have hKsq :
      (((m1Range.card * m2Range.card * jRange.card : ℕ) : ℝ) ^ 2) ≤
        M ^ 6 := by
    calc
      (((m1Range.card * m2Range.card * jRange.card : ℕ) : ℝ) ^ 2) ≤
          (M ^ 3) ^ 2 := pow_le_pow_left₀ hK0 hK 2
      _ = M ^ 6 := by ring
  have hI0 : 0 ≤ ∫ x : ℝ, f x ^ 2 :=
    integral_nonneg fun x => sq_nonneg (f x)
  exact hbase.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hKsq hC0) hI0)

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.sourceFiniteAffineSum_eq_product
#print axioms GuthMaynardJIteration.continuous_sourceFiniteAffineSum
#print axioms GuthMaynardJIteration.sourceFiniteAffineSum_sq_le
#print axioms GuthMaynardJIteration.integral_sq_affine_ratio
#print axioms GuthMaynardJIteration.integrable_sq_affine_ratio
#print axioms GuthMaynardJIteration.integrable_sq_sourceFiniteAffineSum
#print axioms GuthMaynardJIteration.sourceFiniteAffineEnergy_crude
#print axioms GuthMaynardJIteration.sourceFiniteAffineEnergy_crude_card
#print axioms GuthMaynardJIteration.sourceFiniteAffineEnergy_crude_M_six
