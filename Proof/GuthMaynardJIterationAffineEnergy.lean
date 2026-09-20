import GuthMaynardJIterationMediumWindowCount

open scoped BigOperators Real
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-! Literal finite `J` branch and whole-line Cauchy step from TeX 1651--1657. -/

def sourceFiniteAffineSum
    (m1Range m2Range jRange : Finset ℤ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑ m1 ∈ m1Range, ∑ m2 ∈ m2Range, ∑ j ∈ jRange,
    f (((m1 : ℝ) * u + (j : ℝ)) / (m2 : ℝ))

def sourceFiniteAffineEnergy
    (m1Range m2Range jRange : Finset ℤ) (f : ℝ → ℝ) : ℝ :=
  ∫ u : ℝ, (sourceFiniteAffineSum m1Range m2Range jRange f u) ^ 2

def sourceAffineJ
    (configs : Set (Finset ℤ × Finset ℤ × Finset ℤ))
    (f : ℝ → ℝ) : ℝ :=
  sSup {x : ℝ | ∃ c ∈ configs,
    x = sourceFiniteAffineEnergy c.1 c.2.1 c.2.2 f}

/-- A literal admissible finite affine branch is bounded by `J`, once the
set of branch energies is known bounded above. -/
theorem sourceFiniteAffineEnergy_le_sourceAffineJ
    (configs : Set (Finset ℤ × Finset ℤ × Finset ℤ))
    (f : ℝ → ℝ)
    (hbounded : BddAbove {x : ℝ | ∃ c ∈ configs,
      x = sourceFiniteAffineEnergy c.1 c.2.1 c.2.2 f})
    {m1Range m2Range jRange : Finset ℤ}
    (hconfig : (m1Range, m2Range, jRange) ∈ configs) :
    sourceFiniteAffineEnergy m1Range m2Range jRange f ≤
      sourceAffineJ configs f := by
  unfold sourceAffineJ
  apply le_csSup hbounded
  exact ⟨(m1Range, m2Range, jRange), hconfig, rfl⟩

/-- The support-driven finite `j` restriction at TeX 1657. -/
theorem sourceAffineTsum_eq_finite
    (m1Range m2Range jRange : Finset ℤ) (f : ℝ → ℝ) (u : ℝ)
    (hcover : ∀ m1 ∈ m1Range, ∀ m2 ∈ m2Range, ∀ j : ℤ,
      f (((m1 : ℝ) * u + (j : ℝ)) / (m2 : ℝ)) ≠ 0 → j ∈ jRange) :
    (∑ m1 ∈ m1Range, ∑ m2 ∈ m2Range, ∑' j : ℤ,
      f (((m1 : ℝ) * u + (j : ℝ)) / (m2 : ℝ))) =
      sourceFiniteAffineSum m1Range m2Range jRange f u := by
  unfold sourceFiniteAffineSum
  apply Finset.sum_congr rfl
  intro m1 hm1
  apply Finset.sum_congr rfl
  intro m2 hm2
  apply tsum_eq_sum
  intro j hj
  by_contra hnonzero
  exact hj (hcover m1 hm1 m2 hm2 j hnonzero)

theorem mem_sourceIntegerWindow_zero_of_abs_le
    {j : ℤ} {J : ℝ} (hj : |(j : ℝ)| ≤ J) :
    j ∈ sourceIntegerWindow 0 J := by
  unfold sourceIntegerWindow
  rw [Finset.mem_Icc]
  have hjbounds := abs_le.mp hj
  constructor
  · have hreal : (((⌊-J⌋ : ℤ) : ℝ)) ≤ (j : ℝ) :=
      (Int.floor_le (-J)).trans hjbounds.1
    simpa only [zero_sub] using (by exact_mod_cast hreal)
  · have hreal : (j : ℝ) ≤ (((⌈J⌉ : ℤ) : ℝ)) :=
      hjbounds.2.trans (Int.le_ceil J)
    simpa only [zero_add] using (by exact_mod_cast hreal)

/-- Literal support calculation behind `j ≪ M2` at TeX 1657. -/
theorem sourceAffineSupport_implies_j_mem_window
    (f : ℝ → ℝ) {U F Mhi u : ℝ}
    (hMhi : 0 ≤ Mhi)
    (hu : |u| ≤ U)
    {m1 m2 j : ℤ} (hm2 : m2 ≠ 0)
    (hm1hi : |(m1 : ℝ)| ≤ Mhi) (hm2hi : |(m2 : ℝ)| ≤ Mhi)
    (hsupport : ∀ x, f x ≠ 0 → |x| ≤ F)
    (hnonzero : f (((m1 : ℝ) * u + (j : ℝ)) / (m2 : ℝ)) ≠ 0) :
    j ∈ sourceIntegerWindow 0 (Mhi * (F + U)) := by
  let x : ℝ := ((m1 : ℝ) * u + (j : ℝ)) / (m2 : ℝ)
  have hm2R : (m2 : ℝ) ≠ 0 := by exact_mod_cast hm2
  have hx : |x| ≤ F := hsupport x hnonzero
  have hjEq : (j : ℝ) = (m2 : ℝ) * x - (m1 : ℝ) * u := by
    dsimp only [x]
    field_simp [hm2R]
    ring
  apply mem_sourceIntegerWindow_zero_of_abs_le
  rw [hjEq]
  calc
    |(m2 : ℝ) * x - (m1 : ℝ) * u| ≤
        |(m2 : ℝ) * x| + |(m1 : ℝ) * u| := abs_sub _ _
    _ = |(m2 : ℝ)| * |x| + |(m1 : ℝ)| * |u| := by
      rw [abs_mul, abs_mul]
    _ ≤ Mhi * F + Mhi * U := by
      exact add_le_add
        (mul_le_mul hm2hi hx (abs_nonneg _) hMhi)
        (mul_le_mul hm1hi hu (abs_nonneg _) hMhi)
    _ = Mhi * (F + U) := by ring

/-- Whole-line nonnegative Cauchy--Schwarz in the exact squared form of
equation (9.12). -/
theorem integral_mul_sq_le
    (f g : ℝ → ℝ)
    (hfmeas : AEStronglyMeasurable f)
    (hgmeas : AEStronglyMeasurable g)
    (hf2 : Integrable (fun u => f u ^ 2))
    (hg2 : Integrable (fun u => g u ^ 2))
    (hf0 : ∀ u, 0 ≤ f u) (hg0 : ∀ u, 0 ≤ g u) :
    (∫ u : ℝ, f u * g u) ^ 2 ≤
      (∫ u : ℝ, f u ^ 2) * (∫ u : ℝ, g u ^ 2) := by
  have hfm : MemLp f 2 volume := by
    apply (memLp_two_iff_integrable_sq hfmeas).2
    exact hf2
  have hgm : MemLp g 2 volume := by
    apply (memLp_two_iff_integrable_sq hgmeas).2
    exact hg2
  have hpq : Real.HolderConjugate 2 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) hpq
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0)
    (by simpa using hfm) (by simpa using hgm)
  simp only [Real.rpow_two, one_div] at hh
  have hrpow (x : ℝ) : x ^ (2 : ℝ)⁻¹ = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    norm_num
  rw [hrpow, hrpow] at hh
  have hI : 0 ≤ ∫ u : ℝ, f u * g u :=
    integral_nonneg fun u => mul_nonneg (hf0 u) (hg0 u)
  have hA : 0 ≤ ∫ u : ℝ, f u ^ 2 :=
    integral_nonneg fun u => sq_nonneg _
  have hB : 0 ≤ ∫ u : ℝ, g u ^ 2 :=
    integral_nonneg fun u => sq_nonneg _
  nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB,
    sq_nonneg (Real.sqrt (∫ u : ℝ, f u ^ 2) -
      Real.sqrt (∫ u : ℝ, g u ^ 2))]

/-- Exact finite form of the second square bracket in TeX 1654: after the
support-driven `j` restriction, it is the selected branch of `J`. -/
theorem sourceAffinePairIntegral_sq_le_sourceAffineJ
    (mRange jRange : Finset ℤ) (f ftilde : ℝ → ℝ)
    (configs : Set (Finset ℤ × Finset ℤ × Finset ℤ))
    (hconfig : (mRange, mRange, jRange) ∈ configs)
    (hbounded : BddAbove {x : ℝ | ∃ c ∈ configs,
      x = sourceFiniteAffineEnergy c.1 c.2.1 c.2.2 ftilde})
    (hcover : ∀ u, f u ≠ 0 → ∀ m1 ∈ mRange, ∀ m2 ∈ mRange, ∀ j : ℤ,
      ftilde (((m1 : ℝ) * u + (j : ℝ)) / (m2 : ℝ)) ≠ 0 → j ∈ jRange)
    (hfmeas : AEStronglyMeasurable f)
    (hameas : AEStronglyMeasurable
      (sourceFiniteAffineSum mRange mRange jRange ftilde))
    (hf2 : Integrable (fun u => f u ^ 2))
    (ha2 : Integrable (fun u =>
      (sourceFiniteAffineSum mRange mRange jRange ftilde u) ^ 2))
    (hf0 : ∀ u, 0 ≤ f u) (hftilde0 : ∀ u, 0 ≤ ftilde u) :
    (∫ u : ℝ, f u *
      (∑ m1 ∈ mRange, ∑ m2 ∈ mRange, ∑' j : ℤ,
        ftilde (((m1 : ℝ) * u + (j : ℝ)) / (m2 : ℝ)))) ^ 2 ≤
      (∫ u : ℝ, f u ^ 2) * sourceAffineJ configs ftilde := by
  let A : ℝ → ℝ := sourceFiniteAffineSum mRange mRange jRange ftilde
  have hweightedEq : ∀ u, f u *
      (∑ m1 ∈ mRange, ∑ m2 ∈ mRange, ∑' j : ℤ,
        ftilde (((m1 : ℝ) * u + (j : ℝ)) / (m2 : ℝ))) = f u * A u := by
    intro u
    by_cases hfu : f u = 0
    · simp [hfu]
    · rw [sourceAffineTsum_eq_finite mRange mRange jRange ftilde u
        (hcover u hfu)]
  have hA0 : ∀ u, 0 ≤ A u := by
    intro u
    unfold A sourceFiniteAffineSum
    apply Finset.sum_nonneg
    intro m1 hm1
    apply Finset.sum_nonneg
    intro m2 hm2
    apply Finset.sum_nonneg
    intro j hj
    exact hftilde0 _
  calc
    (∫ u : ℝ, f u *
        (∑ m1 ∈ mRange, ∑ m2 ∈ mRange, ∑' j : ℤ,
          ftilde (((m1 : ℝ) * u + (j : ℝ)) / (m2 : ℝ)))) ^ 2 =
      (∫ u : ℝ, f u * A u) ^ 2 := by
        congr 2
        funext u
        exact hweightedEq u
    _ ≤ (∫ u : ℝ, f u ^ 2) *
        sourceFiniteAffineEnergy mRange mRange jRange ftilde := by
      exact integral_mul_sq_le f A hfmeas hameas hf2 ha2 hf0 hA0
    _ ≤ (∫ u : ℝ, f u ^ 2) * sourceAffineJ configs ftilde := by
      apply mul_le_mul_of_nonneg_left
        (sourceFiniteAffineEnergy_le_sourceAffineJ configs ftilde
          hbounded hconfig)
      exact integral_nonneg fun u => sq_nonneg _

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.sourceFiniteAffineEnergy_le_sourceAffineJ
#print axioms GuthMaynardJIteration.sourceAffineTsum_eq_finite
#print axioms GuthMaynardJIteration.sourceAffineSupport_implies_j_mem_window
#print axioms GuthMaynardJIteration.integral_mul_sq_le
#print axioms GuthMaynardJIteration.sourceAffinePairIntegral_sq_le_sourceAffineJ
