import GuthMaynardLemma62CentralTailBounds

/-!
# Finite `m` factorization in Guth--Maynard Lemma 6.2

After the common `v=Nmu` substitution, every dependence on positive `m` is
the unit coefficient phase `m^{-i(t-r)}`.  This file performs the finite sum
and integral interchange exactly, producing the reflected Dirichlet
polynomial used in Section 6.
-/

namespace GuthMaynardLemma62FiniteFactorization

open Real Complex Set MeasureTheory
open scoped FourierTransform SchwartzMap BigOperators
open GuthMaynardSectionThreeCutoff
open GuthMaynardSectionThreeCutoffDerivativeBudget
open GuthMaynardLemma62FarTail
open GuthMaynardLemma62ReflectionSubstitution
open GuthMaynardLemma62CentralTailBounds
open GuthMaynardLemma62AbsoluteMellinTail
open GuthMaynardReflectionKernelVdC
open MAPMRTCorollary53Source

noncomputable section

def reflectedDirichletPolynomial (L : ℕ) (tau : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 L, reflectionScalePhase tau (m : ℝ)

def factorizedReflectedOuter (t N : ℝ) (L : ℕ) (r : ℝ) : ℂ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I) *
      reflectionScalePhase (t - r) N *
      reflectedDirichletPolynomial L (t - r)) *
    reflectedInner (t - r) N (L : ℝ)

theorem reflectionScalePhase_mul
    {tau a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    reflectionScalePhase tau (a * b) =
      reflectionScalePhase tau a * reflectionScalePhase tau b := by
  unfold reflectionScalePhase
  rw [Real.log_mul ha.ne' hb.ne']
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem sum_reflectionScalePhase_mul
    {tau N : ℝ} (hN : 0 < N) (L : ℕ) :
    (∑ m ∈ Finset.Icc 1 L,
        reflectionScalePhase tau ((m : ℝ) * N)) =
      reflectionScalePhase tau N * reflectedDirichletPolynomial L tau := by
  unfold reflectedDirichletPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmIcc := Finset.mem_Icc.mp hm
  have hmPos : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hmIcc.1)
  rw [reflectionScalePhase_mul hmPos hN]
  ring

/-- Exact positive-frequency finite factorization. -/
theorem finite_positive_coefficients_eq_reflectedPolynomial
    {t N : ℝ} (hN : 0 < N) (L : ℕ) (hL : 1 ≤ L) :
    (∑ m ∈ Finset.Icc 1 L,
        sectionThreeFourierCoefficient t ((m : ℝ) * N)) =
      ∫ r : ℝ,
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I) *
            reflectionScalePhase (t - r) N *
            reflectedDirichletPolynomial L (t - r)) *
          reflectedInner (t - r) N (L : ℝ) := by
  calc
    (∑ m ∈ Finset.Icc 1 L,
        sectionThreeFourierCoefficient t ((m : ℝ) * N)) =
      ∑ m ∈ Finset.Icc 1 L,
        ∫ r : ℝ,
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
              mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I) *
              reflectionScalePhase (t - r) ((m : ℝ) * N)) *
            reflectedInner (t - r) N (L : ℝ) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmIcc := Finset.mem_Icc.mp hm
      have hmOne : 1 ≤ (m : ℝ) := by exact_mod_cast hmIcc.1
      have hmL : (m : ℝ) ≤ L := by exact_mod_cast hmIcc.2
      simpa [reflectedInner] using
        (sectionThreeFourierCoefficient_eq_positiveReflectedMellin
          (t := t) hN hmOne hmL)
    _ = ∫ r : ℝ,
        ∑ m ∈ Finset.Icc 1 L,
          ((((1 / (2 * Real.pi) : ℝ) : ℂ) *
              mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I) *
              reflectionScalePhase (t - r) ((m : ℝ) * N)) *
            reflectedInner (t - r) N (L : ℝ)) := by
      rw [integral_finset_sum]
      intro m hm
      have hmIcc := Finset.mem_Icc.mp hm
      have hmOne : 1 ≤ (m : ℝ) := by exact_mod_cast hmIcc.1
      have hmL : (m : ℝ) ≤ L := by exact_mod_cast hmIcc.2
      simpa [reflectedInner] using
        (integrable_positiveReflectedMellin
          (t := t) hN hmOne hmL)
    _ = _ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with r
      rw [← Finset.sum_mul]
      rw [show
          (∑ m ∈ Finset.Icc 1 L,
            (((1 / (2 * Real.pi) : ℝ) : ℂ) *
              mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I) *
              reflectionScalePhase (t - r) ((m : ℝ) * N))) =
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)) *
            (∑ m ∈ Finset.Icc 1 L,
              reflectionScalePhase (t - r) ((m : ℝ) * N)) by
            rw [← Finset.mul_sum]]
      rw [sum_reflectionScalePhase_mul hN]
      ring

/-- The negative frequencies are retained as the conjugate finite reflected
polynomial at `-t`, rather than silently doubled or discarded. -/
theorem finite_negative_coefficients_eq_conj_reflectedPolynomial
    {t N : ℝ} (hN : 0 < N) (L : ℕ) (hL : 1 ≤ L) :
    (∑ m ∈ Finset.Icc 1 L,
        sectionThreeFourierCoefficient t (-((m : ℝ) * N))) =
      starRingEnd ℂ
        (∫ r : ℝ,
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
              mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I) *
              reflectionScalePhase (-t - r) N *
              reflectedDirichletPolynomial L (-t - r)) *
            reflectedInner (-t - r) N (L : ℝ)) := by
  calc
    (∑ m ∈ Finset.Icc 1 L,
        sectionThreeFourierCoefficient t (-((m : ℝ) * N))) =
      ∑ m ∈ Finset.Icc 1 L,
        starRingEnd ℂ
          (sectionThreeFourierCoefficient (-t) ((m : ℝ) * N)) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact sectionThreeFourierCoefficient_neg_eq_conj t ((m : ℝ) * N)
    _ = starRingEnd ℂ
        (∑ m ∈ Finset.Icc 1 L,
          sectionThreeFourierCoefficient (-t) ((m : ℝ) * N)) := by
      rw [map_sum]
    _ = _ := by
      rw [finite_positive_coefficients_eq_reflectedPolynomial hN L hL]

theorem norm_reflectedDirichletPolynomial_le
    (L : ℕ) (tau : ℝ) :
    ‖reflectedDirichletPolynomial L tau‖ ≤ L := by
  unfold reflectedDirichletPolynomial
  calc
    ‖∑ m ∈ Finset.Icc 1 L, reflectionScalePhase tau (m : ℝ)‖ ≤
      ∑ m ∈ Finset.Icc 1 L,
        ‖reflectionScalePhase tau (m : ℝ)‖ := norm_sum_le _ _
    _ = ∑ _m ∈ Finset.Icc 1 L, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [norm_reflectionScalePhase]
    _ = L := by simp

theorem continuous_reflectedDirichletPolynomial
    (L : ℕ) (t : ℝ) :
    Continuous (fun r : ℝ => reflectedDirichletPolynomial L (t - r)) := by
  unfold reflectedDirichletPolynomial reflectionScalePhase
  apply continuous_finset_sum
  intro m hm
  fun_prop

theorem integrable_factorizedReflectedOuter
    {t N : ℝ} (hN : 0 < N) (L : ℕ) (hL : 1 ≤ L) :
    Integrable (factorizedReflectedOuter t N L) := by
  have hsum : Integrable (fun r : ℝ =>
      ∑ m ∈ Finset.Icc 1 L,
        positiveReflectedOuterAtScale t N (L : ℝ) ((m : ℝ) * N) r) := by
    apply integrable_finset_sum
    intro m hm
    have hmIcc := Finset.mem_Icc.mp hm
    have hmOne : 1 ≤ (m : ℝ) := by exact_mod_cast hmIcc.1
    have hmL : (m : ℝ) ≤ L := by exact_mod_cast hmIcc.2
    exact integrable_positiveReflectedOuterAtScale_source hN hmOne hmL
  apply hsum.congr
  filter_upwards with r
  unfold factorizedReflectedOuter positiveReflectedOuterAtScale
  rw [← Finset.sum_mul]
  rw [show
      (∑ m ∈ Finset.Icc 1 L,
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I) *
          reflectionScalePhase (t - r) ((m : ℝ) * N))) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)) *
        (∑ m ∈ Finset.Icc 1 L,
          reflectionScalePhase (t - r) ((m : ℝ) * N)) by
        rw [← Finset.mul_sum]]
  rw [sum_reflectionScalePhase_mul hN]
  ring

theorem norm_factorizedReflectedOuter_central_le
    {t N R r : ℝ} (hN : 0 < N) (hR : 0 < R) (htR : R < t)
    (hr : r ∈ Set.Ioc (-R) R) (J : ℕ) :
    ‖factorizedReflectedOuter t N (2 ^ J) r‖ ≤
      ((1 / (2 * Real.pi)) *
        ((J + 1) * (20 * Real.sqrt (8 * Real.pi) /
          Real.sqrt (t - R)))) *
        (‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖ *
          ‖reflectedDirichletPolynomial (2 ^ J) (t - r)‖) := by
  have hbase := norm_positiveReflectedOuterAtScale_central_le
    (t := t) (c := N) hN hR htR hr J
  have hbase' :
      ‖positiveReflectedOuterAtScale t N ((2 ^ J : ℕ) : ℝ) N r‖ ≤
        ((1 / (2 * Real.pi)) *
          ((J + 1) * (20 * Real.sqrt (8 * Real.pi) /
            Real.sqrt (t - R)))) *
          ‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖ := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hbase
  have hfac :
      ‖factorizedReflectedOuter t N (2 ^ J) r‖ =
        ‖positiveReflectedOuterAtScale
            t N ((2 ^ J : ℕ) : ℝ) N r‖ *
          ‖reflectedDirichletPolynomial (2 ^ J) (t - r)‖ := by
    unfold factorizedReflectedOuter positiveReflectedOuterAtScale
    repeat' rw [norm_mul]
    ring
  rw [hfac]
  calc
    ‖positiveReflectedOuterAtScale
          t N ((2 ^ J : ℕ) : ℝ) N r‖ *
        ‖reflectedDirichletPolynomial (2 ^ J) (t - r)‖ ≤
      (((1 / (2 * Real.pi)) *
          ((J + 1) * (20 * Real.sqrt (8 * Real.pi) /
            Real.sqrt (t - R)))) *
          ‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖) *
        ‖reflectedDirichletPolynomial (2 ^ J) (t - r)‖ :=
      mul_le_mul_of_nonneg_right hbase' (norm_nonneg _)
    _ = _ := by ring

/-- The central reflected integral retains the complete unit-coefficient
Dirichlet polynomial.  This is the exact form needed before the Section 6
large-value estimate is applied. -/
theorem norm_integral_factorizedReflectedOuter_central_le
    {t N R : ℝ} (hN : 0 < N) (hR : 0 < R) (htR : R < t)
    (J : ℕ) :
    ‖∫ r : ℝ in Set.Ioc (-R) R,
        factorizedReflectedOuter t N (2 ^ J) r‖ ≤
      ∫ r : ℝ in Set.Ioc (-R) R,
        ((1 / (2 * Real.pi)) *
          ((J + 1) * (20 * Real.sqrt (8 * Real.pi) /
            Real.sqrt (t - R)))) *
          (‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖ *
            ‖reflectedDirichletPolynomial (2 ^ J) (t - r)‖) := by
  let B : ℝ :=
    (1 / (2 * Real.pi)) *
      ((J + 1) * (20 * Real.sqrt (8 * Real.pi) /
        Real.sqrt (t - R)))
  let g : ℝ → ℝ := fun r =>
    B * (‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖ *
      ‖reflectedDirichletPolynomial (2 ^ J) (t - r)‖)
  have hgContinuous : Continuous g := by
    dsimp only [g, B]
    exact continuous_const.mul
      (GuthMaynardLemma62Fubini.continuous_mellin_line_sectionThree.norm.mul
        (continuous_reflectedDirichletPolynomial (2 ^ J) t).norm)
  have hgIcc : IntegrableOn g (Set.Icc (-R) R) :=
    hgContinuous.integrableOn_Icc
  have hg : IntegrableOn g (Set.Ioc (-R) R) :=
    hgIcc.mono_set Set.Ioc_subset_Icc_self
  apply MeasureTheory.norm_integral_le_of_norm_le hg
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with r hr
  exact norm_factorizedReflectedOuter_central_le hN hR htR hr J

theorem norm_factorizedReflectedOuter_le_log
    {t N r : ℝ} (hN : 0 < N) (L : ℕ) (hL : 1 ≤ L) :
    ‖factorizedReflectedOuter t N L r‖ ≤
      (1 / (2 * Real.pi)) * Real.log (2 * (L : ℝ)) * (L : ℝ) *
        ‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖ := by
  have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hbase := norm_positiveReflectedOuterAtScale_le_log
    (t := t) (c := N) (r := r) hN hLreal
  have hfac :
      ‖factorizedReflectedOuter t N L r‖ =
        ‖positiveReflectedOuterAtScale t N (L : ℝ) N r‖ *
          ‖reflectedDirichletPolynomial L (t - r)‖ := by
    unfold factorizedReflectedOuter positiveReflectedOuterAtScale
    repeat' rw [norm_mul]
    ring
  rw [hfac]
  calc
    ‖positiveReflectedOuterAtScale t N (L : ℝ) N r‖ *
        ‖reflectedDirichletPolynomial L (t - r)‖ ≤
      ((1 / (2 * Real.pi)) * Real.log (2 * (L : ℝ)) *
        ‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖) *
        ‖reflectedDirichletPolynomial L (t - r)‖ :=
      mul_le_mul_of_nonneg_right hbase (norm_nonneg _)
    _ ≤ ((1 / (2 * Real.pi)) * Real.log (2 * (L : ℝ)) *
        ‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖) *
        (L : ℝ) := by
      apply mul_le_mul_of_nonneg_left
        (norm_reflectedDirichletPolynomial_le L (t - r))
      have hlog : 0 ≤ Real.log (2 * (L : ℝ)) :=
        Real.log_nonneg (by linarith)
      positivity
    _ = _ := by ring

/-- Outside the central Mellin window only the crude logarithmic reflection
bound is used; the arbitrary-order absolute Mellin tail is kept explicit. -/
theorem norm_integral_factorizedReflectedOuter_exterior_le
    {t N R : ℝ} (hN : 0 < N) (hR : 0 < R)
    (L : ℕ) (hL : 1 ≤ L) (k : ℕ) (hk : 2 ≤ k) :
    ‖∫ r : ℝ in (Set.Iic (-R) ∪ Set.Ioi R),
        factorizedReflectedOuter t N L r‖ ≤
      ((1 / (2 * Real.pi)) * Real.log (2 * (L : ℝ)) * (L : ℝ)) *
        (2 * (((2 * Real.pi) ^ k * sectionThreeMellinSeminorm k) *
          (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)))) := by
  let C : ℝ :=
    (1 / (2 * Real.pi)) * Real.log (2 * (L : ℝ)) * (L : ℝ)
  have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hlog : 0 ≤ Real.log (2 * (L : ℝ)) :=
    Real.log_nonneg (by linarith)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hmajor : IntegrableOn (fun r : ℝ =>
      C * ‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖)
      (Set.Iic (-R) ∪ Set.Ioi R) :=
    GuthMaynardLemma62MellinInversion.sectionThreeCutoff_verticalIntegrable.norm.integrableOn.const_mul C
  have htail := integral_exterior_norm_sectionThreeMellin_le hk hR
  calc
    ‖∫ r : ℝ in (Set.Iic (-R) ∪ Set.Ioi R),
        factorizedReflectedOuter t N L r‖ ≤
      ∫ r : ℝ in (Set.Iic (-R) ∪ Set.Ioi R),
        C * ‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖ := by
      apply MeasureTheory.norm_integral_le_of_norm_le hmajor
      filter_upwards with r
      simpa only [C] using norm_factorizedReflectedOuter_le_log hN L hL
    _ = C * (∫ r : ℝ in (Set.Iic (-R) ∪ Set.Ioi R),
        ‖mellin sectionThreeCutoff ((1 : ℂ) + r * Complex.I)‖) := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ C * (2 * (((2 * Real.pi) ^ k * sectionThreeMellinSeminorm k) *
          (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)))) :=
      mul_le_mul_of_nonneg_left htail hC
    _ = _ := rfl

theorem finite_positive_coefficients_eq_central_add_exterior
    {t N R : ℝ} (hN : 0 < N) (hR : 0 < R)
    (L : ℕ) (hL : 1 ≤ L) :
    (∑ m ∈ Finset.Icc 1 L,
        sectionThreeFourierCoefficient t ((m : ℝ) * N)) =
      (∫ r : ℝ in Set.Ioc (-R) R,
        factorizedReflectedOuter t N L r) +
      (∫ r : ℝ in (Set.Iic (-R) ∪ Set.Ioi R),
        factorizedReflectedOuter t N L r) := by
  rw [finite_positive_coefficients_eq_reflectedPolynomial hN L hL]
  change (∫ r : ℝ, factorizedReflectedOuter t N L r) = _
  have hInt := integrable_factorizedReflectedOuter (t := t) hN L hL
  have hDisjoint : Disjoint (Set.Ioc (-R) R)
      (Set.Iic (-R) ∪ Set.Ioi R) := by
    rw [Set.disjoint_union_right]
    constructor <;> exact Set.disjoint_left.2 (by
      intro x hx hy
      simp only [Set.mem_Ioc, Set.mem_Iic, Set.mem_Ioi] at hx hy
      linarith)
  have hUnion : Set.Ioc (-R) R ∪ (Set.Iic (-R) ∪ Set.Ioi R) = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Iic, Set.mem_Ioi,
      Set.mem_univ, iff_true]
    by_cases hx : x ≤ -R
    · exact Or.inr (Or.inl hx)
    · have hx' : -R < x := lt_of_not_ge hx
      by_cases hxR : x ≤ R
      · exact Or.inl ⟨hx', hxR⟩
      · exact Or.inr (Or.inr (lt_of_not_ge hxR))
  rw [← MeasureTheory.setIntegral_univ, ← hUnion]
  exact MeasureTheory.setIntegral_union hDisjoint
    (measurableSet_Iic.union measurableSet_Ioi)
    hInt.integrableOn hInt.integrableOn

/-- Exact positive-frequency form of the Lemma 6.2 AFE: the only error is
the explicitly bounded exterior Mellin integral. -/
theorem norm_finite_positive_coefficients_sub_central_le
    {t N R : ℝ} (hN : 0 < N) (hR : 0 < R)
    (L : ℕ) (hL : 1 ≤ L) (k : ℕ) (hk : 2 ≤ k) :
    ‖(∑ m ∈ Finset.Icc 1 L,
        sectionThreeFourierCoefficient t ((m : ℝ) * N)) -
      (∫ r : ℝ in Set.Ioc (-R) R,
        factorizedReflectedOuter t N L r)‖ ≤
      ((1 / (2 * Real.pi)) * Real.log (2 * (L : ℝ)) * (L : ℝ)) *
        (2 * (((2 * Real.pi) ^ k * sectionThreeMellinSeminorm k) *
          (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)))) := by
  rw [finite_positive_coefficients_eq_central_add_exterior hN hR L hL]
  rw [add_sub_cancel_left]
  exact norm_integral_factorizedReflectedOuter_exterior_le
    hN hR L hL k hk

/-- The entire finite negative-frequency sector is nonstationary.  We retain
it as a separately quantified arbitrary-order Fourier-IBP error rather than
silently identifying it with the positive reflected main term. -/
theorem norm_finite_negative_coefficients_le
    (t : ℝ) {N : ℝ} (hN : 0 < N) (L : ℕ) (hL : 1 ≤ L)
    (j : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 L,
        sectionThreeFourierCoefficient t (-((m : ℝ) * N))‖ ≤
      (L : ℝ) *
        (lemma43DerivativeConstant j * (1 + |t|) ^ j *
          N ^ (-(j : ℝ))) := by
  let A : ℝ := lemma43DerivativeConstant j * (1 + |t|) ^ j *
    N ^ (-(j : ℝ))
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (mul_nonneg (lemma43DerivativeConstant_nonneg j) (by positivity))
      (Real.rpow_nonneg hN.le _)
  calc
    ‖∑ m ∈ Finset.Icc 1 L,
        sectionThreeFourierCoefficient t (-((m : ℝ) * N))‖ ≤
      ∑ m ∈ Finset.Icc 1 L,
        ‖sectionThreeFourierCoefficient t (-((m : ℝ) * N))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.Icc 1 L, A := by
      apply Finset.sum_le_sum
      intro m hm
      have hmPos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one
        (Finset.mem_Icc.mp hm).1
      have hmOne : (1 : ℝ) ≤ m := by
        exact_mod_cast (Finset.mem_Icc.mp hm).1
      have hterm := norm_sectionThreeFourierCoefficient_signed_nat_le
        t j m hN hmPos (-1) (by simp)
      have hpow : (m : ℝ) ^ (-(j : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hmOne
          (neg_nonpos.mpr (Nat.cast_nonneg j))
      have hterm' :
          ‖sectionThreeFourierCoefficient t (-((m : ℝ) * N))‖ ≤
            A * (m : ℝ) ^ (-(j : ℝ)) := by
        simpa only [neg_mul, one_mul, A] using hterm
      exact hterm'.trans (mul_le_of_le_one_right hA hpow)
    _ = (L : ℝ) * A := by simp
    _ = _ := rfl

/-- Source-faithful finite two-sided AFE.  The positive frequencies produce
the reflected Dirichlet-polynomial central integral; the negative frequencies
and exterior Mellin region remain as two explicit, independently shrinkable
errors. -/
theorem norm_finite_twoSided_coefficients_sub_central_le
    (t : ℝ) {N R : ℝ} (hN : 0 < N) (hR : 0 < R)
    (L : ℕ) (hL : 1 ≤ L) (k j : ℕ) (hk : 2 ≤ k) :
    ‖((∑ m ∈ Finset.Icc 1 L,
          sectionThreeFourierCoefficient t ((m : ℝ) * N)) +
        (∑ m ∈ Finset.Icc 1 L,
          sectionThreeFourierCoefficient t (-((m : ℝ) * N))) -
        (∫ r : ℝ in Set.Ioc (-R) R,
          factorizedReflectedOuter t N L r))‖ ≤
      ((1 / (2 * Real.pi)) * Real.log (2 * (L : ℝ)) * (L : ℝ)) *
          (2 * (((2 * Real.pi) ^ k * sectionThreeMellinSeminorm k) *
            (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)))) +
        (L : ℝ) *
          (lemma43DerivativeConstant j * (1 + |t|) ^ j *
            N ^ (-(j : ℝ))) := by
  let P : ℂ := ∑ m ∈ Finset.Icc 1 L,
    sectionThreeFourierCoefficient t ((m : ℝ) * N)
  let Q : ℂ := ∑ m ∈ Finset.Icc 1 L,
    sectionThreeFourierCoefficient t (-((m : ℝ) * N))
  let C : ℂ := ∫ r : ℝ in Set.Ioc (-R) R,
    factorizedReflectedOuter t N L r
  have hreassoc : P + Q - C = (P - C) + Q := by ring
  rw [show
      ((∑ m ∈ Finset.Icc 1 L,
          sectionThreeFourierCoefficient t ((m : ℝ) * N)) +
        (∑ m ∈ Finset.Icc 1 L,
          sectionThreeFourierCoefficient t (-((m : ℝ) * N))) -
        (∫ r : ℝ in Set.Ioc (-R) R,
          factorizedReflectedOuter t N L r)) = P + Q - C by rfl,
    hreassoc]
  exact (norm_add_le (P - C) Q).trans
    (add_le_add
      (norm_finite_positive_coefficients_sub_central_le hN hR L hL k hk)
      (norm_finite_negative_coefficients_le t hN L hL j))

end

end GuthMaynardLemma62FiniteFactorization

#print axioms GuthMaynardLemma62FiniteFactorization.reflectionScalePhase_mul
#print axioms GuthMaynardLemma62FiniteFactorization.finite_positive_coefficients_eq_reflectedPolynomial
#print axioms GuthMaynardLemma62FiniteFactorization.finite_negative_coefficients_eq_conj_reflectedPolynomial
#print axioms GuthMaynardLemma62FiniteFactorization.norm_integral_factorizedReflectedOuter_central_le
#print axioms GuthMaynardLemma62FiniteFactorization.norm_finite_positive_coefficients_sub_central_le
#print axioms GuthMaynardLemma62FiniteFactorization.norm_finite_twoSided_coefficients_sub_central_le
