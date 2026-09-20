import GuthMaynardJIterationMediumLocalizedPairs

open scoped BigOperators
open MeasureTheory

noncomputable section
namespace GuthMaynardS3ZeroEllSupport

open GuthMaynardJIteration

/-! Exact support bookkeeping for the zero-product fibre in the signed medium
localization.  The `m₁` sign is retained throughout; the only simplification
is the literal integer identity `m₁ * ell = 0`. -/

def sourceMediumZeroProductPairs
    (m1Range ellRange : Finset ℤ) (M3 B xi : ℝ) : Finset (ℤ × ℤ) :=
  (sourceMediumLocalizedPairs m1Range ellRange M3 B xi).filter
    (fun p => p.1 * p.2 = 0)

def sourceMediumNonzeroEllPairs
    (m1Range ellRange : Finset ℤ) (M3 B xi : ℝ) : Finset (ℤ × ℤ) :=
  (sourceMediumLocalizedPairs m1Range ellRange M3 B xi).filter
    (fun p => p.2 ≠ 0)

theorem mem_sourceMediumZeroProductPairs_iff
    {m1Range ellRange : Finset ℤ} {M3 B xi : ℝ} {p : ℤ × ℤ} :
    p ∈ sourceMediumZeroProductPairs m1Range ellRange M3 B xi ↔
      p ∈ sourceMediumLocalizedPairs m1Range ellRange M3 B xi ∧
        p.1 * p.2 = 0 := by
  simp [sourceMediumZeroProductPairs]

theorem zeroProduct_iff_ell_zero
    {m1Range ellRange : Finset ℤ} {M3 B xi : ℝ}
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0) {p : ℤ × ℤ}
    (hp : p ∈ sourceMediumLocalizedPairs m1Range ellRange M3 B xi) :
    p.1 * p.2 = 0 ↔ p.2 = 0 := by
  have hp1 : p.1 ≠ 0 := by
    exact hm1 p.1 (mem_sourceMediumLocalizedPairs_iff.mp hp).1
  constructor
  · intro hz
    exact (mul_eq_zero.mp hz).resolve_left hp1
  · intro h
    simp [h]

theorem zeroProduct_pair_abs_xi_lt
    {m1Range ellRange : Finset ℤ} {M1 M3 B xi : ℝ}
    (hM1 : 0 ≤ M1) (hM3 : 0 < M3) (hB : 0 ≤ B)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm1hi : ∀ m1 ∈ m1Range, |(m1 : ℝ)| ≤ 2 * M1)
    {p : ℤ × ℤ}
    (hp : p ∈ sourceMediumLocalizedPairs m1Range ellRange M3 B xi)
    (hz : p.1 * p.2 = 0) :
    |xi| < 2 * M1 * B / M3 := by
  have hmem := mem_sourceMediumLocalizedPairs_iff.mp hp
  have hlocal := hmem.2.2
  have hp2 : p.2 = 0 := by
    have hp1 : p.1 ≠ 0 := hm1 p.1 hmem.1
    exact (mul_eq_zero.mp hz).resolve_left hp1
  have hxi : |xi| < (|(p.1 : ℝ)| / M3) * B := by
    simpa [hp2] using hlocal
  have hm1bound : |(p.1 : ℝ)| / M3 ≤ (2 * M1) / M3 := by
    exact div_le_div_of_nonneg_right (hm1hi p.1 hmem.1) hM3.le
  calc
    |xi| < (|(p.1 : ℝ)| / M3) * B := hxi
    _ ≤ ((2 * M1) / M3) * B :=
      mul_le_mul_of_nonneg_right hm1bound hB
    _ = 2 * M1 * B / M3 := by ring

theorem zeroProduct_pair_mem_extra_band
    {m1Range ellRange : Finset ℤ} {M1 M3 B xi : ℝ}
    (hM1 : 0 ≤ M1) (hM3 : 0 < M3) (hB : 0 ≤ B)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm1hi : ∀ m1 ∈ m1Range, |(m1 : ℝ)| ≤ 2 * M1)
    {p : ℤ × ℤ}
    (hp : p ∈ sourceMediumZeroProductPairs m1Range ellRange M3 B xi) :
    |xi| < 2 * M1 * B / M3 := by
  exact zeroProduct_pair_abs_xi_lt hM1 hM3 hB hm1 hm1hi
    (mem_sourceMediumZeroProductPairs_iff.mp hp).1
    (mem_sourceMediumZeroProductPairs_iff.mp hp).2

def sourceMediumZeroEllSum
    (m1Range ellRange m2Range : Finset ℤ) (F fhat : ℝ → ℂ)
  (M3 B xi : ℝ) : ℂ :=
  ∑ p ∈ (sourceMediumLocalizedPairs m1Range ellRange M3 B xi).filter
      (fun p => p.2 = 0),
    sourceFirstPoissonLocalizedPairTerm m2Range F fhat M3 p xi

def sourceMediumNonzeroEllSum
    (m1Range ellRange m2Range : Finset ℤ) (F fhat : ℝ → ℂ)
  (M3 B xi : ℝ) : ℂ :=
  ∑ p ∈ (sourceMediumLocalizedPairs m1Range ellRange M3 B xi).filter
      (fun p => p.2 ≠ 0),
    sourceFirstPoissonLocalizedPairTerm m2Range F fhat M3 p xi

theorem sourceMediumZeroEllSum_eq_zero_of_outside_extra_band
    {m1Range ellRange m2Range : Finset ℤ} (F fhat : ℝ → ℂ)
    {M1 M3 B xi : ℝ} (hM1 : 0 ≤ M1) (hM3 : 0 < M3) (hB : 0 ≤ B)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm1hi : ∀ m1 ∈ m1Range, |(m1 : ℝ)| ≤ 2 * M1)
    (hxi : ¬ |xi| < 2 * M1 * B / M3) :
    sourceMediumZeroEllSum m1Range ellRange m2Range F fhat M3 B xi = 0 := by
  unfold sourceMediumZeroEllSum
  apply Finset.sum_eq_zero
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  exact (hxi (zeroProduct_pair_abs_xi_lt hM1 hM3 hB hm1 hm1hi hp'.1
    (by simp [hp'.2]))).elim

theorem sourceFirstPoissonLocalizedPairSum_eq_zeroEll_add_nonzeroEll
    (m1Range ellRange m2Range : Finset ℤ) (F fhat : ℝ → ℂ)
    (M3 B xi : ℝ) :
    sourceFirstPoissonLocalizedPairSum m1Range ellRange m2Range F fhat M3 B xi =
      sourceMediumZeroEllSum m1Range ellRange m2Range F fhat M3 B xi +
        sourceMediumNonzeroEllSum m1Range ellRange m2Range F fhat M3 B xi := by
  unfold sourceFirstPoissonLocalizedPairSum sourceMediumZeroEllSum
    sourceMediumNonzeroEllSum
  exact (Finset.sum_filter_add_sum_filter_not
    (sourceMediumLocalizedPairs m1Range ellRange M3 B xi)
    (fun p : ℤ × ℤ => p.2 = 0)
    (fun p => sourceFirstPoissonLocalizedPairTerm m2Range F fhat M3 p xi)).symm

theorem norm_sourceMediumZeroEllSum_le
    (m1Range ellRange m2Range : Finset ℤ) (F fhat : ℝ → ℂ)
    {M1 M2 M3 B Kpsi Slow xi : ℝ}
    (hM1 : 0 < M1) (hM3 : 0 ≤ M3) (hKpsi : 0 ≤ Kpsi)
    (hSlow : 0 ≤ Slow) (hcard1 : (m1Range.card : ℝ) ≤ 4 * M1)
    (hF : ∀ z, ‖F z‖ ≤ Kpsi)
    (hinner : ∀ p ∈ (sourceMediumLocalizedPairs m1Range ellRange M3 B xi).filter
        (fun p : ℤ × ℤ => p.2 = 0),
        ‖sourceCorrectedM2FourierInner m2Range fhat p.1 xi‖ ≤
          6 * M2 ^ 2 / M1 * Slow) :
    ‖sourceMediumZeroEllSum m1Range ellRange m2Range F fhat M3 B xi‖ ≤
      24 * Kpsi * M2 ^ 2 * M3 * Slow := by
  let P : Finset (ℤ × ℤ) :=
    (sourceMediumLocalizedPairs m1Range ellRange M3 B xi).filter
      (fun p => p.2 = 0)
  have hPcard : (P.card : ℝ) ≤ 4 * M1 := by
    have hsub : P ⊆ m1Range ×ˢ ({0} : Finset ℤ) := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hbase := mem_sourceMediumLocalizedPairs_iff.mp hp'.1
      exact Finset.mem_product.mpr ⟨hbase.1, by simpa [hp'.2]⟩
    have hc := Finset.card_le_card hsub
    have hc' : P.card ≤ m1Range.card := by
      simpa using hc
    exact (Nat.cast_le.mpr hc').trans hcard1
  have hterm : ∀ p ∈ P,
      ‖sourceFirstPoissonLocalizedPairTerm m2Range F fhat M3 p xi‖ ≤
        M3 * Kpsi * (6 * M2 ^ 2 / M1 * Slow) := by
    intro p hp
    have hpinner := hinner p hp
    have hF' := hF (M3 * ((p.2 : ℝ) - xi / (p.1 : ℝ)))
    unfold sourceFirstPoissonLocalizedPairTerm
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hM3]
    have hleft : 0 ≤ M3 * ‖F (M3 * ((p.2 : ℝ) - xi / (p.1 : ℝ)))‖ := by
      positivity
    have hMF : M3 * ‖F (M3 * ((p.2 : ℝ) - xi / (p.1 : ℝ)))‖ ≤ M3 * Kpsi :=
      mul_le_mul_of_nonneg_left hF' hM3
    exact mul_le_mul_of_nonneg_right hMF (norm_nonneg _)
      |>.trans (mul_le_mul_of_nonneg_left hpinner (by positivity))
  unfold sourceMediumZeroEllSum
  change ‖∑ p ∈ P, sourceFirstPoissonLocalizedPairTerm m2Range F fhat M3 p xi‖ ≤ _
  calc
    _ ≤ ∑ p ∈ P, ‖sourceFirstPoissonLocalizedPairTerm m2Range F fhat M3 p xi‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _p ∈ P, M3 * Kpsi * (6 * M2 ^ 2 / M1 * Slow) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hterm p hp
    _ = (P.card : ℝ) * (M3 * Kpsi * (6 * M2 ^ 2 / M1 * Slow)) := by
      simp [mul_assoc]
    _ ≤ (4 * M1) * (M3 * Kpsi * (6 * M2 ^ 2 / M1 * Slow)) := by
      gcongr
    _ = 24 * Kpsi * M2 ^ 2 * M3 * Slow := by
      field_simp [hM1.ne']
      ring

theorem integral_norm_sq_sourceMediumZeroEllSum_le
    (m1Range ellRange m2Range : Finset ℤ) (F fhat : ℝ → ℂ)
    {M M1 M2 M3 B Kpsi Slow : ℝ}
    (hM : 0 ≤ M) (hM1 : 0 < M1) (hM2 : 0 ≤ M2) (hM3 : 0 < M3)
    (hM1M : M1 ≤ M) (hM2M : M2 ≤ M) (hM3M : M3 ≤ M)
    (hB : 0 ≤ B) (hKpsi : 0 ≤ Kpsi) (hSlow : 0 ≤ Slow)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm1hi : ∀ m1 ∈ m1Range, |(m1 : ℝ)| ≤ 2 * M1)
    (hcard1 : (m1Range.card : ℝ) ≤ 4 * M1)
    (hF : ∀ z, ‖F z‖ ≤ Kpsi)
    (hinner : ∀ (xi : ℝ) (p : ℤ × ℤ),
        p ∈ (sourceMediumLocalizedPairs m1Range ellRange M3 B xi).filter
        (fun p : ℤ × ℤ => p.2 = 0) →
        ‖sourceCorrectedM2FourierInner m2Range fhat p.1 xi‖ ≤
          6 * M2 ^ 2 / M1 * Slow)
    (hint : Integrable (fun xi : ℝ =>
      ‖sourceMediumZeroEllSum m1Range ellRange m2Range F fhat M3 B xi‖ ^ 2)) :
    (∫ xi : ℝ,
      ‖sourceMediumZeroEllSum m1Range ellRange m2Range F fhat M3 B xi‖ ^ 2) ≤
      2304 * Kpsi ^ 2 * B * M ^ 6 * Slow ^ 2 := by
  let Z : ℝ → ℂ := fun xi =>
    sourceMediumZeroEllSum m1Range ellRange m2Range F fhat M3 B xi
  let R : ℝ := 2 * M1 * B / M3
  let C0 : ℝ := 24 * Kpsi * M2 ^ 2 * M3 * Slow
  have hZpoint : ∀ xi, ‖Z xi‖ ≤ C0 := by
    intro xi
    exact norm_sourceMediumZeroEllSum_le m1Range ellRange m2Range F fhat
      hM1 hM3.le hKpsi hSlow hcard1 hF (fun p hp => hinner xi p hp)
  have hZzero : ∀ xi, ¬ |xi| < R → Z xi = 0 := by
    intro xi hxi
    exact sourceMediumZeroEllSum_eq_zero_of_outside_extra_band F fhat
      (by linarith) hM3 hB hm1 hm1hi (by simpa [R] using hxi)
  let I : Set ℝ := Set.Icc (-R) R
  have hR0 : 0 ≤ R := by
    dsimp [R]
    positivity
  have hImeas : MeasurableSet I := measurableSet_Icc
  let G : ℝ → ℝ := I.indicator (fun _ => C0 ^ 2)
  have hGint : Integrable G := by
    apply (MeasureTheory.integrableOn_const (by simp [I, Real.volume_Icc])).integrable_indicator
    exact hImeas
  have hle : ∀ᵐ xi : ℝ ∂ volume, ‖Z xi‖ ^ 2 ≤ G xi := by
    filter_upwards with xi
    by_cases hxiI : xi ∈ I
    · change ‖Z xi‖ ^ 2 ≤ I.indicator (fun _ => C0 ^ 2) xi
      rw [Set.indicator_of_mem hxiI]
      exact pow_le_pow_left₀ (norm_nonneg _) (hZpoint xi) 2
    · change ‖Z xi‖ ^ 2 ≤ I.indicator (fun _ => C0 ^ 2) xi
      rw [Set.indicator_of_notMem hxiI]
      have hnot : ¬ |xi| < R := by
        intro habs
        have hlow : -R < xi := by
          rw [abs_lt] at habs
          exact habs.1
        have hhigh : xi < R := by
          rw [abs_lt] at habs
          exact habs.2
        exact hxiI ⟨hlow.le, hhigh.le⟩
      rw [hZzero xi hnot]
      simp
  have henergy := MeasureTheory.integral_mono_ae hint hGint hle
  have hGvalue : (∫ xi : ℝ, G xi) = (2 * R) * C0 ^ 2 := by
    dsimp [G, I]
    rw [MeasureTheory.integral_indicator hImeas]
    rw [MeasureTheory.setIntegral_const]
    change volume.real (Set.Icc (-R) R) • C0 ^ 2 = (2 * R) * C0 ^ 2
    rw [Measure.real, Real.volume_Icc]
    have hwidth : 0 ≤ R - -R := by linarith
    rw [ENNReal.toReal_ofReal hwidth]
    simp only [smul_eq_mul]
    ring
  rw [hGvalue] at henergy
  rw [show (2 * R) * C0 ^ 2 =
      2304 * Kpsi ^ 2 * B * M1 * M2 ^ 4 * M3 * Slow ^ 2 by
        dsimp [R, C0]
        field_simp [hM3.ne']
        ring] at henergy
  calc
    (∫ xi : ℝ, ‖Z xi‖ ^ 2) ≤
        2304 * Kpsi ^ 2 * B * M1 * M2 ^ 4 * M3 * Slow ^ 2 := henergy
    _ ≤ 2304 * Kpsi ^ 2 * B * M ^ 6 * Slow ^ 2 := by
      have hprod : M1 * M2 ^ 4 * M3 ≤ M * M ^ 4 * M := by
        gcongr
      rw [show M * M ^ 4 * M = M ^ 6 by ring] at hprod
      have hcoeff : 0 ≤ 2304 * Kpsi ^ 2 * B * Slow ^ 2 := by positivity
      calc
        2304 * Kpsi ^ 2 * B * M1 * M2 ^ 4 * M3 * Slow ^ 2 =
            (2304 * Kpsi ^ 2 * B * Slow ^ 2) * (M1 * M2 ^ 4 * M3) := by ring
        _ ≤ (2304 * Kpsi ^ 2 * B * Slow ^ 2) * M ^ 6 :=
          mul_le_mul_of_nonneg_left hprod hcoeff
        _ = 2304 * Kpsi ^ 2 * B * M ^ 6 * Slow ^ 2 := by ring

end GuthMaynardS3ZeroEllSupport

#print axioms GuthMaynardS3ZeroEllSupport.zeroProduct_iff_ell_zero
#print axioms GuthMaynardS3ZeroEllSupport.zeroProduct_pair_abs_xi_lt
#print axioms GuthMaynardS3ZeroEllSupport.zeroProduct_pair_mem_extra_band
#print axioms GuthMaynardS3ZeroEllSupport.sourceMediumZeroEllSum_eq_zero_of_outside_extra_band
#print axioms GuthMaynardS3ZeroEllSupport.sourceFirstPoissonLocalizedPairSum_eq_zeroEll_add_nonzeroEll
#print axioms GuthMaynardS3ZeroEllSupport.norm_sourceMediumZeroEllSum_le
#print axioms GuthMaynardS3ZeroEllSupport.integral_norm_sq_sourceMediumZeroEllSum_le
