import GuthMaynardJIterationFirstPoissonHatgBound

open scoped BigOperators Real FourierTransform

noncomputable section
namespace GuthMaynardJIteration

/-! Explicit finite localized `(m₁, ell)` bookkeeping for TeX 1585--1593. -/

def sourceMediumLocalizedPairs
    (m1Range ellRange : Finset ℤ) (M3 B xi : ℝ) : Finset (ℤ × ℤ) :=
  (m1Range ×ˢ ellRange).filter fun p =>
    |xi - (p.1 : ℝ) * (p.2 : ℝ)| < (|(p.1 : ℝ)| / M3) * B

def sourceMediumLocalizedProducts
    (m1Range ellRange : Finset ℤ) (M3 B xi : ℝ) : Finset ℤ :=
  (sourceMediumLocalizedPairs m1Range ellRange M3 B xi).image
    fun p => p.1 * p.2

def sourceIntegerWindow (xi W : ℝ) : Finset ℤ :=
  Finset.Icc ⌊xi - W⌋ ⌈xi + W⌉

def sourceMediumProductFiber
    (m1Range ellRange : Finset ℤ) (M3 B xi : ℝ) (s : ℤ) :
    Finset (ℤ × ℤ) :=
  (sourceMediumLocalizedPairs m1Range ellRange M3 B xi).filter
    fun p => p.1 * p.2 = s

theorem mem_sourceMediumLocalizedPairs_iff
    {m1Range ellRange : Finset ℤ} {M3 B xi : ℝ} {p : ℤ × ℤ} :
    p ∈ sourceMediumLocalizedPairs m1Range ellRange M3 B xi ↔
      p.1 ∈ m1Range ∧ p.2 ∈ ellRange ∧
        |xi - (p.1 : ℝ) * (p.2 : ℝ)| < (|(p.1 : ℝ)| / M3) * B := by
  simp [sourceMediumLocalizedPairs, and_assoc]

theorem localizedProduct_mem_sourceIntegerWindow
    {m1Range ellRange : Finset ℤ} {M3 B xi W : ℝ}
    (hwindow : ∀ p ∈ sourceMediumLocalizedPairs m1Range ellRange M3 B xi,
      |xi - ((p.1 * p.2 : ℤ) : ℝ)| < W)
    {s : ℤ} (hs : s ∈ sourceMediumLocalizedProducts
      m1Range ellRange M3 B xi) :
    s ∈ sourceIntegerWindow xi W := by
  unfold sourceMediumLocalizedProducts at hs
  rw [Finset.mem_image] at hs
  obtain ⟨p, hp, rfl⟩ := hs
  have h := hwindow p hp
  have hl : xi - W < ((p.1 * p.2 : ℤ) : ℝ) := by
    rw [abs_lt] at h
    linarith
  have hu : ((p.1 * p.2 : ℤ) : ℝ) < xi + W := by
    rw [abs_lt] at h
    linarith
  unfold sourceIntegerWindow
  rw [Finset.mem_Icc]
  constructor
  · exact_mod_cast (Int.floor_le (xi - W)).trans hl.le
  · exact_mod_cast hu.le.trans (Int.le_ceil (xi + W))

theorem card_sourceMediumLocalizedProducts_le_integerWindow
    {m1Range ellRange : Finset ℤ} {M3 B xi W : ℝ}
    (hwindow : ∀ p ∈ sourceMediumLocalizedPairs m1Range ellRange M3 B xi,
      |xi - ((p.1 * p.2 : ℤ) : ℝ)| < W) :
    (sourceMediumLocalizedProducts m1Range ellRange M3 B xi).card ≤
      (sourceIntegerWindow xi W).card := by
  apply Finset.card_le_card
  intro s hs
  exact localizedProduct_mem_sourceIntegerWindow hwindow hs

theorem card_sourceIntegerWindow
    (xi W : ℝ) :
    (sourceIntegerWindow xi W).card =
      (⌈xi + W⌉ + 1 - ⌊xi - W⌋).toNat := by
  unfold sourceIntegerWindow
  exact Int.card_Icc _ _

theorem card_sourceMediumLocalizedPairs_eq_sum_fibers
    (m1Range ellRange : Finset ℤ) (M3 B xi : ℝ) :
    (sourceMediumLocalizedPairs m1Range ellRange M3 B xi).card =
      ∑ s ∈ sourceMediumLocalizedProducts m1Range ellRange M3 B xi,
        (sourceMediumProductFiber m1Range ellRange M3 B xi s).card := by
  unfold sourceMediumLocalizedProducts sourceMediumProductFiber
  exact Finset.card_eq_sum_card_fiberwise fun p hp =>
    Finset.mem_image_of_mem (fun p : ℤ × ℤ => p.1 * p.2) hp

/-- Exact product-window count times a uniform signed-factor multiplicity. -/
theorem card_sourceMediumLocalizedPairs_le_window_mul_fiber
    {m1Range ellRange : Finset ℤ} {M3 B xi W : ℝ} {D : ℕ}
    (hwindow : ∀ p ∈ sourceMediumLocalizedPairs m1Range ellRange M3 B xi,
      |xi - ((p.1 * p.2 : ℤ) : ℝ)| < W)
    (hfiber : ∀ s ∈ sourceMediumLocalizedProducts
      m1Range ellRange M3 B xi,
      (sourceMediumProductFiber m1Range ellRange M3 B xi s).card ≤ D) :
    (sourceMediumLocalizedPairs m1Range ellRange M3 B xi).card ≤
      (sourceIntegerWindow xi W).card * D := by
  rw [card_sourceMediumLocalizedPairs_eq_sum_fibers]
  calc
    (∑ s ∈ sourceMediumLocalizedProducts m1Range ellRange M3 B xi,
        (sourceMediumProductFiber m1Range ellRange M3 B xi s).card) ≤
      ∑ _s ∈ sourceMediumLocalizedProducts m1Range ellRange M3 B xi, D := by
        apply Finset.sum_le_sum
        intro s hs
        exact hfiber s hs
    _ = (sourceMediumLocalizedProducts m1Range ellRange M3 B xi).card * D := by
      simp
    _ ≤ (sourceIntegerWindow xi W).card * D := by
      exact Nat.mul_le_mul_right D
        (card_sourceMediumLocalizedProducts_le_integerWindow hwindow)

def sourceFirstPoissonLocalizedPairTerm
    (m2Range : Finset ℤ) (F fhat : ℝ → ℂ)
    (M3 : ℝ) (p : ℤ × ℤ) (xi : ℝ) : ℂ :=
  ((M3 : ℂ) * F (M3 * ((p.2 : ℝ) - xi / (p.1 : ℝ)))) *
    sourceCorrectedM2FourierInner m2Range fhat p.1 xi

def sourceFirstPoissonLocalizedPairSum
    (m1Range ellRange m2Range : Finset ℤ) (F fhat : ℝ → ℂ)
    (M3 B xi : ℝ) : ℂ :=
  ∑ p ∈ sourceMediumLocalizedPairs m1Range ellRange M3 B xi,
    sourceFirstPoissonLocalizedPairTerm m2Range F fhat M3 p xi

theorem sourceFirstPoissonRetained_eq_localizedFinite
    (ellRange : Finset ℤ) (F : ℝ → ℂ)
    {M3 B m1 : ℝ} (hM3 : 0 < M3) (hm1 : m1 ≠ 0)
    (xi : ℝ)
    (hcover : ∀ ell : ℤ,
      |xi - m1 * (ell : ℝ)| < (|m1| / M3) * B → ell ∈ ellRange) :
    sourceFirstPoissonRetained F M3 B m1 xi =
      ∑ ell ∈ ellRange.filter (fun ell : ℤ =>
        |xi - m1 * (ell : ℝ)| < (|m1| / M3) * B),
        (M3 : ℂ) * F (M3 * ((ell : ℝ) - xi / m1)) := by
  unfold sourceFirstPoissonRetained sourceSecondPoissonRetained
  have hfinite :
      (∑' ell : ℤ,
        schwartzIntegerRetained F (1 / M3) B (xi / m1) ell) =
      ∑ ell ∈ ellRange,
        schwartzIntegerRetained F (1 / M3) B (xi / m1) ell := by
    apply tsum_eq_sum
    intro ell hell
    unfold schwartzIntegerRetained
    rw [if_neg]
    intro hscaled
    apply hell
    apply hcover ell
    apply (firstPoissonLocalization_iff hM3 hm1 B xi ell).mp
    simpa only [firstPoissonFrequency_eq hM3] using hscaled
  rw [hfinite]
  rw [Finset.sum_filter]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ell hellmem
  unfold schwartzIntegerRetained
  have hiff := firstPoissonLocalization_iff hM3 hm1 B xi ell
  have hfreq := firstPoissonFrequency_eq hM3 ell (xi / m1)
  by_cases hlocal : |xi - m1 * (ell : ℝ)| < (|m1| / M3) * B
  · rw [if_pos hlocal, hfreq, if_pos (hiff.mpr hlocal)]
    simp only [div_one, Complex.real_smul, Complex.ofReal_mul]
  · rw [if_neg hlocal, hfreq,
      if_neg (fun hs => hlocal (hiff.mp hs))]
    simp

/-- A supplied finite `ellRange` which contains every strict localized window
turns the retained first-Poisson `tsum` into the explicit localized pair sum. -/
theorem sourceFirstPoissonRetainedFinite_eq_localizedPairSum
    (m1Range ellRange m2Range : Finset ℤ) (F fhat : ℝ → ℂ)
    {M3 B : ℝ} (hM3 : 0 < M3)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (xi : ℝ)
    (hcover : ∀ m1 ∈ m1Range, ∀ ell : ℤ,
      |xi - (m1 : ℝ) * (ell : ℝ)| < (|(m1 : ℝ)| / M3) * B →
        ell ∈ ellRange) :
    sourceFirstPoissonRetainedFinite m1Range m2Range F fhat M3 B xi =
      sourceFirstPoissonLocalizedPairSum
        m1Range ellRange m2Range F fhat M3 B xi := by
  unfold sourceFirstPoissonRetainedFinite
  unfold sourceFirstPoissonLocalizedPairSum sourceMediumLocalizedPairs
  rw [Finset.sum_filter]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro m1 hm1mem
  unfold sourceFirstPoissonRetainedContribution
  rw [sourceFirstPoissonRetained_eq_localizedFinite ellRange F hM3
    (by exact_mod_cast hm1 m1 hm1mem) xi (hcover m1 hm1mem)]
  rw [Finset.sum_mul]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ell hellmem
  by_cases hlocal :
      |xi - (m1 : ℝ) * (ell : ℝ)| < (|(m1 : ℝ)| / M3) * B
  · rw [if_pos hlocal, if_pos hlocal]
    unfold sourceFirstPoissonLocalizedPairTerm
    ring
  · rw [if_neg hlocal, if_neg hlocal]

/-- Finite outer Cauchy--Schwarz with the exact localized pair count and the
corrected `|m₂/m₁|` Fourier inner. -/
theorem norm_sourceFirstPoissonLocalizedPairSum_sq_le
    (m1Range ellRange m2Range : Finset ℤ) (F fhat : ℝ → ℂ)
    {M3 B Kpsi : ℝ} (hM3 : 0 ≤ M3) (hKpsi : 0 ≤ Kpsi)
    (hF : ∀ z, ‖F z‖ ≤ Kpsi) (xi : ℝ) :
    ‖sourceFirstPoissonLocalizedPairSum
        m1Range ellRange m2Range F fhat M3 B xi‖ ^ 2 ≤
      ((sourceMediumLocalizedPairs m1Range ellRange M3 B xi).card : ℝ) *
        ∑ p ∈ sourceMediumLocalizedPairs m1Range ellRange M3 B xi,
          (M3 * Kpsi) ^ 2 *
            ‖sourceCorrectedM2FourierInner m2Range fhat p.1 xi‖ ^ 2 := by
  unfold sourceFirstPoissonLocalizedPairSum
  refine (norm_finset_sum_sq_le_card_mul_sum_norm_sq
    (sourceMediumLocalizedPairs m1Range ellRange M3 B xi)
    (fun p => sourceFirstPoissonLocalizedPairTerm
      m2Range F fhat M3 p xi)).trans ?_
  gcongr with p hp
  unfold sourceFirstPoissonLocalizedPairTerm
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hM3]
  have hbase : 0 ≤ M3 * Kpsi := mul_nonneg hM3 hKpsi
  have hterm : M3 * ‖F (M3 * ((p.2 : ℝ) - xi / (p.1 : ℝ)))‖ ≤
      M3 * Kpsi := mul_le_mul_of_nonneg_left (hF _) hM3
  have hleft : 0 ≤
      M3 * ‖F (M3 * ((p.2 : ℝ) - xi / (p.1 : ℝ)))‖ *
        ‖sourceCorrectedM2FourierInner m2Range fhat p.1 xi‖ := by
    positivity
  simpa only [mul_pow] using
    (pow_le_pow_left₀ hleft
      (mul_le_mul_of_nonneg_right hterm (norm_nonneg _)) 2)

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.localizedProduct_mem_sourceIntegerWindow
#print axioms GuthMaynardJIteration.card_sourceMediumLocalizedProducts_le_integerWindow
#print axioms GuthMaynardJIteration.card_sourceIntegerWindow
#print axioms GuthMaynardJIteration.card_sourceMediumLocalizedPairs_eq_sum_fibers
#print axioms GuthMaynardJIteration.card_sourceMediumLocalizedPairs_le_window_mul_fiber
#print axioms GuthMaynardJIteration.sourceFirstPoissonRetained_eq_localizedFinite
#print axioms GuthMaynardJIteration.sourceFirstPoissonRetainedFinite_eq_localizedPairSum
#print axioms GuthMaynardJIteration.norm_sourceFirstPoissonLocalizedPairSum_sq_le
