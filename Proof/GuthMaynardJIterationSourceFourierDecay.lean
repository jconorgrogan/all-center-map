import GuthMaynardJIterationFirstPoissonHatgBound

/-!
# Source Fourier-decay quantifiers in Guth--Maynard Lemma 9.2

The hypothesis following the statement of Lemma 9.2 is kept literally: for
every positive loss exponent and every nonnegative integer decay order there
is a constant, uniform in the frequency.  `S` represents `sup_u f(u)`.
-/

open scoped BigOperators Real FourierTransform

noncomputable section
namespace GuthMaynardJIteration

def SourceFourierRapidDecay
    (fhat : ℝ → ℂ) (T S : ℝ) : Prop :=
  ∀ eta : ℝ, 0 < eta → ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ z : ℝ, z ≠ 0 →
      ‖fhat z‖ ≤ C * T ^ eta * (T / |z|) ^ j * S

/-- Literal specialization of the source decay hypothesis at
`z=(m₂/m₁)ξ`. -/
theorem sourceFourierRapidDecay_at_dyadicRatio
    (fhat : ℝ → ℂ) {T S eta : ℝ}
    (hdecay : SourceFourierRapidDecay fhat T S) (heta : 0 < eta)
    (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m1 m2 xi : ℝ},
      m1 ≠ 0 → m2 ≠ 0 → xi ≠ 0 →
      ‖fhat ((m2 / m1) * xi)‖ ≤
        C * T ^ eta * (T / (|m2 / m1| * |xi|)) ^ j * S := by
  obtain ⟨C, hC, hbound⟩ := hdecay eta heta j
  refine ⟨C, hC, ?_⟩
  intro m1 m2 xi hm1 hm2 hxi
  have hratio : m2 / m1 ≠ 0 := div_ne_zero hm2 hm1
  have hz : (m2 / m1) * xi ≠ 0 := mul_ne_zero hratio hxi
  simpa only [abs_mul] using hbound ((m2 / m1) * xi) hz

/-- Dyadic lower control on `|m₂/m₁|` turns the specialized source bound
into a uniform estimate for every coefficient in the block. -/
theorem sourceFourierRapidDecay_at_ratio_lower
    (fhat : ℝ → ℂ) {T S eta C Rlo : ℝ} (j : ℕ)
    (hT : 0 ≤ T) (hS : 0 ≤ S) (hC : 0 ≤ C) (hRlo : 0 < Rlo)
    (hbound : ∀ {m1 m2 xi : ℝ},
      m1 ≠ 0 → m2 ≠ 0 → xi ≠ 0 →
      ‖fhat ((m2 / m1) * xi)‖ ≤
        C * T ^ eta * (T / (|m2 / m1| * |xi|)) ^ j * S)
    {m1 m2 xi : ℝ} (hm1 : m1 ≠ 0) (hm2 : m2 ≠ 0) (hxi : xi ≠ 0)
    (hratio : Rlo ≤ |m2 / m1|) :
    ‖fhat ((m2 / m1) * xi)‖ ≤
      C * T ^ eta * (T / (Rlo * |xi|)) ^ j * S := by
  refine (hbound hm1 hm2 hxi).trans ?_
  have hxiabs : 0 < |xi| := abs_pos.mpr hxi
  have hdenlo : 0 < Rlo * |xi| := mul_pos hRlo hxiabs
  have hden : Rlo * |xi| ≤ |m2 / m1| * |xi| :=
    mul_le_mul_of_nonneg_right hratio hxiabs.le
  have hfrac : T / (|m2 / m1| * |xi|) ≤ T / (Rlo * |xi|) :=
    div_le_div_of_nonneg_left hT hdenlo hden
  have hfrac0 : 0 ≤ T / (|m2 / m1| * |xi|) := by positivity
  have hpow := pow_le_pow_left₀ hfrac0 hfrac j
  have hfac : 0 ≤ C * T ^ eta := mul_nonneg hC (Real.rpow_nonneg hT eta)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow hfac) hS

/-- Corrected Fourier inner with all dyadic losses visible. -/
theorem norm_sourceCorrectedM2FourierInner_le_decay
    (m2Range : Finset ℤ) (fhat : ℝ → ℂ) (m1 : ℤ) (xi : ℝ)
    {T S eta C Rlo Rhi N2 : ℝ} (j : ℕ)
    (hT : 0 ≤ T) (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hRlo : 0 < Rlo) (hRhi : 0 ≤ Rhi)
    (hN2 : (m2Range.card : ℝ) ≤ N2)
    (hm1 : m1 ≠ 0) (hxi : xi ≠ 0)
    (hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0)
    (hratioLo : ∀ m2 ∈ m2Range,
      Rlo ≤ |((m2 : ℝ) / (m1 : ℝ))|)
    (hratioHi : ∀ m2 ∈ m2Range,
      |((m2 : ℝ) / (m1 : ℝ))| ≤ Rhi)
    (hbound : ∀ {m1 m2 xi : ℝ},
      m1 ≠ 0 → m2 ≠ 0 → xi ≠ 0 →
      ‖fhat ((m2 / m1) * xi)‖ ≤
        C * T ^ eta * (T / (|m2 / m1| * |xi|)) ^ j * S) :
    ‖sourceCorrectedM2FourierInner m2Range fhat m1 xi‖ ≤
      N2 * Rhi * (C * T ^ eta * (T / (Rlo * |xi|)) ^ j * S) := by
  unfold sourceCorrectedM2FourierInner
  calc
    ‖∑ m2 ∈ m2Range,
        ((|((m2 : ℝ) / (m1 : ℝ))| : ℝ) : ℂ) *
          fhat (((m2 : ℝ) / (m1 : ℝ)) * xi)‖ ≤
      ∑ m2 ∈ m2Range,
        ‖((|((m2 : ℝ) / (m1 : ℝ))| : ℝ) : ℂ) *
          fhat (((m2 : ℝ) / (m1 : ℝ)) * xi)‖ := norm_sum_le _ _
    _ ≤ ∑ _m2 ∈ m2Range,
        Rhi * (C * T ^ eta * (T / (Rlo * |xi|)) ^ j * S) := by
      apply Finset.sum_le_sum
      intro m2 hm2mem
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (abs_nonneg _)]
      exact mul_le_mul (hratioHi m2 hm2mem)
        (sourceFourierRapidDecay_at_ratio_lower fhat j hT hS hC hRlo
          hbound (by exact_mod_cast hm1)
          (by exact_mod_cast hm2 m2 hm2mem) hxi (hratioLo m2 hm2mem))
        (norm_nonneg _) hRhi
    _ = (m2Range.card : ℝ) *
        (Rhi * (C * T ^ eta * (T / (Rlo * |xi|)) ^ j * S)) := by simp
    _ ≤ N2 * Rhi *
        (C * T ^ eta * (T / (Rlo * |xi|)) ^ j * S) := by
      have hD : 0 ≤ C * T ^ eta * (T / (Rlo * |xi|)) ^ j * S := by
        positivity
      calc
        (m2Range.card : ℝ) * (Rhi *
            (C * T ^ eta * (T / (Rlo * |xi|)) ^ j * S)) ≤
          N2 * (Rhi *
            (C * T ^ eta * (T / (Rlo * |xi|)) ^ j * S)) :=
          mul_le_mul_of_nonneg_right hN2 (mul_nonneg hRhi hD)
        _ = _ := by ring

/-- Elementary conversion from reciprocal powers to the integrable
`(1+|ξ|)^{-p}` envelope on `|ξ|≥1`. -/
theorem reciprocal_abs_pow_le_one_add_abs
    {xi : ℝ} (hxi : 1 ≤ |xi|) (p : ℕ) :
    (1 / |xi|) ^ p ≤ 2 ^ p / (1 + |xi|) ^ p := by
  have hxi0 : 0 < |xi| := lt_of_lt_of_le (by norm_num) hxi
  have hone : 0 < 1 + |xi| := by positivity
  have hlin : 1 + |xi| ≤ 2 * |xi| := by linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |xi|) hlin p
  rw [mul_pow] at hp
  rw [one_div_pow]
  exact (div_le_div_iff₀ (pow_pos hxi0 p) (pow_pos hone p)).2 (by
    simpa [mul_comm] using hp)

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.sourceFourierRapidDecay_at_dyadicRatio
#print axioms GuthMaynardJIteration.sourceFourierRapidDecay_at_ratio_lower
#print axioms GuthMaynardJIteration.norm_sourceCorrectedM2FourierInner_le_decay
#print axioms GuthMaynardJIteration.reciprocal_abs_pow_le_one_add_abs
