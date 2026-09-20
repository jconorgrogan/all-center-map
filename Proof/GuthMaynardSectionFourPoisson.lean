import GuthMaynardEquation55Split
import GuthMaynardJIterationPoisson

/-!
# The scaled Poisson identity in Guth--Maynard Lemma 4.5

This is the one-dimensional identity applied independently in the three
column variables of the cubic trace.  It is proved for the literal Section 3
Schwartz cutoff and retains the exact factor `N` and frequency `m*N`.
-/

namespace GuthMaynardSectionFourPoisson

open scoped BigOperators FourierTransform SchwartzMap
open GuthMaynardSectionThreeCutoff
open GuthMaynardSectionThreeCutoffDerivativeBudget
open GuthMaynardS1Source
open GuthMaynardJIteration

noncomputable section

private theorem summable_finset_sum
    {I B : Type*} (s : Finset I) (f : I → B → ℂ)
    (hf : ∀ i ∈ s, Summable (f i)) :
    Summable fun b => ∑ i ∈ s, f i b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Exact scaled Poisson formula
`sum_n h_t(n/N) = N sum_m hhat_t(mN)` for positive integral `N`. -/
theorem tsum_sectionThreeOscillatory_scaled_eq
    (t : ℝ) {N : ℕ} (hN : 0 < N) :
    (∑' n : ℤ, sectionThreeOscillatory t ((n : ℝ) / (N : ℝ))) =
      (N : ℂ) * ∑' m : ℤ, sourceHhat t ((m : ℝ) * (N : ℝ)) := by
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hscale : (0 : ℝ) < 1 / (N : ℝ) := one_div_pos.mpr hNreal
  have h := scaled_modulated_poisson
    (sectionThreeOscillatory t)
    (sectionThreeOscillatory_hasCompactSupport t)
    (sectionThreeOscillatory_contDiff t)
    hscale 0
  have hleft :
      (∑' n : ℤ,
        sectionThreeOscillatory t ((1 / (N : ℝ)) * n) *
          GuthMaynardJIteration.sourcePhase (0 * n)) =
      ∑' n : ℤ, sectionThreeOscillatory t ((n : ℝ) / (N : ℝ)) := by
    apply tsum_congr
    intro n
    simp [GuthMaynardJIteration.sourcePhase, div_eq_mul_inv, mul_comm]
  have hright :
      ((1 / (N : ℝ))⁻¹ : ℝ) •
          (∑' m : ℤ, FourierTransform.fourier
            (sectionThreeOscillatory t)
            (((m : ℝ) - 0) / (1 / (N : ℝ)))) =
        (N : ℂ) * ∑' m : ℤ, sourceHhat t ((m : ℝ) * (N : ℝ)) := by
    rw [show (1 / (N : ℝ))⁻¹ = (N : ℝ) by field_simp]
    rw [show ((N : ℝ) •
        (∑' m : ℤ, FourierTransform.fourier
          (sectionThreeOscillatory t)
          (((m : ℝ) - 0) / (1 / (N : ℝ))))) =
        (N : ℂ) *
          (∑' m : ℤ, FourierTransform.fourier
            (sectionThreeOscillatory t)
            (((m : ℝ) - 0) / (1 / (N : ℝ)))) by
          simp]
    congr 1
    apply tsum_congr
    intro m
    unfold sourceHhat
    change FourierTransform.fourier (sectionThreeOscillatory t)
        (((m : ℝ) - 0) / (1 / (N : ℝ))) =
      FourierTransform.fourier (sectionThreeOscillatory t)
        ((m : ℝ) * (N : ℝ))
    simp
  exact hleft ▸ hright ▸ h

/-- Absolute summability of the scaled Fourier side.  This is the legal
Fubini/reindexing input for the three independent Poisson sums. -/
theorem summable_norm_sourceHhat_scaled
    (t : ℝ) {N : ℕ} (hN : 0 < N) :
    Summable fun m : ℤ => ‖sourceHhat t ((m : ℝ) * (N : ℝ))‖ := by
  let F : 𝓢(ℝ, ℂ) := 𝓕 (sectionThreeOscillatorySchwartz t)
  have hfull : Summable fun k : ℤ => F (k : ℝ) := by
    apply summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    exact (F.isBigO_cocompact_rpow (-2)).comp_tendsto
      Int.tendsto_coe_cofinite
  have hinj : Function.Injective (fun m : ℤ => m * (N : ℤ)) := by
    intro a b hab
    exact (mul_right_cancel₀ (by exact_mod_cast hN.ne') hab)
  have hsub : Summable fun m : ℤ => F ((m * (N : ℤ) : ℤ) : ℝ) := by
    simpa only [Function.comp_apply] using hfull.comp_injective hinj
  have hnorm := hsub.norm
  apply hnorm.congr
  intro m
  unfold sourceHhat F
  norm_cast

/-- The legal three-fold Fubini product on the Fourier side. -/
theorem sourceHhat_three_tsum_product
    (t₁ t₂ t₃ : ℝ) {N : ℕ} (hN : 0 < N) :
    (∑' m₁ : ℤ, sourceHhat t₁ ((m₁ : ℝ) * (N : ℝ))) *
        (∑' m₂ : ℤ, sourceHhat t₂ ((m₂ : ℝ) * (N : ℝ))) *
        (∑' m₃ : ℤ, sourceHhat t₃ ((m₃ : ℝ) * (N : ℝ))) =
      ∑' p : (ℤ × ℤ) × ℤ,
        sourceHhat t₁ ((p.1.1 : ℝ) * (N : ℝ)) *
          sourceHhat t₂ ((p.1.2 : ℝ) * (N : ℝ)) *
          sourceHhat t₃ ((p.2 : ℝ) * (N : ℝ)) := by
  let f₁ : ℤ → ℂ := fun m => sourceHhat t₁ ((m : ℝ) * (N : ℝ))
  let f₂ : ℤ → ℂ := fun m => sourceHhat t₂ ((m : ℝ) * (N : ℝ))
  let f₃ : ℤ → ℂ := fun m => sourceHhat t₃ ((m : ℝ) * (N : ℝ))
  have h₁ : Summable fun m => ‖f₁ m‖ :=
    summable_norm_sourceHhat_scaled t₁ hN
  have h₂ : Summable fun m => ‖f₂ m‖ :=
    summable_norm_sourceHhat_scaled t₂ hN
  have h₃ : Summable fun m => ‖f₃ m‖ :=
    summable_norm_sourceHhat_scaled t₃ hN
  have h₁₂ := tsum_mul_tsum_of_summable_norm h₁ h₂
  have h₁₂₃ := tsum_mul_tsum_of_summable_norm (h₁.mul_norm h₂) h₃
  change (∑' m, f₁ m) * (∑' m, f₂ m) * (∑' m, f₃ m) = _
  rw [h₁₂]
  exact h₁₂₃

/-- Triple Poisson identity for one closed walk of ordinates.  This is the
exact analytic equality immediately before the finite sum over rows in
Lemma 4.5. -/
theorem triple_poisson_closedWalk
    (t₁ t₂ t₃ : ℝ) {N : ℕ} (hN : 0 < N) :
    (∑' n₁ : ℤ,
        sectionThreeOscillatory (t₁ - t₂) ((n₁ : ℝ) / (N : ℝ))) *
      (∑' n₂ : ℤ,
        sectionThreeOscillatory (t₂ - t₃) ((n₂ : ℝ) / (N : ℝ))) *
      (∑' n₃ : ℤ,
        sectionThreeOscillatory (t₃ - t₁) ((n₃ : ℝ) / (N : ℝ))) =
    ∑' p : (ℤ × ℤ) × ℤ, (N : ℂ) ^ 3 *
      (sourceHhat (t₁ - t₂) ((p.1.1 : ℝ) * (N : ℝ)) *
        sourceHhat (t₂ - t₃) ((p.1.2 : ℝ) * (N : ℝ)) *
        sourceHhat (t₃ - t₁) ((p.2 : ℝ) * (N : ℝ))) := by
  rw [tsum_sectionThreeOscillatory_scaled_eq (t₁ - t₂) hN,
    tsum_sectionThreeOscillatory_scaled_eq (t₂ - t₃) hN,
    tsum_sectionThreeOscillatory_scaled_eq (t₃ - t₁) hN]
  have hprod := sourceHhat_three_tsum_product
    (t₁ - t₂) (t₂ - t₃) (t₃ - t₁) hN
  let A := ∑' m : ℤ, sourceHhat (t₁ - t₂) ((m : ℝ) * (N : ℝ))
  let B := ∑' m : ℤ, sourceHhat (t₂ - t₃) ((m : ℝ) * (N : ℝ))
  let C := ∑' m : ℤ, sourceHhat (t₃ - t₁) ((m : ℝ) * (N : ℝ))
  change ((N : ℂ) * A) * ((N : ℂ) * B) * ((N : ℂ) * C) = _
  calc
    ((N : ℂ) * A) * ((N : ℂ) * B) * ((N : ℂ) * C) =
        (N : ℂ) ^ 3 * (A * B * C) := by ring
    _ = (N : ℂ) ^ 3 *
        (∑' p : (ℤ × ℤ) × ℤ,
          sourceHhat (t₁ - t₂) ((p.1.1 : ℝ) * (N : ℝ)) *
            sourceHhat (t₂ - t₃) ((p.1.2 : ℝ) * (N : ℝ)) *
            sourceHhat (t₃ - t₁) ((p.2 : ℝ) * (N : ℝ))) := by
          rw [← hprod]
    _ = _ := by rw [tsum_mul_left]

/-- The normalized cubic trace before and after applying the three Poisson
identities, still with the finite row sums outside.  Moving those finite sums
inside the absolutely convergent frequency sum is the only remaining Fubini
step before the literal `I_m` notation. -/
def sourceNormalizedTraceCube (N : ℕ) (W : Finset ℝ) : ℂ :=
  ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
    (∑' n₁ : ℤ,
        sectionThreeOscillatory (t₁ - t₂) ((n₁ : ℝ) / (N : ℝ))) *
      (∑' n₂ : ℤ,
        sectionThreeOscillatory (t₂ - t₃) ((n₂ : ℝ) / (N : ℝ))) *
      (∑' n₃ : ℤ,
        sectionThreeOscillatory (t₃ - t₁) ((n₃ : ℝ) / (N : ℝ)))

theorem sourceNormalizedTraceCube_eq_rowSum_frequencyTsum
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) :
    sourceNormalizedTraceCube N W =
      ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        ∑' p : (ℤ × ℤ) × ℤ, (N : ℂ) ^ 3 *
          (sourceHhat (t₁ - t₂) ((p.1.1 : ℝ) * (N : ℝ)) *
            sourceHhat (t₂ - t₃) ((p.1.2 : ℝ) * (N : ℝ)) *
            sourceHhat (t₃ - t₁) ((p.2 : ℝ) * (N : ℝ))) := by
  unfold sourceNormalizedTraceCube
  apply Finset.sum_congr rfl
  intro t₁ ht₁
  apply Finset.sum_congr rfl
  intro t₂ ht₂
  apply Finset.sum_congr rfl
  intro t₃ ht₃
  exact triple_poisson_closedWalk t₁ t₂ t₃ hN

/-- Absolute summability of the literal three-frequency integrand for one
closed walk. -/
theorem summable_sourceFrequencyKernel
    (t₁ t₂ t₃ : ℝ) {N : ℕ} (hN : 0 < N) :
    Summable fun p : (ℤ × ℤ) × ℤ =>
      (N : ℂ) ^ 3 *
        (sourceHhat (t₁ - t₂) ((p.1.1 : ℝ) * (N : ℝ)) *
          sourceHhat (t₂ - t₃) ((p.1.2 : ℝ) * (N : ℝ)) *
          sourceHhat (t₃ - t₁) ((p.2 : ℝ) * (N : ℝ))) := by
  let f₁ : ℤ → ℂ := fun m => sourceHhat (t₁ - t₂) ((m : ℝ) * (N : ℝ))
  let f₂ : ℤ → ℂ := fun m => sourceHhat (t₂ - t₃) ((m : ℝ) * (N : ℝ))
  let f₃ : ℤ → ℂ := fun m => sourceHhat (t₃ - t₁) ((m : ℝ) * (N : ℝ))
  have h₁ : Summable fun m => ‖f₁ m‖ :=
    summable_norm_sourceHhat_scaled (t₁ - t₂) hN
  have h₂ : Summable fun m => ‖f₂ m‖ :=
    summable_norm_sourceHhat_scaled (t₂ - t₃) hN
  have h₃ : Summable fun m => ‖f₃ m‖ :=
    summable_norm_sourceHhat_scaled (t₃ - t₁) hN
  have hprod : Summable fun p : (ℤ × ℤ) × ℤ =>
      f₁ p.1.1 * f₂ p.1.2 * f₃ p.2 :=
    (h₁.mul_norm h₂ |>.mul_norm h₃).of_norm
  exact (hprod.mul_left ((N : ℂ) ^ 3)).congr (by
    intro p
    rfl)

/-- Finite row sums commute with the absolutely convergent frequency sum.
This closes the Fubini step in Lemma 4.5 and reaches the paper's literal
`I_m` notation. -/
theorem sourceNormalizedTraceCube_eq_tsum_sourceIm
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) :
    sourceNormalizedTraceCube N W =
      ∑' p : (ℤ × ℤ) × ℤ,
        GuthMaynardEquation55Split.sourceIm N W p.1.1 p.1.2 p.2 := by
  rw [sourceNormalizedTraceCube_eq_rowSum_frequencyTsum hN W]
  let K : ℝ → ℝ → ℝ → ((ℤ × ℤ) × ℤ) → ℂ :=
    fun t₁ t₂ t₃ p => (N : ℂ) ^ 3 *
      (sourceHhat (t₁ - t₂) ((p.1.1 : ℝ) * (N : ℝ)) *
        sourceHhat (t₂ - t₃) ((p.1.2 : ℝ) * (N : ℝ)) *
        sourceHhat (t₃ - t₁) ((p.2 : ℝ) * (N : ℝ)))
  have hK (t₁ t₂ t₃ : ℝ) : Summable (K t₁ t₂ t₃) := by
    exact summable_sourceFrequencyKernel t₁ t₂ t₃ hN
  have hK₃ (t₁ t₂ : ℝ) :
      Summable fun p => ∑ t₃ ∈ W, K t₁ t₂ t₃ p := by
    exact summable_finset_sum W (fun t₃ p => K t₁ t₂ t₃ p)
      fun t₃ _ => hK t₁ t₂ t₃
  have hK₂ (t₁ : ℝ) :
      Summable fun p => ∑ t₂ ∈ W, ∑ t₃ ∈ W, K t₁ t₂ t₃ p := by
    exact summable_finset_sum W
      (fun t₂ p => ∑ t₃ ∈ W, K t₁ t₂ t₃ p)
      fun t₂ _ => hK₃ t₁ t₂
  have hK₁ :
      Summable fun p => ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        K t₁ t₂ t₃ p := by
    exact summable_finset_sum W
      (fun t₁ p => ∑ t₂ ∈ W, ∑ t₃ ∈ W, K t₁ t₂ t₃ p)
      fun t₁ _ => hK₂ t₁
  have hcomm :
      (∑' p, ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        K t₁ t₂ t₃ p) =
      ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, ∑' p,
        K t₁ t₂ t₃ p := by
    rw [Summable.tsum_finsetSum (fun t₁ _ => hK₂ t₁)]
    apply Finset.sum_congr rfl
    intro t₁ ht₁
    rw [Summable.tsum_finsetSum (fun t₂ _ => hK₃ t₁ t₂)]
    apply Finset.sum_congr rfl
    intro t₂ ht₂
    rw [Summable.tsum_finsetSum (fun t₃ _ => hK t₁ t₂ t₃)]
  rw [← hcomm]
  apply tsum_congr
  intro p
  unfold GuthMaynardEquation55Split.sourceIm K
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t₁ ht₁
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t₂ ht₂
  rw [Finset.mul_sum]

end
end GuthMaynardSectionFourPoisson

#print axioms GuthMaynardSectionFourPoisson.tsum_sectionThreeOscillatory_scaled_eq
#print axioms GuthMaynardSectionFourPoisson.summable_norm_sourceHhat_scaled
#print axioms GuthMaynardSectionFourPoisson.sourceHhat_three_tsum_product
#print axioms GuthMaynardSectionFourPoisson.triple_poisson_closedWalk
#print axioms GuthMaynardSectionFourPoisson.sourceNormalizedTraceCube_eq_rowSum_frequencyTsum
#print axioms GuthMaynardSectionFourPoisson.sourceNormalizedTraceCube_eq_tsum_sourceIm
