import GuthMaynardLemma295CriticalTailPointwise
import GuthMaynardMellinTail
import GuthMaynardLemma295ExactMScale

/-!
# Arbitrary-order two-sided critical-line truncation
-/

namespace GuthMaynardLemma295CriticalTailIntegral

open Set MeasureTheory
open GuthMaynardLemma295CriticalMajorant
open GuthMaynardJutilaReflection2941
open GuthMaynardLemma295CriticalTailPointwise
open GuthMaynardLemma295MellinPolynomialDecay
open GuthMaynardMellinTail
open GuthMaynardLemma295ExactMScale

noncomputable section

def criticalTailDecayOrder (epsilon A : ℝ) : ℕ :=
  Nat.ceil ((A + 1 + 2 * epsilon) / epsilon) + 2

theorem criticalTailDecayOrder_two_le (epsilon A : ℝ) :
    2 ≤ criticalTailDecayOrder epsilon A := by
  unfold criticalTailDecayOrder
  omega

theorem criticalTailDecayOrder_exponent_le
    {epsilon A : ℝ} (hepsilon : 0 < epsilon) :
    1 + 2 * epsilon - epsilon * (criticalTailDecayOrder epsilon A : ℝ) ≤
      -A := by
  have hceil : (A + 1 + 2 * epsilon) / epsilon ≤
      (Nat.ceil ((A + 1 + 2 * epsilon) / epsilon) : ℝ) := Nat.le_ceil _
  have hmul : A + 1 + 2 * epsilon ≤
      epsilon * (Nat.ceil ((A + 1 + 2 * epsilon) / epsilon) : ℝ) := by
    simpa [mul_comm] using (div_le_iff₀ hepsilon).mp hceil
  unfold criticalTailDecayOrder
  push_cast
  nlinarith

 theorem inv_one_add_abs_pow_le_rpow_neg
    {t : ℝ} (k : ℕ) (ht : 0 < |t|) :
    1 / (1 + |t| ^ k) ≤ Real.rpow |t| (-(k : ℝ)) := by
  have hpow : 0 < |t| ^ k := pow_pos ht _
  calc
    1 / (1 + |t| ^ k) ≤ 1 / |t| ^ k := by
      exact one_div_le_one_div_of_le hpow (by linarith)
    _ = Real.rpow |t| (-(k : ℝ)) := by
      calc
        1 / |t| ^ k = (Real.rpow |t| (k : ℝ))⁻¹ := by
          have hr : Real.rpow |t| (k : ℝ) = |t| ^ k :=
            Real.rpow_natCast |t| k
          rw [one_div]
          exact congrArg Inv.inv hr.symm
        _ = Real.rpow |t| (-(k : ℝ)) :=
          (Real.rpow_neg ht.le (k : ℝ)).symm

 theorem norm_negativeNatPowerTail_le
    {F : ℝ → ℂ} {C R : ℝ} {k : ℕ}
    (hk : 2 ≤ k) (hR : 0 < R)
    (hbound : ∀ r, r < -R → ‖F r‖ ≤ C * (-r) ^ (-(k : ℝ))) :
    ‖∫ r : ℝ in Iic (-R), F r‖ ≤
      C * (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)) := by
  rw [← integral_comp_neg_Ioi]
  apply norm_positiveNatPowerTail_le hk hR
  intro r hr
  simpa using hbound (-r) (by linarith)

 theorem norm_criticalTail_positive_le
    {N : ℝ} (hN : 0 < N) (K k : ℕ) (g : ℝ) {R : ℝ}
    (hk : 2 ≤ k) (hR : 0 < R) :
    ‖∫ t : ℝ in Ioi R, lemma295CriticalIntegrand N K g t‖ ≤
      (Real.sqrt N * K * sourceMellinDecayConstantAt (1 / 2) k) *
        (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)) := by
  apply norm_positiveNatPowerTail_le hk hR
  intro t ht
  have ht0 : 0 < |t| := abs_pos.mpr (ne_of_gt (hR.trans ht))
  have hp := norm_lemma295CriticalIntegrand_le_arbitraryOrder hN K k g t
  have hC0 : 0 ≤ Real.sqrt N * K := mul_nonneg (Real.sqrt_nonneg _) (by positivity)
  calc
    ‖lemma295CriticalIntegrand N K g t‖ ≤
        Real.sqrt N * K *
          (sourceMellinDecayConstantAt (1 / 2) k / (1 + |t| ^ k)) := hp
    _ = (Real.sqrt N * K * sourceMellinDecayConstantAt (1 / 2) k) *
          (1 / (1 + |t| ^ k)) := by ring
    _ ≤ (Real.sqrt N * K * sourceMellinDecayConstantAt (1 / 2) k) *
          Real.rpow t (-(k : ℝ)) := by
      have hinv : 1 / (1 + |t| ^ k) ≤ Real.rpow t (-(k : ℝ)) := by
        simpa [abs_of_pos (hR.trans ht)] using
          inv_one_add_abs_pow_le_rpow_neg k ht0
      exact mul_le_mul_of_nonneg_left
        hinv (mul_nonneg
          (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))
          (sourceMellinDecayConstantAt_nonneg _ _))

theorem norm_criticalTail_negative_le
    {N : ℝ} (hN : 0 < N) (K k : ℕ) (g : ℝ) {R : ℝ}
    (hk : 2 ≤ k) (hR : 0 < R) :
    ‖∫ t : ℝ in Iic (-R), lemma295CriticalIntegrand N K g t‖ ≤
      (Real.sqrt N * K * sourceMellinDecayConstantAt (1 / 2) k) *
        (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)) := by
  apply norm_negativeNatPowerTail_le hk hR
  intro t ht
  have htneg : t < 0 := lt_of_lt_of_le ht (neg_nonpos.mpr hR.le)
  have ht0 : 0 < |t| := abs_pos.mpr (ne_of_lt htneg)
  have hp := norm_lemma295CriticalIntegrand_le_arbitraryOrder hN K k g t
  calc
    ‖lemma295CriticalIntegrand N K g t‖ ≤
        Real.sqrt N * K *
          (sourceMellinDecayConstantAt (1 / 2) k / (1 + |t| ^ k)) := hp
    _ = (Real.sqrt N * K * sourceMellinDecayConstantAt (1 / 2) k) *
          (1 / (1 + |t| ^ k)) := by ring
    _ ≤ (Real.sqrt N * K * sourceMellinDecayConstantAt (1 / 2) k) *
          Real.rpow (-t) (-(k : ℝ)) := by
      have hinv : 1 / (1 + |t| ^ k) ≤ Real.rpow (-t) (-(k : ℝ)) := by
        simpa [abs_of_neg htneg] using
          inv_one_add_abs_pow_le_rpow_neg k ht0
      exact mul_le_mul_of_nonneg_left
        hinv (mul_nonneg
          (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))
          (sourceMellinDecayConstantAt_nonneg _ _))

/-- Both critical half-line tails are `O_A(T^-A)` at the corrected exact
reflection length. -/
theorem exists_norm_criticalTail_exactM_le
    {epsilon A : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T N g : ℝ}, 1 ≤ T → 1 ≤ N →
        N ≤ sourceReflectionNumerator29_40 T epsilon →
        let M := reflectedLength29_40 T epsilon N
        let K := ⌊M⌋₊
        let R := Real.rpow T epsilon
        ‖∫ t : ℝ in Ioi R, lemma295CriticalIntegrand N K g t‖ ≤
            C * Real.rpow T (-A) ∧
          ‖∫ t : ℝ in Iic (-R), lemma295CriticalIntegrand N K g t‖ ≤
            C * Real.rpow T (-A) := by
  let k := criticalTailDecayOrder epsilon A
  let C₀ := sourceMellinDecayConstantAt (1 / 2) k
  let C := max 1 C₀
  refine ⟨C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro T N g hT hN hNcap
  dsimp only
  let M := reflectedLength29_40 T epsilon N
  let K := ⌊M⌋₊
  let R := Real.rpow T epsilon
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hRpos : 0 < R := Real.rpow_pos_of_pos hTpos _
  have hk : 2 ≤ k := criticalTailDecayOrder_two_le _ _
  have hMone : 1 ≤ M := one_le_reflectedLength29_40 hTpos hNpos hNcap
  have hKle : (K : ℝ) ≤ M := by
    dsimp [K]
    exact floor_reflectedLength_le (zero_le_one.trans hMone)
  have hsqrt : Real.sqrt N ≤ N := by
    rw [Real.sqrt_le_iff]
    constructor
    · exact zero_le_one.trans hN
    · nlinarith
  have hscale : Real.sqrt N * (K : ℝ) ≤
      sourceReflectionNumerator29_40 T epsilon := by
    calc
      Real.sqrt N * (K : ℝ) ≤ N * M := by
        exact mul_le_mul hsqrt hKle (Nat.cast_nonneg _) (zero_le_one.trans hN)
      _ = sourceReflectionNumerator29_40 T epsilon := by
        dsimp [M]
        exact N_mul_reflectedLength29_40 hNpos.ne'
  have hden : 1 ≤ (k : ℝ) - 1 := by
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hRpow0 : 0 ≤ Real.rpow R (1 - (k : ℝ)) :=
    Real.rpow_nonneg hRpos.le _
  have hfactor :
      Real.rpow R (1 - (k : ℝ)) / ((k : ℝ) - 1) ≤
        Real.rpow R (1 - (k : ℝ)) := div_le_self hRpow0 hden
  have hcompose : Real.rpow R (1 - (k : ℝ)) =
      Real.rpow T (epsilon * (1 - (k : ℝ))) := by
    dsimp [R]
    exact (Real.rpow_mul hTpos.le epsilon (1 - (k : ℝ))).symm
  have hproduct : sourceReflectionNumerator29_40 T epsilon *
      Real.rpow R (1 - (k : ℝ)) =
        Real.rpow T (1 + 2 * epsilon - epsilon * (k : ℝ)) := by
    unfold sourceReflectionNumerator29_40
    rw [hcompose]
    calc
      Real.rpow T (1 + epsilon) *
          Real.rpow T (epsilon * (1 - (k : ℝ))) =
        Real.rpow T ((1 + epsilon) + epsilon * (1 - (k : ℝ))) :=
          (Real.rpow_add hTpos _ _).symm
      _ = Real.rpow T (1 + 2 * epsilon - epsilon * (k : ℝ)) := by
        congr 1
        ring
  have hexp : 1 + 2 * epsilon - epsilon * (k : ℝ) ≤ -A := by
    dsimp [k]
    exact criticalTailDecayOrder_exponent_le hepsilon
  have htime : sourceReflectionNumerator29_40 T epsilon *
      (Real.rpow R (1 - (k : ℝ)) / ((k : ℝ) - 1)) ≤
        Real.rpow T (-A) := by
    calc
      sourceReflectionNumerator29_40 T epsilon *
          (Real.rpow R (1 - (k : ℝ)) / ((k : ℝ) - 1)) ≤
        sourceReflectionNumerator29_40 T epsilon *
          Real.rpow R (1 - (k : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hfactor
              (Real.rpow_nonneg hTpos.le _)
      _ = Real.rpow T (1 + 2 * epsilon - epsilon * (k : ℝ)) := hproduct
      _ ≤ Real.rpow T (-A) := Real.rpow_le_rpow_of_exponent_le hT hexp
  have hC₀ : 0 ≤ C₀ := sourceMellinDecayConstantAt_nonneg _ _
  have hcommon :
      (Real.sqrt N * (K : ℝ) * C₀) *
          (Real.rpow R (1 - (k : ℝ)) / ((k : ℝ) - 1)) ≤
        C * Real.rpow T (-A) := by
    calc
      (Real.sqrt N * (K : ℝ) * C₀) *
          (Real.rpow R (1 - (k : ℝ)) / ((k : ℝ) - 1)) =
        C₀ * ((Real.sqrt N * (K : ℝ)) *
          (Real.rpow R (1 - (k : ℝ)) / ((k : ℝ) - 1))) := by ring
      _ ≤ C₀ * (sourceReflectionNumerator29_40 T epsilon *
          (Real.rpow R (1 - (k : ℝ)) / ((k : ℝ) - 1))) := by
            gcongr
      _ ≤ C * Real.rpow T (-A) := by
        have hfactor0 : 0 ≤
            Real.rpow R (1 - (k : ℝ)) / ((k : ℝ) - 1) :=
          div_nonneg hRpow0 (by linarith)
        have hsource0 : 0 ≤ sourceReflectionNumerator29_40 T epsilon :=
          Real.rpow_nonneg hTpos.le _
        exact mul_le_mul (le_max_right _ _) htime
          (mul_nonneg hsource0 hfactor0)
          (zero_le_one.trans (le_max_left _ _))
  constructor
  · exact (norm_criticalTail_positive_le hNpos K k g hk hRpos).trans hcommon
  · exact (norm_criticalTail_negative_le hNpos K k g hk hRpos).trans hcommon

end
end GuthMaynardLemma295CriticalTailIntegral

#print axioms GuthMaynardLemma295CriticalTailIntegral.inv_one_add_abs_pow_le_rpow_neg
#print axioms GuthMaynardLemma295CriticalTailIntegral.norm_negativeNatPowerTail_le
#print axioms GuthMaynardLemma295CriticalTailIntegral.norm_criticalTail_positive_le
#print axioms GuthMaynardLemma295CriticalTailIntegral.norm_criticalTail_negative_le
#print axioms GuthMaynardLemma295CriticalTailIntegral.exists_norm_criticalTail_exactM_le
