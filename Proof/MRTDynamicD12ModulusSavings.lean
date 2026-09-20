import MRTProposition61TypeIIDivisorNormalizationV3

/-!
# Uniform modulus savings for the dynamic D12 normalization

The three inequalities below isolate the only modulus arithmetic used by the
later D12 absorption: a fourth-power divisor loss is bounded by a fixed
subpower constant, and the Dirichlet constraint `lambda <= 1/(q Q)` converts
the resulting factors into the displayed powers of `Q`.
-/

namespace MRTDynamicD12ModulusSavings

open MRTProposition61TypeIIDivisorNormalizationV3
open MAPMRTCorollary53Source

noncomputable section

set_option maxHeartbeats 800000

theorem modulus_savings_of_d4_bound
    {X Q q lambda H D4 Cd : ℝ}
    (hX : 0 < X) (hQ : 0 < Q) (hq : 1 ≤ q) (hlambda : 0 < lambda)
    (hH : 0 < H) (hqQ : q ≤ Q)
    (hlambdaCap : lambda ≤ 1 / (q * Q))
    (hD4 : 0 ≤ D4) (hCd : 0 ≤ Cd)
    (hD4bound : D4 ≤ Cd * Real.rpow q (1 / 8 : ℝ)) :
    D4 * Real.sqrt Q * (q * lambda) ≤ Cd * Real.rpow Q (-3 / 8 : ℝ) ∧
    D4 * Real.sqrt Q ≤ Cd * Real.rpow Q (5 / 8 : ℝ) ∧
    D4 * q * Real.sqrt Q ≤ Cd * Real.rpow Q (13 / 8 : ℝ) := by
  have hq0 : 0 < q := by linarith
  have hqnonneg : 0 ≤ q := hq0.le
  have hQnonneg : 0 ≤ Q := hQ.le
  have hqpow : Real.rpow q (1 / 8 : ℝ) ≤ Real.rpow Q (1 / 8 : ℝ) :=
    Real.rpow_le_rpow hqnonneg hqQ (by norm_num)
  have hsqrtQ : Real.sqrt Q = Real.rpow Q (1 / 2 : ℝ) := by
    simpa only [Real.rpow_eq_pow] using (Real.sqrt_eq_rpow Q)
  have hqLam : q * lambda ≤ 1 / Q := by
    calc
      q * lambda ≤ q * (1 / (q * Q)) :=
        mul_le_mul_of_nonneg_left hlambdaCap hqnonneg
      _ = 1 / Q := by field_simp
  have hqpow0 : 0 ≤ Real.rpow q (1 / 8 : ℝ) :=
    Real.rpow_nonneg hqnonneg _
  have hQpow0 (e : ℝ) : 0 ≤ Real.rpow Q e := Real.rpow_nonneg hQnonneg _
  have hqLamnonneg : 0 ≤ q * lambda := mul_nonneg hqnonneg hlambda.le
  have hfirst :
      D4 * Real.sqrt Q * (q * lambda) ≤
        (Cd * Real.rpow q (1 / 8 : ℝ)) *
          Real.rpow Q (1 / 2 : ℝ) * (q * lambda) := by
    rw [hsqrtQ]
    have h₁ := mul_le_mul_of_nonneg_right hD4bound
      (mul_nonneg (hQpow0 (1 / 2 : ℝ)) hqLamnonneg)
    simpa [mul_assoc, mul_left_comm, mul_comm] using h₁
  have hsecond :
      D4 * Real.sqrt Q ≤
        (Cd * Real.rpow q (1 / 8 : ℝ)) *
          Real.rpow Q (1 / 2 : ℝ) := by
    rw [hsqrtQ]
    have h₁ := mul_le_mul_of_nonneg_right hD4bound
      (hQpow0 (1 / 2 : ℝ))
    simpa [mul_assoc, mul_left_comm, mul_comm] using h₁
  have hthird :
      D4 * q * Real.sqrt Q ≤
        (Cd * Real.rpow q (1 / 8 : ℝ)) * q *
          Real.rpow Q (1 / 2 : ℝ) := by
    rw [hsqrtQ]
    have h₁ := mul_le_mul_of_nonneg_right hD4bound
      (mul_nonneg hqnonneg (hQpow0 (1 / 2 : ℝ)))
    simpa [mul_assoc, mul_left_comm, mul_comm] using h₁
  have hfirst' :
      (Cd * Real.rpow q (1 / 8 : ℝ)) *
          Real.rpow Q (1 / 2 : ℝ) * (q * lambda) ≤
        Cd * Real.rpow Q (1 / 8 : ℝ) *
          Real.rpow Q (1 / 2 : ℝ) * (1 / Q) := by
    have h₁ := mul_le_mul_of_nonneg_right hqpow
      (mul_nonneg (mul_nonneg hCd (hQpow0 (1 / 2 : ℝ))) hqLamnonneg)
    calc
      _ ≤ Real.rpow Q (1 / 8 : ℝ) *
          (Cd * Real.rpow Q (1 / 2 : ℝ) * (q * lambda)) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using h₁
      _ ≤ Real.rpow Q (1 / 8 : ℝ) *
          (Cd * Real.rpow Q (1 / 2 : ℝ) * (1 / Q)) := by
        have := mul_le_mul_of_nonneg_left hqLam
          (mul_nonneg (mul_nonneg (hQpow0 (1 / 8 : ℝ)) hCd)
            (hQpow0 (1 / 2 : ℝ)))
        simpa [mul_assoc, mul_left_comm, mul_comm] using this
      _ = _ := by ring
  have hsecond' :
      (Cd * Real.rpow q (1 / 8 : ℝ)) * Real.rpow Q (1 / 2 : ℝ) ≤
        Cd * Real.rpow Q (1 / 8 : ℝ) * Real.rpow Q (1 / 2 : ℝ) := by
    have h₁ := mul_le_mul_of_nonneg_right hqpow
      (mul_nonneg hCd (hQpow0 (1 / 2 : ℝ)))
    simpa [mul_assoc, mul_left_comm, mul_comm] using h₁
  have hthird' :
      (Cd * Real.rpow q (1 / 8 : ℝ)) * q * Real.rpow Q (1 / 2 : ℝ) ≤
        (Cd * Real.rpow Q (1 / 8 : ℝ)) * Q * Real.rpow Q (1 / 2 : ℝ) := by
    have h₁ := mul_le_mul_of_nonneg_right hqpow
      (mul_nonneg (mul_nonneg hCd hqnonneg) (hQpow0 (1 / 2 : ℝ)))
    calc
      _ ≤ Real.rpow Q (1 / 8 : ℝ) *
          (Cd * q * Real.rpow Q (1 / 2 : ℝ)) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using h₁
      _ ≤ Real.rpow Q (1 / 8 : ℝ) *
          (Cd * Q * Real.rpow Q (1 / 2 : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hqQ
          (mul_nonneg (mul_nonneg (hQpow0 (1 / 8 : ℝ)) hCd)
            (hQpow0 (1 / 2 : ℝ)))
        simpa [mul_assoc, mul_left_comm, mul_comm] using this
      _ = _ := by ring
  have hfirst'' :
      Cd * Real.rpow Q (1 / 8 : ℝ) * Real.rpow Q (1 / 2 : ℝ) * (1 / Q) =
        Cd * Real.rpow Q (-3 / 8 : ℝ) := by
    have hinv : (1 / Q) = Real.rpow Q (-1 : ℝ) := by
      calc
        1 / Q = Q⁻¹ := by simp only [one_div]
        _ = Real.rpow Q (-1 : ℝ) := (Real.rpow_neg_one Q).symm
    rw [hinv]
    have hpow : Real.rpow Q (1 / 8 : ℝ) *
        (Real.rpow Q (1 / 2 : ℝ) * Real.rpow Q (-1 : ℝ)) =
        Real.rpow Q (-3 / 8 : ℝ) := by
      have hpow23 : Real.rpow Q (1 / 2 : ℝ) * Real.rpow Q (-1 : ℝ) =
          Real.rpow Q ((1 / 2 : ℝ) + (-1 : ℝ)) :=
        (Real.rpow_add hQ _ _).symm
      have hpow812 : Real.rpow Q (1 / 8 : ℝ) *
          Real.rpow Q ((1 / 2 : ℝ) + (-1 : ℝ)) =
          Real.rpow Q ((1 / 8 : ℝ) + ((1 / 2 : ℝ) + (-1 : ℝ))) :=
        (Real.rpow_add hQ _ _).symm
      calc
        _ = Real.rpow Q (1 / 8 : ℝ) *
            Real.rpow Q ((1 / 2 : ℝ) + (-1 : ℝ)) := by
          rw [hpow23]
        _ = Real.rpow Q ((1 / 8 : ℝ) + ((1 / 2 : ℝ) + (-1 : ℝ))) := by
          exact hpow812
        _ = _ := by congr 1 <;> norm_num
    calc
      _ = Cd * (Real.rpow Q (1 / 8 : ℝ) *
          (Real.rpow Q (1 / 2 : ℝ) * Real.rpow Q (-1 : ℝ))) := by ring
      _ = _ := by rw [hpow]
  have hsecond'' :
      Cd * Real.rpow Q (1 / 8 : ℝ) * Real.rpow Q (1 / 2 : ℝ) =
        Cd * Real.rpow Q (5 / 8 : ℝ) := by
    have hpow : Real.rpow Q (1 / 8 : ℝ) * Real.rpow Q (1 / 2 : ℝ) =
        Real.rpow Q ((1 / 8 : ℝ) + (1 / 2 : ℝ)) :=
      (Real.rpow_add hQ _ _).symm
    calc
      _ = Cd * (Real.rpow Q (1 / 8 : ℝ) * Real.rpow Q (1 / 2 : ℝ)) := by ring
      _ = Cd * Real.rpow Q ((1 / 8 : ℝ) + (1 / 2 : ℝ)) := by
        rw [hpow]
      _ = _ := by congr 1 <;> norm_num
  have hthird'' :
      (Cd * Real.rpow Q (1 / 8 : ℝ)) * Q * Real.rpow Q (1 / 2 : ℝ) =
        Cd * Real.rpow Q (13 / 8 : ℝ) := by
    have hQhalf : Q * Real.rpow Q (1 / 2 : ℝ) =
        Real.rpow Q ((1 : ℝ) + (1 / 2 : ℝ)) := by
      have hQone : Q = Real.rpow Q (1 : ℝ) := (Real.rpow_one Q).symm
      calc
        _ = Real.rpow Q (1 : ℝ) * Real.rpow Q (1 / 2 : ℝ) := by
          congr 1
        _ = _ := (Real.rpow_add hQ _ _).symm
    have hpow : Real.rpow Q (1 / 8 : ℝ) *
        Real.rpow Q ((1 : ℝ) + (1 / 2 : ℝ)) =
        Real.rpow Q ((1 / 8 : ℝ) + ((1 : ℝ) + (1 / 2 : ℝ))) :=
      (Real.rpow_add hQ _ _).symm
    calc
      _ = Cd * (Real.rpow Q (1 / 8 : ℝ) *
          (Q * Real.rpow Q (1 / 2 : ℝ))) := by ring
      _ = Cd * (Real.rpow Q (1 / 8 : ℝ) *
          Real.rpow Q ((1 : ℝ) + (1 / 2 : ℝ))) := by rw [hQhalf]
      _ = Cd * Real.rpow Q ((1 / 8 : ℝ) + ((1 : ℝ) + (1 / 2 : ℝ))) := by
        rw [hpow]
      _ = _ := by congr 1 <;> norm_num
  refine ⟨?_, ?_, ?_⟩
  · exact hfirst.trans (hfirst'.trans (le_of_eq (by simpa [mul_assoc] using hfirst'')))
  · exact hsecond.trans (hsecond'.trans (le_of_eq (by simpa [mul_assoc] using hsecond'')))
  · exact hthird.trans (hthird'.trans (le_of_eq hthird''))

theorem exists_uniform_d12_modulus_constant :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ q : ℕ, 1 ≤ q →
      (divisorCount q : ℝ) ^ 4 ≤
        Cd * Real.rpow (q : ℝ) (1 / 8 : ℝ) := by
  simpa using
    (exists_divisorCount_four_le_subpower (1 / 8 : ℝ) (by norm_num))

end
end MRTDynamicD12ModulusSavings

#print axioms MRTDynamicD12ModulusSavings.modulus_savings_of_d4_bound
#print axioms MRTDynamicD12ModulusSavings.exists_uniform_d12_modulus_constant
