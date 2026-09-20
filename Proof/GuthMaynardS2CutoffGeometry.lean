import GuthMaynardS1PowerLedger

/-! # Actual dyadic gap and Fourier-cutoff choices for S2 -/

namespace GuthMaynardS2CutoffGeometry

open GuthMaynardS1PowerLedger

noncomputable section

/-- With T=N^(6/5), a small fixed subpower factor fits inside N. -/
theorem two_time_subpower_le_sourceN {N T delta : ℝ}
    (hN : 1 ≤ N) (hT : T = Real.rpow N (6 / 5 : ℝ))
    (hT16 : 16 ≤ T) (hd : delta ≤ 1 / 12) :
    2 * Real.rpow T delta ≤ N := by
  have hN0 : 0 ≤ N := le_trans zero_le_one hN
  have hTpow : T ≤ N ^ 2 := by
    rw [hT]
    exact (Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (6 / 5 : ℝ) ≤ 2)).trans_eq
      (Real.rpow_natCast N 2)
  have hN4 : 4 ≤ N := by nlinarith
  have hpow : Real.rpow T delta ≤ Real.sqrt N := by
    rw [hT]
    calc
      _ = Real.rpow N ((6 / 5 : ℝ) * delta) :=
        (Real.rpow_mul hN0 (6 / 5 : ℝ) delta).symm
      _ ≤ Real.rpow N (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN (by linarith)
      _ = Real.sqrt N := (Real.sqrt_eq_rpow N).symm
  have hs : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0
  nlinarith [sq_nonneg (Real.sqrt N - 2)]

/-- Ordinary numeric choices for every dyadic scale. L supplies a Fourier
cutoff between T^delta and2T^delta times the local dual length. -/
theorem exists_sourceS2_dyadic_cutoffs {N T delta : ℝ}
    (hN : 1 ≤ N) (hT : T = Real.rpow N (6 / 5 : ℝ))
    (hT16 : 16 ≤ T) (hd0 : 0 < delta) (hd : delta ≤ 1 / 12) :
    ∃ K L : ℕ,
      N * (2 : ℝ) ^ K ≤ T ∧ T < N * (2 : ℝ) ^ (K + 1) ∧
      Real.rpow T delta ≤ (2 : ℝ) ^ L ∧
      (2 : ℝ) ^ L ≤ 2 * Real.rpow T delta ∧
      ∀ i : ℕ, i ≤ K → (2 : ℝ) ^ (i + L) ≤ T := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hTone : 1 ≤ T := one_le_sourceT hN hT
  have hNT := sourceN_le_T hN hT
  have hquot : 1 ≤ T / N := (le_div_iff₀ hNpos).mpr (by simpa using hNT)
  obtain ⟨K, hKlo, hKhi⟩ := exists_nat_pow_near hquot (by norm_num : (1 : ℝ) < 2)
  obtain ⟨l, hllo, hlhi⟩ := exists_nat_pow_near
    (Real.one_le_rpow hTone hd0.le) (by norm_num : (1 : ℝ) < 2)
  change (2 : ℝ) ^ l ≤ Real.rpow T delta at hllo
  change Real.rpow T delta < (2 : ℝ) ^ (l + 1) at hlhi
  have hKN : N * (2 : ℝ) ^ K ≤ T := by
    have h := (le_div_iff₀ hNpos).mp hKlo
    nlinarith
  have hKcover : T < N * (2 : ℝ) ^ (K + 1) := by
    have h := (div_lt_iff₀ hNpos).mp hKhi
    nlinarith
  have hLup : (2 : ℝ) ^ (l + 1) ≤ 2 * Real.rpow T delta := by
    rw [pow_succ]
    nlinarith
  have hLN : (2 : ℝ) ^ (l + 1) ≤ N :=
    hLup.trans (two_time_subpower_le_sourceN hN hT hT16 hd)
  refine ⟨K, l + 1, hKN, hKcover, hlhi.le, hLup, ?_⟩
  intro i hi
  calc
    (2 : ℝ) ^ (i + (l + 1)) = (2 : ℝ) ^ i * (2 : ℝ) ^ (l + 1) := pow_add _ _ _
    _ ≤ (2 : ℝ) ^ K * N :=
      mul_le_mul (pow_le_pow_right₀ (by norm_num) hi) hLN (by positivity) (by positivity)
    _ ≤ T := by nlinarith

end
end GuthMaynardS2CutoffGeometry

#print axioms GuthMaynardS2CutoffGeometry.exists_sourceS2_dyadic_cutoffs
