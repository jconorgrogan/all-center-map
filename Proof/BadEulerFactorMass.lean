import APFoundation
import Mathlib.NumberTheory.Chebyshev

namespace MAPBadEulerFactorMass

open scoped ArithmeticFunction BigOperators

noncomputable section

/-- Bad-prime contribution at one prime-power exponent. -/
def badPrimePowersAtExponent (q K k : ℕ) : ℝ :=
  ∑ p ∈ Finset.Ioc 0 K with p.Prime,
    if ¬ (p ^ k).Coprime q then
      ArithmeticFunction.vonMangoldt (p ^ k)
    else 0

theorem badPrimePowersAtExponent_le_log
    {q K k : ℕ} (hq : 1 ≤ q) (hk : 1 ≤ k) :
    badPrimePowersAtExponent q K k ≤ Real.log q := by
  classical
  unfold badPrimePowersAtExponent
  rw [← Finset.sum_filter]
  have hsubset :
      ((Finset.Ioc 0 K).filter Nat.Prime).filter
          (fun p => ¬ (p ^ k).Coprime q) ⊆
        q.divisors := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    rw [Nat.mem_divisors]
    constructor
    · have hpow : (p ^ k).Coprime q ↔ p.Coprime q :=
        Nat.coprime_pow_left_iff (Nat.zero_lt_of_lt hk) p q
      have hncp : ¬ p.Coprime q := fun h => hp.2 (hpow.mpr h)
      exact hp.1.2.dvd_iff_not_coprime.mpr hncp
    · exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hq)
  calc
    (∑ p ∈ ((Finset.Ioc 0 K).filter Nat.Prime).filter
        (fun p => ¬ (p ^ k).Coprime q),
        ArithmeticFunction.vonMangoldt (p ^ k)) =
        ∑ p ∈ ((Finset.Ioc 0 K).filter Nat.Prime).filter
          (fun p => ¬ (p ^ k).Coprime q),
          ArithmeticFunction.vonMangoldt p := by
      apply Finset.sum_congr rfl
      intro p hp
      exact ArithmeticFunction.vonMangoldt_apply_pow (Nat.ne_of_gt hk)
    _ ≤ ∑ d ∈ q.divisors, ArithmeticFunction.vonMangoldt d := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = Real.log q := ArithmeticFunction.vonMangoldt_sum

/-- Literal von Mangoldt mass up to `N` supported at integers sharing a prime
factor with `q`. -/
def badMangoldtMassUpTo (q N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 N,
    if ¬ n.Coprime q then ArithmeticFunction.vonMangoldt n else 0

/-- The missing-Euler-factor mass is at most one copy of `log q` for each
possible prime-power exponent.  This is the finite quantitative estimate needed
after primitive induction; no asymptotic notation is used. -/
theorem badMangoldtMassUpTo_le
    {q N : ℕ} (hq : 1 ≤ q) :
    badMangoldtMassUpTo q N ≤
      (⌊Real.log (N : ℝ) / Real.log 2⌋₊ : ℝ) * Real.log q := by
  classical
  let f : ℕ → ℝ := fun n =>
    if ¬ n.Coprime q then ArithmeticFunction.vonMangoldt n else 0
  have hprimePow :
      ∑ n ∈ Finset.Ioc 0 N, f n =
        ∑ n ∈ Finset.Ioc 0 N with IsPrimePow n, f n := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnot
    simp only [Finset.mem_filter, not_and] at hnot
    have hnpp : ¬ IsPrimePow n := hnot hn
    simp only [f]
    by_cases hcop : n.Coprime q
    · simp [hcop]
    · simp [hcop, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnpp]
  have hdecomp :
      ∑ n ∈ Finset.Ioc 0 N with IsPrimePow n, f n =
        ∑ k ∈ Finset.Icc 1 ⌊Real.log (N : ℝ) / Real.log 2⌋₊,
          badPrimePowersAtExponent q
            ⌊(N : ℝ) ^ ((1 : ℝ) / k)⌋₊ k := by
    simpa only [badPrimePowersAtExponent, f, Nat.floor_natCast]
      using (Chebyshev.sum_PrimePow_eq_sum_sum f (show 0 ≤ (N : ℝ) by positivity))
  change (∑ n ∈ Finset.Ioc 0 N, f n) ≤ _
  rw [hprimePow, hdecomp]
  calc
    (∑ k ∈ Finset.Icc 1 ⌊Real.log (N : ℝ) / Real.log 2⌋₊,
        badPrimePowersAtExponent q
          ⌊(N : ℝ) ^ ((1 : ℝ) / k)⌋₊ k) ≤
        ∑ _k ∈ Finset.Icc 1 ⌊Real.log (N : ℝ) / Real.log 2⌋₊,
          Real.log q := by
      apply Finset.sum_le_sum
      intro k hk
      exact badPrimePowersAtExponent_le_log hq (Finset.mem_Icc.mp hk).1
    _ = (⌊Real.log (N : ℝ) / Real.log 2⌋₊ : ℝ) * Real.log q := by
      simp [Nat.card_Icc, nsmul_eq_mul]

/-- Restricting from all positive integers up to `N` to any natural interval
cannot increase the bad-prime Mangoldt mass. -/
theorem badMangoldtMass_Ioc_le_upTo (q m N : ℕ) :
    (∑ n ∈ (Finset.Ioc m N).filter (fun n => ¬ n.Coprime q),
        ArithmeticFunction.vonMangoldt n) ≤ badMangoldtMassUpTo q N := by
  classical
  unfold badMangoldtMassUpTo
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    exact ⟨⟨Nat.zero_lt_of_lt hn.1.1, hn.1.2⟩, hn.2⟩
  · intro n hn hnot
    exact ArithmeticFunction.vonMangoldt_nonneg

variable {q : ℕ} [NeZero q]

/-- Exact logarithmic bound for the primitive/imprimitive correction on a
natural interval. -/
theorem norm_imprimitiveMangoldtCorrection_Ioc_le
    (chi : DirichletCharacter ℂ q) (m N : ℕ) :
    ‖APFoundation.imprimitiveMangoldtCorrection chi (Finset.Ioc m N)‖ ≤
      (⌊Real.log (N : ℝ) / Real.log 2⌋₊ : ℝ) * Real.log q := by
  apply (APFoundation.norm_imprimitiveMangoldtCorrection_le chi
    (Finset.Ioc m N)).trans
  calc
    (∑ n ∈ (Finset.Ioc m N).filter (fun n => ¬ n.Coprime q),
        ArithmeticFunction.vonMangoldt n) ≤ badMangoldtMassUpTo q N :=
      badMangoldtMass_Ioc_le_upTo q m N
    _ ≤ (⌊Real.log (N : ℝ) / Real.log 2⌋₊ : ℝ) * Real.log q :=
      badMangoldtMassUpTo_le q.pos_of_neZero

/-- The character projector's normalized sum of all primitive/imprimitive
corrections obeys the same exact logarithmic bound, with no `phi(q)` loss. -/
theorem norm_normalized_imprimitiveMangoldtCorrections_Ioc_le
    (a : ZMod q) (m N : ℕ) :
    ‖(q.totient : ℂ)⁻¹ *
        ∑ chi : DirichletCharacter ℂ q,
          chi a * APFoundation.imprimitiveMangoldtCorrection chi
            (Finset.Ioc m N)‖ ≤
      (⌊Real.log (N : ℝ) / Real.log 2⌋₊ : ℝ) * Real.log q := by
  apply (APFoundation.norm_normalized_imprimitiveMangoldtCorrections_le a
    (Finset.Ioc m N)).trans
  exact (badMangoldtMass_Ioc_le_upTo q m N).trans
    (badMangoldtMassUpTo_le q.pos_of_neZero)

end
end MAPBadEulerFactorMass
