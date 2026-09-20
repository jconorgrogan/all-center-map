import MRTDynamicD12SmoothSampledHolder
import MRTLemma215DynamicFactorExtractionV3

namespace MRTDynamicD12SmoothShell
open scoped BigOperators
open MRTDynamicD12SmoothSampled
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215PreliminaryExpansion MRTLemma215DynamicFactorExtractionV3
open MAPMRTProposition61TypeD1Factorization MAPMRTCorollary25Instantiation
open MAPHBPerronSourceData
noncomputable section

/-- The literal source log-index guard includes the independent global cutoff. -/
theorem source_guard_iff_mem_clipped {N n : ℕ}
    (j : Fin (sourceDyadicCount N)) :
    (2 ≤ n ∧ n ≤ N ∧ (n-1).log2 = (j : ℕ)) ↔
      n ∈ Finset.Ioc (2^(j : ℕ)) (min (2*2^(j : ℕ)) N) := by
  have hp : 1 ≤ 2^(j : ℕ) := Nat.one_le_pow _ _ (by omega)
  constructor
  · rintro ⟨hn2, hnN, hj⟩
    have hs := (log2_sub_one_eq_iff_mem_Ioc hn2).mp hj
    simp only [Finset.mem_Ioc] at hs ⊢
    exact ⟨hs.1, le_min hs.2 hnN⟩
  · intro hn
    have hs := Finset.mem_Ioc.mp hn
    have hn2 : 2 ≤ n := by omega
    exact ⟨hn2, (le_min_iff.mp hs.2).2,
      (log2_sub_one_eq_iff_mem_Ioc hn2).mpr
        (Finset.mem_Ioc.mpr ⟨hs.1, (le_min_iff.mp hs.2).1⟩)⟩

/-- Exact normalized shell on the critical line, for arbitrary coefficients.
In particular the top shell remains clipped at `N`. -/
theorem sourceDyadicPolynomial_eq_clipped_sum {N : ℕ}
    (j : Fin (sourceDyadicCount N)) (phase f : ℕ → ℂ) (t : ℝ) :
    dyadicFactorPolynomial (2^(j : ℕ) : ℝ) phase (sourceDyadicCoeff N f j) t =
      ∑ n ∈ Finset.Ioc (2^(j : ℕ)) (min (2*2^(j : ℕ)) N),
        normalizedTwistedTerm phase f n t := by
  classical
  let I := Finset.Ioc (2^(j : ℕ)) (min (2*2^(j : ℕ)) N)
  have hsub : I ⊆ realDyadicSupport (2^(j : ℕ) : ℝ) := by
    intro n hn
    have hs := Finset.mem_Ioc.mp hn
    have hlo : (2^(j : ℕ) : ℝ) < n := by exact_mod_cast hs.1
    have hhi : (n : ℝ) ≤ 2 * (2^(j : ℕ) : ℝ) := by
      exact_mod_cast (le_min_iff.mp hs.2).1
    apply mem_realDyadicSupport.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, ?_⟩, hlo.le, hhi⟩
    exact_mod_cast hhi.trans (Nat.le_ceil _)
  unfold dyadicFactorPolynomial
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro n hn
    have hg := (source_guard_iff_mem_clipped j).mpr hn
    simp [normalizedTwistedTerm, characterTwist, sourceDyadicCoeff, hg]
  · intro n hn hout
    have hg : ¬ (2 ≤ n ∧ n ≤ N ∧ (n-1).log2 = (j : ℕ)) := by
      intro hg
      exact hout ((source_guard_iff_mem_clipped j).mp hg)
    simp [normalizedTwistedTerm, characterTwist, sourceDyadicCoeff, hg]

theorem hbZetaShell_polynomial_eq_clipped_interval {q : ℕ} (X : ℝ)
    (j : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    dyadicFactorPolynomial (2^(j : ℕ) : ℝ) (fun n ↦ chi n) (hbZetaShell X j) t =
      smoothIntervalPolynomial q (2^(j : ℕ))
        (min (2*2^(j : ℕ)) (hbFactorCutoff X)) chi t := by
  change dyadicFactorPolynomial _ _ (sourceDyadicCoeff _ complexZetaAF j) _ = _
  rw [sourceDyadicPolynomial_eq_clipped_sum]
  unfold smoothIntervalPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt
    (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hn).1)
  simp [normalizedTwistedTerm, characterTwist, complexZetaAF, complexifyArithmetic,
    ArithmeticFunction.zeta_apply, hn0]

theorem hbLogShell_polynomial_eq_clipped_interval {q : ℕ} (X : ℝ)
    (j : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    dyadicFactorPolynomial (2^(j : ℕ) : ℝ) (fun n ↦ chi n) (hbLogShell X j) t =
      smoothLogIntervalPolynomial q (2^(j : ℕ))
        (min (2*2^(j : ℕ)) (hbFactorCutoff X)) chi t := by
  change dyadicFactorPolynomial _ _ (sourceDyadicCoeff _ complexLogAF j) _ = _
  rw [sourceDyadicPolynomial_eq_clipped_sum]
  unfold smoothLogIntervalPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  simp only [normalizedTwistedTerm, characterTwist, complexLogAF, complexifyArithmetic_apply,
    ArithmeticFunction.log_apply]
  ring

theorem dynamicZetaFactor_polynomial_eq_clipped_interval {q : ℕ} (X : ℝ)
    (j : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    dyadicFactorPolynomial ((dynamicZetaFactor X j).length : ℝ) (fun n ↦ chi n)
      (dynamicZetaFactor X j).coeff t =
      smoothIntervalPolynomial q (2^(j : ℕ))
        (min (2*2^(j : ℕ)) (hbFactorCutoff X)) chi t := by
  simpa only [dynamicZetaFactor, Nat.cast_pow, Nat.cast_ofNat] using
    hbZetaShell_polynomial_eq_clipped_interval X j chi t

theorem dynamicLogFactor_polynomial_eq_clipped_interval {q : ℕ} (X : ℝ)
    (j : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    dyadicFactorPolynomial ((dynamicLogFactor X j).length : ℝ) (fun n ↦ chi n)
      (dynamicLogFactor X j).coeff t =
      smoothLogIntervalPolynomial q (2^(j : ℕ))
        (min (2*2^(j : ℕ)) (hbFactorCutoff X)) chi t := by
  simpa only [dynamicLogFactor, Nat.cast_pow, Nat.cast_ofNat] using
    hbLogShell_polynomial_eq_clipped_interval X j chi t

end
end MRTDynamicD12SmoothShell
#print axioms MRTDynamicD12SmoothShell.dynamicZetaFactor_polynomial_eq_clipped_interval
#print axioms MRTDynamicD12SmoothShell.dynamicLogFactor_polynomial_eq_clipped_interval
