import JutilaTotientLogBound

/-! # Arbitrarily small logarithmic coefficient for the totient quotient

Adjoining all small integers to the Euler product replaces their contribution
by a fixed additive constant. Large prime factors are counted in base K+1.
No prime distribution theorem is used. -/
namespace MAPJutilaTotientSmallLogBound
open scoped BigOperators
open Filter Topology
open MAPJutilaTotientLogBound
noncomputable section

theorem div_totient_le_cutoff_add_log
    {K : ℕ} (hK : 2 ≤ K) (q : ℕ) (hq : 0 < q) :
    (q : ℝ)/(Nat.totient q : ℝ) ≤
      (K : ℝ) + Real.log (q : ℝ)/Real.log ((K+1 : ℕ) : ℝ) := by
  let small : Finset ℕ := Finset.Icc 2 K
  let large := q.primeFactors.filter (fun p => K < p)
  let A := small ∪ q.primeFactors
  have hA : ∀ p ∈ A, 2 ≤ p := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.mem_Icc.mp hp).1
    · exact (Nat.prime_of_mem_primeFactors hp).two_le
  have hsub : q.primeFactors ⊆ A := Finset.subset_union_right
  have hprod : (q : ℝ)/(Nat.totient q : ℝ) ≤ (A.card : ℝ)+1 := by
    rw [div_totient_eq_prod q hq]
    apply LE.le.trans _ (prod_div_pred_le_card_add_one A hA)
    apply Finset.prod_le_prod_of_subset_of_one_le hsub
    · intro p hp
      have hpR : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
      exact div_nonneg (Nat.cast_nonneg p) (by linarith)
    intro p hp hnot
    have hpR : (1 : ℝ) < p := by exact_mod_cast (show 1<p by have := hA p hp; omega)
    exact (le_div_iff₀ (by linarith : 0 < (p : ℝ)-1)).mpr (by linarith)
  have hAsub : A ⊆ small ∪ large := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact Finset.mem_union_left _ hp
    · by_cases hpK : p ≤ K
      · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).two_le,hpK⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp,by omega⟩)
  have hcardNat : A.card+1 ≤ K+large.card := by
    have hb := (Finset.card_le_card hAsub).trans (Finset.card_union_le small large)
    have hsmall : small.card = K-1 := by dsimp [small]; rw [Nat.card_Icc]; omega
    rw [hsmall] at hb
    omega
  have hcard : (A.card : ℝ)+1 ≤ (K : ℝ)+(large.card : ℝ) := by exact_mod_cast hcardNat
  have hlargeSub : large ⊆ q.primeFactors := Finset.filter_subset _ _
  have hlargePow : (K+1)^large.card ≤ q := by
    calc
      (K+1)^large.card ≤ ∏ p ∈ large, p :=
        Finset.pow_card_le_prod _ id (K+1) (fun p hp => by
          have := (Finset.mem_filter.mp hp).2
          change K+1 ≤ p
          omega)
      _ ≤ ∏ p ∈ q.primeFactors, p := Finset.prod_le_prod_of_subset_of_one_le' hlargeSub
        (fun p hp hnot => (Nat.prime_of_mem_primeFactors hp).one_le)
      _ ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  have hpowReal : (((K+1 : ℕ) : ℝ)^large.card) ≤ (q : ℝ) := by exact_mod_cast hlargePow
  have hbase : (1 : ℝ) < ((K+1 : ℕ) : ℝ) := by exact_mod_cast (show 1<K+1 by omega)
  have hlog := Real.log_le_log (pow_pos (zero_lt_one.trans hbase) _) hpowReal
  rw [Real.log_pow] at hlog
  have hcount : (large.card : ℝ) ≤ Real.log (q : ℝ)/Real.log ((K+1 : ℕ) : ℝ) :=
    (le_div_iff₀ (Real.log_pos hbase)).mpr hlog
  exact hprod.trans (hcard.trans (add_le_add le_rfl hcount))

/-- Uniformly over every positive modulus below the scale D, the quotient
q/phi(q) is eventually smaller than any fixed positive multiple of log D. -/
theorem eventually_uniform_div_totient_le_mul_log
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ D : ℝ in atTop, ∀ q : ℕ, 0 < q → (q : ℝ) ≤ D →
      (q : ℝ)/(Nat.totient q : ℝ) ≤ c*Real.log D := by
  obtain ⟨n, hn⟩ := exists_nat_ge (Real.exp (2/c))
  let K : ℕ := max 2 n
  have hK : 2 ≤ K := le_max_left _ _
  have hbase : (1 : ℝ) < ((K+1 : ℕ) : ℝ) := by exact_mod_cast (show 1<K+1 by omega)
  have hexp : Real.exp (2/c) ≤ ((K+1 : ℕ) : ℝ) :=
    hn.trans (Nat.cast_le.mpr (by dsimp [K]; omega))
  have hlogK : 2/c ≤ Real.log ((K+1 : ℕ) : ℝ) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hexp
  have hcoef : 1 ≤ (c/2)*Real.log ((K+1 : ℕ) : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlogK hc.le
    have hc0 : c ≠ 0 := hc.ne'
    field_simp [hc0] at h
    nlinarith
  filter_upwards [(Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2*(K : ℝ)/c))),
      eventually_ge_atTop (1 : ℝ)] with D hDlog hD
  intro q hq hqD
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hlogqD : Real.log (q : ℝ) ≤ Real.log D := Real.log_le_log (Nat.cast_pos.mpr hq) hqD
  have hfrac : Real.log (q : ℝ)/Real.log ((K+1 : ℕ) : ℝ) ≤ (c/2)*Real.log D := by
    apply (div_le_iff₀ (Real.log_pos hbase)).mpr
    have h := mul_le_mul_of_nonneg_right hcoef hlogD
    nlinarith
  have hconst : (K : ℝ) ≤ (c/2)*Real.log D := by
    have h := (div_le_iff₀ hc).mp hDlog
    nlinarith
  have hb := div_totient_le_cutoff_add_log hK q hq
  linarith
end
end MAPJutilaTotientSmallLogBound
#print axioms MAPJutilaTotientSmallLogBound.eventually_uniform_div_totient_le_mul_log
